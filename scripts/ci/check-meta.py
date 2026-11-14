#!/usr/bin/env python3
"""Fail on metaprogramming and compiler escapes in the project's Lean sources.

Usage: python3 scripts/ci/check-meta.py [path ...]

Without arguments, checks `Incognita/`, `Statements/`, `Exploration/` and their root files
(`Incognita.lean`, `Statements.lean`, `Exploration.lean`), from the repository root. CI runs it
before any build: code that runs at elaboration time could otherwise act on the runner or forge
declarations the kernel never checked.

Forbidden (decision D9 of Incognita v3): `#eval`, `run_cmd`, `run_elab`, `run_meta`, `run_tac`,
`by_elab`, `elab`, `elab_rules`, `macro`, `macro_rules`, `syntax`, `initialize`,
`builtin_initialize`, `unsafe`, `meta`, `implemented_by`, `extern`, `set_option`, `simproc`,
`dsimproc` (and their `_decl` forms), `native_decide`, every `register_*` and `declare_*`
command, and the attributes that extend Lean (`command_elab`, `term_elab`, `tactic`, `delab`,
`app_unexpander`, `env_linter`, `init`, `export`, `csimp`, `builtin_*`, ...), as `@[...]` or
`attribute [...]`.

Words are matched as whole identifiers (`elaborate` or `my_macro_lemma` are fine). Comments,
docstrings included, are ignored: an English docstring may say "initialized" or "syntax". String
literals are NOT ignored (a forbidden word inside a string fails, which is the safe side), and a
string literal containing `--`, `/-` or `-/` fails too: such a string could declare a notation
token that hides code from this comment-aware check.
"""

import re
import sys
from pathlib import Path

DEFAULT_PATHS = ["Incognita", "Statements", "Exploration",
                 "Incognita.lean", "Statements.lean", "Exploration.lean"]

WORDS = [
    "run_cmd", "run_elab", "run_meta", "run_tac", "by_elab",
    "elab", "elab_rules", "macro", "macro_rules", "syntax", "initialize", "builtin_initialize",
    "unsafe", "meta", "implemented_by", "extern", "set_option",
    "simproc", "dsimproc", "simproc_decl", "dsimproc_decl", "builtin_simproc", "builtin_dsimproc",
    "native_decide",
]
PREFIXES = ["register_", "declare_"]

ATTRIBUTES = {
    "command_elab", "term_elab", "tactic", "delab", "app_unexpander", "app_delab", "env_linter",
    "init", "export", "csimp", "code_action", "hole_code_action", "command_code_action",
    "tactic_code_action", "widget_module", "server_rpc_method", "incremental", "implemented_by",
    "extern", "macro", "simproc", "simprocs", "term_parser", "command_parser", "tactic_parser",
    "run_builtin_parser_attribute_hooks", "run_parser_attribute_hooks", "combinator_formatter",
    "combinator_parenthesizer", "formatter", "parenthesizer", "category_parenthesizer",
    "eval", "sevalprocs", "seval",
}

IDENT_CHAR = re.compile(r"[\w'!?₀-ₜᵢ-ᵪⱼ]")
CHAR_LIT = re.compile(r"'(\\(x[0-9a-fA-F]{2}|u\{?[0-9a-fA-F]+\}?|.)|[^\\'\n])'")
WORD_RE = re.compile(
    r"(?<![\w'.!?])(" + "|".join(re.escape(w) for w in sorted(WORDS, key=len, reverse=True))
    + r"|(?:" + "|".join(PREFIXES) + r")\w+)(?![\w'!?])")
EVAL_RE = re.compile(r"#eval(?![\w'])")
ATTR_RE = re.compile(r"(@\[|(?<![\w'.])attribute\s*\[)([^\]]*)\]", re.S)
ENTRY_HEAD = re.compile(r"^\s*(?:(?:local|scoped)\s+)?-?\s*([\w'.!?]+)")


class LexError(Exception):
    pass


def is_ident_char(ch):
    return bool(IDENT_CHAR.match(ch))


def blank(s):
    return "".join("\n" if c == "\n" else " " for c in s)


def scan_string(text, i, strings):
    """`text[i]` is the opening quote of an ordinary string. Returns the index after its end.
    Braces are read as interpolations, possibly with nested strings: for a string that is not
    interpolated this can only make the string look longer than it is (the safe side)."""
    n = len(text)
    j = i + 1
    depth = 0
    while j < n:
        c = text[j]
        if c == "\\":
            j += 2
            continue
        if depth == 0:
            if c == '"':
                strings.append((i, j + 1))
                return j + 1
            if c == "{":
                depth = 1
            j += 1
            continue
        # inside an interpolation
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
        elif c == '"':
            j = scan_string(text, j, strings)
            continue
        j += 1
    raise LexError("unterminated string literal")


def strip_comments(text):
    """The text with comments blanked out (line numbers kept), and the string literal spans."""
    out = []
    strings = []
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(blank(text[i:j]))
            i = j
            continue
        if text.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth > 0:
                if text.startswith("/-", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("-/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            if depth > 0:
                raise LexError("unterminated comment")
            out.append(blank(text[i:j]))
            i = j
            continue
        prev_ident = i > 0 and is_ident_char(text[i - 1])
        if c == "r" and not prev_ident:
            m = re.match(r'r(#*)"', text[i:])
            if m:
                close = '"' + m.group(1)
                j = text.find(close, i + len(m.group(0)))
                if j < 0:
                    raise LexError("unterminated raw string literal")
                j += len(close)
                strings.append((i, j))
                out.append(text[i:j])
                i = j
                continue
        if c == '"':
            j = scan_string(text, i, strings)
            out.append(text[i:j])
            i = j
            continue
        if c == "'" and not prev_ident:
            m = CHAR_LIT.match(text, i)
            if m:
                out.append(text[i:m.end()])
                i = m.end()
                continue
        if c == "«":  # «identifier»
            j = text.find("»", i)
            if j < 0:
                raise LexError("unterminated «")
            out.append(text[i:j + 1])
            i = j + 1
            continue
        out.append(c)
        i += 1
    return "".join(out), strings


def line_of(text, pos):
    return text.count("\n", 0, pos) + 1


def check_text(text):
    """Problems of one source text, as (line, message)."""
    try:
        code, strings = strip_comments(text)
    except LexError as e:
        return [(0, f"cannot be checked: {e}")]
    problems = []
    for a, b in strings:
        s = text[a:b]
        if "--" in s or "/-" in s or "-/" in s:
            problems.append((line_of(text, a), "string literal containing a comment marker"))
    for m in WORD_RE.finditer(code):
        problems.append((line_of(code, m.start()), f"'{m.group(1)}' is forbidden"))
    for m in EVAL_RE.finditer(code):
        problems.append((line_of(code, m.start()), "'#eval' is forbidden"))
    for m in ATTR_RE.finditer(code):
        for entry in m.group(2).split(","):
            h = ENTRY_HEAD.match(entry)
            if not h:
                continue
            name = h.group(1)
            if name in ATTRIBUTES or name.startswith("builtin_"):
                problems.append((line_of(code, m.start()), f"attribute '{name}' is forbidden"))
    return sorted(set(problems))


def lean_files(paths):
    for p in paths:
        path = Path(p)
        if path.is_dir():
            yield from sorted(path.rglob("*.lean"))
        elif path.is_file():
            yield path


def main(argv):
    paths = argv[1:] or DEFAULT_PATHS
    failures = 0
    files = 0
    for f in lean_files(paths):
        files += 1
        text = f.read_text(encoding="utf-8")
        for line, msg in check_text(text):
            print(f"{f.as_posix()}:{line}: {msg}")
            failures += 1
    if failures:
        print(f"check-meta: {failures} problems in the Lean sources: metaprogramming, compiler "
              "escapes and set_option are not allowed here (scripts/ci/check-meta.py)",
              file=sys.stderr)
        return 1
    print(f"check-meta: {files} Lean files checked, no metaprogramming")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
