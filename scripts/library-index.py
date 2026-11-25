#!/usr/bin/env python3
"""Index of the declarations of the library and of its Lean dependencies, without compiling.

Writes one Markdown line per declaration of `Incognita/` and `Statements/` (frozen statements,
listed as such; their proofs are never read) and of the packages LMLExplore, LeanMachineLearning
(LML), TauCeti and Statlib under `.lake/packages/` (never Mathlib): kind, full name (namespaces
resolved), a one-line signature (truncated), the first sentence of the docstring, `file:line`.
Lines are grouped by module, so that `grep <name> .agents/library-index.md` gives the declaration
and where it is. A section "Possible duplicates" (warnings only) lists declarations of `Incognita/`
that share their last name component with a declaration of another module, or have the same
one-line signature: the gardener reads it (AGENTS.md section 8).

The parser is a heuristic over the source text (comments and docstrings masked, declarations at
column 0, `namespace`/`section`/`end` tracked); it does not elaborate: section `variable`s,
`where` auxiliaries, generated names (anonymous instances, structure projections other than the
fields listed) and declarations made by commands (`to_additive`, `@[simps]`) are not resolved.

Usage:
  python3 scripts/library-index.py [--repo DIR] [--ref REF] [--packages DIR] [--out FILE]
                                   [--max-bytes N] [--no-packages]
With --ref, `Incognita/` and `Statements/` are read from that commit of the repository (git
cat-file, no checkout); otherwise from the working tree of --repo. The packages are read from
--packages (default `<repo>/.lake/packages`); a missing package is skipped and named in the header.
Owner request of 2026-11-25 (a searchable index of the library, so that agents reuse it).
"""
import argparse
import bisect
import os
import re
import subprocess
import sys
from collections import defaultdict

PACKAGES = ["LMLExplore", "LeanMachineLearning", "TauCeti", "Statlib"]
PKG_SHORT = {"LeanMachineLearning": "LML"}
# Directories of a package that are not part of its library.
SKIP_DIRS = {".lake", ".git", ".github", "test", "tests", "Test", "scripts", "docs", "doc",
             "blueprint", "home_page", "Archive", "Counterexamples", "Exploration", "examples",
             "Examples", "bench", "Bench"}
KINDS = {"theorem": "thm", "lemma": "lemma", "def": "def", "abbrev": "abbrev",
         "structure": "structure", "class": "class", "class inductive": "class",
         "inductive": "inductive", "instance": "instance", "axiom": "axiom", "opaque": "opaque",
         "alias": "alias", "irreducible_def": "def"}
MODIFIERS = {"private", "protected", "noncomputable", "nonrec", "partial", "unsafe", "public",
             "meta", "scoped", "local"}
WORD = re.compile(r"[A-Za-z_][\w']*")
IDENT = re.compile(r"«[^»]*»|[^\s:()\[\]{}⦃⦄⟨⟩,]+")
OPEN = "([{⦃⟨"
CLOSE = ")]}⦄⟩"
DEFAULT_MAX_BYTES = 1_000_000


# ---------------------------------------------------------------- masking comments and strings
def mask(src):
    """(masked text, docstrings): comments and string contents replaced by spaces (newlines kept,
    so offsets and line numbers are those of the source); docstrings as (start, end, text) with
    `kind` '-' for `/--` and '!' for `/-!`."""
    out = list(src)
    docs = []
    i, n = 0, len(src)

    def blank(a, b):
        for k in range(a, b):
            if out[k] != "\n":
                out[k] = " "

    while i < n:
        c = src[i]
        if c == "-" and src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            blank(i, j)
            i = j
        elif c == "/" and src.startswith("/-", i):
            kind = src[i + 2] if i + 2 < n and src[i + 2] in "-!" else ""
            depth, j = 1, i + 2
            while j < n and depth:
                if src.startswith("/-", j):
                    depth += 1
                    j += 2
                elif src.startswith("-/", j):
                    depth -= 1
                    j += 2
                else:
                    j += 1
            if kind:
                docs.append((i, j, kind, src[i + 3:j - 2]))
            blank(i, j)
            i = j
        elif c == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            blank(i + 1, min(j, n))
            i = j + 1
        elif c == "'" and (i == 0 or not (src[i - 1].isalnum() or src[i - 1] in "_'.!?")):
            # a character literal 'x' or '\n' (a prime after an identifier is part of the name)
            m = re.match(r"'(\\.|[^\\'\n])'", src[i:i + 4])
            if m:
                blank(i + 1, i + m.end() - 1)
                i += m.end()
            else:
                i += 1
        else:
            i += 1
    return "".join(out), docs


def first_sentence(doc, cap):
    text = re.sub(r"\s+", " ", doc).strip()
    if not text:
        return ""
    m = re.search(r"(?<=[.!?])\s(?=[A-Z`$(\[*])", text)
    para = re.split(r"\s{2,}", doc.strip())[0]
    if m:
        text = text[:m.start()]
    elif len(para) < len(doc.strip()):
        text = re.sub(r"\s+", " ", para)
    return truncate(text, cap)


def truncate(s, cap):
    if cap is None or len(s) <= cap:
        return s
    return s[:max(cap - 1, 0)].rstrip() + "…"


def oneline(s):
    return re.sub(r"\s+", " ", s).strip()


# ---------------------------------------------------------------- parsing one file
def skip_attrs(text, p):
    """Skip attributes `@[...]` (balanced brackets, several lines allowed) and whitespace."""
    attrs = []
    while text.startswith("@[", p):
        depth, j = 0, p + 1
        while j < len(text):
            if text[j] == "[":
                depth += 1
            elif text[j] == "]":
                depth -= 1
                if depth == 0:
                    break
            j += 1
        attrs.append(text[p + 2:j])
        p = j + 1
        while p < len(text) and text[p] in " \t\n":
            p += 1
    return p, attrs


def read_signature(text, p, limit=4000):
    """The text from p to the end of the header: `:=` or `where` at depth 0, a line starting a
    `|` (pattern matching, constructors), `deriving`, or a line at column 0."""
    depth, j, n = 0, p, min(len(text), p + limit)
    while j < n:
        c = text[j]
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth = max(depth - 1, 0)
        elif c == "\n":
            k = j + 1
            if k < len(text) and text[k] not in " \t\n":
                break
            rest = text[k:k + 80].lstrip(" \t")
            if depth == 0 and (rest.startswith("|") or rest.startswith("deriving ")):
                break
        elif depth == 0:
            if text.startswith(":=", j):
                break
            if text.startswith("where", j) and (j == 0 or text[j - 1] in " \t\n") \
                    and (j + 5 >= len(text) or not (text[j + 5].isalnum() or text[j + 5] in "_'")):
                break
        j += 1
    return text[p:j], j


def fields_after(text, j, kind):
    """Field names of a structure or class (`where` block), constructor names of an inductive."""
    names = []
    lines = text[j:].split("\n")
    if kind in ("structure", "class"):
        if not text.startswith("where", j):
            return names
        indent = None
        for ln in lines[1:]:
            if not ln.strip():
                continue
            if ln[0] not in " \t":
                break
            ind = len(ln) - len(ln.lstrip())
            if indent is None:
                indent = ind
            if ind != indent:
                continue
            s = ln.strip()
            if "::" in s.split(":=")[0] and re.match(r"^[\w']+\s*::", s):
                continue  # the constructor's name
            m = re.match(r"^\(?\s*((?:[\w'.]+\s+)*[\w'.]+)\s*(?:[({\[⦃][^:]*)?:(?!=)", s)
            if m:
                names.extend(m.group(1).split())
    elif kind == "inductive":
        for ln in lines[1:]:
            s = ln.strip()
            if not s:
                continue
            if ln[0] not in " \t|":
                break
            m = re.match(r"^\|\s*([^\s:(\[{]+)", s)
            if m:
                names.append(m.group(1))
    return names


def parse_file(src, module, path, frozen=False, sig_cap=4000):
    """The declarations of one Lean file: dicts with kind, name, sig, doc, line, private,
    deprecated, fields, module, path."""
    text, docs = mask(src)
    doc_by_end = {}
    for (a, b, k, body) in docs:
        if k == "-":
            doc_by_end[b] = body
    module_title = ""
    for (a, b, k, body) in docs:
        if k == "!":
            t = body.strip().splitlines()[0] if body.strip() else ""
            module_title = re.sub(r"^#+\s*", "", t).strip()
            break
    scopes = []  # list of (kind, [name parts])
    decls = []
    line_starts = [0] + [m.end() for m in re.finditer("\n", text)]
    done = -1  # end of the last header read: its attribute lines are not read again
    for p0 in line_starts:
        if p0 < done or p0 >= len(text) or text[p0] in " \t\n":
            continue
        p, attrs = skip_attrs(text, p0)
        mods = []
        while True:
            m = WORD.match(text, p)
            if not m or m.group(0) not in MODIFIERS:
                break
            mods.append(m.group(0))
            p = m.end()
            while p < len(text) and text[p] in " \t":
                p += 1
        m = WORD.match(text, p)
        if not m:
            continue
        w = m.group(0)
        rest = text[m.end():text.find("\n", m.end()) if "\n" in text[m.end():] else len(text)]
        if w == "namespace":
            nm = rest.strip().split()
            if nm:
                scopes.append(("namespace", nm[0].split(".")))
            continue
        if w == "section":
            scopes.append(("section", []))
            continue
        if w == "mutual":
            scopes.append(("mutual", []))
            continue
        if w == "end":
            if scopes:
                scopes.pop()
            continue
        kw = w
        q = m.end()
        if w == "class" and re.match(r"\s+inductive\b", text[q:]):
            kw = "class inductive"
            q = text.index("inductive", q) + len("inductive")
        if kw not in KINDS:
            continue
        kind = KINDS[kw]
        while q < len(text) and text[q] in " \t\n":
            q += 1
        names = []
        if kind == "alias":
            if text.startswith("⟨", q):
                e = text.find("⟩", q)
                names = [x.strip() for x in text[q + 1:e].split(",") if x.strip() and x.strip() != "_"]
                q = e + 1
            else:
                mm = IDENT.match(text, q)
                if mm:
                    names = [mm.group(0)]
                    q = mm.end()
        elif kind == "instance":
            if text.startswith("(priority", q):
                e = text.find(")", q)
                q = len(text) if e < 0 else e + 1
                while q < len(text) and text[q] in " \t\n":
                    q += 1
            mm = IDENT.match(text, q)
            if mm and not mm.group(0).startswith(":"):
                names = [mm.group(0)]
                q = mm.end()
            else:
                names = [None]
        else:
            mm = IDENT.match(text, q)
            if not mm:
                continue
            names = [mm.group(0)]
            q = mm.end()
        sig_raw, j = read_signature(text, q, sig_cap)
        done = j
        lineno = bisect.bisect_right(line_starts, m.start())
        sig = oneline(sig_raw)
        if kind == "alias":
            sig = oneline(text[q:text.find("\n", q)]) if "\n" in text[q:] else oneline(text[q:])
        fields = fields_after(text, j, kind) if kind in ("structure", "class", "inductive") else []
        # the docstring: the last one ending before the attributes, with only blanks between
        doc = ""
        k = p0
        while k > 0 and src[k - 1] in " \t\r\n":
            k -= 1
        if k in doc_by_end:
            doc = doc_by_end[k]
        ns = [x for (_, parts) in scopes for x in parts]
        deprecated = any(a.strip().startswith("deprecated") for a in attrs)
        for nm in names:
            if nm is None:
                full = None
            else:
                nm = nm.replace("«", "").replace("»", "")
                full = nm[len("_root_."):] if nm.startswith("_root_.") else ".".join(ns + [nm])
            decls.append({
                "kind": "frozen" if frozen and kind in ("thm", "lemma") else kind,
                "name": full, "sig": sig, "doc": doc, "line": lineno,
                "private": "private" in mods, "deprecated": deprecated, "fields": fields,
                "module": module, "path": path, "title": module_title})
    return decls


# ---------------------------------------------------------------- sources
def module_of(rel):
    return rel[:-len(".lean")].replace("/", ".").replace("\\", ".")


def git_files(repo, ref, roots):
    out = subprocess.run(["git", "-C", repo, "ls-tree", "-r", "--name-only", ref, "--"] + roots,
                         capture_output=True, text=True, check=True).stdout.split("\n")
    paths = [p for p in out if p.endswith(".lean")]
    if not paths:
        return []
    proc = subprocess.run(["git", "-C", repo, "cat-file", "--batch"],
                          input="".join(f"{ref}:{p}\n" for p in paths).encode(),
                          capture_output=True, check=True)
    data, pos, res = proc.stdout, 0, []
    for p in paths:
        nl = data.index(b"\n", pos)
        header = data[pos:nl].split()
        pos = nl + 1
        if len(header) < 3 or header[1] != b"blob":
            continue
        size = int(header[2])
        res.append((p, data[pos:pos + size].decode("utf-8", "replace")))
        pos += size + 1
    return res


def fs_files(base, roots, skip_dirs=frozenset()):
    res = []
    for root in roots:
        top = os.path.join(base, root)
        if os.path.isfile(top) and top.endswith(".lean"):
            with open(top, encoding="utf-8", errors="replace") as f:
                res.append((root, f.read()))
            continue
        for d, subdirs, files in os.walk(top):
            subdirs[:] = sorted(s for s in subdirs if s not in skip_dirs and not s.startswith("."))
            for fn in sorted(files):
                if fn.endswith(".lean"):
                    full = os.path.join(d, fn)
                    rel = os.path.relpath(full, base).replace("\\", "/")
                    with open(full, encoding="utf-8", errors="replace") as f:
                        res.append((rel, f.read()))
    return res


def package_files(pkg_dir):
    """The library files of a package: every .lean file outside the skipped directories, except
    the lakefile."""
    roots = sorted(x for x in os.listdir(pkg_dir)
                   if x not in SKIP_DIRS and not x.startswith(".")
                   and (os.path.isdir(os.path.join(pkg_dir, x)) or x.endswith(".lean"))
                   and x not in ("lakefile.lean",))
    return fs_files(pkg_dir, roots, SKIP_DIRS)


def collect(repo, ref, packages_dir, use_packages=True):
    groups = []  # (source label, prefix of paths, decls)
    roots = ["Incognita", "Statements"]
    files = git_files(repo, ref, roots) if ref else fs_files(repo, roots)
    decls = []
    for rel, src in files:
        if rel.startswith("Incognita/") or rel.startswith("Statements/"):
            decls += parse_file(src, module_of(rel), rel, frozen=rel.startswith("Statements/"))
    groups.append(("Incognita", decls))
    found, missing = [], []
    if use_packages:
        for pkg in PACKAGES:
            d = os.path.join(packages_dir, pkg)
            if not os.path.isdir(d):
                missing.append(pkg)
                continue
            found.append(pkg)
            pdecls = []
            for rel, src in package_files(d):
                pdecls += [dict(x, path=f".lake/packages/{pkg}/{rel}")
                           for x in parse_file(src, module_of(rel), rel)]
            groups.append((pkg, pdecls))
    return groups, found, missing


# ---------------------------------------------------------------- duplicates
GENERIC_TAILS = {"ext", "mk", "of", "map", "comp", "id", "refl", "symm", "trans", "le", "lt",
                 "measurable", "continuous", "integrable", "pos", "nonneg", "def", "eq", "iff",
                 "mono", "zero", "one", "add", "mul", "sub", "neg", "inv", "aux", "main",
                 "toFun", "coe", "val", "property", "out", "spec", "intro", "elim"}


def tail(name):
    return name.rsplit(".", 1)[-1]


def norm_sig(s):
    return re.sub(r"\s+", " ", s).strip()


def is_own(d):
    return d["path"].startswith("Incognita/")


def duplicates(all_decls, max_items=200):
    """Warnings: (reason, [decls]) for declarations of Incognita/ that share their last name
    component with a declaration of another module, or have the same one-line signature."""
    pool = [d for d in all_decls if d["name"] and not d["deprecated"] and not d["private"]
            and d["kind"] not in ("alias", "instance", "frozen")]
    declared = {d["name"] for d in all_decls if d["name"]}
    proofs = set()
    for d in all_decls:
        m = re.match(r"Incognita\.Statements\.(P\d+)\.(.+)$", d["name"] or "")
        if d["kind"] == "frozen" and m:
            proofs |= {f"Incognita.{m.group(1)}.{m.group(2)}{s}" for s in ("", "_false")}
    by_tail = defaultdict(list)
    for d in pool:
        by_tail[tail(d["name"])].append(d)
    out, seen = [], set()
    rank = {"def": 0, "abbrev": 0, "structure": 0, "class": 0, "inductive": 0, "opaque": 0,
            "axiom": 0, "thm": 1, "lemma": 1, "frozen": 2}
    for t, ds in by_tail.items():
        if t in GENERIC_TAILS or len(t) < 5:
            continue
        if not any(is_own(d) for d in ds):
            continue
        mods = {d["module"] for d in ds}
        if len(mods) < 2 or len(mods) > 4:
            continue  # same module: overloads in namespaces; many modules: a generic API name
        # the proof of a frozen statement has its name by rule (often a wrapper of a lemma)
        ds = [d for d in ds if d["name"] not in proofs]
        # `A.foo` and `B.foo` with `A`, `B` declared types: the API of two types (dot notation)
        parents = {d["name"].rsplit(".", 1)[0] for d in ds if "." in d["name"]}
        if len(parents) == len(ds) and all(x in declared for x in parents):
            continue
        if len({d["module"] for d in ds}) < 2:
            continue
        key = tuple(sorted(d["name"] for d in ds))
        if key in seen:
            continue
        seen.add(key)
        out.append((min(rank.get(d["kind"], 1) for d in ds), "same name", ds))
    by_sig = defaultdict(list)
    for d in pool:
        s = norm_sig(d["sig"])
        # a statement proved twice; witnesses `_satisfiable` are one per frozen statement by rule
        if len(s) >= 30 and d["kind"] in ("thm", "lemma") and d["name"] not in proofs \
                and not d["name"].endswith("_satisfiable"):
            by_sig[(rank.get(d["kind"], 1), s)].append(d)
    for (r, s), ds in by_sig.items():
        if len({d["name"] for d in ds}) < 2 or not any(is_own(d) for d in ds):
            continue
        key = tuple(sorted(d["name"] for d in ds))
        if key in seen:
            continue
        seen.add(key)
        out.append((r, "same signature", ds))
    out.sort(key=lambda x: (x[0], x[1], tail(x[2][0]["name"])))
    return [(why, ds) for (_, why, ds) in out[:max_items]], len(out)


# ---------------------------------------------------------------- rendering
LEVELS = [  # (signature cap for Incognita, for packages, docstring cap, docs for package lemmas)
    (160, 160, 140, True),
    (110, 90, 110, True),
    (110, 0, 100, True),
    (0, 0, 90, True),
    (0, 0, 80, False),
]


def render_decl(d, sig_cap, doc_cap):
    kind = d["kind"] + (" (private)" if d["private"] else "") + \
        (" (deprecated)" if d["deprecated"] else "")
    name = f"`{d['name']}`" if d["name"] else "(anonymous)"
    parts = [f"- {kind} {name}"]
    if sig_cap and d["sig"]:
        parts.append(f" `{truncate(d['sig'].replace('`', ''), sig_cap)}`")
    if d["fields"]:
        f = d["fields"]
        parts.append(f" {{{', '.join(f[:8])}{', …' if len(f) > 8 else ''}}}")
    if doc_cap:
        s = first_sentence(d["doc"], doc_cap)
        if s:
            parts.append(f" — {s}")
    parts.append(f" ({d['path']}:{d['line']})")
    return "".join(parts)


def render(groups, found, missing, dups, ndups, ref, level, max_bytes):
    sig_own, sig_pkg, doc_cap, pkg_lemma_docs = LEVELS[level]
    total = sum(len(ds) for _, ds in groups)
    head = ["# Library index",
            "",
            "Declarations of `Incognita/`, `Statements/` (frozen statements) and of the "
            "dependencies " + (", ".join(f"`{p}`" for p in found) or "(none)") +
            " (never Mathlib: search it with Grep, path `.lake/packages/mathlib/Mathlib`), "
            "generated by `scripts/library-index.py` without compiling"
            + (f" at `{ref[:12]}`" if ref else "") + ". One line per declaration: kind, full "
            "name, signature (truncated), first sentence of the docstring, `file:line`. "
            "**Search it before writing a general lemma or a definition** "
            "(`grep -n -i <word> .agents/library-index.md`), then read the file it points to: "
            "the heuristic parser does not elaborate (section variables, generated names, "
            "`to_additive` are missing).",
            ""]
    if missing:
        head += [f"Not indexed (not found under `.lake/packages/`): "
                 f"{', '.join(f'`{p}`' for p in missing)}.", ""]
    head += [f"{total} declarations; detail level {level} of {len(LEVELS) - 1} "
             f"(signatures {'cut at ' + str(sig_own) + ' characters' if sig_own else 'dropped'}"
             f"{'' if sig_pkg == sig_own else ' in Incognita, ' + ('cut at ' + str(sig_pkg) if sig_pkg else 'dropped') + ' in the packages'}"
             f", to stay under {max_bytes} bytes).", ""]
    body = ["## Possible duplicates", "",
            "Warnings, never errors: declarations of `Incognita/` that share their last name "
            "component with a declaration of another module, or have the same one-line "
            "signature. Many are different objects under the same name (then one name should "
            "change, or an equivalence lemma relate them); the gardener examines them "
            "(AGENTS.md section 8)."
            + (f" Showing {len(dups)} of {ndups}." if ndups > len(dups) else ""), ""]
    if not dups:
        body.append("None found.")
    for why, ds in dups:
        body.append(f"- {why}: " + "; ".join(
            f"{d['kind']} `{d['name']}` ({d['path']}:{d['line']})" for d in ds))
    body.append("")
    for label, ds in groups:
        if not ds:
            continue
        short = PKG_SHORT.get(label, label)
        body += [f"# {label}" + (f" ({short})" if short != label else ""), ""]
        by_mod = defaultdict(list)
        for d in ds:
            by_mod[d["module"]].append(d)
        own = label == "Incognita"
        for mod in sorted(by_mod):
            title = by_mod[mod][0]["title"]
            body.append(f"## {mod}" + (f": {truncate(title, 80)}" if title else ""))
            for d in sorted(by_mod[mod], key=lambda x: x["line"]):
                dc = doc_cap if (own or pkg_lemma_docs or d["kind"] not in ("thm", "lemma")) else 0
                body.append(render_decl(d, sig_own if own else sig_pkg, dc))
            body.append("")
    return "\n".join(head + body) + "\n"


def build(groups, found, missing, ref, max_bytes):
    all_decls = [d for _, ds in groups for d in ds]
    dups, ndups = duplicates(all_decls)
    for level in range(len(LEVELS)):
        text = render(groups, found, missing, dups, ndups, ref, level, max_bytes)
        if len(text.encode()) <= max_bytes:
            return text
    data = text.encode()[:max_bytes]
    cut = data.rfind(b"\n")
    return data[:cut].decode("utf-8", "ignore") + \
        "\n\n(The index was cut at the size cap: search the sources with Grep for the rest.)\n"


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--repo", default=".")
    ap.add_argument("--ref", default="")
    ap.add_argument("--packages", default="")
    ap.add_argument("--out", default="-")
    ap.add_argument("--max-bytes", type=int, default=DEFAULT_MAX_BYTES)
    ap.add_argument("--no-packages", action="store_true")
    a = ap.parse_args(argv)
    pk = a.packages or os.path.join(a.repo, ".lake", "packages")
    groups, found, missing = collect(a.repo, a.ref, pk, not a.no_packages)
    text = build(groups, found, missing, a.ref, a.max_bytes)
    if a.out == "-":
        sys.stdout.buffer.write(text.encode("utf-8"))
    else:
        with open(a.out, "w", encoding="utf-8", newline="\n") as f:
            f.write(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
