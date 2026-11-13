#!/usr/bin/env python3
"""Write, on standard output, the Markdown summary of a pull request for the human who merges it.

The summary is the pull request's description (where agents put their results in mathematical form,
see scripts/agent.sh), followed by the Lean statements that the pull request adds or changes in the
library (`Incognita/`) and in the frozen statements (`Statements/`): each declaration whose header
touches an added line, with its docstring and its signature, without the proof. CI turns it into a
PDF (.github/workflows/summary.yml).

Environment: PR_TITLE, PR_BODY, PR_URL, BASE_SHA, HEAD_SHA.
"""
import os
import re
import subprocess

DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|unsafe|partial)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|instance|inductive|axiom|opaque)\b")


def git(*args):
    return subprocess.run(["git", *args], capture_output=True, text=True, check=True).stdout


def added_lines(base, head, path):
    """Line numbers, in the head version of `path`, of the lines added by the pull request."""
    out = git("diff", "-U0", base, head, "--", path)
    lines = set()
    for m in re.finditer(r"^@@ -\d+(?:,\d+)? \+(\d+)(?:,(\d+))? @@", out, re.M):
        start, count = int(m.group(1)), int(m.group(2) or "1")
        lines.update(range(start, start + count))
    return lines


def declarations(text):
    """(first line, last line, text) of each declaration header: docstring, then signature up to
    `:=` or `where` (1-based line numbers)."""
    lines = text.split("\n")
    result = []
    i = 0
    while i < len(lines):
        if DECL.match(lines[i]):
            start = i
            # include the docstring just above
            j = i - 1
            if j >= 0 and lines[j].rstrip().endswith("-/"):
                while j >= 0 and not lines[j].lstrip().startswith("/--"):
                    j -= 1
                if j >= 0:
                    start = j
            end = i
            while end < len(lines) and ":=" not in lines[end] and not re.search(r"\bwhere\b", lines[end]):
                end += 1
            end = min(end, len(lines) - 1)
            header = "\n".join(lines[start:end + 1])
            header = re.sub(r":=.*$", ":= …", header, flags=re.S)
            result.append((start + 1, end + 1, header))
            i = end + 1
        else:
            i += 1
    return result


def main():
    base_ref, head = os.environ["BASE_SHA"], os.environ["HEAD_SHA"]
    base = git("merge-base", base_ref, head).strip()
    title = os.environ.get("PR_TITLE", "")
    body = os.environ.get("PR_BODY", "") or "(no description)"
    url = os.environ.get("PR_URL", "")

    print(f"# {title}\n")
    print(f"Pull request: <{url}>  \nCommit: `{head[:12]}`\n")
    print(body.replace("\r\n", "\n"))
    print("\n# Lean statements of this pull request\n")
    print("Declarations of `Incognita/` and `Statements/` whose header the pull request adds or "
          "changes; proofs omitted.\n")

    changed = git("diff", "--name-status", base, head, "--", "Incognita", "Statements").split("\n")
    found = False
    for row in filter(None, changed):
        status, path = row.split("\t")[0], row.split("\t")[-1]
        if not path.endswith(".lean"):
            continue
        if status.startswith("D"):
            print(f"## `{path}`\n\nDeleted.\n")
            found = True
            continue
        text = git("show", f"{head}:{path}")
        new = added_lines(base, head, path)
        decls = [d for d in declarations(text) if any(n in new for n in range(d[0], d[1] + 1))]
        if not decls:
            continue
        found = True
        print(f"## `{path}`\n")
        for _, _, header in decls:
            print("```lean")
            print(header)
            print("```\n")
    if not found:
        print("None: the pull request changes no declaration header in `Incognita/` or `Statements/`.\n")

    files = git("diff", "--name-status", base, head).strip()
    print("# Files changed\n")
    for row in filter(None, files.split("\n")):
        parts = row.split("\t")
        print(f"- `{parts[0]}` `{parts[-1]}`")


if __name__ == "__main__":
    main()
