#!/usr/bin/env python3
"""The library's metadata, computed from the repository (never written by hand).

    certify.py [--repo DIR] report [--audit FILE] [--out FILE]
        Certification of every paper on the tree (catalogue/certification.md format): level 0-3,
        conditional, re-check passes, badges "used by N" and "audited by a human".
    certify.py [--repo DIR] leanok
        papers/<P>/certification.tex for each paper (never committed): the labels whose frozen
        statement is proved (green "LEAN APPROVED" box) and the certification line of the PDF.
    certify.py [--repo DIR] bib [--check]
        papers/library.bib (keys INC-P<nnn>, with the version): generated, never committed
        (.gitignore); written before compiling a paper. --check: fail if out of date.
    certify.py [--repo DIR] check [--base REF]
        META.toml fields (roadmap: an existing roadmap), depends_on, citations of library papers,
        open questions, directions.md; with --base, the version rules and the append-only rules
        against REF (directions.md, catalogue/garden.md, errata and statement corrections).
    certify.py [--repo DIR] items ROADMAP [--free]
        Items of a roadmap (D, F, C): "<id> open|closed|covered|dropped <detail>".
    certify.py [--repo DIR] items-hash ROADMAP
    certify.py [--repo DIR] dependants
        "<P> <n>": papers depending on each paper (formalisation priority).
    certify.py [--repo DIR] depchecks
        "<D> <P><nnn>v<k>-><v>": dependencies of D revised since D cited them.
    certify.py [--repo DIR] disputed-deps
        "<D> <P>": papers depending on a disputed paper.
    certify.py [--repo DIR] add-candidates --paper DIR --report FILE --pr N --head SHA
        Append the open questions the scope referee rated as candidates to
        roadmaps/<R>/directions.md; prints the number of entries added.
    certify.py [--repo DIR] proposal --base REF --head REF
        Check a pull request of propose-roadmap; prints "new <Name> <domain> existing|new" or
        "extension <R>/X<k> <domain> existing".
    certify.py [--repo DIR] approve-roadmap --base REF --text TEXT
        Set the status of the proposal files changed since REF from proposed to approved.
    certify.py [--repo DIR] verify-scripted --kind approved|directions --parent REF --head REF
        Check that a scripted commit of the loop does only what its kind allows.
    certify.py [--repo DIR] dropped-only --base REF --head REF
        Check that the directions.md files changed since REF only gain `Dropped (` lines under
        existing entries (what garden may do), never a new entry.

Rules: AGENTS.md (sections 4, 5, 9), papers/README.md, roadmaps/README.md, catalogue/README.md.
Reads only text files and git objects; never runs anything from the repository. Python 3.11+.
"""
import argparse
import datetime
import hashlib
import os
import re
import subprocess
import sys
import tomllib

REPO_URL = "https://github.com/prevostad/Incognita"
RECHECK_TYPES = ("back-translation", "double-formalisation", "known-cases")
LEVEL_NAMES = {0: "submitted", 1: "accepted", 2: "Lean-verified", 3: "re-verified"}
PAPER_DIR = re.compile(r"^P(\d{3})-[a-z0-9][a-z0-9-]*$")
DEP_RE = re.compile(r"^P(\d{3})v(\d+):((?:def|lem|prop|thm|cor):[A-Za-z0-9_.:-]+)$")
ITEM_RE = re.compile(r"^\s*- \*\*([DF]\d+)\.")
CLOSED_RE = re.compile(r"(?i)\b(pending owner decision|on hold)\b|(?<![\w-])closed(?![\w-])")
ENTRY_RE = re.compile(r"^## (E|SC|C)(\d+)\b")
STATUS_LINE = re.compile(r"^\| Status \| \*\*([a-z]+)\*\*")
ROADMAP_NAME = re.compile(r"^[A-Z][A-Za-z0-9]+$")
INC_CITE = re.compile(r"\\cite[pt]?\*?(?:\[[^\]]*\])*\{([^}]*)\}")


class Fail(Exception):
    pass


# ---------------------------------------------------------------- reading the tree
class Tree:
    """The repository at a git ref (ref is not None) or in the working directory (ref None)."""

    def __init__(self, repo, ref=None):
        self.repo = repo
        self.ref = ref

    def git(self, *args, check=True):
        r = subprocess.run(["git", "-C", self.repo, "-c", "core.quotePath=false", *args],
                           capture_output=True, text=True)
        if check and r.returncode != 0:
            raise Fail("git %s: %s" % (" ".join(args), r.stderr.strip()))
        return r.stdout

    def read(self, path):
        if self.ref is None:
            try:
                with open(os.path.join(self.repo, path), encoding="utf-8") as f:
                    return f.read()
            except (FileNotFoundError, IsADirectoryError, NotADirectoryError):
                return None
        r = subprocess.run(["git", "-C", self.repo, "show", "%s:%s" % (self.ref, path)],
                           capture_output=True)
        return r.stdout.decode("utf-8", "replace") if r.returncode == 0 else None

    def ls(self, path):
        if self.ref is None:
            try:
                return sorted(os.listdir(os.path.join(self.repo, path)))
            except (FileNotFoundError, NotADirectoryError):
                return []
        out = self.git("ls-tree", "--name-only", "%s:%s" % (self.ref, path), check=False)
        return sorted(x for x in out.splitlines() if x)

    def exists(self, path):
        return self.read(path) is not None


def toml(text, where):
    try:
        return tomllib.loads(text)
    except tomllib.TOMLDecodeError as e:
        raise Fail("%s: invalid TOML (%s)" % (where, e))


def braced(text, start):
    """(content, end): the content of the balanced braces opening at text[start] == '{', and the
    index just after the closing brace."""
    depth, i = 0, start
    while i < len(text):
        c = text[i]
        if c == "\\":
            i += 2
            continue
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
            if depth == 0:
                return text[start + 1:i], i + 1
        i += 1
    return text[start + 1:], len(text)


def strip_comments(tex):
    return "\n".join(re.sub(r"(?<!\\)%.*", "", line) for line in tex.splitlines())


class Paper:
    def __init__(self, tree, d):
        self.dir = d
        self.num = PAPER_DIR.match(d).group(1)
        self.prefix = "P" + self.num
        meta_text = tree.read("papers/%s/META.toml" % d)
        self.meta = toml(meta_text, "papers/%s/META.toml" % d) if meta_text is not None else {}
        self.has_meta = meta_text is not None
        self.tex = tree.read("papers/%s/paper.tex" % d) or ""
        self.version = self.meta.get("version", 1)
        self.kind = self.meta.get("kind", "")
        self.roadmap = self.meta.get("roadmap", "")
        self.directions = self.meta.get("directions", [])
        self.depends_on = self.meta.get("depends_on", [])
        self.authors = self.meta.get("authors", [])
        self.human_authors = self.meta.get("human_authors", [])   # a paper of the owner (AGENTS.md 5.1)
        self.withdrawn = tree.exists("papers/%s/withdrawn.md" % d)
        self.errata = tree.read("papers/%s/errata.md" % d) or ""
        self.corrections = tree.read("papers/%s/statement-corrections.md" % d) or ""
        self.audits = tree.read("papers/%s/human-audits.md" % d) or ""

    @property
    def title(self):
        t = strip_comments(self.tex)
        m = re.search(r"\\title\s*(\[[^\]]*\])?\s*\{", t)
        if not m:
            return self.dir
        s = braced(t, m.end() - 1)[0]
        while True:
            k = s.find("\\thanks")
            j = s.find("{", k) if k >= 0 else -1
            if j < 0:
                break
            s = s[:k] + s[braced(s, j)[1]:]
        return " ".join(s.split())

    @property
    def year(self):
        m = re.search(r"\\date\{(\d{4})-\d{2}-\d{2}\}", self.tex)
        return m.group(1) if m else None

    def labels(self):
        return set(re.findall(r"\\label\{([^}]*)\}", strip_comments(self.tex)))

    def deps(self):
        """[(prefix, version, label)] of depends_on, bad entries skipped."""
        out = []
        for d in self.depends_on:
            m = DEP_RE.match(d) if isinstance(d, str) else None
            if m:
                out.append(("P" + m.group(1), int(m.group(2)), m.group(3)))
        return out

    def open_questions(self):
        """[(label, title, statement)] of the openquestion environments."""
        out = []
        t = strip_comments(self.tex)
        for m in re.finditer(r"\\begin\{openquestion\}(\[[^\]]*\])?(.*?)\\end\{openquestion\}", t, re.S):
            title = (m.group(1) or "[]")[1:-1].strip()
            body = m.group(2)
            lab = re.search(r"\\label\{(oq:[^}]*)\}", body)
            text = re.sub(r"\\label\{[^}]*\}", "", body).strip()
            out.append((lab.group(1) if lab else None, title, " ".join(text.split())))
        return out


def papers(tree):
    out = []
    for d in tree.ls("papers"):
        if PAPER_DIR.match(d) and tree.exists("papers/%s/META.toml" % d):
            out.append(Paper(tree, d))
    return out


def by_prefix(ps):
    return {p.prefix: p for p in ps}


# ---------------------------------------------------------------- errata and corrections
def entries(text, kinds=("E", "SC")):
    """[(id, revised, resolved, frozen statement or None, lines)] of a file of entries."""
    out, cur = [], None
    for line in text.splitlines():
        m = ENTRY_RE.match(line)
        if line.startswith("## "):
            if cur:
                out.append(cur)
            cur = None
            if m and m.group(1) in kinds:
                cur = [m.group(1) + m.group(2), False, False, None, [line]]
            continue
        if cur is None:
            continue
        cur[4].append(line)
        s = re.sub(r"^- ", "", line)
        if s.startswith("Revised in "):
            cur[1] = True
        elif s.startswith("Resolved by "):
            cur[2] = True
        elif line.startswith("- Frozen statement:"):
            v = line.split(":", 1)[1].strip().replace("`", "").split()
            cur[3] = v[0] if v else None
    if cur:
        out.append(cur)
    return out


def superseded(p):
    names = set()
    for e in entries(p.errata) + entries(p.corrections):
        if e[2] and e[3]:
            names.add(re.sub(r"^Incognita\.Statements\.[^.]*\.", "", e[3]))
    return names


def open_errata(p):
    return [e[0] for e in entries(p.errata) if not e[1] and not e[2]]


# ---------------------------------------------------------------- Lean status
def lean_status(tree, audit_file):
    """{(prefix, name): open|proved|refuted}, frozen statements (lock files) only."""
    st = {}
    for d in tree.ls("Statements"):
        if re.match(r"^P\d{3}$", d):
            for f in tree.ls("Statements/" + d):
                if f.endswith(".lock"):
                    st[(d, f[:-5])] = "open"
    if audit_file:
        with open(audit_file, encoding="utf-8") as f:
            for line in f:
                w = line.split()
                if len(w) == 3 and w[2] in ("open", "proved", "refuted"):
                    k = re.match(r"^(P\d{3})", w[0])
                    if k:
                        st[(k.group(1), w[1])] = w[2]
    else:
        for f in tree.ls("catalogue/results"):
            m = re.match(r"^(P\d{3})-(.+)\.toml$", f)
            if not m:
                continue
            data = toml(tree.read("catalogue/results/" + f), "catalogue/results/" + f)
            if (m.group(1), m.group(2)) in st:
                st[(m.group(1), m.group(2))] = "refuted" if data.get("status") == "refuted" else "proved"
    return st


def markers(tree):
    """{(prefix, name): marker dict} of the proof markers."""
    out = {}
    for f in tree.ls("catalogue/results"):
        m = re.match(r"^(P\d{3})-(.+)\.toml$", f)
        if m:
            try:
                out[(m.group(1), m.group(2))] = toml(tree.read("catalogue/results/" + f), f)
            except Fail:
                pass
    return out


# ---------------------------------------------------------------- gardening log
def garden_rows(tree):
    """[(date, model, paper prefix, check, outcome, main sha)] of the re-check rows of
    catalogue/garden.md (columns Date | Model | Item | Check | Outcome | Main)."""
    rows = []
    for line in (tree.read("catalogue/garden.md") or "").splitlines():
        if not line.startswith("|"):
            continue
        c = [x.strip().strip("`") for x in line.strip().strip("|").split("|")]
        if len(c) < 6 or c[3] not in RECHECK_TYPES:
            continue
        m = re.match(r"^(P\d{3})", c[2])
        if not m:
            continue
        # The documented format: "confirmed: <details>" or "failed: <details>" (catalogue/README.md).
        o = re.match(r"(confirmed|failed)\b", c[4].strip().lower())
        outcome = o.group(1) if o else ""
        rows.append((c[0], c[1], m.group(1), c[3], outcome, c[5]))
    return rows


def lib_tree(tree, sha):
    if not re.match(r"^[0-9a-f]{7,40}$", sha or ""):
        return None
    r = subprocess.run(["git", "-C", tree.repo, "rev-parse", "--verify", "-q", "%s^{commit}:Incognita" % sha],
                       capture_output=True, text=True)
    return r.stdout.strip() if r.returncode == 0 else None


def counted_rechecks(tree, rows):
    """The passes that bring something new: a check type or a model not seen before for this
    paper, or the library (Incognita/) changed since the last counted pass."""
    counted, types, models, last_tree = [], set(), set(), None
    for r in rows:
        if r[4] != "confirmed":
            continue
        t = lib_tree(tree, r[5])
        changed = t is not None and last_tree is not None and t != last_tree
        if not counted or r[3] not in types or r[1] not in models or changed:
            counted.append(r)
            types.add(r[3])
            models.add(r[1])
            if t is not None:
                last_tree = t
    return counted


# ---------------------------------------------------------------- referees (merge trailers)
def referees(tree, p):
    """"both referees" if the commit that last changed paper.tex was merged by the loop after both
    referees accepted (trailer Incognita-Reviews), "the owner" otherwise, None without git."""
    r = subprocess.run(["git", "-C", tree.repo, "log", "-1", "--format=%B", tree.ref or "HEAD", "--",
                        "papers/%s/paper.tex" % p.dir], capture_output=True, text=True)
    if r.returncode != 0 or not r.stdout.strip():
        return None
    if re.search(r"^Incognita-Reviews: .*referee-scope=accept.*referee-proofs=accept", r.stdout, re.M):
        return "both referees"
    return "the owner"


# ---------------------------------------------------------------- certification
class Cert:
    pass


def certify(tree, audit_file=None):
    ps = papers(tree)
    idx = by_prefix(ps)
    st = lean_status(tree, audit_file)
    rows = garden_rows(tree)
    certs = {}
    for p in ps:
        c = Cert()
        c.paper = p
        sup = superseded(p)
        frozen = {n: s for (pp, n), s in st.items() if pp == p.prefix and n not in sup}
        c.frozen = frozen
        c.verified = bool(frozen) and all(s == "proved" for s in frozen.values())
        prows = [r for r in rows if r[2] == p.prefix]
        c.rechecks = counted_rechecks(tree, prows)
        last = prows[-1] if prows else None
        c.recheck_failed = bool(last and last[4] == "failed")
        refuted = [n for n, s in frozen.items() if s == "refuted"]
        c.disputed_why = []
        if open_errata(p):
            c.disputed_why.append("errata " + " ".join(open_errata(p)))
        if refuted:
            c.disputed_why.append("refuted " + " ".join(sorted(refuted)))
        if c.recheck_failed:
            c.disputed_why.append("re-check failed (%s, %s)" % (last[3], last[0]))
        c.referees = referees(tree, p)
        if p.withdrawn:
            c.own = 0
            c.status = "withdrawn"
        elif c.disputed_why:
            c.own = 0
            c.status = "disputed"
        else:
            c.own = 3 if c.verified and c.rechecks else 2 if c.verified else 1
            c.status = LEVEL_NAMES[c.own]
        certs[p.prefix] = c
    # Caps by dependencies (a dependency missing from the library caps at 0).
    memo = {}

    def eff(pref, stack=()):
        if pref in memo:
            return memo[pref]
        if pref not in certs or pref in stack:
            return 0
        c = certs[pref]
        v = c.own
        for (dp, _k, _l) in c.paper.deps():
            v = min(v, eff(dp, stack + (pref,)))
        memo[pref] = v
        return v

    for pref, c in certs.items():
        c.level = eff(pref)
        c.conditional = [d for d in c.paper.deps() if eff(d[0]) < 2]
        c.capped = c.level < c.own
        c.used_by = sorted(q.prefix for q in ps if q.prefix != pref and certs[q.prefix].verified
                           and any(d[0] == pref for d in q.deps()))
        c.dependants = sorted(q.prefix for q in ps if any(d[0] == pref for d in q.deps()))
        c.human = []
        for line in c.paper.audits.splitlines():
            m = re.match(r"^- (.+?), (\d{4}-\d{2}-\d{2}), v(\d+)(:.*)?$", line.strip())
            if m:
                c.human.append((m.group(1), m.group(2), int(m.group(3))))
        c.outdated_deps = [(d, idx[d[0]].version) for d in c.paper.deps()
                           if d[0] in idx and idx[d[0]].version > d[1]]
    return ps, certs


def level_text(c):
    if c.status in ("withdrawn", "disputed"):
        return "0 %s (%s)" % (c.status, "; ".join(c.disputed_why) or "withdrawn.md")
    if c.capped:
        return "%d %s (own level %d %s)" % (c.level, "capped" if c.level == 0 else LEVEL_NAMES[c.level] + ", capped",
                                            c.own, LEVEL_NAMES[c.own])
    t = "%d %s" % (c.level, LEVEL_NAMES[c.level])
    if c.level == 1 and c.referees == "the owner":
        t += " (by the owner)"
    return t


def badges(c):
    b = []
    if c.used_by:
        b.append("used by %d (%s)" % (len(c.used_by), ", ".join(c.used_by)))
    for who, date, v in c.human:
        b.append("audited by a human: %s, %s, v%d%s" % (who, date, v,
                 "" if v == c.paper.version else " (current: v%d)" % c.paper.version))
    return "; ".join(b) or "-"


def notes(c):
    n = []
    if c.conditional:
        n.append("conditional on " + ", ".join("%sv%d:%s" % d for d in c.conditional))
    if c.outdated_deps:
        n.append("dependency check pending: " + ", ".join("%sv%d -> v%d" % (d[0], d[1], v) for d, v in c.outdated_deps))
    if c.frozen:
        k = sum(1 for s in c.frozen.values() if s == "proved")
        n.append("%d/%d frozen statements proved" % (k, len(c.frozen)))
    elif c.status != "withdrawn":
        n.append("no frozen statement yet")
    return "; ".join(n) or "-"


def cmd_report(args, tree):
    ps, certs = certify(tree, args.audit)
    head = tree.git("rev-parse", tree.ref or "HEAD", check=False).strip()[:12] or "?"
    lines = [
        "# Certification of the library",
        "",
        "Generated by `scripts/certify.py report` (never edited by hand, never committed) on %s, "
        "from `main` at `%s`. Lean status: %s. Rules: AGENTS.md, section 9." % (
            datetime.date.today().isoformat(), head,
            "`lake exe audit --status`" if args.audit else "the proof markers (`catalogue/results/`)"),
        "",
        "Levels: 0 submitted (open pull request), disputed or withdrawn; 1 accepted; 2 Lean-verified "
        "(every frozen statement proved); 3 re-verified by gardening. A paper's level is capped by "
        "the levels of the papers it depends on.",
        "",
        "| Paper | Version | Roadmap | Level | Re-checks | Badges | Notes |",
        "|---|---|---|---|---|---|---|",
    ]
    for p in sorted(ps, key=lambda q: q.num):
        c = certs[p.prefix]
        rc = "%d (%s)" % (len(c.rechecks), ", ".join("%s by %s" % (r[3], r[1]) for r in c.rechecks)) if c.rechecks else "0"
        lines.append("| [%s](../papers/%s/) | v%d | %s | %s | %s | %s | %s |" % (
            p.prefix, p.dir, p.version, p.roadmap or "-", level_text(c), rc, badges(c), notes(c)))
    if not ps:
        lines.append("| (no paper on main yet) | | | | | | |")
    text = "\n".join(lines) + "\n"
    if args.out:
        with open(args.out, "w", encoding="utf-8") as f:
            f.write(text)
    else:
        sys.stdout.write(text)


def tex_escape(s):
    return re.sub(r"([#$%&_{}])", r"\\\1", s).replace("~", r"\textasciitilde{}")


def cmd_leanok(args, tree):
    ps, certs = certify(tree, args.audit)
    mk = markers(tree)
    for p in ps:
        c = certs[p.prefix]
        out = ["% Generated by scripts/certify.py leanok for the PDF; never committed (.gitignore).",
               "% Never write \\leanok by hand: it comes from here (proof markers checked by the audit)."]
        sup = superseded(p)
        for (pp, name), m in sorted(mk.items()):
            if pp != p.prefix or name in sup or c.frozen.get(name) != "proved":
                continue
            label = m.get("label")
            proof = m.get("proof", "Incognita.%s.%s" % (pp, name))
            if isinstance(label, str) and re.match(r"^[A-Za-z0-9_.:-]+$", label):
                out.append("\\incognitaverified{%s}{%s}" % (label, proof))
        line = "Incognita library, %s, version %d. Certification: level %s. Re-checks: %d. Badges: %s." % (
            p.prefix, p.version, level_text(c), len(c.rechecks), badges(c))
        out.append("\\incognitacertification{%s}" % tex_escape(line))
        with open(os.path.join(tree.repo, "papers", p.dir, "certification.tex"), "w", encoding="utf-8") as f:
            f.write("\n".join(out) + "\n")
        print("papers/%s/certification.tex: %s" % (p.dir, level_text(c)))


# ---------------------------------------------------------------- library.bib
def bib_text(tree):
    out = ["% papers/library.bib: the papers of the Incognita library. Generated by",
           "% `python3 scripts/certify.py bib` from papers/*/META.toml and the titles of papers/*/paper.tex:",
           "% never edit it by hand (CI checks it). Cite a library paper as \\cite[Theorem~2]{INC-P001} and",
           "% record the exact version in META.toml (depends_on = [\"P001v2:thm:main\"]). AGENTS.md, section 5.6.",
           ""]
    for p in sorted(papers(tree), key=lambda q: q.num):
        title = p.title.replace("\n", " ")
        authors = ", ".join(a for a in p.authors if isinstance(a, str)) or "unknown"
        humans = [h for h in p.human_authors if isinstance(h, str) and h.strip()] \
            if isinstance(p.human_authors, list) else []
        if humans:   # a paper of the owner: its human authors; the models only revised it
            author = " and ".join(tex_escape(h.strip()) for h in humans)
            note = "Version %d. Written by %s" % (p.version, tex_escape(", ".join(humans)))
            if p.authors:
                note += "; AI assistance: %s" % tex_escape(authors)
        else:
            author = "{Incognita agents}"
            note = "Version %d. Written by %s" % (p.version, tex_escape(authors))
        fields = [("author", author), ("title", "{%s}" % title)]
        if p.year:
            fields.append(("year", p.year))
        fields += [("howpublished", "Incognita library, paper \\texttt{%s}" % tex_escape(p.dir)),
                   ("version", str(p.version)),
                   ("note", note),
                   ("url", "%s/tree/main/papers/%s" % (REPO_URL, p.dir))]
        out.append("@misc{INC-%s," % p.prefix)
        for k, v in fields:
            out.append("  %-12s = {%s}," % (k, v))
        out.append("}")
        out.append("")
    return "\n".join(out)


def cmd_bib(args, tree):
    want = bib_text(tree)
    path = os.path.join(tree.repo, "papers", "library.bib")
    have = tree.read("papers/library.bib")
    if args.check:
        if have != want:
            print("papers/library.bib is out of date: run `python3 scripts/certify.py bib` and commit it")
            sys.exit(1)
        print("papers/library.bib is up to date")
        return
    if have != want:
        with open(path, "w", encoding="utf-8", newline="\n") as f:
            f.write(want)
        print("papers/library.bib written")
    else:
        print("papers/library.bib already up to date")


# ---------------------------------------------------------------- check (CI)
def check_tree(tree, base=None):
    errors = []
    ps = papers(tree)
    idx = by_prefix(ps)
    for d in tree.ls("papers"):
        if d.startswith("P") and tree.read("papers/%s/META.toml" % d) is None and tree.ls("papers/" + d):
            errors.append("papers/%s: no META.toml" % d)
        elif d.startswith("P") and not PAPER_DIR.match(d) and tree.ls("papers/" + d):
            errors.append("papers/%s: a paper directory is P<nnn>-<slug> (lowercase letters, digits, hyphens)" % d)
    nums = {}
    for p in ps:
        w = "papers/%s/META.toml" % p.dir
        nums.setdefault(p.num, []).append(p.dir)
        for k in ("roadmap", "kind", "directions", "authors", "version"):
            if k not in p.meta:
                errors.append("%s: missing field %s" % (w, k))
        extra = set(p.meta) - {"roadmap", "kind", "directions", "authors", "version", "depends_on", "source",
                               "human_authors"}
        if extra:
            errors.append("%s: unknown fields %s" % (w, ", ".join(sorted(extra))))
        if "human_authors" in p.meta and not (isinstance(p.human_authors, list) and p.human_authors
                                              and all(isinstance(h, str) and h.strip() for h in p.human_authors)):
            errors.append("%s: human_authors is a non-empty list of names" % w)
        if not isinstance(p.version, int) or p.version < 1:
            errors.append("%s: version must be an integer >= 1" % w)
        if p.kind not in ("internal", "external", "definitions"):
            errors.append("%s: kind must be internal, external or definitions" % w)
        if not isinstance(p.roadmap, str) or not ROADMAP_NAME.match(p.roadmap):
            errors.append("%s: roadmap must be the name of a roadmap (letters and digits, starting with a capital)" % w)
        elif tree.read("roadmaps/%s/ROADMAP.md" % p.roadmap) is None:
            errors.append("%s: there is no roadmap roadmaps/%s/" % (w, p.roadmap))
        if not isinstance(p.directions, list) or not all(isinstance(x, str) and re.match(r"^[DFC]\d+$", x) for x in p.directions):
            errors.append("%s: directions is a list of items D<n>, F<n> or C<n>" % w)
        if not isinstance(p.depends_on, list):
            errors.append("%s: depends_on is a list" % w)
            continue
        cited = set()
        for key in INC_CITE.findall(strip_comments(p.tex)):
            for k in key.split(","):
                k = k.strip()
                if k.startswith("INC-"):
                    cited.add(k[4:])
        deps = set()
        for dep in p.depends_on:
            m = DEP_RE.match(dep) if isinstance(dep, str) else None
            if not m:
                errors.append("%s: depends_on entry %r is not P<nnn>v<k>:<label> (label def:, lem:, prop:, thm: or cor:)" % (w, dep))
                continue
            dp, k, label = "P" + m.group(1), int(m.group(2)), m.group(3)
            deps.add(dp)
            if dp == p.prefix:
                errors.append("%s: a paper does not depend on itself" % w)
            elif dp not in idx:
                errors.append("%s: depends on %s, which is not in the library" % (w, dp))
            else:
                q = idx[dp]
                if k > q.version:
                    errors.append("%s: depends on %sv%d but %s is at version %d" % (w, dp, k, dp, q.version))
                elif k == q.version and label not in q.labels():
                    errors.append("%s: %s has no label %s" % (w, dp, label))
        for dp in sorted(cited - deps):
            errors.append("papers/%s/paper.tex cites INC-%s, which is not in depends_on" % (p.dir, dp))
        for dp in sorted(deps - cited):
            errors.append("papers/%s/paper.tex does not cite INC-%s (in depends_on)" % (p.dir, dp))
        t = strip_comments(p.tex)
        if p.tex and not re.search(r"\\section\*?\{Open questions\}", t):
            errors.append("papers/%s/paper.tex: no section \"Open questions\"" % p.dir)
        oqs = p.open_questions()
        if p.kind == "internal" and p.tex and not oqs:
            errors.append("papers/%s/paper.tex: an internal paper states at least one open question (openquestion environment)" % p.dir)
        for lab, _t, _s in oqs:
            if not lab:
                errors.append("papers/%s/paper.tex: an open question without \\label{oq:...}" % p.dir)
        if re.search(r"\\(leanok|mathlibok)\b", t):
            errors.append("papers/%s/paper.tex: \\leanok and \\mathlibok come from the audit, never from the paper" % p.dir)
    for n, ds in nums.items():
        if len(ds) > 1:
            errors.append("papers: number %s used by %s" % (n, ", ".join(ds)))
    # Cycles in depends_on.
    graph = {p.prefix: [d[0] for d in p.deps()] for p in ps}
    state = {}

    def visit(v, path):
        state[v] = 1
        for w in graph.get(v, []):
            if state.get(w) == 1:
                errors.append("depends_on: cycle " + " -> ".join(path + [v, w]))
            elif w in graph and not state.get(w):
                visit(w, path + [v])
        state[v] = 2

    for v in graph:
        if not state.get(v):
            visit(v, [])
    # papers/library.bib is generated and never committed (.gitignore): nothing to check here.
    for r in tree.ls("roadmaps"):
        text = tree.read("roadmaps/%s/directions.md" % r)
        if text is not None:
            errors += check_directions(text, "roadmaps/%s/directions.md" % r)
    if base is not None:
        bt = Tree(tree.repo, base)
        bidx = by_prefix(papers(bt))
        for p in ps:
            w = "papers/%s/META.toml" % p.dir
            b = bidx.get(p.prefix)
            if b is None:
                if p.version != 1:
                    errors.append("%s: a new paper has version 1" % w)
                continue
            if b.dir != p.dir:
                errors.append("papers/%s: renamed from papers/%s" % (p.dir, b.dir))
                continue
            if b.meta.get("human_authors") != p.meta.get("human_authors"):
                errors.append("%s: human_authors never changes (AGENTS.md 5.1)" % w)
            changed = b.tex != p.tex
            if changed and p.version != b.version + 1:
                errors.append("%s: paper.tex changed, so version must be %d (now %s)" % (w, b.version + 1, p.version))
            if not changed and p.version != b.version:
                errors.append("%s: version changes only with a new paper.tex (keep %d)" % (w, b.version))
        for r in tree.ls("roadmaps"):
            old = bt.read("roadmaps/%s/directions.md" % r)
            new = tree.read("roadmaps/%s/directions.md" % r)
            if old is not None:
                errors += directions_append_only(old, new, "roadmaps/%s/directions.md" % r)
        # The gardening log: rows are only appended.
        old = bt.read("catalogue/garden.md")
        if old is not None:
            errors += lines_append_only(old, tree.read("catalogue/garden.md"), "catalogue/garden.md")
        # Errata and statement corrections: entries never edited, renumbered or deleted; under an
        # entry, only the lines of later roles (`Revised in …`, `Resolved by …`).
        for d in bt.ls("papers"):
            for f in ("errata.md", "statement-corrections.md"):
                old = bt.read("papers/%s/%s" % (d, f))
                if old is not None:
                    errors += entries_append_only(old, tree.read("papers/%s/%s" % (d, f)), "papers/%s/%s" % (d, f))
    return errors


def trim(lines):
    while lines and not lines[-1].strip():
        lines = lines[:-1]
    return lines


def lines_append_only(old, new, where):
    """Every line of old stays, in order, at the start of new (lines are only appended)."""
    if new is None:
        return ["%s: deleted (it is append-only)" % where]
    o, n = trim(old.splitlines()), new.splitlines()
    if n[:len(o)] != o:
        return ["%s: existing lines were changed or removed (it is append-only)" % where]
    return []


def entries_append_only(old, new, where):
    """Errata (E<k>) and statement corrections (SC<n>): the text before the first entry and every
    entry stay; new entries come after the old ones; under an old entry, only lines starting with
    `Revised in` or `Resolved by` (possibly as list items) may be added."""
    if new is None:
        return ["%s: deleted (entries are never deleted)" % where]

    def split(text):
        head, ents, cur = [], [], None
        for line in text.splitlines():
            m = ENTRY_RE.match(line)
            if m and m.group(1) in ("E", "SC"):
                cur = [m.group(1) + m.group(2), [line]]
                ents.append(cur)
            elif cur is None:
                head.append(line)
            else:
                cur[1].append(line)
        return head, ents

    errs = []
    oh, oe = split(old)
    nh, ne = split(new)
    if trim(oh) != trim(nh)[:len(trim(oh))] or (oe and trim(nh) != trim(oh)):
        errs.append("%s: the text before the entries was changed" % where)
    if [e[0] for e in ne[:len(oe)]] != [e[0] for e in oe]:
        errs.append("%s: entries were removed, renumbered or reordered" % where)
        return errs
    for (eid, ol), (_, nl) in zip(oe, ne):
        ol = trim(ol)
        if nl[:len(ol)] != ol:
            errs.append("%s: %s was edited (only lines may be added under an entry)" % (where, eid))
            continue
        for line in nl[len(ol):]:
            s = re.sub(r"^- ", "", line.strip())
            if line.strip() and not (s.startswith("Revised in ") or s.startswith("Resolved by ")):
                errs.append("%s: under %s, only a line \"Revised in …\" or \"Resolved by …\" may be added" % (where, eid))
                break
    return errs


def direction_entries(text):
    """{C-id: [lines]} in file order (an OrderedDict by construction)."""
    out, cur = {}, None
    for line in text.splitlines():
        if line.startswith("## "):
            m = re.match(r"^## (C\d+) ", line)
            cur = m.group(1) if m else None
            if cur:
                out[cur] = [line]
            continue
        if cur:
            out[cur].append(line)
    return out


def check_directions(text, where):
    errs = []
    ids = [int(k[1:]) for k in direction_entries(text)]
    if ids != list(range(1, len(ids) + 1)):
        errs.append("%s: entries must be C1, C2, ... in order (got %s)" % (where, ", ".join("C%d" % i for i in ids)))
    for k, lines in direction_entries(text).items():
        body = "\n".join(lines)
        for f in ("- Statement:", "- Source:", "- Rating:"):
            if f not in body:
                errs.append("%s: %s has no line %s" % (where, k, f))
    return errs


def directions_append_only(old, new, where):
    errs = []
    if new is None:
        return ["%s: deleted (entries are never deleted)" % where]
    o, n = direction_entries(old), direction_entries(new)
    if list(n)[:len(o)] != list(o):
        errs.append("%s: entries were removed or reordered" % where)
    for k, lines in o.items():
        nl = n.get(k, [])
        while lines and not lines[-1].strip():
            lines = lines[:-1]
        if nl[:len(lines)] != lines:
            errs.append("%s: %s was edited (only lines may be added under an entry)" % (where, k))
        for line in nl[len(lines):]:
            if line.strip() and not line.startswith("Dropped ("):
                errs.append("%s: under %s, only a line \"Dropped (<date>, <role>, <model>): <reason>\" may be added" % (where, k))
    return errs


def cmd_check(args, tree):
    errors = check_tree(tree, args.base)
    for e in errors:
        print("error: " + e)
    if errors:
        sys.exit(1)
    print("library metadata: ok (%d papers)" % len(papers(tree)))


# ---------------------------------------------------------------- roadmap items
def roadmap_status(text):
    for line in (text or "").splitlines():
        m = STATUS_LINE.match(line)
        if m:
            return m.group(1)
    return None


def roadmap_domain(text):
    for line in (text or "").splitlines():
        m = re.match(r"^\| Domain \| `?([a-z0-9-]+)`?", line)
        if m:
            return m.group(1)
    return None


def doc_items(text):
    """[(id, closed?)] of the D and F items of a roadmap or an extension."""
    out, cur, buf = [], None, []
    for line in text.splitlines():
        m = ITEM_RE.match(line)
        if m or line.startswith("#") or (cur and re.match(r"^\s*- ", line)):
            if cur:
                out.append((cur, bool(CLOSED_RE.search(" ".join(buf)))))
            cur, buf = (m.group(1), [line]) if m else (None, [])
            continue
        if cur:
            buf.append(line)
    if cur:
        out.append((cur, bool(CLOSED_RE.search(" ".join(buf)))))
    return out


def extensions(tree, r):
    out = []
    for f in tree.ls("roadmaps/%s/extensions" % r):
        m = re.match(r"^X(\d+)\.md$", f)
        if m:
            text = tree.read("roadmaps/%s/extensions/%s" % (r, f)) or ""
            out.append((int(m.group(1)), roadmap_status(text), text))
    return sorted(out)


def items(tree, r):
    """[(id, state, detail)]: state open, closed, covered (detail: the papers), dropped."""
    if not ROADMAP_NAME.match(r or ""):
        raise Fail("bad roadmap name %r" % r)
    text = tree.read("roadmaps/%s/ROADMAP.md" % r)
    if text is None:
        raise Fail("no roadmap %s" % r)
    found = [(i, "closed" if c else "open", "") for i, c in doc_items(text)]
    for k, status, et in extensions(tree, r):
        for i, c in doc_items(et):
            if i.startswith("D"):
                found.append((i, "closed" if c or status != "approved" else "open",
                              "" if status == "approved" else "extension X%d %s" % (k, status)))
    for k, lines in direction_entries(tree.read("roadmaps/%s/directions.md" % r) or "").items():
        dropped = any(x.startswith("Dropped (") for x in lines)
        found.append((k, "dropped" if dropped else "open", ""))
    served = {}
    for p in papers(tree):
        if p.roadmap == r:
            for i in p.directions:
                served.setdefault(i, []).append(p.prefix)
    out = []
    for i, s, d in found:
        if s == "open" and i in served:
            out.append((i, "covered", " ".join(served[i])))
        else:
            out.append((i, s, d))
    return out


def cmd_items(args, tree):
    for i, s, d in items(tree, args.roadmap):
        if args.free and s != "open":
            continue
        print(("%s %s %s" % (i, s, d)).rstrip())


def cmd_items_hash(args, tree):
    ids = sorted("%s:%s" % (i, s if s in ("closed", "dropped") else "") for i, s, _ in items(tree, args.roadmap))
    print(hashlib.sha256("\n".join(ids).encode()).hexdigest()[:16])


# ---------------------------------------------------------------- dependencies
def cmd_dependants(args, tree):
    ps = papers(tree)
    for p in sorted(ps, key=lambda q: q.num):
        n = sum(1 for q in ps if any(d[0] == p.prefix for d in q.deps()))
        print("%s %d" % (p.dir, n))


def cmd_depchecks(args, tree):
    ps = papers(tree)
    idx = by_prefix(ps)
    for p in sorted(ps, key=lambda q: q.num):
        if p.withdrawn:
            continue
        for dp, k, _label in p.deps():
            if dp in idx and idx[dp].version > k:
                print("%s %sv%d->v%d" % (p.dir, dp, k, idx[dp].version))


def cmd_disputed_deps(args, tree):
    ps, certs = certify(tree, args.audit)
    for p in sorted(ps, key=lambda q: q.num):
        for dp, k, _l in p.deps():
            c = certs.get(dp)
            if c is None or c.status in ("disputed", "withdrawn"):
                print("%s %s %s" % (p.dir, dp, c.status if c else "missing"))


# ---------------------------------------------------------------- candidate directions
DIRECTIONS_HEADER = """# Candidate directions of {r}

The open questions of accepted papers that the scope referee rated as candidates (interest,
novelty, fit), added by the loop when the paper is merged (`scripts/certify.py add-candidates`).
A writer may take an entry `C<n>` like a direction `D<n>` of [ROADMAP.md](ROADMAP.md): its paper
lists it in `directions` (META.toml). **Append-only**: entries are never edited, renumbered or
deleted; `garden` (or the owner) may add a line `Dropped (<date>, <role>, <model>): <reason>`
under an entry. The status is computed (AGENTS.md, section 4): candidate, taken (an open pull
request serves it), done by P<nnn> (a paper on `main` serves it), covered (a rejected paper served
it), dropped.
"""


def scope_ratings(report):
    """{label: (interest, novelty, fit, candidate)} from the table "## Open questions" of a scope
    report: | Question | Interest | Novelty | Fit | Candidate | ... |."""
    out = {}
    for line in report.splitlines():
        if not line.startswith("|"):
            continue
        c = [x.strip().strip("`*") for x in line.strip().strip("|").split("|")]
        if len(c) >= 5 and re.match(r"^oq:[A-Za-z0-9_.:-]+$", c[0]):
            out[c[0]] = (c[1], c[2], c[3], c[4].lower().startswith("yes"))
    return out


def cmd_add_candidates(args, tree):
    if not PAPER_DIR.match(args.paper or ""):
        raise Fail("bad paper directory %r" % args.paper)
    p = Paper(tree, args.paper)
    if not isinstance(p.roadmap, str) or not ROADMAP_NAME.match(p.roadmap) \
            or tree.read("roadmaps/%s/ROADMAP.md" % p.roadmap) is None:
        raise Fail("%s: unknown roadmap %r" % (p.dir, p.roadmap))
    with open(args.report, encoding="utf-8") as f:
        ratings = scope_ratings(f.read())
    path = "roadmaps/%s/directions.md" % p.roadmap
    text = tree.read(path) or DIRECTIONS_HEADER.format(r=p.roadmap)
    have = direction_entries(text)
    n = len(have)
    added = []
    today = args.date or datetime.date.today().isoformat()
    for label, title, statement in p.open_questions():
        if not label or label not in ratings or not ratings[label][3]:
            continue
        src = "%sv%d %s" % (p.prefix, p.version, label)
        # Once per question: a later version of the paper does not add it again.
        seen = re.compile(r"from %sv\d+ %s\)" % (p.prefix, re.escape(label)))
        if any(seen.search(lines[0]) for lines in have.values()):
            continue
        n += 1
        interest, novelty, fit, _ = ratings[label]
        added.append("\n".join([
            "",
            "## C%d (%s, from %s)" % (n, today, src),
            "- Title: %s" % (title or "-"),
            "- Statement: %s" % statement,
            "- Source: papers/%s, version %d, label %s" % (p.dir, p.version, label),
            "- Rating: interest %s; novelty %s; fit %s (referee-scope, pull request #%s, head %s)" % (
                interest, novelty, fit, args.pr, args.head[:12]),
        ]))
    if added:
        text = text.rstrip("\n") + "\n" + "\n".join(added) + "\n"
        with open(os.path.join(tree.repo, path), "w", encoding="utf-8", newline="\n") as f:
            f.write(text)
    print(len(added))


# ---------------------------------------------------------------- roadmap proposals
def domains(tree):
    out = set()
    for r in tree.ls("roadmaps"):
        t = tree.read("roadmaps/%s/ROADMAP.md" % r)
        if t and roadmap_status(t) == "approved" and roadmap_domain(t):
            out.add(roadmap_domain(t))
    return out


def changed(tree, base, head, *paths):
    out = tree.git("diff", "--name-status", "--no-renames", base, head, "--", *paths)
    return [tuple(line.split("\t", 1)) for line in out.splitlines() if line]


def proposal(tree, base, head):
    bt, ht = Tree(tree.repo, base), Tree(tree.repo, head)
    ch = changed(tree, base, head, "roadmaps")
    if any(st != "A" for st, _ in ch):
        raise Fail("a proposal only adds files under roadmaps/: %s" % ", ".join("%s %s" % c for c in ch if c[0] != "A"))
    paths = sorted(p for _, p in ch)
    m = [re.match(r"^roadmaps/([A-Z][A-Za-z0-9]+)/(ROADMAP|KNOWN)\.md$", p) for p in paths]
    if len(paths) == 2 and all(m) and m[0].group(1) == m[1].group(1):
        name = m[0].group(1)
        if bt.ls("roadmaps/" + name):
            raise Fail("roadmaps/%s already exists on main" % name)
        rm = ht.read("roadmaps/%s/ROADMAP.md" % name)
        kn = ht.read("roadmaps/%s/KNOWN.md" % name) or ""
        if roadmap_status(rm) != "proposed":
            raise Fail("roadmaps/%s/ROADMAP.md: the status line must be | Status | **proposed** ... |" % name)
        d = roadmap_domain(rm)
        if not d:
            raise Fail("roadmaps/%s/ROADMAP.md: no line | Domain | <domain> |" % name)
        if kn.splitlines()[:1] != ["Reviewed by owner: no"]:
            raise Fail("roadmaps/%s/KNOWN.md: the first line must be \"Reviewed by owner: no\"" % name)
        return "new %s %s %s" % (name, d, "existing" if d in domains(bt) else "new")
    m = re.match(r"^roadmaps/([A-Za-z0-9]+)/extensions/X(\d+)\.md$", paths[0]) if len(paths) == 1 else None
    if m:
        r, k = m.group(1), int(m.group(2))
        rt = bt.read("roadmaps/%s/ROADMAP.md" % r)
        if roadmap_status(rt) != "approved":
            raise Fail("roadmaps/%s is not an approved roadmap on main" % r)
        want = 1 + max([x[0] for x in extensions(bt, r)] or [0])
        if k != want:
            raise Fail("the next extension of %s is X%d, not X%d" % (r, want, k))
        et = ht.read(paths[0])
        if roadmap_status(et) != "proposed":
            raise Fail("%s: the status line must be | Status | **proposed** ... |" % paths[0])
        old = {i for i, _ in doc_items(rt)} | {i for _, _, t in extensions(bt, r) for i, _ in doc_items(t)}
        new = [i for i, _ in doc_items(et)]
        if not new or any(not i.startswith("D") or i in old for i in new):
            raise Fail("%s: new directions D<n> with numbers not used in the roadmap" % paths[0])
        return "extension %s/X%d %s existing" % (r, k, roadmap_domain(rt) or "-")
    raise Fail("a proposal adds either roadmaps/<New>/ROADMAP.md and KNOWN.md, or one "
               "roadmaps/<Roadmap>/extensions/X<k>.md (got: %s)" % (", ".join(paths) or "nothing"))


def cmd_proposal(args, tree):
    print(proposal(tree, args.base, args.head))


def proposal_files(tree, base):
    return [p for st, p in changed(tree, base, "HEAD", "roadmaps")
            if st == "A" and re.search(r"/(ROADMAP\.md|extensions/X\d+\.md)$", p)]


def cmd_approve_roadmap(args, tree):
    files = proposal_files(tree, args.base)
    if not files:
        raise Fail("no proposal file since %s" % args.base)
    for path in files:
        full = os.path.join(tree.repo, path)
        with open(full, encoding="utf-8") as f:
            lines = f.read().split("\n")
        hits = [i for i, x in enumerate(lines) if re.match(r"^\| Status \| \*\*proposed\*\*.*\|\s*$", x)]
        if len(hits) != 1:
            raise Fail("%s: exactly one line | Status | **proposed** ... | expected" % path)
        lines[hits[0]] = "| Status | **approved** (%s) |" % args.text.replace("|", "/")
        with open(full, "w", encoding="utf-8", newline="\n") as f:
            f.write("\n".join(lines))
        print(path)


def cmd_verify_scripted(args, tree):
    diff = tree.git("diff", "--no-renames", "-U0", args.parent, args.head)
    ch = changed(tree, args.parent, args.head)
    if not ch:
        raise Fail("the scripted commit changes nothing")
    for st, path in ch:
        if args.kind == "directions":
            if not re.match(r"^roadmaps/[A-Za-z0-9]+/directions\.md$", path):
                raise Fail("a directions commit changes only roadmaps/<R>/directions.md (got %s)" % path)
        elif args.kind == "approved":
            if st != "M" or not re.search(r"^roadmaps/[A-Za-z0-9]+/(ROADMAP\.md|extensions/X\d+\.md)$", path):
                raise Fail("an approval commit changes only proposal files (got %s %s)" % (st, path))
    minus = [x for x in diff.splitlines() if x.startswith("-") and not x.startswith("--- ")]
    plus = [x for x in diff.splitlines() if x.startswith("+") and not x.startswith("+++ ")]
    if args.kind == "directions":
        if minus:
            raise Fail("a directions commit only adds lines")
        for st, path in ch:
            old = Tree(tree.repo, args.parent).read(path)
            new = Tree(tree.repo, args.head).read(path) or ""
            errs = check_directions(new, path) + (directions_append_only(old, new, path) if old else [])
            for line in new.splitlines()[len((old or "").splitlines()):]:
                if line.startswith("Dropped ("):
                    errs.append("%s: a scripted commit drops nothing" % path)
            if errs:
                raise Fail("; ".join(errs))
    else:
        if len(minus) != len(ch) or len(plus) != len(ch):
            raise Fail("an approval commit changes exactly one line per file")
        if not all(re.match(r"^-\| Status \| \*\*proposed\*\*", x) for x in minus) or \
           not all(re.match(r"^\+\| Status \| \*\*approved\*\* \(", x) for x in plus):
            raise Fail("an approval commit only turns | Status | **proposed** into **approved**")
    print("ok: scripted %s commit" % args.kind)


def cmd_dropped_only(args, tree):
    """garden's changes to candidate directions: `Dropped (` lines under existing entries only."""
    errs = []
    for st, path in changed(tree, args.base, args.head, "roadmaps"):
        if not re.match(r"^roadmaps/[A-Za-z0-9]+/directions\.md$", path):
            continue
        if st != "M":
            errs.append("%s: %s (a directions.md is only modified)" % (path, st))
            continue
        old = Tree(tree.repo, args.base).read(path) or ""
        new = Tree(tree.repo, args.head).read(path) or ""
        errs += directions_append_only(old, new, path)
        o, n = direction_entries(old), direction_entries(new)
        if list(n) != list(o):
            errs.append("%s: new entries %s (only the loop adds candidate directions)" % (
                path, ", ".join(k for k in n if k not in o) or "?"))
        oh = old.split("\n## ", 1)[0]
        if not new.startswith(oh):
            errs.append("%s: the header was changed" % path)
    for e in errs:
        print("error: " + e)
    if errs:
        sys.exit(1)
    print("ok: only Dropped lines")


# ---------------------------------------------------------------- main
def main(argv):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--repo", default=".")
    ap.add_argument("--ref", default=None, help="read the tree at this git ref instead of the working tree")
    sub = ap.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("report"); s.add_argument("--audit"); s.add_argument("--out")
    s = sub.add_parser("leanok"); s.add_argument("--audit")
    s = sub.add_parser("bib"); s.add_argument("--check", action="store_true")
    s = sub.add_parser("check"); s.add_argument("--base")
    s = sub.add_parser("items"); s.add_argument("roadmap"); s.add_argument("--free", action="store_true")
    s = sub.add_parser("items-hash"); s.add_argument("roadmap")
    sub.add_parser("dependants")
    sub.add_parser("depchecks")
    s = sub.add_parser("disputed-deps"); s.add_argument("--audit")
    s = sub.add_parser("add-candidates")
    s.add_argument("--paper", required=True); s.add_argument("--report", required=True)
    s.add_argument("--pr", required=True); s.add_argument("--head", required=True); s.add_argument("--date")
    s = sub.add_parser("proposal"); s.add_argument("--base", required=True); s.add_argument("--head", required=True)
    s = sub.add_parser("approve-roadmap"); s.add_argument("--base", required=True); s.add_argument("--text", required=True)
    s = sub.add_parser("verify-scripted"); s.add_argument("--kind", required=True, choices=["approved", "directions"])
    s.add_argument("--parent", required=True); s.add_argument("--head", required=True)
    s = sub.add_parser("dropped-only"); s.add_argument("--base", required=True); s.add_argument("--head", required=True)
    args = ap.parse_args(argv)
    tree = Tree(os.path.abspath(args.repo), args.ref)
    fn = {"report": cmd_report, "leanok": cmd_leanok, "bib": cmd_bib, "check": cmd_check,
          "items": cmd_items, "items-hash": cmd_items_hash, "dependants": cmd_dependants,
          "depchecks": cmd_depchecks, "disputed-deps": cmd_disputed_deps,
          "add-candidates": cmd_add_candidates, "proposal": cmd_proposal,
          "approve-roadmap": cmd_approve_roadmap, "verify-scripted": cmd_verify_scripted,
          "dropped-only": cmd_dropped_only}[args.cmd]
    try:
        fn(args, tree)
    except Fail as e:
        print("error: %s" % e, file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main(sys.argv[1:])
