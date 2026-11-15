#!/usr/bin/env python3
"""The public page of the accepted papers (GitHub Pages): one card per paper on main, with its
three stages of verification (refereeing, Lean, gardening), its interest score and its PDF.

Usage: python3 scripts/site.py --out <dir> [--pdfs <dir>]
  --pdfs: the compiled PDFs, named <paper directory>.pdf (the reader build, copied to
          <out>/<prefix>.pdf, link "PDF") and <paper directory>-blueprint.pdf (the blueprint build,
          copied to <out>/<prefix>-blueprint.pdf, link "Blueprint (with dependencies)").
The verification comes from scripts/certify.py (the proof markers of catalogue/results/, the merge
trailers and catalogue/garden.md), as in the PDFs, which print the same certification line. The
interest score is read from the last scope report on the pull request that added the paper (trusted:
written by INCOGNITA_OWNER with the loop's marker), through the GitHub API (GH_TOKEN or
GITHUB_TOKEN); without network it is shown as unknown. Written by Claude for the owner, 2026-11-15.
"""
import argparse
import datetime
import html
import json
import os
import re
import shutil
import subprocess
import sys
import urllib.request

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import certify as C  # noqa: E402

REPO = os.environ.get("GITHUB_REPOSITORY", "prevostad/Incognita")
OWNER = os.environ.get("INCOGNITA_OWNER", REPO.split("/")[0])
TOKEN = os.environ.get("GH_TOKEN") or os.environ.get("GITHUB_TOKEN") or ""


def git(repo, *args):
    r = subprocess.run(["git", "-C", repo, *args], capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else ""


def added_by_pr(repo, d):
    """The pull request that added papers/<d>/ (the squash or merge title ends with (#N))."""
    out = git(repo, "log", "--diff-filter=A", "--format=%s", "--", "papers/%s/META.toml" % d)
    for line in reversed(out.splitlines()):
        m = re.search(r"\(#(\d+)\)\s*$", line)
        if m:
            return int(m.group(1))
    out = git(repo, "log", "--format=%s", "--", "papers/%s/paper.tex" % d)
    for line in out.splitlines():
        m = re.search(r"\(#(\d+)\)\s*$", line)
        if m:
            return int(m.group(1))
    return None


def api(path):
    req = urllib.request.Request("https://api.github.com/" + path,
                                 headers={"Accept": "application/vnd.github+json",
                                          "User-Agent": "incognita-site"})
    if TOKEN:
        req.add_header("Authorization", "Bearer " + TOKEN)
    with urllib.request.urlopen(req, timeout=30) as r:
        return json.load(r)


def interest(pr):
    """(score out of 10, one-line reason, report URL) from the last trusted scope report, or Nones."""
    if not pr:
        return None, None, None
    try:
        comments = []
        page = 1
        while True:
            batch = api("repos/%s/issues/%d/comments?per_page=100&page=%d" % (REPO, pr, page))
            comments += batch
            if len(batch) < 100:
                break
            page += 1
    except Exception as e:  # no network, rate limit: shown as unknown
        print("warning: comments of #%s: %s" % (pr, e), file=sys.stderr)
        return None, None, None
    score = url = reason = None
    for c in reversed(comments):   # the last report gives the score; the last substantive reason is kept
        body = c.get("body") or ""
        if (c.get("user") or {}).get("login") != OWNER or not body.startswith("<!-- incognita:referee-scope:"):
            continue
        m = re.search(r"^\|\s*Interest\s*\|\s*(\d+)\s*/\s*(10|5)\b[^|]*\|\s*([^|\n]*)", body, re.M)
        if not m:
            continue
        if score is None:
            score = int(m.group(1)) * (2 if m.group(2) == "5" else 1)
            url = c.get("html_url")
        r = m.group(3).strip()
        if len(r) > 30 and not re.match(r"(?i)(unchanged|same|as before)", r):
            reason = r
            break
    return score, reason or "", url


def first_sentence(s, n=320):
    s = s or ""
    m = re.match(r"(.+?[.!?])(\s|$)", s)
    s = m.group(1) if m else s
    return s if len(s) <= n else s[: n - 1] + "…"


def stages(c):
    """The three stages, each (state, text): state in done, partial, todo, bad."""
    if c.status == "withdrawn":
        return [("bad", "Withdrawn by the owner"), ("todo", "-"), ("todo", "-")]
    review = ("done", "Accepted by two AI referees" if c.referees == "both referees"
              else "Merged by the owner")
    n = len(c.frozen)
    k = sum(1 for s in c.frozen.values() if s == "proved")
    if c.verified:
        lean = ("done", "Lean-verified: %d/%d frozen statements proved" % (k, n))
    elif n:
        lean = ("partial", "Formalising: %d/%d frozen statements proved" % (k, n))
    else:
        lean = ("todo", "Not formalised yet")
    if c.recheck_failed:
        garden = ("bad", "Last re-check failed")
    elif c.rechecks:
        garden = ("done", "Re-verified %d time%s" % (len(c.rechecks), "" if len(c.rechecks) == 1 else "s"))
    else:
        garden = ("todo", "Not re-verified yet")
    return [review, lean, garden]


CSS = """
:root{--bg:#fbfaf7;--fg:#1d1d1f;--muted:#5f6368;--card:#fff;--line:#e3e1db;--ok:#1a7f37;--part:#9a6700;
--todo:#8c8c8c;--bad:#cf222e;--link:#0b57d0}
@media (prefers-color-scheme:dark){:root{--bg:#141414;--fg:#ececec;--muted:#a0a0a0;--card:#1e1e1e;
--line:#333;--ok:#3fb950;--part:#d29922;--todo:#7d7d7d;--bad:#f85149;--link:#8ab4f8}}
*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--fg);
font:16px/1.5 system-ui,-apple-system,"Segoe UI",sans-serif}
main{max-width:920px;margin:0 auto;padding:32px 16px 64px}h1{font-size:1.7rem;margin:0 0 4px}
.sub{color:var(--muted);margin:0 0 24px}a{color:var(--link)}
.card{background:var(--card);border:1px solid var(--line);border-radius:10px;padding:18px 20px;margin:0 0 16px}
.head{display:flex;gap:12px;align-items:baseline;justify-content:space-between;flex-wrap:wrap}
.id{font-family:ui-monospace,Consolas,monospace;color:var(--muted);font-size:.9rem}
h2{font-size:1.15rem;margin:4px 0 6px;line-height:1.35}.meta{color:var(--muted);font-size:.92rem;margin:0 0 12px}
.stages{display:grid;grid-template-columns:repeat(3,1fr);gap:8px;margin:0 0 12px}
.stage{border:1px solid var(--line);border-radius:8px;padding:8px 10px;font-size:.9rem}
.stage b{display:block;font-size:.78rem;text-transform:uppercase;letter-spacing:.04em;color:var(--muted)}
.done{border-left:4px solid var(--ok)}.partial{border-left:4px solid var(--part)}
.todo{border-left:4px solid var(--todo)}.bad{border-left:4px solid var(--bad)}
.mark{font-weight:600}.done .mark{color:var(--ok)}.partial .mark{color:var(--part)}.todo .mark{color:var(--todo)}.bad .mark{color:var(--bad)}
.interest{display:flex;gap:12px;align-items:flex-start;margin:0 0 12px;font-size:.92rem}
.score{font-weight:700;font-size:1.25rem;white-space:nowrap}.reason{color:var(--muted)}
.warn{color:var(--bad);font-weight:600;margin:0 0 10px}.links a{margin-right:16px}
footer{color:var(--muted);font-size:.85rem;margin-top:32px}
@media (max-width:640px){.stages{grid-template-columns:1fr}}
"""


def card(p, c, pdf, score, reason, url, pr, blueprint=None):
    e = html.escape
    authors = p.human_authors if isinstance(p.human_authors, list) and p.human_authors else p.authors
    who = ", ".join(a for a in authors if isinstance(a, str))
    if p.human_authors and p.authors:
        who += " (revised by %s)" % ", ".join(a for a in p.authors if isinstance(a, str))
    out = ['<article class="card">', '<div class="head"><span class="id">%s · version %d · %s</span></div>'
           % (e(p.prefix), p.version, e(p.roadmap or "-")),
           "<h2>%s</h2>" % e(re.sub(r"\s+", " ", re.sub(r"\\\\(\[[^\]]*\])?", " ", p.title))),
           '<p class="meta">%s · items %s</p>' % (e(who or "unknown"), e(", ".join(map(str, p.directions)) or "-"))]
    if c.status in ("disputed", "withdrawn"):
        out.append('<p class="warn">%s: %s</p>' % (e(c.status.capitalize()), e("; ".join(c.disputed_why) or "withdrawn.md")))
    if c.capped and c.status not in ("disputed", "withdrawn"):
        out.append('<p class="warn">Conditional: depends on papers not verified at its level (%s).</p>'
                   % e(", ".join(d[0] for d in c.conditional)))
    names = ["1 · Refereeing", "2 · Lean", "3 · Gardening"]
    signs = {"done": "✓", "partial": "◐", "todo": "–", "bad": "✗"}
    out.append('<div class="stages">')
    for name, (state, text) in zip(names, stages(c)):
        out.append('<div class="stage %s"><b>%s</b><span class="mark">%s</span> %s</div>'
                   % (state, e(name), signs[state], e(text)))
    out.append("</div>")
    if score is not None:
        out.append('<div class="interest"><span class="score">%d/10</span><span class="reason">'
                   'Interest (scope referee). %s %s</span></div>'
                   % (score, e(first_sentence(reason)), '<a href="%s">Report</a>' % e(url) if url else ""))
    else:
        out.append('<div class="interest"><span class="score">–/10</span><span class="reason">'
                   'Interest: no scope report found.</span></div>')
    links = []
    if pdf:
        links.append('<a href="%s">PDF</a>' % e(pdf))
    if blueprint:
        links.append('<a href="%s">Blueprint (with dependencies)</a>' % e(blueprint))
    links.append('<a href="https://github.com/%s/tree/main/papers/%s">Sources</a>' % (e(REPO), e(p.dir)))
    if pr:
        links.append('<a href="https://github.com/%s/pull/%d">Pull request and reports</a>' % (e(REPO), pr))
    out.append('<p class="links">%s</p>' % " ".join(links))
    out.append("</article>")
    return "\n".join(out)


def main(argv):
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=".")
    ap.add_argument("--out", required=True)
    ap.add_argument("--pdfs", default=None)
    a = ap.parse_args(argv)
    os.makedirs(a.out, exist_ok=True)
    tree = C.Tree(a.repo)
    ps, certs = C.certify(tree, None)
    cards = []
    for p in sorted(ps, key=lambda q: q.num, reverse=True):
        c = certs[p.prefix]
        pdf = blueprint = None
        if a.pdfs:
            src = os.path.join(a.pdfs, p.dir + ".pdf")
            if os.path.exists(src):
                shutil.copy(src, os.path.join(a.out, p.prefix + ".pdf"))
                pdf = p.prefix + ".pdf"
            src = os.path.join(a.pdfs, p.dir + "-blueprint.pdf")
            if os.path.exists(src):
                shutil.copy(src, os.path.join(a.out, p.prefix + "-blueprint.pdf"))
                blueprint = p.prefix + "-blueprint.pdf"
        pr = added_by_pr(a.repo, p.dir)
        score, reason, url = interest(pr)
        cards.append(card(p, c, pdf, score, reason, url, pr, blueprint))
    head = git(a.repo, "rev-parse", "--short=12", "HEAD").strip() or "?"
    today = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
    page = """<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Incognita papers</title><meta name="description" content="Accepted papers of the Incognita library, with their verification and interest.">
<link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/katex.min.css">
<script defer src="https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/katex.min.js"></script>
<script defer src="https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/contrib/auto-render.min.js"
 onload="renderMathInElement(document.body,{delimiters:[{left:'$',right:'$',display:false}],throwOnError:false})"></script>
<style>%s</style></head><body><main>
<h1>Incognita: accepted papers</h1>
<p class="sub">Research by AI agents, refereed by AI agents, then verified in Lean 4. Each paper shows its three stages
of verification: <b>refereeing</b> (two AI referees accepted it), <b>Lean</b> (its frozen statements proved),
<b>gardening</b> (the proofs re-checked later). A paper that is only refereed has not been checked by Lean: read it
as a preprint. The PDF prints the same certification under its title and a green box under each Lean-verified
statement; the blueprint is the same text with the dependencies of every statement and proof printed, for
formalisers. <a href="https://github.com/%s">Repository</a>.</p>
%s
<footer>Generated by <code>scripts/site.py</code> from <code>main</code> at <code>%s</code>, %s. Rebuilt at every change of
the papers or of their verification, and every day.</footer>
</main></body></html>
""" % (CSS, html.escape(REPO), "\n".join(cards) or "<p>No accepted paper yet.</p>", html.escape(head), today)
    with open(os.path.join(a.out, "index.html"), "w", encoding="utf-8") as f:
        f.write(page)
    open(os.path.join(a.out, ".nojekyll"), "w").close()
    print("%s: %d papers" % (os.path.join(a.out, "index.html"), len(ps)))


if __name__ == "__main__":
    main(sys.argv[1:])
