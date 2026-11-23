#!/usr/bin/env python3
"""Statistics of the Incognita loop, computed from GitHub and the repository only (owner request of
2026-11-19).

The state of a night (~/.incognita/state/nights/<night>/events.tsv and usage.tsv) lives only on the
server, which the owner deletes between nights. scripts/night.sh therefore posts it with the night
report on the pinned issue "Night reports" (post_night_report in scripts/lib.sh), in blocks that this
script writes (events-block) and reads back:

    <details><summary>Raw events of the night of 2026-11-19 (part 1/1, 68 lines; read by scripts/stats.py)</summary>

    <!-- incognita:events v1 night=2026-11-19 part=1/1 lines=68 -->
    ~~~tsv
    2026-11-19 21:47:16<TAB>task<TAB>fix-pr<TAB>67<TAB>ok pushed #67 b0ebb5d1a324 (turns 19, 181s, $0.53)
    ~~~

    </details>

One line per event, the columns of events.tsv: time (server time, UTC), kind, role, target, text.
The readings of the weekly usage (usage.tsv) are lines of kind `usage`, text `ok <weekly %> <weekly
reset> <five-hour %> <five-hour reset> <source>` or `err <reason>`. Every data line starts with its
time, so no line can close the fence. Only comments of the owner's account are read (the loop posts
with it, and so does scripts/stats-backfill.sh); a line is kept once, whatever the number of
comments that carry it. Nights before these blocks existed are read from the task list of their
night reports (sessions only, to the minute).

Usage:
    stats.py [--repo DIR] [--fixtures DIR] [--json FILE] [--html FILE]
        Every metric (production, quality, formalisation, cost) as JSON (--json; "-": stdout) and as
        an HTML fragment (--html; scripts/site.py puts it in the page stats.html of the site).
        GitHub is read with GH_TOKEN or GITHUB_TOKEN. Without a token, or when GitHub cannot be
        read, the metrics that need it are marked unavailable and the others (formalisation, merge
        trailers, errata: from the repository) are still computed. --fixtures DIR reads GitHub from
        files instead (tests, no network): pulls.json, issues.json, comments/<n>.json, in the format
        of the REST API.
    stats.py events-block --night NIGHT --out DIR [--budget BYTES] [--log FILE] FILE...
        The events files (a missing one is skipped) as blocks DIR/part-<k>.md of at most BYTES
        bytes each (default 60000); prints the number of parts (0: no event). Lines that are not
        events, or that look like a secret, are left out; the others are cleaned as the loop cleans
        what it posts (control and bidi characters, `<!--`, `@`). --log: the night's log, which gives
        their model to task lines written before it was recorded (scripts/stats-backfill.sh).

The metrics (agents/README.md, "Statistics"): production, quality, formalisation, cost (by role,
night, paper, Lean pull request, stage, model; to acceptance and to Lean verification),
contributors, interest scores, the Lean library over time, loop efficiency (open to merge, duration
of "Build and check"), literature and candidate directions. Extended on 2026-11-19 (owner).
    stats.py events-read FILE...
        The events stored in comment bodies (Markdown files), one TSV line each, the night first.

Reads only text files, git objects and the GitHub API; never runs anything from the repository.
Written by Claude for the owner, 2026-11-19. Python 3.11+.
"""
import argparse
import collections
import datetime
import html
import json
import os
import re
import statistics
import subprocess
import sys
import urllib.parse
import urllib.request

REPO =os.environ.get("GITHUB_REPOSITORY", "prevostad/Incognita")
OWNER = os.environ.get("INCOGNITA_OWNER", REPO.split("/")[0])
TOKEN = os.environ.get("GH_TOKEN") or os.environ.get("GITHUB_TOKEN") or ""
REPORT_TITLE = "Night reports"
CI_CHECK = "Build and check"   # the check of the workflow CI (CI_JQ in scripts/lib.sh)

# ---------------------------------------------------------------- the events blocks
BLOCK_VERSION = 1
MARK_RE = re.compile(r"^<!-- incognita:events v(\d+) night=([A-Za-z0-9-]{1,32}) part=(\d+)/(\d+) lines=(\d+) -->$")
LINE_RE = re.compile(r"^(\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2})\t([a-z][a-z0-9-]{0,40})\t([^\t]{0,80})\t([^\t]{0,120})\t([^\t]*)$")
NIGHT_RE = re.compile(r"^[A-Za-z0-9-]{1,32}$")
# What looks like a secret (as SECRET_RE and sanitize in scripts/lib.sh): such a line is left out.
SECRET_RE = re.compile(r"sk-ant-[A-Za-z0-9_-]{8,}|gh[pousr]_[A-Za-z0-9]{20,}|github_pat_[A-Za-z0-9_]{20,}"
                       r"|-----BEGIN [A-Z ]*PRIVATE KEY-----|CLAUDE_CODE_OAUTH_TOKEN|Bearer [A-Za-z0-9._-]{20,}")
ZWSP = "​"


def clean_field(s):
    """A field of an event as the loop posts agent text (sanitize in scripts/lib.sh): control and
    bidi characters removed, `<!--` escaped, `@` followed by a zero-width space. Idempotent."""
    s = "".join(c for c in s if ord(c) >= 32 and ord(c) != 127 and not (0x202A <= ord(c) <= 0x202E)
                and not (0x2066 <= ord(c) <= 0x2069))
    s = s.replace("<!--", "&lt;!--")
    return re.sub("@(?!%s)" % ZWSP, "@" + ZWSP, s)


def event_lines(paths):
    """(kept lines sorted by time, number of lines left out) of events files."""
    kept, dropped = [], 0
    for path in paths:
        try:
            with open(path, encoding="utf-8", errors="replace") as f:
                raw = f.read().splitlines()
        except (FileNotFoundError, IsADirectoryError, NotADirectoryError):
            continue
        for line in raw:
            if not line.strip():
                continue
            if SECRET_RE.search(line):
                dropped += 1
                continue
            cols = line.split("\t")
            if len(cols) != 5:
                dropped += 1
                continue
            line = "\t".join(clean_field(c) for c in cols)
            if not LINE_RE.match(line):
                dropped += 1
                continue
            kept.append(line)
    kept.sort(key=lambda x: x[:19])   # stable: the order of the files within one second
    return kept, dropped


def block_text(night, part, total, lines, dropped=0):
    note = "; %d line%s left out" % (dropped, "" if dropped == 1 else "s") if dropped and part == 1 else ""
    return ("<details><summary>Raw events of the night of %s (part %d/%d, %d lines%s; read by "
            "scripts/stats.py)</summary>\n\n<!-- incognita:events v%d night=%s part=%d/%d lines=%d -->\n"
            "~~~tsv\n%s~~~\n\n</details>\n"
            % (night, part, total, len(lines), note, BLOCK_VERSION, night, part, total, len(lines),
               "".join(x + "\n" for x in lines)))


LOG_SESSION = re.compile(r"^(\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2}) == session: (\S+) (\S+), model ([A-Za-z0-9._:\[\]-]+),")


def with_models(lines, logs):
    """Task lines written before the model was recorded (2026-11-19) get it from the night's log:
    the model of the last line `== session: <role> <target>, model <m>, …` of the same role and target
    before the task ended. Used by scripts/stats-backfill.sh (--log)."""
    starts = []
    for path in logs or []:
        try:
            with open(path, encoding="utf-8", errors="replace") as f:
                for line in f:
                    m = LOG_SESSION.match(line)
                    if m:
                        starts.append(m.groups())
        except (FileNotFoundError, IsADirectoryError, NotADirectoryError):
            continue
    if not starts:
        return lines
    out = []
    for line in lines:
        c = line.split("\t")
        m = SESSION_RE.search(c[4]) or EXIT_RE.search(c[4])
        if c[1] == "task" and m and m.group(m.re.groups) is None:
            ms = [s[3] for s in starts if s[1] == c[2] and s[2] == c[3] and s[0] <= c[0]]
            if ms and re.match(r"^[A-Za-z0-9._:\[\]-]+$", ms[-1]):
                c[4] = re.sub(r"\)\s*$", ", model %s)" % ms[-1], c[4])
                line = "\t".join(c)
        out.append(line)
    return out


def events_block(night, paths, budget=60000, logs=None):
    """The parts (Markdown texts) of the events of a night, each at most `budget` bytes."""
    if not NIGHT_RE.match(night):
        raise ValueError("bad night name: %r" % night)
    lines, dropped = event_lines(paths)
    lines = with_models(lines, logs)
    if not lines:
        return []
    room = budget - len(block_text(night, 99, 99, [], 999).encode())
    chunks, cur, size = [], [], 0
    for line in lines:
        n = len(line.encode()) + 1
        if cur and size + n > room:
            chunks.append(cur)
            cur, size = [], 0
        cur.append(line)
        size += n
    chunks.append(cur)
    return [block_text(night, k + 1, len(chunks), c, dropped) for k, c in enumerate(chunks)]


def read_blocks(body):
    """[(night, part, total, declared lines, [lines])] of the events blocks of a comment body."""
    out = []
    lines = (body or "").replace("\r\n", "\n").split("\n")
    i = 0
    while i < len(lines):
        m = MARK_RE.match(lines[i].strip())
        i += 1
        if not m or int(m.group(1)) != BLOCK_VERSION:
            continue
        if i >= len(lines) or not lines[i].startswith("~~~"):
            continue
        i += 1
        rows = []
        while i < len(lines) and not lines[i].startswith("~~~"):
            if LINE_RE.match(lines[i]):
                rows.append(lines[i])
            i += 1
        out.append((m.group(2), int(m.group(3)), int(m.group(4)), int(m.group(5)), rows))
    return out


# ---------------------------------------------------------------- GitHub (API or fixtures)
class Unavailable(Exception):
    pass


class Api:
    """The GitHub REST API with a token; any failure raises Unavailable."""

    def __init__(self, token):
        self.token = token
        self.calls = 0

    def get(self, path):
        req = urllib.request.Request("https://api.github.com/" + path,
                                     headers={"Accept": "application/vnd.github+json",
                                              "User-Agent": "incognita-stats"})
        req.add_header("Authorization", "Bearer " + self.token)
        self.calls += 1
        try:
            with urllib.request.urlopen(req, timeout=30) as r:
                return json.load(r)
        except Exception as e:  # network, rate limit, permissions
            raise Unavailable("%s: %s" % (path.split("?")[0], e))

    def pages(self, path, limit=30):
        out = []
        sep = "&" if "?" in path else "?"
        for page in range(1, limit + 1):
            batch = self.get("%s%sper_page=100&page=%d" % (path, sep, page))
            out += batch
            if len(batch) < 100:
                break
        return out

    def pulls(self):
        return self.pages("repos/%s/pulls?state=all" % REPO)

    def issues(self):
        return self.pages("repos/%s/issues?state=all&creator=%s" % (REPO, OWNER))

    def comments(self, n):
        return self.pages("repos/%s/issues/%d/comments" % (REPO, n))

    def check_runs(self, sha):
        return self.get("repos/%s/commits/%s/check-runs?check_name=%s&per_page=100"
                        % (REPO, sha, urllib.parse.quote(CI_CHECK))).get("check_runs", [])


class Fixtures:
    """The same answers from files: pulls.json, issues.json, comments/<n>.json (tests)."""

    def __init__(self, d):
        self.d = d
        self.calls = 0

    def load(self, name, default=None):
        try:
            with open(os.path.join(self.d, name), encoding="utf-8") as f:
                return json.load(f)
        except FileNotFoundError:
            if default is None:
                raise Unavailable("fixture %s missing" % name)
            return default

    def pulls(self):
        return self.load("pulls.json")

    def issues(self):
        return self.load("issues.json", [])

    def comments(self, n):
        return self.load(os.path.join("comments", "%d.json" % n), [])

    def check_runs(self, sha):
        return self.load(os.path.join("checks", "%s.json" % sha), {}).get("check_runs", [])


def source_from(fixtures):
    if fixtures:
        return Fixtures(fixtures), None
    if TOKEN:
        return Api(TOKEN), None
    return None, "no GitHub token (GH_TOKEN or GITHUB_TOKEN)"


# ---------------------------------------------------------------- pull requests and their comments
ROLE_LINE = re.compile(r"^Role: `([a-z-]+)`\. Target: `([^`]*)`\.")
MARKER = re.compile(r"^<!-- incognita:([a-z-]+):([0-9a-f]{40}) -->$")
VERDICT = re.compile(r"^Verdict:\s*([a-z_]+)", re.M)
DEFECT = re.compile(r"^\|\s*((?:SC|PF)\d+\.\d+)\s*\|\s*([FGLRP])\s*\|", re.M)
PAPER_DIR = re.compile(r"^(P\d{3})-[a-z0-9][a-z0-9-]*$")
PAPER_PREFIX = re.compile(r"^(P\d{3})\b")
REFEREES = ("referee-scope", "referee-proofs")
REVIEWS = ("review-pr", "review-statements", "review-roadmap")
REVIEW_ROLES = REFEREES + REVIEWS
LEAN_ROLES = ("prove", "formalize-statements")
FIX_KINDS = ("fix-pr", "fix-pr-nochange")
RUBRIC_ORDER = ("correctness", "reuse", "scope", "attribution", "api-design", "generality", "placement",
                "naming", "documentation", "proof-quality", "quality-pass")


def trusted(comments):
    """The comments of the owner's account whose first line is the loop's marker, oldest first:
    {kind, sha, body (marker removed), created_at, url}."""
    out = []
    for c in comments or []:
        if (c.get("user") or {}).get("login") != OWNER:
            continue
        lines = (c.get("body") or "").replace("\r\n", "\n").split("\n")
        m = MARKER.match(lines[0])
        if m:
            out.append({"kind": m.group(1), "sha": m.group(2), "body": "\n".join(lines[1:]),
                        "created_at": c.get("created_at") or "", "url": c.get("html_url") or ""})
    return sorted(out, key=lambda x: x["created_at"])


def verdict_of(body):
    m = VERDICT.search(body or "")
    if not m:
        return None
    v = m.group(1)
    return "major" if v == "minor" else v


def pr_record(p):
    body = p.get("body") or ""
    m = ROLE_LINE.match(body.split("\n", 1)[0])
    head, base = p.get("head") or {}, p.get("base") or {}
    hr, br = (head.get("repo") or {}).get("full_name"), (base.get("repo") or {}).get("full_name")
    ref = head.get("ref") or ""
    labels = [x.get("name") for x in p.get("labels") or []]
    state = ("merged" if p.get("merged_at") else "rejected" if p.get("state") == "closed" and "rejected" in labels
             else "closed" if p.get("state") == "closed" else "open")
    r = {"number": p.get("number"), "title": p.get("title") or "", "role": m.group(1) if m else None,
         "target": m.group(2) if m else None, "ref": ref, "state": state, "labels": labels,
         "created": p.get("created_at") or "", "merged": p.get("merged_at") or "",
         "closed": p.get("closed_at") or "", "by": "owner" if ref.startswith("owner/") else "agents",
         "login": (p.get("user") or {}).get("login") or "?", "sha": head.get("sha") or "",
         "body": body}
    mm = re.search(r"Model: `([^`]*)`", body.split("\n", 1)[0])
    r["model"] = mm.group(1) if mm else None
    r["agents"] = bool(m) and (hr is None or br is None or hr == br) \
        and (ref.startswith("agent/") or ref.startswith("owner/")) and (p.get("user") or {}).get("login") == OWNER
    pm = PAPER_DIR.match(r["target"] or "")
    tm = PAPER_PREFIX.match(r["title"])
    r["paper"] = pm.group(1) if pm else tm.group(1) if tm else None
    return r


def seconds_between(a, b):
    try:
        t0 = datetime.datetime.fromisoformat(a.replace("Z", "+00:00"))
        t1 = datetime.datetime.fromisoformat(b.replace("Z", "+00:00"))
    except (ValueError, AttributeError):
        return None
    return (t1 - t0).total_seconds()


def days(a, b):
    s = seconds_between(a, b)
    return None if s is None else round(s / 86400, 1)


def median(xs):
    xs = [x for x in xs if x is not None]
    return round(statistics.median(xs), 1) if xs else None


def mean(xs):
    xs = [x for x in xs if x is not None]
    return round(sum(xs) / len(xs), 2) if xs else None


def production(prs, tc):
    papers = []
    for r in prs:
        if r["role"] != "write-paper":
            continue
        cs = tc.get(r["number"], [])
        papers.append({"pr": r["number"], "paper": r["paper"], "by": r["by"], "state": r["state"],
                       "submitted": r["created"][:10], "accepted": r["merged"][:10] or None,
                       "accepted_at": r["merged"] or None,
                       "days_to_accept": days(r["created"], r["merged"]) if r["merged"] else None,
                       "revision_rounds": sum(1 for c in cs if c["kind"] == "revise"),
                       "repairs": sum(1 for c in cs if c["kind"] in ("revise-fix", "revise-fix-nochange")),
                       "scope_reports": sum(1 for c in cs if c["kind"] == "referee-scope"),
                       "proofs_reports": sum(1 for c in cs if c["kind"] == "referee-proofs")})
    acc = [p for p in papers if p["state"] == "merged"]
    count = collections.Counter(p["state"] for p in papers)
    by = {w: collections.Counter(p["state"] for p in papers if p["by"] == w) for w in ("agents", "owner")}
    revs = [r for r in prs if r["role"] == "revise"]
    return {"papers": sorted(papers, key=lambda p: p["pr"]),
            "written": len(papers), "accepted": count["merged"], "rejected": count["rejected"],
            "in_review": count["open"], "closed": count["closed"],
            "by": {w: {"written": sum(c.values()), "accepted": c["merged"], "rejected": c["rejected"],
                       "in_review": c["open"]} for w, c in by.items()},
            "revision_rounds_mean": mean([p["revision_rounds"] for p in acc]),
            "revision_rounds_max": max([p["revision_rounds"] for p in papers], default=None),
            "days_to_accept_median": median([p["days_to_accept"] for p in acc]),
            "days_to_accept_mean": mean([p["days_to_accept"] for p in acc]),
            "new_versions": {"opened": len(revs), "merged": sum(1 for r in revs if r["state"] == "merged")}}


def quality(prs, tc):
    ref_v = {k: collections.Counter() for k in REFEREES}
    rev_v = {k: collections.Counter() for k in REVIEWS}
    rub_v = collections.defaultdict(collections.Counter)
    defects = {k: collections.Counter() for k in REFEREES}
    first_round = {k: collections.Counter() for k in REFEREES}
    seen = set()
    lean = []
    for r in prs:
        cs = tc.get(r["number"], [])
        firsts = set()
        for c in cs:
            k, v = c["kind"], verdict_of(c["body"])
            if k in REFEREES:
                if v:
                    ref_v[k][v] += 1
                    if k not in firsts:
                        first_round[k][v] += 1
                        firsts.add(k)
                for did, cls in DEFECT.findall(c["body"]):
                    if (r["number"], did) not in seen:
                        seen.add((r["number"], did))
                        defects[k][cls] += 1
            elif k in REVIEWS and v:
                rev_v[k][v] += 1
            elif k.startswith("rubric-") and v:
                rub_v[k[len("rubric-"):]][v] += 1
        rubric = [c for c in cs if c["kind"].startswith("rubric-")]
        if r["role"] in LEAN_ROLES or rubric:
            lean.append({"pr": r["number"], "paper": r["paper"], "role": r["role"], "state": r["state"],
                         "fix_rounds": sum(1 for c in cs if c["kind"] in FIX_KINDS),
                         "reviews": sum(1 for c in cs if c["kind"] in ("review-pr", "review-statements")),
                         "changes_requested": sum(1 for c in cs if c["kind"] in ("review-pr", "review-statements")
                                                  and verdict_of(c["body"]) == "request_changes"),
                         "rubric_reports": len(rubric),
                         "blocks": sum(1 for c in rubric if verdict_of(c["body"]) == "block")})
    order = [x for x in RUBRIC_ORDER if x in rub_v] + sorted(x for x in rub_v if x not in RUBRIC_ORDER)
    return {"referee_verdicts": {k: dict(v) for k, v in ref_v.items()},
            "referee_first_round": {k: dict(v) for k, v in first_round.items()},
            "defects": {k: {c: v[c] for c in "FGLRP"} for k, v in defects.items()},
            "review_verdicts": {k: dict(v) for k, v in rev_v.items()},
            "rubric_verdicts": {x: {v: rub_v[x][v] for v in ("approve", "request_changes", "block")} for x in order},
            "lean_prs": sorted(lean, key=lambda x: x["pr"]),
            "fix_rounds_mean": mean([x["fix_rounds"] for x in lean if x["state"] == "merged"])}


PREDICTED_RE = re.compile(r"^\|\s*Predicted interest\s*\|\s*(\d+)\s*/\s*10\b", re.M)
INTEREST_RE = re.compile(r"^\|\s*Interest\s*\|\s*(\d+)\s*/\s*(10|5)\b[^|]*\|\s*([^|\n]*)", re.M)


def interest_from(tcs):
    """(score out of 10, one-line reason, report URL) of the trusted comments of the pull request
    that added a paper: the score of the last scope report that gives one (a score out of 5, of
    older reports, is doubled), the reason of the last substantive one; Nones without a score.
    Also used by scripts/site.py."""
    score = url = reason = None
    for c in reversed(tcs or []):
        if c["kind"] != "referee-scope":
            continue
        m = INTEREST_RE.search(c["body"])
        if not m:
            continue
        if score is None:
            score = int(m.group(1)) * (2 if m.group(2) == "5" else 1)
            url = c.get("url")
        r = m.group(3).strip()
        if len(r) > 30 and not re.match(r"(?i)(unchanged|same|as before)", r):
            reason = r
            break
    return score, reason or "", url


def predicted_from(tcs):
    """The authors' predicted interest (out of 10) copied by the last scope report that gives one
    (owner, 2026-11-23), or None."""
    for c in reversed(tcs or []):
        if c["kind"] == "referee-scope":
            m = PREDICTED_RE.search(c["body"])
            if m:
                return int(m.group(1))
    return None


def interest(prs, tc):
    rows = []
    for r in prs:
        if r["role"] == "write-paper" and r["paper"]:
            s, _reason, url = interest_from(tc.get(r["number"], []))
            p = predicted_from(tc.get(r["number"], []))
            rows.append({"paper": r["paper"], "pr": r["number"], "state": r["state"], "score": s, "url": url,
                         "predicted": p})
    scores = [x["score"] for x in rows if x["score"] is not None]
    gaps = [x["predicted"] - x["score"] for x in rows if x["score"] is not None and x["predicted"] is not None]
    return {"papers": sorted(rows, key=lambda x: x["paper"]), "median": median(scores), "mean": mean(scores),
            "distribution": {str(k): scores.count(k) for k in range(1, 11)},
            "overestimate_mean": mean(gaps), "overestimate_n": len(gaps)}


PR_KINDS = {"write-paper": "paper", "revise": "paper", "formalize-statements": "statements", "prove": "proofs",
            "bibliographer": "literature", "garden": "garden", "loop": "scripted", "propose-roadmap": "roadmap"}


def pr_kind(r):
    return PR_KINDS.get(r["role"], "other") if r["agents"] else "human"


def efficiency(all_prs, src, tasks, events, warnings):
    """Open to merge and the duration of the check "Build and check" (on the last head) per kind of
    pull request; failed, skipped and parked tasks."""
    merge_h = collections.defaultdict(list)
    for r in all_prs:
        if r["merged"]:
            s = seconds_between(r["created"], r["merged"])
            if s is not None:
                merge_h[pr_kind(r)].append(round(s / 3600, 1))
    ci = collections.defaultdict(list)
    fails = 0
    for r in all_prs:
        if not r["sha"] or src is None or fails >= 5:
            continue
        try:
            runs = [x for x in src.check_runs(r["sha"]) if x.get("name") == CI_CHECK
                    and x.get("started_at") and x.get("completed_at")]
            fails = 0
        except Unavailable as e:
            fails += 1
            if fails == 5:
                warnings.append("check runs not read any more after 5 failures (%s)" % e)
            continue
        if runs:
            x = max(runs, key=lambda y: y["completed_at"])
            s = seconds_between(x["started_at"], x["completed_at"])
            if s is not None:
                ci[pr_kind(r)].append(round(s / 60, 1))

    def summary(xs):
        return {"count": len(xs), "median": median(xs), "mean": mean(xs), "max": max(xs) if xs else None}
    kinds = sorted(set(merge_h) | set(ci))
    tk = tasks or []
    return {"open_to_merge_hours": {k: summary(merge_h.get(k, [])) for k in kinds},
            "ci_minutes": {k: summary(ci.get(k, [])) for k in kinds},
            "ci_minutes_all": summary([v for xs in ci.values() for v in xs]),
            "tasks": None if tasks is None else {
                "total": len(tk), "fail": sum(1 for t in tk if t["outcome"] == "fail"),
                "skip": sum(1 for t in tk if t["outcome"] == "skip"),
                "fail_by_role": dict(collections.Counter(t["role"] for t in tk if t["outcome"] == "fail").most_common()),
                "fail_reasons": dict(collections.Counter(t["detail"] for t in tk if t["outcome"] == "fail").most_common()),
                "skip_reasons": dict(collections.Counter(t["detail"] for t in tk if t["outcome"] == "skip").most_common()),
                "parked": sorted("%s %s" % (e[3], e[4]) for e in events or [] if e[2] == "parked"),
                "loop_restarts": sum(1 for e in events or [] if e[2] == "loop-died"),
                "refused": sum(1 for e in events or [] if e[2] == "refused")}}


def contributors(all_prs, form, tasks, by_role):
    """Humans (their merged pull requests, their papers), agents by role, models."""
    humans = collections.defaultdict(lambda: {"prs_merged": 0, "owner_papers": 0})
    for r in all_prs:
        if not r["agents"] and r["merged"]:
            humans[r["login"]]["prs_merged"] += 1
        if r["agents"] and r["by"] == "owner" and r["role"] in ("write-paper", "revise"):
            humans[r["login"]]["owner_papers"] += 1
    authors = collections.defaultdict(list)
    for p in form["papers"]:
        for a in p.get("human_authors") or []:
            authors[a].append(p["paper"])
    roles = collections.defaultdict(lambda: {"prs_opened": 0, "prs_merged": 0})
    models_prs = collections.Counter()
    for r in all_prs:
        if r["agents"] and r["ref"].startswith("agent/"):
            roles[r["role"]]["prs_opened"] += 1
            roles[r["role"]]["prs_merged"] += 1 if r["merged"] else 0
            if r["model"] and r["model"] != "-":
                models_prs[r["model"]] += 1
    for k, v in (by_role or {}).items():
        roles[k].update(sessions=v["sessions"], hours=round(v["seconds"] / 3600, 1), usd=v["usd"])
    return {"humans": dict(sorted(humans.items())), "human_authors": dict(sorted(authors.items())),
            "agents_by_role": dict(sorted(roles.items())), "prs_by_model": dict(models_prs.most_common())}


def milestones(prod, form, tasks):
    """Per paper: the cumulative cost of its sessions until its acceptance (merge of the pull request
    that added it) and until its Lean verification (level 2), when reached."""
    acc = {x["paper"]: x for x in (prod or {}).get("papers", []) if x["paper"]}
    out = {}
    for p in form["papers"]:
        k = p["paper"]
        ts = [t for t in tasks if t["paper"] == k]
        a = acc.get(k)
        at = iso_utc(a.get("accepted_at")) if a and a.get("accepted_at") else None
        vt = p.get("verified_at")
        out[k] = {"accepted_at": at, "verified_at": vt, "sessions": len(ts),
                  "usd_total": round(sum(t["usd"] or 0 for t in ts), 2),
                  "usd_to_acceptance": round(sum(t["usd"] or 0 for t in ts if t["time"] <= at), 2) if at else None,
                  "usd_to_verification": round(sum(t["usd"] or 0 for t in ts if t["time"] <= vt), 2) if vt else None}
    return out


# ---------------------------------------------------------------- the repository
def git(repo, *args):
    r = subprocess.run(["git", "-C", repo, "-c", "core.quotePath=false", *args], capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else ""


def merges(repo):
    """The merge commits of the loop (trailer Incognita-Role): by role, and the PR numbers."""
    out = git(repo, "log", "--format=%s%x1f%(trailers:key=Incognita-Role,valueonly,separator=%x2c)%x1f"
                     "%(trailers:key=Incognita-Reviews,valueonly,separator=%x2c)%x1e", "HEAD")
    by_role, numbers, owner_merged = collections.Counter(), {}, 0
    for rec in out.split("\x1e"):
        f = rec.strip("\n").split("\x1f")
        if len(f) < 3:
            continue
        m = re.search(r"\(#(\d+)\)\s*$", f[0])
        role = f[1].strip()
        if role:
            by_role[role] += 1
            if m:
                numbers[int(m.group(1))] = {"role": role, "reviews": f[2].strip()}
        elif m or f[0].startswith("Merge pull request #"):
            owner_merged += 1
    return {"by_role": dict(sorted(by_role.items())), "by_the_loop": sum(by_role.values()),
            "by_the_owner": owner_merged, "prs": numbers}


def utc(epoch):
    """'YYYY-MM-DD HH:MM:SS' in UTC, the format of the events' times (the server runs in UTC)."""
    return datetime.datetime.fromtimestamp(epoch, datetime.timezone.utc).strftime("%Y-%m-%d %H:%M:%S")


def iso_utc(s):
    """An ISO time of GitHub ('2026-11-16T10:00:00Z') in the format of the events' times."""
    return (s or "").replace("T", " ").replace("Z", "")[:19] or None


# Lean declarations (at the start of a line, after attributes and modifiers).
DECL_RE = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*"
                     r"(theorem|lemma|def|abbrev|instance|structure|class|inductive|alias|example|opaque|axiom)\b")
# A line at column 0 that ends the declaration before it (for the length of a proof).
TOP_RE = re.compile(r"^(?:@\[|/--|/-!|--|#|section\b|namespace\b|end\b|open\b|variable\b|attribute\b|set_option\b|"
                    r"universe\b|noncomputable section|private\b|protected\b|noncomputable\b|theorem\b|lemma\b|def\b|"
                    r"abbrev\b|instance\b|structure\b|class\b|inductive\b|alias\b|example\b|opaque\b|axiom\b|import\b)")
DEPRECATED_RE = re.compile(r"@\[\s*deprecated\b")


def lean_counts(text):
    """{files, lines, theorems, defs, deprecated} of one .lean file."""
    c = collections.Counter(files=1, lines=text.count("\n") + (0 if text.endswith("\n") or not text else 1))
    for line in text.splitlines():
        m = DECL_RE.match(line)
        if m:
            k = m.group(1)
            c["theorems" if k in ("theorem", "lemma") else "defs" if k in ("def", "abbrev") else "others"] += 1
    c["deprecated"] = len(DEPRECATED_RE.findall(text))
    return c


def proof_lengths(text):
    """[(name, lines)] of the theorems and lemmas of a file: from the declaration to the next top-level
    line, without the trailing blank lines."""
    lines = text.splitlines()
    out = []
    starts = [i for i, x in enumerate(lines) if DECL_RE.match(x)]
    for i in starts:
        m = DECL_RE.match(lines[i])
        if m.group(1) not in ("theorem", "lemma"):
            continue
        j = i + 1
        while j < len(lines) and not (lines[j][:1].strip() and TOP_RE.match(lines[j])):
            j += 1
        while j > i + 1 and not lines[j - 1].strip():
            j -= 1
        name = re.search(r"\b(?:theorem|lemma)\s+(\S+)", lines[i])
        out.append((name.group(1) if name else "?", j - i))
    return out


def lean_history(repo):
    """The Lean library under Incognita/ and Statements/: per day (the last commit of the day on the
    first-parent line of HEAD) files, lines, theorems and lemmas, defs, deprecated aliases; and the
    distribution of the proof lengths now."""
    days = collections.OrderedDict()
    for line in git(repo, "log", "--first-parent", "--format=%H %ct", "HEAD").splitlines():
        sha, ct = line.split()
        d = utc(int(ct))[:10]
        if d not in days:
            days[d] = sha   # newest first: the day's last commit
    trees, blobs = {}, set()
    for d, sha in days.items():
        files = []
        for row in git(repo, "ls-tree", "-r", sha, "--", "Incognita", "Statements").splitlines():
            meta, path = row.split("\t", 1)
            if path.endswith(".lean"):
                files.append((path, meta.split()[2]))
                blobs.add(meta.split()[2])
        trees[d] = files
    texts = {}
    if blobs:
        r = subprocess.run(["git", "-C", repo, "cat-file", "--batch"],
                           input=("\n".join(sorted(blobs)) + "\n").encode(), capture_output=True)
        data, k = r.stdout, 0
        while k < len(data):
            nl = data.index(b"\n", k)
            head = data[k:nl].decode().split()
            if len(head) < 3:
                break
            size = int(head[2])
            texts[head[0]] = data[nl + 1:nl + 1 + size].decode("utf-8", "replace")
            k = nl + 1 + size + 1
    counts = {b: lean_counts(t) for b, t in texts.items()}
    series = []
    for d in sorted(trees):
        row = {"day": d}
        for part in ("Incognita", "Statements"):
            c = sum((counts.get(b, collections.Counter()) for p, b in trees[d] if p.startswith(part + "/")),
                    collections.Counter())
            row[part] = {k: c.get(k, 0) for k in ("files", "lines", "theorems", "defs", "deprecated")}
        series.append(row)
    lengths = []
    if series:
        for p, b in trees[max(trees)]:
            if p.startswith("Incognita/"):
                lengths += [(p, n, k) for n, k in proof_lengths(texts.get(b, ""))]
    ks = sorted(k for _, _, k in lengths)
    buckets = collections.OrderedDict((b, 0) for b in ("1-5", "6-20", "21-50", "51-100", "101-200", ">200"))
    for k in ks:
        b = "1-5" if k <= 5 else "6-20" if k <= 20 else "21-50" if k <= 50 else "51-100" if k <= 100 \
            else "101-200" if k <= 200 else ">200"
        buckets[b] += 1
    return {"series": series, "proofs": {"count": len(ks), "median": median(ks), "max": ks[-1] if ks else None,
                                         "buckets": dict(buckets),
                                         "longest": [{"name": n, "file": p, "lines": k} for p, n, k in
                                                     sorted(lengths, key=lambda x: -x[2])[:5]]}}


TO_CHECK_RE = re.compile(r"\(\s*to be checked\s*\)", re.I)


def literature(repo):
    """References of literature/bibliography.json, source notes, and "(to be checked)" in the Lean
    files and the papers."""
    try:
        with open(os.path.join(repo, "literature", "bibliography.json"), encoding="utf-8") as f:
            refs = len(json.load(f))
    except (FileNotFoundError, ValueError):
        refs = None
    notes = sorted(x for x in os.listdir(os.path.join(repo, "literature", "notes"))
                   if x.endswith(".md") and x not in ("TEMPLATE.md", "README.md")) \
        if os.path.isdir(os.path.join(repo, "literature", "notes")) else []
    marks = {"lean": collections.Counter(), "papers": collections.Counter()}
    for top, kind, ext in (("Incognita", "lean", ".lean"), ("Statements", "lean", ".lean"), ("papers", "papers", ".tex")):
        for d, _dirs, files in os.walk(os.path.join(repo, top)):
            for fn in files:
                if not fn.endswith(ext) or (kind == "papers" and fn != "paper.tex"):
                    continue
                path = os.path.join(d, fn)
                with open(path, encoding="utf-8", errors="replace") as f:
                    n = len(TO_CHECK_RE.findall(f.read()))
                if n:
                    marks[kind][os.path.relpath(path, repo).replace(os.sep, "/")] = n
    return {"references": refs, "source_notes": len(notes),
            "to_be_checked": {k: {"occurrences": sum(v.values()), "files": dict(sorted(v.items()))} for k, v in marks.items()}}


def directions(repo, C, prs):
    """Candidate directions (roadmaps/*/directions.md) per roadmap: total, open, taken (an open paper
    pull request of the roadmap names the entry in its description), done (a paper on main lists it
    in META.toml), dropped."""
    tree = C.Tree(repo)
    out = {}
    for r in tree.ls("roadmaps"):
        text = tree.read("roadmaps/%s/directions.md" % r)
        if text is None or not C.ROADMAP_NAME.match(r):
            continue
        try:
            items = {i: (s, d) for i, s, d in C.items(tree, r) if re.match(r"^C\d+$", i)}
        except C.Fail:
            continue
        open_prs = [p for p in prs or [] if p["state"] == "open" and p["role"] == "write-paper" and p["target"] == r]
        row = collections.Counter(total=len(items))
        for i, (s, _d) in items.items():
            taken = any(re.search(r"\b%s\b" % i, p["body"] + " " + p["title"]) for p in open_prs)
            k = "dropped" if s == "dropped" else "done" if s == "covered" else "taken" if taken else "open"
            row[k] += 1
        out[r] = {k: row.get(k, 0) for k in ("total", "open", "taken", "done", "dropped")}
        if prs is None:
            out[r]["taken"] = None
    return out


def formalisation(repo, C):
    tree = C.Tree(repo)
    ps, certs = C.certify(tree, None)
    papers, levels = [], collections.Counter()
    for p in sorted(ps, key=lambda q: q.num):
        c = certs[p.prefix]
        k = sum(1 for s in c.frozen.values() if s == "proved")
        name = c.status if c.status in ("disputed", "withdrawn") else C.LEVEL_NAMES[c.level]
        levels["%d %s" % (c.level, name)] += 1
        papers.append({"paper": p.prefix, "dir": p.dir, "kind": p.kind, "roadmap": p.roadmap, "version": p.version,
                       "level": c.level, "status": name, "frozen": len(c.frozen), "proved": k,
                       "human_authors": [a for a in p.human_authors if isinstance(a, str)]
                       if isinstance(p.human_authors, list) else [],
                       "refuted": sum(1 for s in c.frozen.values() if s == "refuted"),
                       "errata": len(C.entries(p.errata, ("E",))),
                       "errata_open": len([e for e in C.entries(p.errata, ("E",)) if not e[1] and not e[2]]),
                       "corrections": len(C.entries(p.corrections, ("SC",))),
                       "corrections_resolved": len([e for e in C.entries(p.corrections, ("SC",)) if e[2]])})
    # Over time: the day each lock (frozen statement) and each proof marker reached the branch.
    log = git(repo, "log", "--reverse", "--diff-filter=A", "--format=@%ct", "--name-only", "HEAD", "--",
              "Statements", "catalogue/results")
    day, when, events = None, None, []
    for line in log.splitlines():
        if line.startswith("@"):
            when = utc(int(line[1:]))
            day = when[:10]
            continue
        m = re.match(r"^Statements/(P\d{3})/(.+)\.lock$", line)
        if m:
            events.append((day, m.group(1), "frozen", when))
        m = re.match(r"^catalogue/results/(P\d{3})-(.+)\.toml$", line)
        if m:
            events.append((day, m.group(1), "proved", when))
    # A Lean-verified paper (level 2 or more): verified when its last lock or proof marker arrived.
    for x in papers:
        ts = [e[3] for e in events if e[1] == x["paper"]]
        x["verified_at"] = max(ts) if certs[x["paper"]].verified and ts else None
    timeline = collections.defaultdict(list)
    tot = collections.defaultdict(lambda: [0, 0])
    for d, p, what, _ in events:
        tot[p][0 if what == "frozen" else 1] += 1
        if timeline[p] and timeline[p][-1][0] == d:
            timeline[p][-1] = [d, tot[p][0], tot[p][1]]
        else:
            timeline[p].append([d, tot[p][0], tot[p][1]])
    return {"papers": papers, "levels": dict(sorted(levels.items())), "timeline": dict(sorted(timeline.items())),
            "frozen": sum(p["frozen"] for p in papers), "proved": sum(p["proved"] for p in papers)}


# ---------------------------------------------------------------- nights: events and night reports
REPORT_HEAD = re.compile(r"^# Night report (\S+)\s*$", re.M)
REPORT_SPAN = re.compile(r"^(\d{4}-\d{2}-\d{2} \d{2}:\d{2}) → (\d{4}-\d{2}-\d{2} \d{2}:\d{2}) \(server time\)\. "
                         r"Stopped: (.*?)\.?\s*$", re.M)
REPORT_USAGE = re.compile(r"^Weekly usage of the subscription[^:]*: (.*?) at the start, (.*?) at the end; "
                          r"cap ([^;]*?)(?:; weekly reset ([^;]*?))?\.\s*$", re.M)
REPORT_TASK = re.compile(r"^- (\d{2}):(\d{2}) (\S+) (\S+): (.*)$")
# The session of a task event: "(turns N, Ss, $C)" or "(exit R, Ss)", since 2026-11-19 with ", model M"
# before the parenthesis closes (older events have none: model "unrecorded").
SESSION_RE = re.compile(r"\(turns (\d+|\?), (\d+)s, \$([0-9.]+|\?)(?:, model ([A-Za-z0-9._:\[\]-]+))?\)\s*$")
EXIT_RE = re.compile(r"\(exit (-?\d+), (\d+)s(?:, model ([A-Za-z0-9._:\[\]-]+))?\)\s*$")
MADE_RE = re.compile(r"\b(?:pr|draft) #(\d+)\b")


def pct(s):
    m = re.match(r"\s*(\d+(?:\.\d+)?) %", s or "")
    return float(m.group(1)) if m else None


def parse_report(body):
    m = REPORT_HEAD.search(body)
    if not m:
        return None
    rep = {"night": m.group(1), "start": None, "end": None, "stopped": None, "usage_start": None,
           "usage_end": None, "cap": None, "tasks": []}
    s = REPORT_SPAN.search(body)
    if s:
        rep["start"], rep["end"], rep["stopped"] = s.group(1), s.group(2), s.group(3)
    u = REPORT_USAGE.search(body)
    if u:
        rep["usage_start"], rep["usage_end"], rep["cap"] = pct(u.group(1)), pct(u.group(2)), pct(u.group(3))
    lines = body.split("\n")
    if "Tasks:" in lines and rep["start"]:
        # The task list of a night report is the whole events.tsv of its night (every run of it),
        # in order, to the minute: a time earlier than the one before is on the next day.
        day = datetime.date.fromisoformat(rep["night"]) if re.match(r"^\d{4}-\d{2}-\d{2}$", rep["night"]) \
            else datetime.date.fromisoformat(rep["start"][:10])
        last = None
        for line in lines[lines.index("Tasks:") + 1:]:
            t = REPORT_TASK.match(line)
            if not t:
                if line.startswith("</details>"):
                    break
                continue
            hm = (int(t.group(1)), int(t.group(2)))
            if last is not None and hm < last:
                day += datetime.timedelta(days=1)
            last = hm
            rep["tasks"].append(("%s %02d:%02d:00" % (day.isoformat(), hm[0], hm[1]), "task", t.group(3),
                                 t.group(4), t.group(5)))
    return rep


def session(text):
    """(outcome, turns, seconds, usd, model) of the text of a task event."""
    w = text.split()
    outcome = w[0] if w else "?"
    m = SESSION_RE.search(text)
    if m:
        return (outcome, None if m.group(1) == "?" else int(m.group(1)), int(m.group(2)),
                None if m.group(3) == "?" else float(m.group(3)), m.group(4))
    m = EXIT_RE.search(text)
    if m:
        return outcome, None, int(m.group(2)), None, m.group(3)
    return outcome, None, None, None, None


def nights(issue_comments):
    """(events, reports, warnings): events [(night, time, kind, role, target, text, source)], the
    lines of the blocks and, for what no block covers, the task lists of the night reports."""
    warnings, seen, events, reports = [], set(), [], []
    parts = collections.defaultdict(dict)
    for c in issue_comments or []:
        if (c.get("user") or {}).get("login") != OWNER:
            continue
        body = c.get("body") or ""
        for night, part, total, declared, rows in read_blocks(body):
            parts[night][part] = total
            if len(rows) != declared:
                warnings.append("events of the night of %s, part %d/%d: %d lines instead of %d"
                                % (night, part, total, len(rows), declared))
            for line in rows:
                if (night, line) in seen:
                    continue
                seen.add((night, line))
                events.append((night, *line.split("\t"), "events"))
        if MARKER.match(body.split("\n", 1)[0]) and body.split("\n", 1)[0].startswith("<!-- incognita:night-report:"):
            rep = parse_report(body)
            if rep:
                reports.append(rep)
    for night, ps in parts.items():
        total = max(ps.values())
        missing = [k for k in range(1, total + 1) if k not in ps]
        if missing:
            warnings.append("events of the night of %s: parts %s missing" % (night, ", ".join(map(str, missing))))
    covered = {(e[0], e[1][:16], e[3], e[4], e[5].split(" ", 1)[0]) for e in events if e[2] == "task"}
    have = set()
    for rep in sorted(reports, key=lambda r: r["start"] or ""):
        for t in rep["tasks"]:
            k = (rep["night"], t[0][:16], t[2], t[3], t[4].split(" ", 1)[0])
            if k in covered or k in have:
                continue
            have.add(k)
            events.append((rep["night"], *t, "report"))
    events.sort(key=lambda e: (e[1], e[0]))
    return events, reports, warnings


def category(role):
    if role.startswith("rubric-"):
        return "rubrics"
    return "reviews" if role in REVIEW_ROLES else "writing"


# The stages of a paper's way (AGENTS.md 5.5): the role of a session gives its stage; a review, a
# rubric or a fix round belongs to the stage of the pull request it works on.
STAGES = ("writing", "refereeing", "acceptance", "statements", "proofs", "gardening", "bibliography", "other")
STAGE_OF_ROLE = {"write-paper": "writing", "referee-scope": "refereeing", "referee-proofs": "refereeing",
                 "revise": "refereeing", "formalize-statements": "statements", "review-statements": "statements",
                 "prove": "proofs", "garden": "gardening", "bibliographer": "bibliography"}


def stage_of(role, pr_role):
    if role in ("review-pr", "fix-pr") or role.startswith("rubric-"):
        return "refereeing" if pr_role in ("write-paper", "revise") else STAGE_OF_ROLE.get(pr_role or "", "other")
    return STAGE_OF_ROLE.get(role, "other")


def cost(events, reports, prinfo, merged_prs):
    tasks = []
    created = {}   # PR -> (role, paper) of the session that opened it
    for night, time, kind, role, target, text, src in events:
        if kind != "task":
            continue
        outcome, turns, secs, usd, model = session(text)
        m = MADE_RE.search(text)
        pm = PAPER_DIR.match(target)
        if m:
            created.setdefault(int(m.group(1)), (role, pm.group(1) if pm else None))
        w = text.split()
        tasks.append({"night": night, "time": time, "role": role, "target": target, "outcome": outcome,
                      "detail": w[1] if len(w) > 1 else "", "turns": turns, "seconds": secs, "usd": usd,
                      "model": model or "unrecorded", "made": int(m.group(1)) if m else None,
                      "paper": pm.group(1) if pm else None, "quota_cut": "quota-cut" in w[:3], "source": src})

    def pr_role(n):
        if n in prinfo:
            return prinfo[n]["role"]
        return created.get(n, (None,))[0] or (merged_prs.get(n) or {}).get("role")

    def pr_paper(n):
        if n in prinfo and prinfo[n]["paper"]:
            return prinfo[n]["paper"]
        return created.get(n, (None, None))[1]

    def is_lean(n):
        if n in prinfo:
            return prinfo[n]["role"] in LEAN_ROLES or prinfo[n].get("lean", False)
        return created.get(n, (None,))[0] in LEAN_ROLES or (merged_prs.get(n) or {}).get("role") in LEAN_ROLES

    def add(d, t):
        d["sessions"] += 1
        d["seconds"] += t["seconds"] or 0
        d["usd"] += t["usd"] or 0

    def zero():
        return {"sessions": 0, "seconds": 0, "usd": 0.0}

    by_role = collections.defaultdict(lambda: {"sessions": 0, "ok": 0, "fail": 0, "skip": 0, "seconds": 0,
                                               "usd": 0.0, "turns": 0})
    per_paper = collections.defaultdict(lambda: {c: zero() for c in ("writing", "reviews", "rubrics")})
    per_pr = collections.defaultdict(lambda: {c: zero() for c in ("writing", "reviews", "rubrics")})
    by_stage = {s: zero() for s in STAGES}
    by_model = collections.defaultdict(zero)
    for t in tasks:
        r = by_role[t["role"]]
        r["sessions"] += 1
        r[t["outcome"] if t["outcome"] in ("ok", "fail", "skip") else "fail"] += 1
        r["seconds"] += t["seconds"] or 0
        r["usd"] += t["usd"] or 0
        r["turns"] += t["turns"] or 0
        pr = int(t["target"]) if t["target"].isdigit() else t["made"]
        paper = t["paper"] or (pr_paper(pr) if pr else None)
        t["pr"], t["paper"] = pr, paper
        t["stage"] = stage_of(t["role"], pr_role(pr) if pr else None)
        if t["role"] == "fix-pr" and t["target"] == "main":
            t["stage"] = "other"
        add(by_stage[t["stage"]], t)
        add(by_model[t["model"]], t)
        cat = category(t["role"])
        if paper:
            add(per_paper[paper][cat], t)
        if pr and is_lean(pr):
            add(per_pr[pr][cat], t)
    # Per night: the sessions, the waits, the usage (night reports: start and end of every run).
    nights_out = collections.OrderedDict()
    keys = sorted({e[0] for e in events} | {r["night"] for r in reports})
    for k in keys:
        nt = [t for t in tasks if t["night"] == k]
        ne = [e for e in events if e[0] == k]
        runs = sorted([r for r in reports if r["night"] == k], key=lambda r: r["start"] or "")
        waits = collections.Counter()
        for e in ne:
            if e[2] == "quota-wait":
                m = re.match(r"(\d+)s(?: \((.*?)\))?", e[5])
                if m:
                    why = m.group(2) or "?"
                    why = ("rate limit" if why.startswith("rate limit") else "usage unknown" if why.startswith("usage unknown")
                           else "five-hour window" if "five-hour" in why else why)
                    waits[why] += int(m.group(1))
        readings = [float(e[5].split()[1]) for e in ne if e[2] == "usage" and e[5].startswith("ok ")
                    and re.match(r"^\d+(\.\d+)?$", e[5].split()[1] if len(e[5].split()) > 1 else "")]
        deltas = [r["usage_end"] - r["usage_start"] for r in runs
                  if r["usage_start"] is not None and r["usage_end"] is not None and r["usage_end"] >= r["usage_start"]]
        sources = sorted({e[6] for e in ne})
        nights_out[k] = {
            "sessions": len(nt), "ok": sum(1 for t in nt if t["outcome"] == "ok"),
            "fail": sum(1 for t in nt if t["outcome"] == "fail"), "skip": sum(1 for t in nt if t["outcome"] == "skip"),
            "seconds": sum(t["seconds"] or 0 for t in nt), "usd": round(sum(t["usd"] or 0 for t in nt), 2),
            "merges": sum(1 for e in ne if e[2] == "merge") if "events" in sources else None,
            "quota_wait_min": {w: round(s / 60) for w, s in waits.items()} if "events" in sources else None,
            "idle_min": round(sum(int(m.group(1)) for e in ne if e[2] == "idle"
                                  for m in [re.match(r"(\d+)s", e[5])] if m) / 60) if "events" in sources else None,
            "quota_cuts": sum(1 for t in nt if t["quota_cut"]),
            "rate_limits": sum(1 for e in ne if e[2] == "quota"),
            # A stop at the cap: its event, or (nights without events) the reason of the run's report.
            "weekly_cap": max(sum(1 for e in ne if e[2] == "weekly-cap"),
                              sum(1 for r in runs if (r["stopped"] or "").startswith("weekly cap"))),
            "usage_start": runs[0]["usage_start"] if runs else None,
            "usage_end": runs[-1]["usage_end"] if runs else (readings[-1] if readings else None),
            "usage_max": max(readings) if readings else None,
            "usage_points": round(sum(deltas), 1) if deltas else None,
            "cap": runs[-1]["cap"] if runs else None,
            "runs": [{"start": r["start"], "end": r["end"], "stopped": r["stopped"], "usage_start": r["usage_start"],
                      "usage_end": r["usage_end"], "cap": r["cap"]} for r in runs],
            "source": "+".join(sources) or "report"}
    pts = [(n["usd"], n["usage_points"]) for n in nights_out.values() if n["usage_points"]]
    for r in by_role.values():
        r["usd"] = round(r["usd"], 2)
    for d in list(per_paper.values()) + list(per_pr.values()) + [by_stage, by_model]:
        for c in d.values():
            c["usd"] = round(c["usd"], 2)
    by_stage["acceptance"]["merges"] = sum(1 for e in events if e[2] == "merge")   # collect() takes the trailers'
    return {"sessions": len(tasks), "seconds": sum(t["seconds"] or 0 for t in tasks),
            "by_stage": by_stage,
            "by_model": dict(sorted(by_model.items(), key=lambda kv: -kv[1]["usd"])),
            "_tasks": tasks,
            "usd": round(sum(t["usd"] or 0 for t in tasks), 2),
            "by_role": dict(sorted(by_role.items(), key=lambda kv: -kv[1]["usd"])),
            "per_night": nights_out,
            "per_paper": dict(sorted(per_paper.items())),
            "per_lean_pr": {str(k): dict(v, paper=pr_paper(k)) for k, v in sorted(per_pr.items())},
            "usd_per_weekly_point": round(sum(u for u, _ in pts) / sum(p for _, p in pts), 2) if pts else None,
            "quota": {"sessions_cut": sum(1 for t in tasks if t["quota_cut"]),
                      "rate_limits": sum(n["rate_limits"] for n in nights_out.values()),
                      "weekly_cap_stops": sum(n["weekly_cap"] for n in nights_out.values()),
                      "wait_min": dict(sum((collections.Counter(n["quota_wait_min"] or {}) for n in nights_out.values()),
                                           collections.Counter()))}}


# ---------------------------------------------------------------- everything
def collect(repo=".", fixtures=None):
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import certify as C  # noqa: E402  (only here: events-block runs without it)

    src, why = source_from(fixtures)
    data = {"generated": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%d %H:%M UTC"),
            "repo": REPO, "head": git(repo, "rev-parse", "--short=12", "HEAD").strip() or None,
            "github": {"available": False, "reason": why}, "warnings": []}
    data["formalisation"] = formalisation(repo, C)
    mg = merges(repo)
    data["merges"] = {k: v for k, v in mg.items() if k != "prs"}
    prs, tc, issue_comments = [], {}, None
    if src is not None:
        try:
            prs = [pr_record(p) for p in src.pulls()]
            for r in prs:
                if r["agents"]:
                    tc[r["number"]] = trusted(src.comments(r["number"]))
            n = os.environ.get("INCOGNITA_REPORT_ISSUE")
            if not (n and n.isdigit()):
                n = next((i["number"] for i in src.issues() if i.get("title") == REPORT_TITLE
                          and "pull_request" not in i and (i.get("user") or {}).get("login") == OWNER), None)
            issue_comments = src.comments(int(n)) if n else []
            if not n:
                data["warnings"].append('no issue "%s" found' % REPORT_TITLE)
            data["github"] = {"available": True, "reason": None, "calls": src.calls, "report_issue": int(n) if n else None}
        except Unavailable as e:
            data["github"] = {"available": False, "reason": str(e)}
            prs, tc, issue_comments = [], {}, None
    all_prs = prs
    prs = [r for r in prs if r["agents"]]
    gh_ok = data["github"]["available"]
    if gh_ok:
        data["production"] = production(prs, tc)
        data["quality"] = quality(prs, tc)
        for x in data["quality"]["lean_prs"]:
            x["merged_by_the_loop"] = x["pr"] in mg["prs"]
        data["interest"] = interest(prs, tc)
    else:
        data["production"] = data["quality"] = data["interest"] = None
    lean_prs = {x["pr"] for x in (data["quality"] or {}).get("lean_prs", [])}
    prinfo = {r["number"]: dict(r, lean=r["number"] in lean_prs) for r in prs}
    tasks = events = None
    if issue_comments is not None:
        events, reports, w = nights(issue_comments)
        data["warnings"] += w
        data["cost"] = cost(events, reports, prinfo, mg["prs"])
        tasks = data["cost"].pop("_tasks")
        # Acceptance: the loop's merges, all of them (merge trailers), not only the nights with events.
        data["cost"]["by_stage"]["acceptance"]["merges"] = mg["by_the_loop"]
        data["cost"]["milestones"] = milestones(data["production"], data["formalisation"], tasks)
        data["nights"] = {"with_events": sorted({e[0] for e in events if e[6] == "events"}),
                          "from_reports_only": sorted({e[0] for e in events if e[6] == "report"}
                                                      - {e[0] for e in events if e[6] == "events"})}
    else:
        data["cost"] = data["nights"] = None
    data["contributors"] = contributors(all_prs, data["formalisation"], tasks,
                                        (data["cost"] or {}).get("by_role")) if gh_ok else None
    if data["contributors"] is not None:
        data["contributors"]["models"] = (data["cost"] or {}).get("by_model")
    data["efficiency"] = efficiency(all_prs, src if gh_ok else None, tasks, events, data["warnings"]) if gh_ok else None
    data["lean"] = lean_history(repo)
    data["literature"] = literature(repo)
    data["directions"] = directions(repo, C, prs if gh_ok else None)
    if gh_ok:
        data["github"]["calls"] = src.calls
    return data


# ---------------------------------------------------------------- HTML fragment
def fmt(x, nd=1):
    if x is None:
        return "–"
    if isinstance(x, float):
        return ("%%.%df" % nd) % x
    return str(x)


def hours(s):
    return fmt(round((s or 0) / 3600, 1))


def money(x):
    return "–" if x is None else "$%.0f" % x if x >= 100 else "$%.2f" % x


def table(head, rows, num=()):
    e = html.escape
    out = ['<div class="scroll"><table><thead><tr>%s</tr></thead><tbody>'
           % "".join('<th%s>%s</th>' % (' class="n"' if i in num else "", e(h)) for i, h in enumerate(head))]
    for r in rows:
        out.append("<tr>%s</tr>" % "".join('<td%s>%s</td>' % (' class="n"' if i in num else "", c)
                                          for i, c in enumerate(r)))
    if not rows:
        out.append('<tr><td colspan="%d">(none)</td></tr>' % len(head))
    out.append("</tbody></table></div>")
    return "\n".join(out)


def bar(x, top):
    w = 0 if not top or not x else max(2, round(100 * x / top))
    return '<span class="bar" style="width:%dpx"></span>' % w


def pr_link(n):
    return '<a href="https://github.com/%s/pull/%d">#%d</a>' % (html.escape(REPO), n, n)


def html_fragment(d):
    e = html.escape
    out = []
    p, q, f, c = d.get("production"), d.get("quality"), d["formalisation"], d.get("cost")
    gh = d["github"]
    if not gh["available"]:
        out.append('<p class="warn">GitHub could not be read (%s): production, quality and cost are not shown.</p>'
                   % e(gh["reason"] or "?"))
    # Production
    out.append('<section><h2 id="production">Production</h2>')
    if p:
        out.append("<p>%d papers written (%d by the agents, %d by the owner): %d accepted, %d rejected, %d in review. "
                   "Accepted papers: median %s days from submission to acceptance, %s revision rounds on average. "
                   "New versions of accepted papers: %d opened, %d merged. Merges by the loop: %d.</p>"
                   % (p["written"], p["by"]["agents"]["written"], p["by"]["owner"]["written"], p["accepted"],
                      p["rejected"], p["in_review"], fmt(p["days_to_accept_median"]), fmt(p["revision_rounds_mean"]),
                      p["new_versions"]["opened"], p["new_versions"]["merged"], d["merges"]["by_the_loop"]))
        out.append(table(["Paper", "Pull request", "By", "State", "Submitted", "Accepted", "Days",
                          "Revision rounds", "Repairs", "Scope reports", "Proofs reports"],
                         [[e(x["paper"] or "?"), pr_link(x["pr"]), e(x["by"]), e(x["state"]), e(x["submitted"]),
                           e(x["accepted"] or "–"), fmt(x["days_to_accept"]), fmt(x["revision_rounds"]),
                           fmt(x["repairs"]), fmt(x["scope_reports"]), fmt(x["proofs_reports"])]
                          for x in p["papers"]], num=(6, 7, 8, 9, 10)))
    out.append(table(["Role", "Pull requests merged by the loop"],
                     [[e(r), fmt(n)] for r, n in d["merges"]["by_role"].items()], num=(1,)))
    out.append("</section>")
    # Quality
    if q:
        out.append('<section><h2 id="quality">Quality</h2>')
        out.append("<h3>Referees</h3>")
        vs = ("accept", "major", "reject")
        out.append(table(["Referee"] + ["%s (all reports)" % v for v in vs] + ["%s (first report)" % v for v in vs],
                         [[e(k)] + [fmt(q["referee_verdicts"][k].get(v, 0)) for v in vs]
                          + [fmt(q["referee_first_round"][k].get(v, 0)) for v in vs] for k in REFEREES],
                         num=range(1, 7)))
        out.append("<p>Defects raised (each defect once, by its ID): F fatal, G gap, L local error, R readability, "
                   "P presentation (AGENTS.md 5.4).</p>")
        out.append(table(["Referee", "F", "G", "L", "R", "P"],
                         [[e(k)] + [fmt(q["defects"][k][x]) for x in "FGLRP"] for k in REFEREES], num=range(1, 6)))
        out.append("<h3>Reviews and rubrics</h3>")
        rv = ("approve", "request_changes", "reject")
        out.append(table(["Review"] + list(rv), [[e(k)] + [fmt(q["review_verdicts"][k].get(v, 0)) for v in rv]
                                                  for k in REVIEWS], num=(1, 2, 3)))
        out.append(table(["Rubric (Tau Ceti)", "approve", "request_changes", "block"],
                         [[e(k)] + [fmt(v[x]) for x in ("approve", "request_changes", "block")]
                          for k, v in q["rubric_verdicts"].items()], num=(1, 2, 3)))
        out.append("<h3>Lean pull requests</h3><p>Fix rounds per merged Lean pull request: %s on average.</p>"
                   % fmt(q["fix_rounds_mean"]))
        lp = (c or {}).get("per_lean_pr", {})
        out.append(table(["Pull request", "Paper", "Role", "State", "Fix rounds", "Reviews", "Changes requested",
                          "Rubric reports", "Blocks", "Cost: writing", "reviews", "rubrics"],
                         [[pr_link(x["pr"]), e(x["paper"] or "–"), e(x["role"] or "?"), e(x["state"]),
                           fmt(x["fix_rounds"]), fmt(x["reviews"]), fmt(x["changes_requested"]),
                           fmt(x["rubric_reports"]), fmt(x["blocks"])]
                          + ([money(lp[str(x["pr"])][k]["usd"]) for k in ("writing", "reviews", "rubrics")]
                             if str(x["pr"]) in lp else ["–", "–", "–"])
                          for x in q["lean_prs"]], num=range(4, 12)))
        out.append("</section>")
    # Formalisation
    out.append('<section><h2 id="formalisation">Formalisation</h2>')
    out.append("<p>%d frozen statements, %d proved. Papers by certification level: %s.</p>"
               % (f["frozen"], f["proved"], e(", ".join("%s: %d" % kv for kv in f["levels"].items()) or "none")))
    out.append(table(["Paper", "Version", "Roadmap", "Level", "Frozen", "Proved", "Refuted", "Errata (open)",
                      "Statement corrections (resolved)"],
                     [[e(x["paper"]), fmt(x["version"]), e(x["roadmap"] or "–"), e("%d %s" % (x["level"], x["status"])),
                       fmt(x["frozen"]), fmt(x["proved"]), fmt(x["refuted"]), "%d (%d)" % (x["errata"], x["errata_open"]),
                       "%d (%d)" % (x["corrections"], x["corrections_resolved"])] for x in f["papers"]],
                     num=(1, 4, 5, 6, 7, 8)))
    tl = f["timeline"]
    if tl:
        papers = list(tl)
        dates = sorted({x[0] for v in tl.values() for x in v})
        rows = []
        for dt in dates:
            row = [e(dt)]
            for pp in papers:
                last = [x for x in tl[pp] if x[0] <= dt]
                row.append("%d / %d" % (last[-1][2], last[-1][1]) if last else "–")
            rows.append(row)
        out.append("<h3>Over time</h3><p>Proved / frozen statements of each paper, on the day they reached <code>main</code>.</p>")
        out.append(table(["Day"] + papers, rows, num=range(1, len(papers) + 1)))
    out.append("</section>")
    # Cost
    if c:
        out.append('<section><h2 id="cost">Cost</h2>')
        out.append("<p>%d sessions, %s hours, %s. The dollar figures are the API-equivalent cost reported by Claude "
                   "Code for each session; the sessions run on the owner's subscription, which bills by weekly usage, "
                   "not per session. %s</p>"
                   % (c["sessions"], hours(c["seconds"]), money(c["usd"]),
                      "About %s per point of weekly usage." % money(c["usd_per_weekly_point"])
                      if c["usd_per_weekly_point"] else ""))
        qc = c["quota"]
        out.append("<p>Quota: %d sessions cut by a limit, %d rate limits, %d stops at the weekly cap; waits %s.</p>"
                   % (qc["sessions_cut"], qc["rate_limits"], qc["weekly_cap_stops"],
                      e(", ".join("%s %d min" % kv for kv in sorted(qc["wait_min"].items())) or "none")))
        top = max([r["usd"] for r in c["by_role"].values()], default=0)
        out.append("<h3>By role</h3>")
        out.append(table(["Role", "Sessions", "ok", "fail", "skip", "Hours", "Cost", "", "Cost per session"],
                         [[e(k), fmt(r["sessions"]), fmt(r["ok"]), fmt(r["fail"]), fmt(r["skip"]), hours(r["seconds"]),
                           money(r["usd"]), bar(r["usd"], top), money(r["usd"] / r["sessions"] if r["sessions"] else None)]
                          for k, r in c["by_role"].items()], num=(1, 2, 3, 4, 5, 6, 8)))
        top = max([n["usd"] for n in c["per_night"].values()], default=0)
        out.append("<h3>By night</h3><p>Weekly usage: the figure of claude.ai at the start of the night's first run "
                   "and at the end of its last; points used: the sum over its runs. Nights before 2026-11-19 come from "
                   "the task lists of the night reports (sessions only).</p>")
        out.append(table(["Night", "Sessions", "Hours", "Cost", "", "Merges", "Quota waits (min)", "Idle (min)",
                          "Cut by a limit", "Weekly usage", "Points used", "Stopped"],
                         [[e(k), fmt(n["sessions"]), hours(n["seconds"]), money(n["usd"]), bar(n["usd"], top),
                           fmt(n["merges"]), fmt(sum(n["quota_wait_min"].values()) if n["quota_wait_min"] is not None else None),
                           fmt(n["idle_min"]), fmt(n["quota_cuts"] + n["rate_limits"]),
                           "%s → %s %%" % (fmt(n["usage_start"], 0), fmt(n["usage_end"], 0)),
                           fmt(n["usage_points"], 0), e("; ".join(r["stopped"] or "?" for r in n["runs"]) or "–")]
                          for k, n in c["per_night"].items()], num=(1, 2, 3, 5, 6, 7, 8, 10)))
        out.append("<h3>By paper</h3><p>Every session on the paper, its pull requests and its Lean pull requests: "
                   "writing (authors' roles), reviews (referees and reviews), rubrics.</p>")
        out.append(table(["Paper", "Writing", "Reviews", "Rubrics", "Total", "Sessions"],
                         [[e(k)] + [money(v[x]["usd"]) for x in ("writing", "reviews", "rubrics")]
                          + [money(sum(v[x]["usd"] for x in v)), fmt(sum(v[x]["sessions"] for x in v))]
                          for k, v in c["per_paper"].items()], num=(1, 2, 3, 4, 5)))
        out.append("</section>")
    out.append(html_more(d))
    notes = []
    if d.get("nights"):
        notes.append("Nights with raw events: %s; from the night reports only: %s."
                     % (", ".join(d["nights"]["with_events"]) or "none", ", ".join(d["nights"]["from_reports_only"]) or "none"))
    for w in d.get("warnings") or []:
        notes.append("Warning: %s." % w)
    if notes:
        out.append('<p class="sub">%s</p>' % e(" ".join(notes)))
    return "\n".join(out)


def html_more(d):
    """The sections added on 2026-11-19 (owner): stages, contributors, interest, Lean library,
    efficiency, literature and directions."""
    e = html.escape
    out = []
    c = d.get("cost")
    if c:
        out.append('<section><h2 id="stages">Cost by stage</h2><p>The stages of a paper (AGENTS.md 5.5): a review, '
                   'a rubric or a fix round counts in the stage of the pull request it works on; acceptance is the '
                   "loop's merges (no session).</p>")
        st = c["by_stage"]
        top = max([v["usd"] for v in st.values()], default=0)
        out.append(table(["Stage", "Sessions", "Hours", "Cost", ""],
                         [[e(k) + (" (%d merges)" % v["merges"] if "merges" in v else ""), fmt(v["sessions"]),
                           hours(v["seconds"]), money(v["usd"]), bar(v["usd"], top)] for k, v in st.items()],
                         num=(1, 2, 3)))
        ms = c.get("milestones") or {}
        out.append("<h3>Per paper, to acceptance and to Lean verification</h3><p>Cost of the sessions on the paper "
                   "(its pull requests, its statements and proofs) until the merge of the pull request that added it, "
                   "and until it was Lean-verified (level 2), when it was.</p>")
        out.append(table(["Paper", "Accepted", "To acceptance", "Lean-verified", "To verification", "Total", "Sessions"],
                         [[e(k), e((v["accepted_at"] or "–")[:10]), money(v["usd_to_acceptance"]),
                           e((v["verified_at"] or "–")[:10]), money(v["usd_to_verification"]), money(v["usd_total"]),
                           fmt(v["sessions"])] for k, v in ms.items()], num=(2, 4, 5, 6)))
        out.append("</section>")
    k = d.get("contributors")
    if k:
        out.append('<section><h2 id="contributors">Contributors</h2><h3>Humans</h3>')
        out.append(table(["GitHub account", "Pull requests merged (human)", "Papers submitted (owner/* branches)"],
                         [[e(n), fmt(v["prs_merged"]), fmt(v["owner_papers"])] for n, v in k["humans"].items()],
                         num=(1, 2)))
        out.append(table(["Human author (META.toml)", "Papers"],
                         [[e(n), e(", ".join(v))] for n, v in k["human_authors"].items()]))
        out.append("<h3>Agents</h3>")
        out.append(table(["Role", "Pull requests opened", "merged", "Sessions", "Hours", "Cost"],
                         [[e(n), fmt(v["prs_opened"]), fmt(v["prs_merged"]), fmt(v.get("sessions")), fmt(v.get("hours")),
                           money(v.get("usd"))] for n, v in k["agents_by_role"].items()], num=(1, 2, 3, 4, 5)))
        out.append("<h3>Models</h3><p>The model of each session (recorded since 2026-11-19; earlier ones from the "
                   "night's log when it was backfilled, else unrecorded).</p>")
        out.append(table(["Model", "Sessions", "Hours", "Cost"],
                         [[e(n), fmt(v["sessions"]), hours(v["seconds"]), money(v["usd"])]
                          for n, v in (k.get("models") or {}).items()], num=(1, 2, 3)))
        out.append("</section>")
    i = d.get("interest")
    if i:
        out.append('<section><h2 id="interest">Interest</h2><p>The score out of 10 of the scope referee, on the pull '
                   "request that added the paper (its last report that gives one): median %s, mean %s. The authors' "
                   "predicted score minus the referee's, on average: %s (%s papers).</p>"
                   % (fmt(i["median"]), fmt(i["mean"]), fmt(i.get("overestimate_mean")), fmt(i.get("overestimate_n", 0))))
        top = max(i["distribution"].values(), default=0)
        out.append(table(["Score", "Papers", ""], [[e(s), fmt(n), bar(n, top)] for s, n in i["distribution"].items()],
                         num=(1,)))
        out.append(table(["Paper", "Pull request", "State", "Score", "Predicted"],
                         [[e(x["paper"]), pr_link(x["pr"]), e(x["state"]),
                           ('<a href="%s">%d/10</a>' % (e(x["url"]), x["score"])) if x["score"] is not None else "–",
                           ("%d/10" % x["predicted"]) if x.get("predicted") is not None else "–"]
                          for x in i["papers"]], num=(3, 4)))
        out.append("</section>")
    lean = d.get("lean")
    if lean and lean["series"]:
        out.append('<section><h2 id="lean">Lean library</h2><p>Per day, on <code>main</code> (its last commit of the '
                   "day): the files and lines of <code>Incognita/</code> (the library) and <code>Statements/</code> (the "
                   "frozen statements), their theorems and lemmas, definitions and deprecated aliases.</p>")
        rows = []
        for r in lean["series"]:
            a, s = r["Incognita"], r["Statements"]
            rows.append([e(r["day"]), fmt(a["files"]), fmt(a["lines"]), fmt(a["theorems"]), fmt(a["defs"]),
                         fmt(a["deprecated"]), fmt(s["files"]), fmt(s["lines"]), fmt(s["theorems"])])
        out.append(table(["Day", "Library files", "lines", "theorems", "defs", "deprecated", "Statement files", "lines",
                          "statements"], rows, num=range(1, 9)))
        pf = lean["proofs"]
        out.append("<p>Proofs now: %d theorems and lemmas, median %s lines, longest %s lines (lines from the declaration "
                   "to the next one).</p>" % (pf["count"], fmt(pf["median"]), fmt(pf["max"])))
        out.append(table(["Lines", "Theorems and lemmas"], [[e(b), fmt(n)] for b, n in pf["buckets"].items()], num=(1,)))
        out.append(table(["Longest", "File", "Lines"],
                         [["<code>%s</code>" % e(x["name"]), e(x["file"]), fmt(x["lines"])] for x in pf["longest"]],
                         num=(2,)))
        out.append("</section>")
    ef = d.get("efficiency")
    if ef:
        out.append('<section><h2 id="efficiency">Loop efficiency</h2>')
        out.append(table(["Kind of pull request", "Merged", "Open to merge, median (h)", "mean (h)",
                          "CI runs", "Build and check, median (min)", "mean (min)"],
                         [[e(kk), fmt(ef["open_to_merge_hours"][kk]["count"]), fmt(ef["open_to_merge_hours"][kk]["median"]),
                           fmt(ef["open_to_merge_hours"][kk]["mean"]), fmt(ef["ci_minutes"][kk]["count"]),
                           fmt(ef["ci_minutes"][kk]["median"]), fmt(ef["ci_minutes"][kk]["mean"])]
                          for kk in ef["open_to_merge_hours"]], num=range(1, 7)))
        t = ef.get("tasks")
        if t:
            out.append("<p>%d tasks: %d failed (%s), %d skipped (%s). Parked targets: %s. Loop restarts: %d; outputs "
                       "refused: %d.</p>"
                       % (t["total"], t["fail"], e(", ".join("%s %d" % kv for kv in t["fail_by_role"].items()) or "none"),
                          t["skip"], e(", ".join("%s %d" % kv for kv in t["skip_reasons"].items()) or "none"),
                          e(", ".join(t["parked"]) or "none"), t["loop_restarts"], t["refused"]))
        out.append("</section>")
    lit, dr = d.get("literature"), d.get("directions")
    out.append('<section><h2 id="literature">Literature and directions</h2>')
    if lit:
        tc = lit["to_be_checked"]
        out.append("<p>%s references in <code>literature/bibliography.json</code>, %d source notes. Marked "
                   '"(to be checked)": %d in the Lean files (%d files), %d in the papers (%d papers).</p>'
                   % (fmt(lit["references"]), lit["source_notes"], tc["lean"]["occurrences"], len(tc["lean"]["files"]),
                      tc["papers"]["occurrences"], len(tc["papers"]["files"])))
    if dr:
        out.append("<p>Candidate directions (<code>roadmaps/*/directions.md</code>): taken, an open paper pull request "
                   "of the roadmap names it; done, a paper on <code>main</code> serves it.</p>")
        out.append(table(["Roadmap", "Total", "Open", "Taken", "Done", "Dropped"],
                         [[e(r)] + [fmt(v[x]) for x in ("total", "open", "taken", "done", "dropped")]
                          for r, v in dr.items()], num=range(1, 6)))
    out.append("</section>")
    return "\n".join(out)


# ---------------------------------------------------------------- command line
def main(argv):
    if argv and argv[0] == "events-block":
        ap = argparse.ArgumentParser(prog="stats.py events-block")
        ap.add_argument("--night", required=True)
        ap.add_argument("--out", required=True)
        ap.add_argument("--budget", type=int, default=60000)
        ap.add_argument("--log", action="append", default=[], help="the night's log: models of older task lines")
        ap.add_argument("files", nargs="+")
        a = ap.parse_args(argv[1:])
        parts = events_block(a.night, a.files, a.budget, a.log)
        os.makedirs(a.out, exist_ok=True)
        for k, text in enumerate(parts, 1):
            with open(os.path.join(a.out, "part-%d.md" % k), "w", encoding="utf-8", newline="\n") as f:
                f.write(text)
        print(len(parts))
        return 0
    if argv and argv[0] == "events-read":
        for path in argv[1:]:
            with open(path, encoding="utf-8") as f:
                for night, _p, _t, _n, rows in read_blocks(f.read()):
                    for line in rows:
                        sys.stdout.write("%s\t%s\n" % (night, line))
        return 0
    ap = argparse.ArgumentParser(prog="stats.py")
    ap.add_argument("--repo", default=".")
    ap.add_argument("--fixtures", default=None)
    ap.add_argument("--json", default=None)
    ap.add_argument("--html", default=None)
    a = ap.parse_args(argv)
    d = collect(a.repo, a.fixtures)
    if a.json:
        text = json.dumps(d, indent=1, ensure_ascii=False, sort_keys=False)
        if a.json == "-":
            sys.stdout.write(text + "\n")
        else:
            with open(a.json, "w", encoding="utf-8") as f:
                f.write(text + "\n")
    if a.html:
        with open(a.html, "w", encoding="utf-8") as f:
            f.write(html_fragment(d) + "\n")
    if not a.json and not a.html:
        print("github: %s; sessions: %s; papers written: %s" % (
            "read" if d["github"]["available"] else "not read (%s)" % d["github"]["reason"],
            d["cost"]["sessions"] if d["cost"] else "?", d["production"]["written"] if d["production"] else "?"))
    for w in d["warnings"]:
        print("warning: %s" % w, file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
