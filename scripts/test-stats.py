#!/usr/bin/env python3
"""Offline test of scripts/stats.py on fixtures: a small repository (papers, locks, proof markers,
errata, merge trailers) and GitHub answers in files (pull requests, their comments, the issue "Night
reports" with events blocks and an older report). No network, no token. Needs git and Python 3.11+.
Usage: python3 scripts/test-stats.py (also run by scripts/test-lib.sh). Owner request of 2026-11-19.
"""
import json
import os
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import stats as S  # noqa: E402

S.REPO, S.OWNER, S.TOKEN = "owner/repo", "owner", ""
os.environ.pop("INCOGNITA_REPORT_ISSUE", None)
fails = 0


def ok(name, cond):
    global fails
    print(("ok   " if cond else "FAIL ") + name)
    if not cond:
        fails += 1


def write(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        f.write(text)


def sh(repo, *args, date="2026-11-17T12:00:00+00:00"):
    env = dict(os.environ, GIT_AUTHOR_DATE=date, GIT_COMMITTER_DATE=date, GIT_AUTHOR_NAME="t",
               GIT_AUTHOR_EMAIL="t@t", GIT_COMMITTER_NAME="t", GIT_COMMITTER_EMAIL="t@t")
    subprocess.run(["git", "-C", repo, *args], check=True, capture_output=True, env=env)


SHA = "0123456789abcdef0123456789abcdef01234567"


def comment(kind, body, at, login="owner", sha=SHA):
    return {"user": {"login": login}, "created_at": at, "html_url": "https://x/%s" % at,
            "body": "<!-- incognita:%s:%s -->\n%s" % (kind, sha, body)}


def pr(n, role, target, title, ref, state="closed", merged=None, labels=(), login="owner", fork=False,
       created="2026-11-15T10:00:00Z", extra="", sha=""):
    body = ("Role: `%s`. Target: `%s`. Model: `opus`.\n\nSummary.%s" % (role, target, extra) if role
            else "A human pull request.")
    return {"number": n, "title": title, "body": body, "state": state, "merged_at": merged, "created_at": created,
            "closed_at": merged, "labels": [{"name": x} for x in labels], "user": {"login": login},
            "head": {"ref": ref, "sha": sha, "repo": {"full_name": "mallory/repo" if fork else "owner/repo"}},
            "base": {"repo": {"full_name": "owner/repo"}}}


LEAN_A = """import Mathlib

/-! # A -/

namespace Incognita

/-- A def. -/
def f (n : Nat) : Nat := n + 1

theorem f_pos (n : Nat) : 0 < f n := by
  unfold f
  omega

@[simp] lemma f_zero : f 0 = 1 := rfl

-- (to be checked) against [LS]
@[deprecated (since := "2026-11-18")] alias f_pos' := f_pos

end Incognita
"""
DIRECTIONS = "# Candidate directions of BB\n\n" + "".join(
    "## C%d (2026-11-15, from P001v1 oq:q%d)\n- Statement: q%d\n- Source: P001\n- Rating: high\n%s\n"
    % (k, k, k, "Dropped (2026-11-16, garden, m): known.\n" if k == 1 else "") for k in (1, 2, 3, 4))


with tempfile.TemporaryDirectory() as t:
    # ---- the repository: two papers, two frozen statements of P001 (one proved), errata
    repo = os.path.join(t, "repo")
    os.makedirs(repo)
    sh(repo, "init", "-q", "-b", "main")
    write(os.path.join(repo, "papers/P001-alpha/META.toml"),
          'roadmap = "BB"\nkind = "internal"\nversion = 1\nhuman_authors = ["A. Owner"]\n')
    write(os.path.join(repo, "papers/P001-alpha/paper.tex"), "\\title{P001-alpha}\nA bound [LS] (to be checked).\n")
    write(os.path.join(repo, "papers/P002-beta/META.toml"), 'roadmap = "BB"\nkind = "internal"\nversion = 1\ndirections = ["C2"]\n')
    write(os.path.join(repo, "papers/P002-beta/paper.tex"), "\\title{P002-beta}\n")
    write(os.path.join(repo, "roadmaps/BB/ROADMAP.md"), "# Roadmap\n\n| | |\n|---|---|\n| Status | **approved** (2026-11-14) |\n\n"
          "## Open directions\n\n- **D1. One.** Text.\n")
    write(os.path.join(repo, "roadmaps/BB/directions.md"), DIRECTIONS)
    write(os.path.join(repo, "literature/bibliography.json"), json.dumps({"A20": {}, "B21": {}}))
    write(os.path.join(repo, "literature/notes/A20.md"), "# A20\n")
    write(os.path.join(repo, "literature/notes/TEMPLATE.md"), "# Template\n")
    write(os.path.join(repo, "papers/P001-alpha/errata.md"), "# Errata\n\n## E1 (2026-11-18, prove, m)\n\n- Frozen statement: `x`\n")
    write(os.path.join(repo, "papers/P001-alpha/statement-corrections.md"),
          "# Corrections\n\n## SC1 (2026-11-18, prove, m)\n\n- Resolved by #9\n")
    sh(repo, "add", "-A")
    sh(repo, "commit", "-qm", "P001: the paper (#1)\n\nIncognita-Role: write-paper\nIncognita-Reviews: referee-scope=accept referee-proofs=accept",
       date="2026-11-16T12:00:00+00:00")
    write(os.path.join(repo, "Statements/P001/a.lock"), "x\n")
    write(os.path.join(repo, "Statements/P001/b.lock"), "y\n")
    write(os.path.join(repo, "Statements/P001/a.lean"), "theorem a : True := sorry\n")
    write(os.path.join(repo, "Incognita/A.lean"), LEAN_A)
    sh(repo, "add", "-A")
    sh(repo, "commit", "-qm", "P001 statements (#3)\n\nIncognita-Role: formalize-statements\nIncognita-Reviews: review-statements=approve",
       date="2026-11-17T12:00:00+00:00")
    write(os.path.join(repo, "catalogue/results/P001-a.toml"), 'paper = "P001-alpha"\nstatus = "proved"\n')
    write(os.path.join(repo, "Statements/P002/c.lock"), "z\n")
    write(os.path.join(repo, "catalogue/results/P002-c.toml"), 'paper = "P002-beta"\nstatus = "proved"\n')
    write(os.path.join(repo, "Incognita/B.lean"), "theorem g : True := by\n  trivial\n")
    sh(repo, "add", "-A")
    sh(repo, "commit", "-qm", "Docs by the owner (#6)", date="2026-11-18T12:00:00+00:00")

    # ---- GitHub
    fx = os.path.join(t, "fx")
    pulls = [pr(1, "write-paper", "BB", "P001: alpha", "agent/write-paper-1", merged="2026-11-16T10:00:00Z",
                created="2026-11-14T10:00:00Z", sha="a" * 40),
             pr(2, "write-paper", "BB", "P002: beta", "owner/beta", labels=["rejected"]),
             pr(3, "formalize-statements", "P001-alpha", "P001 statements", "agent/formalize-statements-1",
                merged="2026-11-17T10:00:00Z"),
             pr(4, "write-paper", "BB", "P009: from a fork", "agent/write-paper-9", state="open", fork=True),
             pr(5, None, None, "Docs", "docs/x", merged="2026-11-18T10:00:00Z", sha="b" * 40),
             pr(7, "write-paper", "BB", "P003: by someone else", "agent/write-paper-7", state="open", login="mallory"),
             pr(8, "write-paper", "BB", "P010: gamma", "agent/write-paper-8", state="open", extra=" Serves C3."),
             pr(10, None, None, "Typo", "fix/typo", login="alice", created="2026-11-18T08:00:00Z",
                merged="2026-11-18T10:00:00Z")]
    write(os.path.join(fx, "pulls.json"), json.dumps(pulls))
    run = {"name": "Build and check", "started_at": "2026-11-15T10:00:00Z", "completed_at": "2026-11-15T10:12:00Z"}
    write(os.path.join(fx, "checks", "a" * 40 + ".json"),
          json.dumps({"check_runs": [run, {"name": "Compile papers", "started_at": "2026-11-15T10:00:00Z",
                                           "completed_at": "2026-11-15T11:00:00Z"}]}))
    write(os.path.join(fx, "checks", "b" * 40 + ".json"),
          json.dumps({"check_runs": [dict(run, completed_at="2026-11-15T10:30:00Z")]}))
    c1 = [comment("referee-scope", "Verdict: major\n\n| ID | Class | Node | Step | Defect | Fix |\n|---|---|---|---|---|---|\n"
                  "| SC1.1 | G | sec:intro | claim | x | y |\n| SC1.2 | P | sec:x | s | x | y |\n", "2026-11-14T11:00:00Z"),
          comment("referee-proofs", "Verdict: minor\n\n| PF1.1 | L | lem:a | 2 | x | y |\n", "2026-11-14T11:10:00Z"),
          comment("revise", "Revision round 1 of 4: pushed.", "2026-11-14T12:00:00Z"),
          comment("referee-scope", "Verdict: accept\n\n| Criterion | State | Summary |\n|---|---|---|\n"
                  "| Interest | 7/10 | A solid and useful result for the field, clearly new. |\n\n"
                  "| SC2.1 | P | sec:y | s | x | y |\n\n## Previous defects G, L and R\n\n"
                  "| SC1.1 (G) | yes | fixed |\n| SC1.2 | P | sec:x | s | repeated | y |\n", "2026-11-15T11:00:00Z"),
          comment("referee-proofs", "Verdict: accept\n", "2026-11-15T11:10:00Z"),
          comment("referee-scope", "Verdict: reject\n\n| SC9.1 | F | x | x | x | x |\n", "2026-11-15T12:00:00Z", login="mallory")]
    write(os.path.join(fx, "comments", "1.json"), json.dumps(c1))
    c2 = [comment("referee-scope", "Verdict: reject\n\n| SC1.1 | F | thm:main | known | x | y |\n", "2026-11-16T11:00:00Z"),
          comment("rejected", "Closed by the script.", "2026-11-16T11:01:00Z")]
    write(os.path.join(fx, "comments", "2.json"), json.dumps(c2))
    c3 = [comment("review-statements", "Verdict: request_changes\n", "2026-11-16T13:00:00Z"),
          comment("fix-pr", "Fix round: pushed.", "2026-11-16T14:00:00Z"),
          comment("review-statements", "Verdict: approve\n", "2026-11-16T15:00:00Z"),
          comment("rubric-correctness", "Verdict: approve\n", "2026-11-16T16:00:00Z"),
          comment("rubric-reuse", "Verdict: block\n", "2026-11-16T16:10:00Z"),
          comment("fix-pr-nochange", "Fix round: no change.", "2026-11-16T17:00:00Z"),
          comment("rubric-reuse", "Verdict: approve\n", "2026-11-16T18:00:00Z")]
    write(os.path.join(fx, "comments", "3.json"), json.dumps(c3))
    write(os.path.join(fx, "issues.json"), json.dumps([{"number": 9, "title": "Night reports", "user": {"login": "owner"}},
                                                      {"number": 8, "title": "Night reports", "user": {"login": "mallory"}}]))
    ev = os.path.join(t, "events.tsv")
    write(ev, "\n".join([
        "2026-11-16 21:00:00\ttask\twrite-paper\tBB\tok pr #1 (turns 10, 3600s, $10.5)",
        "2026-11-16 22:00:00\ttask\treferee-scope\t1\tok verdict major https://x (turns 5, 600s, $2.25)",
        "2026-11-16 22:30:00\ttask\tformalize-statements\tP001-alpha\tok pr #3 (turns 9, 1200s, $4)",
        "2026-11-16 23:00:00\ttask\trubric-reuse\t3\tok verdict block (turns 3, 300s, $1)",
        "2026-11-16 23:10:00\ttask\tfix-pr\t3\tskip quota-cut partial (turns 1, 60s, $0.5)",
        "2026-11-16 23:11:00\tquota\tfix-pr\t3\trate limited until 01:00",
        "2026-11-16 23:12:00\tquota-wait\t-\t-\t3600s (rate limit)",
        "2026-11-17 01:00:00\tmerge\tformalize-statements\t3\tstatements — P001 statements",
        "2026-11-17 01:01:00\ttask\treview-pr\t5\tfail agent.sh exit 1 (exit 1, 30s)",
        "2026-11-17 01:02:00\task-owner\treview-pr\t5\tleaked sk-ant-oat01-ABCDEFGHIJKLMNOPQRSTUVWXYZ by mistake",
        "2026-11-17 01:04:00\ttask\tprove\tP002-beta\tok pr #11 (turns 2, 100s, $2, model sonnet)",
        "not an event line",
        "2026-11-17 01:03:00\tidle\t-\t-\t1200s"]) + "\n")
    us = os.path.join(t, "usage.tsv")
    write(us, "2026-11-16 20:59:00\tusage\t-\t-\tok 40 1795399200 4 1795111800 lean\n"
              "2026-11-17 01:05:00\tusage\t-\t-\tok 52 1795399200 30 1795111800 lean\n")
    parts = S.events_block("2026-11-16", [ev, us, os.path.join(t, "missing.tsv")])
    ok("events-block: one part, the secret and the stray line left out",
       len(parts) == 1 and "sk-ant" not in parts[0] and "not an event" not in parts[0] and "lines=13" in parts[0]
       and "2 lines left out" in parts[0])
    small = S.events_block("2026-11-16", [ev, us], budget=900)
    ok("events-block: split under the budget, nothing lost",
       len(small) > 1 and all(len(p.encode()) <= 900 for p in small)
       and sum(len(b[4]) for p in small for b in S.read_blocks(p)) == 13)
    try:
        S.events_block("../x", [ev])
        ok("events-block: a bad night name is refused", False)
    except ValueError:
        ok("events-block: a bad night name is refused", True)
    report_old = ("# Night report 2026-11-14\n\n2026-11-14 21:00 → 2026-11-15 05:00 (server time). Stopped: deadline.\n\n"
                  "Weekly usage of the subscription (claude.ai, Settings, Usage): 10 % (read with lean's Claude login "
                  "(tauceti status)) at the start, 20 % (read with lean's Claude login (tauceti status)) at the end; cap 90 % "
                  "(INCOGNITA_WEEKLY_CAP); weekly reset 2026-11-23 02:00 UTC.\n\n## 8. Machine statistics\n\n<details>\n\nTasks:\n\n"
                  "- 23:50 referee-proofs 1: ok verdict major https://x (turns 4, 400s, $1.5)\n"
                  "- 00:10 revise 1: ok pushed #1 abc (turns 20, 1000s, $6)\n\n</details>\n")
    report_new = ("# Night report 2026-11-16\n\n2026-11-16 20:58 → 2026-11-17 01:06 (server time). Stopped: deadline.\n\n"
                  "Weekly usage of the subscription (claude.ai, Settings, Usage): 40 % at the start, 52 % at the end; cap 90 % "
                  "(INCOGNITA_WEEKLY_CAP).\n\n## 8. Machine statistics\n\n<details>\n\nTasks:\n\n"
                  "- 21:00 write-paper BB: ok pr #1 (turns 10, 3600s, $10.5)\n\n</details>\n\n" + parts[0])
    c9 = [comment("night-report", report_old, "2026-11-15T05:00:00Z"),
          comment("night-report", report_new, "2026-11-17T01:06:00Z"),
          {"user": {"login": "owner"}, "created_at": "2026-11-19T10:00:00Z",
           "body": "# Backfill of the night of 2026-11-16\n\n" + parts[0]},   # a backfill of the same night
          {"user": {"login": "mallory"}, "created_at": "2026-11-19T11:00:00Z",
           "body": S.events_block("2026-11-20", [ev])[0]}]
    write(os.path.join(fx, "comments", "9.json"), json.dumps(c9))

    d = S.collect(repo, fx)
    p, q, f, c = d["production"], d["quality"], d["formalisation"], d["cost"]
    ok("github read from the fixtures", d["github"]["available"] and d["github"]["report_issue"] == 9)
    ok("production: agents' and owner's papers only (no fork, no other account)",
       p["written"] == 3 and p["accepted"] == 1 and p["rejected"] == 1 and p["in_review"] == 1 and p["by"]["owner"]["rejected"] == 1)
    ok("production: days to acceptance, revision rounds",
       p["papers"][0]["days_to_accept"] == 2.0 and p["papers"][0]["revision_rounds"] == 1
       and p["papers"][0]["scope_reports"] == 2)
    ok("quality: referee verdicts (minor read as major; another account ignored)",
       q["referee_verdicts"]["referee-scope"] == {"major": 1, "accept": 1, "reject": 1}
       and q["referee_verdicts"]["referee-proofs"] == {"major": 1, "accept": 1})
    ok("quality: first-round verdicts", q["referee_first_round"]["referee-scope"] == {"major": 1, "reject": 1})
    ok("quality: defects by class, each ID once, not the table of previous defects",
       q["defects"]["referee-scope"] == {"F": 1, "G": 1, "L": 0, "R": 0, "P": 2}
       and q["defects"]["referee-proofs"]["L"] == 1)
    ok("quality: rubric verdicts by rubric, in Tau Ceti's order",
       list(q["rubric_verdicts"]) == ["correctness", "reuse"]
       and q["rubric_verdicts"]["reuse"] == {"approve": 1, "request_changes": 0, "block": 1})
    lp = q["lean_prs"]
    ok("quality: fix rounds per Lean PR", len(lp) == 1 and lp[0]["pr"] == 3 and lp[0]["fix_rounds"] == 2
       and lp[0]["blocks"] == 1 and lp[0]["changes_requested"] == 1 and lp[0]["merged_by_the_loop"])
    ok("formalisation: frozen, proved, errata, corrections",
       f["frozen"] == 3 and f["proved"] == 2 and f["papers"][0]["errata_open"] == 1
       and f["papers"][0]["corrections_resolved"] == 1 and f["papers"][0]["status"] == "disputed")
    ok("formalisation: over time", f["timeline"]["P001"] == [["2026-11-17", 2, 0], ["2026-11-18", 2, 1]])
    ok("merge trailers: by role, and the owner's merges",
       d["merges"]["by_role"] == {"formalize-statements": 1, "write-paper": 1} and d["merges"]["by_the_owner"] == 1)
    ok("cost: every session once (events, a duplicate block, the report's task list), not another account's",
       c["sessions"] == 9 and d["nights"] == {"with_events": ["2026-11-16"], "from_reports_only": ["2026-11-14"]})
    ok("cost: by role", c["by_role"]["write-paper"]["usd"] == 10.5 and c["by_role"]["review-pr"]["fail"] == 1
       and c["by_role"]["review-pr"]["seconds"] == 30)
    n16, n14 = c["per_night"]["2026-11-16"], c["per_night"]["2026-11-14"]
    ok("cost: per night (events)", n16["usd"] == 20.25 and n16["merges"] == 1 and n16["idle_min"] == 20
       and n16["quota_wait_min"] == {"rate limit": 60} and n16["quota_cuts"] == 1 and n16["rate_limits"] == 1
       and n16["usage_start"] == 40 and n16["usage_end"] == 52 and n16["usage_max"] == 52 and n16["usage_points"] == 12)
    ok("cost: per night (report only; the day turns at midnight)", n14["sessions"] == 2 and n14["usd"] == 7.5
       and n14["merges"] is None and n14["usage_points"] == 10)
    pp = c["per_paper"]["P001"]
    ok("cost: per paper, writing vs reviews vs rubrics",
       pp["writing"]["usd"] == 21.0 and pp["reviews"]["usd"] == 3.75 and pp["rubrics"]["usd"] == 1.0)
    l3 = c["per_lean_pr"]["3"]
    ok("cost: per Lean PR", l3["writing"]["usd"] == 4.5 and l3["rubrics"]["usd"] == 1.0 and l3["paper"] == "P001")
    ok("cost: quota", c["quota"]["sessions_cut"] == 1 and c["quota"]["rate_limits"] == 1
       and c["quota"]["wait_min"] == {"rate limit": 60})
    ok("cost: dollars per weekly point", c["usd_per_weekly_point"] == round(27.75 / 22, 2))
    # ---- the extension of 2026-11-19: stages, contributors, models, Lean library, interest, efficiency,
    # literature, directions
    st = c["by_stage"]
    ok("stages: a review, rubric or fix round counts in the stage of its pull request",
       list(st) == list(S.STAGES) and st["writing"]["usd"] == 10.5 and st["refereeing"]["usd"] == 9.75
       and st["statements"]["usd"] == 5.5 and st["proofs"]["usd"] == 2.0 and st["other"]["sessions"] == 1
       and st["acceptance"]["merges"] == 2 and st["acceptance"]["sessions"] == 0)
    ms = c["milestones"]
    ok("stages: cost per paper to acceptance and to Lean verification",
       ms["P001"]["accepted_at"] == "2026-11-16 10:00:00" and ms["P001"]["usd_to_acceptance"] == 7.5
       and ms["P001"]["usd_total"] == 25.75 and ms["P001"]["usd_to_verification"] is None
       and ms["P002"]["verified_at"] == "2026-11-18 12:00:00" and ms["P002"]["usd_to_verification"] == 2.0)
    ok("models: by session, older events unrecorded",
       c["by_model"]["sonnet"] == {"sessions": 1, "seconds": 100, "usd": 2.0} and c["by_model"]["unrecorded"]["sessions"] == 8)
    ok("models: the parser reads both forms", S.session("ok pr #1 (turns 2, 100s, $2, model opus)")[4] == "opus"
       and S.session("fail x (exit 1, 30s, model claude-opus-5-5)")[4] == "claude-opus-5-5"
       and S.session("ok pr #1 (turns 2, 100s, $2)")[3:] == (2.0, None))
    log = os.path.join(t, "night.log")
    write(log, "2026-11-16 20:00:00 == session: write-paper BB, model opus, 14000s\n"
               "2026-11-16 21:30:00 == session: referee-scope 1, model sonnet, 3600s, PR #1 head abc\n")
    lines, _ = S.event_lines([ev])
    wm = S.with_models(lines, [log])
    ok("models: older task lines get theirs from the night's log (backfill)",
       any(x.endswith("(turns 10, 3600s, $10.5, model opus)") for x in wm)
       and any(x.endswith("(turns 5, 600s, $2.25, model sonnet)") for x in wm)
       and any(x.endswith("(turns 9, 1200s, $4)") for x in wm) and any(x.endswith("$2, model sonnet)") for x in wm))
    k = d["contributors"]
    ok("contributors: humans by GitHub login, the owner's papers, META human_authors",
       k["humans"] == {"owner": {"prs_merged": 1, "owner_papers": 1}, "alice": {"prs_merged": 1, "owner_papers": 0}}
       and k["human_authors"] == {"A. Owner": ["P001"]})
    ok("contributors: agents by role, pull requests by model",
       k["agents_by_role"]["write-paper"]["prs_opened"] == 2 and k["agents_by_role"]["write-paper"]["prs_merged"] == 1
       and k["agents_by_role"]["write-paper"]["usd"] == 10.5 and k["prs_by_model"] == {"opus": 3}
       and k["models"]["sonnet"]["sessions"] == 1)
    i = d["interest"]
    ok("interest: the score of the last scope report that gives one; distribution",
       [(x["paper"], x["score"]) for x in i["papers"]] == [("P001", 7), ("P002", None), ("P010", None)]
       and i["distribution"]["7"] == 1 and sum(i["distribution"].values()) == 1 and i["median"] == 7)
    ok("interest: the reason, shared with site.py",
       S.interest_from(S.trusted(c1))[:2] == (7, "A solid and useful result for the field, clearly new."))
    lean = d["lean"]
    ok("Lean library: one sample per day", [r["day"] for r in lean["series"]] == ["2026-11-16", "2026-11-17", "2026-11-18"]
       and lean["series"][0]["Incognita"]["files"] == 0)
    ok("Lean library: files, lines, theorems and lemmas, defs, deprecated aliases",
       lean["series"][1]["Incognita"] == {"files": 1, "lines": LEAN_A.count("\n"), "theorems": 2, "defs": 1, "deprecated": 1}
       and lean["series"][2]["Incognita"]["theorems"] == 3 and lean["series"][2]["Statements"]["theorems"] == 1)
    ok("Lean library: proof lengths now",
       lean["proofs"]["count"] == 3 and lean["proofs"]["buckets"]["1-5"] == 3 and lean["proofs"]["max"] == 3
       and lean["proofs"]["longest"][0]["name"] == "f_pos")
    ef = d["efficiency"]
    ok("efficiency: open to merge by kind of pull request",
       ef["open_to_merge_hours"]["paper"]["median"] == 48.0 and ef["open_to_merge_hours"]["statements"]["median"] == 48.0
       and ef["open_to_merge_hours"]["human"] == {"count": 2, "median": 37.0, "mean": 37.0, "max": 72.0})
    ok("efficiency: duration of Build and check (other checks ignored)",
       ef["ci_minutes"]["paper"]["median"] == 12.0 and ef["ci_minutes"]["human"]["median"] == 30.0
       and ef["ci_minutes_all"]["count"] == 2)
    ok("efficiency: failed and skipped tasks",
       ef["tasks"]["fail"] == 1 and ef["tasks"]["fail_by_role"] == {"review-pr": 1}
       and ef["tasks"]["skip_reasons"] == {"quota-cut": 1} and ef["tasks"]["parked"] == [])
    lit = d["literature"]
    ok("literature: references, source notes, (to be checked)",
       lit["references"] == 2 and lit["source_notes"] == 1 and lit["to_be_checked"]["lean"]["occurrences"] == 1
       and lit["to_be_checked"]["papers"]["files"] == {"papers/P001-alpha/paper.tex": 1})
    ok("directions: total, open, taken, done, dropped",
       d["directions"] == {"BB": {"total": 4, "open": 1, "taken": 1, "done": 1, "dropped": 1}})
    frag = S.html_fragment(d)
    ok("html: every section", all('id="%s"' % x in frag for x in (
        "production", "quality", "formalisation", "cost", "stages", "contributors", "interest", "lean", "efficiency",
        "literature")))
    ok("json: serialisable", bool(json.dumps(d)))

    # ---- without a token: the repository's metrics only
    d0 = S.collect(repo, None)
    ok("no token: GitHub marked unavailable, the repository still read",
       not d0["github"]["available"] and "token" in d0["github"]["reason"] and d0["production"] is None
       and d0["cost"] is None and d0["formalisation"]["frozen"] == 3 and d0["lean"]["proofs"]["count"] == 3
       and d0["literature"]["references"] == 2 and d0["directions"]["BB"]["taken"] is None
       and d0["efficiency"] is None and d0["interest"] is None)
    ok("no token: the page says so", "could not be read" in S.html_fragment(d0))
    # ---- GitHub failing in the middle: unavailable, never half-read
    os.remove(os.path.join(fx, "pulls.json"))
    d1 = S.collect(repo, fx)
    ok("GitHub failing: unavailable", not d1["github"]["available"] and d1["quality"] is None)

print("%d failure(s)" % fails)
sys.exit(1 if fails else 0)
