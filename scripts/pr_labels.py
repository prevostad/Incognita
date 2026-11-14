#!/usr/bin/env python3
"""Keep one state label, and one role label, on every open pull request (for humans; the loop reads
the commit statuses themselves).

State labels (exactly one per open pull request of this repository, none when it has needs-human):
  merge-conflict   no longer merges cleanly into main
  awaiting-CI      the build has not reported on the last commit yet
  ci-failed        the build failed on the last commit
  awaiting-review  the build is green; the needed reviews of the last commit are not all there
  awaiting-author  a reviewer or referee asked for changes (or rejected) on the last commit, or the
                   pull request is a draft labelled incomplete (an agent continues it)
  ready-to-merge   build green and the needed reviews accept the last commit
  veto-window      a roadmap proposal approved by review-roadmap, waiting for the end of its veto
                   window or for the owner's approval (the loop then approves and merges it)
The build is the check "Build and check" (workflow CI) and, for paper pull requests or when it ran,
"Compile papers" (workflow Papers), as in scripts/lib.sh (CI_JQ).
Agents' pull requests (branch agent/*, opened by the owner's account, first line "Role: `<role>`...")
need trusted commit statuses, i.e. created by the owner's account (the loop), never by a workflow:
papers (roles write-paper, revise) "Referee scope" and "Referee proofs" (verdict accept) and
"Incognita review"; roadmap proposals (role propose-roadmap) "Incognita review" (verdict approve
of review-roadmap) and then "Incognita loop" (verdict approved: the scripted approval); other pull
requests "Incognita review" (verdict approve).
Pull requests from forks get the label `fork` and no state: the agents ignore them.
The labels set by the loop (scripts/lib.sh, ensure_labels) are created here with the same colours
and never removed: incomplete (a draft whose session stopped), rejected (a paper closed by the
referees), needs-human (the agents gave up: the owner decides; no state label then), veto (the
owner vetoes a roadmap proposal).

Role labels: role:<role>, for the roles of v3 (agents/roles/), from the first line of the
description of an agent's pull request.

Run by .github/workflows/pr-labels.yml (GH_TOKEN, GH_REPO, INCOGNITA_OWNER in the environment); safe to
run by hand (the owner is then the account of `gh`).
"""
import json
import os
import re
import subprocess

STATES = {
    "merge-conflict": ("B60205", "No longer merges cleanly into main; needs a rebase"),
    "awaiting-CI": ("FBCA04", "The build has not reported on the last commit yet"),
    "ci-failed": ("D93F0B", "The build failed on the last commit"),
    "awaiting-review": ("0E8A16", "Build green; the needed reviews of the last commit are not all there"),
    "awaiting-author": ("C5DEF5", "A reviewer asked for changes on the last commit"),
    "ready-to-merge": ("1D76DB", "Build green and the last commit accepted by the needed reviews"),
    "veto-window": ("5319E7", "Roadmap proposal approved by review-roadmap: approved by the loop after the veto window"),
}
FORK = ("fork", "BFD4F2", "From a fork: ignored by the agents")
LOOP_LABELS = {  # same as ensure_labels in scripts/lib.sh
    "incomplete": ("FBCA04", "A session stopped before the end: its work is kept, an agent continues it"),
    "rejected": ("B60205", "Paper rejected by the referees (reports kept); the owner may reopen it"),
    "needs-human": ("B60205", "The agents cannot go further: the owner decides"),
    "veto": ("B60205", "The owner vetoes this roadmap proposal (or comments: veto)"),
}
ROLE_COLOR = "EDEDED"
ROLE_LINE = re.compile(r"^Role: `([a-z-]+)`\. Target: `([^`]*)`\.")
# The roles that open pull requests (ROLES in scripts/lib.sh, without the reviewers).
ROLES = {"write-paper", "revise", "formalize-statements", "prove", "fix-pr", "bibliographer", "garden",
         "propose-roadmap"}
PAPER_ROLES = {"write-paper", "revise"}
BAD = {"FAILURE", "TIMED_OUT", "STARTUP_FAILURE", "ERROR"}   # cancelled: rerun by the loop after 2 h
GOOD = {"SUCCESS", "NEUTRAL", "SKIPPED"}


def gh(*args, check=True):
    return subprocess.run(["gh", *args], capture_output=True, text=True, check=check).stdout


def ensure_label(name, color, description):
    gh("label", "create", name, "--color", color, "--description", description, "--force", check=False)


def owner():
    login = os.environ.get("INCOGNITA_OWNER") or os.environ.get("GITHUB_REPOSITORY_OWNER")
    return login or gh("api", "user", "--jq", ".login").strip()


def statuses(repo, sha, me):
    """Latest status of each context: {context: (state, trusted, description)}."""
    try:
        data = json.loads(gh("api", f"repos/{repo}/commits/{sha}/statuses?per_page=100"))
    except (subprocess.CalledProcessError, json.JSONDecodeError):
        return {}
    latest = {}
    for s in data:
        c = s.get("context")
        if c not in latest or s.get("created_at", "") > latest[c].get("created_at", ""):
            latest[c] = s
    return {c: (s.get("state"), (s.get("creator") or {}).get("login") == me, s.get("description") or "")
            for c, s in latest.items()}


def verdict(sts, context, roles):
    """The verdict of a trusted status of this context written by one of these roles, or None."""
    state, trusted, desc = sts.get(context, (None, False, ""))
    if not trusted:
        return None
    r = re.search(r"role=([a-z-]+)", desc)
    v = re.search(r"verdict=([a-z_]+)", desc)
    if r and v and r.group(1) in roles:
        return v.group(1)
    return None


def role_of(pr, me):
    if pr.get("isCrossRepository") or not pr.get("headRefName", "").startswith("agent/"):
        return None
    if (pr.get("author") or {}).get("login") != me:
        return None
    m = ROLE_LINE.match((pr.get("body") or "").split("\n", 1)[0])
    return m.group(1) if m and m.group(1) in ROLES else None


def build_of(pr, role):
    """SUCCESS, a failure, or None (still running or missing), as CI_JQ in scripts/lib.sh."""
    present = {}
    for c in pr.get("statusCheckRollup") or []:
        if c.get("name") in ("Build and check", "Compile papers"):  # check runs
            present[c["name"]] = c.get("conclusion") or c.get("status")
    needed = {"Build and check"} | ({"Compile papers"} if role in PAPER_ROLES else set())
    values = [present.get(name) for name in sorted(needed | set(present))]
    for v in values:
        if v in BAD:
            return v
    if all(v in GOOD for v in values):
        return "SUCCESS"
    return None


def state_of(pr, role, repo, me):
    if pr.get("mergeable") == "CONFLICTING":
        return "merge-conflict"
    if pr.get("isDraft") and "incomplete" in {label["name"] for label in pr.get("labels") or []}:
        return "awaiting-author"
    build = build_of(pr, role)
    if build is None:
        return "awaiting-CI"
    if build != "SUCCESS":
        return "ci-failed"
    sts = statuses(repo, pr["headRefOid"], me)
    if role is None:  # a human pull request: "Incognita review" set by the workflow or the owner
        review = sts.get("Incognita review", (None,))[0]
        return {"success": "ready-to-merge", "failure": "awaiting-author", "error": "awaiting-author"}.get(
            review, "awaiting-review")
    if role in PAPER_ROLES:
        scope = verdict(sts, "Referee scope", {"referee-scope"})
        proofs = verdict(sts, "Referee proofs", {"referee-proofs"})
        if scope in ("major", "minor", "reject") or proofs in ("major", "minor", "reject"):
            return "awaiting-author"
        if scope == "accept" and proofs == "accept" and verdict(sts, "Incognita review", {"referees"}) == "accept":
            return "ready-to-merge"
        return "awaiting-review"
    if role == "propose-roadmap":
        v = verdict(sts, "Incognita review", {"review-roadmap"})
        if v in ("request_changes", "reject"):
            return "awaiting-author"
        if v != "approve":
            return "awaiting-review"
        return "ready-to-merge" if verdict(sts, "Incognita loop", {"loop"}) == "approved" else "veto-window"
    v = verdict(sts, "Incognita review", {"review-pr", "review-statements"})
    if v == "approve":
        return "ready-to-merge"
    if v in ("request_changes", "reject"):
        return "awaiting-author"
    return "awaiting-review"


def main():
    repo = os.environ.get("GH_REPO") or gh("repo", "view", "--json", "nameWithOwner", "--jq", ".nameWithOwner").strip()
    me = owner()
    for name, (color, description) in {**STATES, **LOOP_LABELS}.items():
        ensure_label(name, color, description)
    ensure_label(*FORK)
    prs = json.loads(gh("pr", "list", "--state", "open", "--limit", "200", "--json",
                        "number,mergeable,labels,body,statusCheckRollup,headRefName,headRefOid,"
                        "isCrossRepository,author,isDraft"))
    for pr in prs:
        current = {label["name"] for label in pr["labels"]}
        add, remove = [], []
        if pr.get("isCrossRepository"):
            wanted, role = FORK[0], None
            remove = [s for s in STATES if s in current]
            if FORK[0] not in current:
                add.append(FORK[0])
        else:
            role = role_of(pr, me)
            # needs-human: the owner decides; no state label competes with it.
            wanted = "needs-human" if "needs-human" in current else state_of(pr, role, repo, me)
            remove = [s for s in STATES if s in current and s != wanted]
            if wanted not in current:
                add.append(wanted)
            if role and f"role:{role}" not in current:
                ensure_label(f"role:{role}", ROLE_COLOR, f"Opened by an agent with the role {role}")
                add.append(f"role:{role}")
        if add or remove:
            args = ["pr", "edit", str(pr["number"])]
            for name in add:
                args += ["--add-label", name]
            for name in remove:
                args += ["--remove-label", name]
            gh(*args, check=False)
        print(f"#{pr['number']}: {wanted}" + (f", role:{role}" if role else ""))


if __name__ == "__main__":
    main()
