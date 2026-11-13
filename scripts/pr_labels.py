#!/usr/bin/env python3
"""Keep one state label, and one role label, on every open pull request.

State labels (exactly one per open pull request, recomputed from GitHub's data):
  merge-conflict   no longer merges cleanly into main
  awaiting-CI      the build has not reported on the last commit yet
  ci-failed        the build failed on the last commit
  awaiting-review  the build is green; the reviewer has not judged the last commit yet
  awaiting-author  the reviewer requested changes (or blocked) on the last commit
  ready-to-merge   the build is green and the reviewer approved the last commit: for the owner
The label needs-human (set by scripts/loop.sh) is left alone.

Role labels: role:<role>, read from the line "Role: `<role>`" that scripts/agent.sh writes in the
description of an agent's pull request.

Run by .github/workflows/pr-labels.yml (GH_TOKEN in the environment); safe to run by hand.
"""
import json
import subprocess

STATES = {
    "merge-conflict": ("B60205", "No longer merges cleanly into main; needs a rebase"),
    "awaiting-CI": ("FBCA04", "The build has not reported on the last commit yet"),
    "ci-failed": ("D93F0B", "The build failed on the last commit"),
    "awaiting-review": ("0E8A16", "Build green; the reviewer has not judged the last commit yet"),
    "awaiting-author": ("C5DEF5", "The reviewer requested changes on the last commit"),
    "ready-to-merge": ("1D76DB", "Build green and last commit approved: for the owner to merge"),
}
ROLE_COLOR = "EDEDED"


def gh(*args, check=True):
    return subprocess.run(["gh", *args], capture_output=True, text=True, check=check).stdout


def ensure_label(name, color, description):
    gh("label", "create", name, "--color", color, "--description", description, "--force", check=False)


def state_of(pr):
    if pr.get("mergeable") == "CONFLICTING":
        return "merge-conflict"
    build = review = None
    for c in pr.get("statusCheckRollup") or []:
        if c.get("name") == "Build and check":  # a check run
            build = c.get("conclusion") or c.get("status")
        elif c.get("context") == "Incognita review":  # a commit status
            review = c.get("state")
    if build in (None, "QUEUED", "IN_PROGRESS", "PENDING", "WAITING", "REQUESTED", ""):
        return "awaiting-CI"
    if build != "SUCCESS":
        return "ci-failed"
    if review == "SUCCESS":
        return "ready-to-merge"
    if review in ("FAILURE", "ERROR"):
        return "awaiting-author"
    return "awaiting-review"


def role_of(pr):
    body = pr.get("body") or ""
    marker = "Role: `"
    if marker not in body:
        return None
    return body.split(marker, 1)[1].split("`", 1)[0]


def main():
    for name, (color, description) in STATES.items():
        ensure_label(name, color, description)
    prs = json.loads(gh("pr", "list", "--state", "open", "--limit", "100", "--json",
                        "number,mergeable,labels,body,statusCheckRollup"))
    for pr in prs:
        current = {label["name"] for label in pr["labels"]}
        wanted = state_of(pr)
        add, remove = [], [s for s in STATES if s in current and s != wanted]
        if wanted not in current:
            add.append(wanted)
        role = role_of(pr)
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
