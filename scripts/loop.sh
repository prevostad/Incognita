#!/usr/bin/env bash
# Run n agent tasks, one after the other, each time the most useful one in the order of AGENTS.md:
# review pull requests, review proposed questions, audit the attribution of new results, research
# open questions or formalise known results (alternately, with a bibliographer task every fourth
# time), propose questions; gardening every tenth task. See agents/README.md.
#
# Usage: scripts/loop.sh [n]        (run it in the main checkout, on branch main, never edited by hand)
set -euo pipefail

n=${1:-1}
root="$(git rev-parse --show-toplevel)"
cd "$root"

approved() {
  grep -l '^| Status | \*\*approved' programmes/*/PROGRAMME.md 2>/dev/null \
    | xargs -r -n1 dirname | xargs -r -n1 basename
}
questions_in() {  # questions of the approved programmes
  for p in $(approved); do ls programmes/"$p"/questions/Q*.md 2>/dev/null || true; done
}
# Automatic merging, by category (comma-separated in INCOGNITA_AUTOMERGE): exploration
# (Exploration/), literature (literature/, catalogue/), questions (programmes/*/questions/),
# library (Incognita/, catalogue/). Empty, the default: nothing is merged automatically. A pull
# request touching any other path (Statements/, human-owned paths) is never merged automatically.
automerge=",${INCOGNITA_AUTOMERGE:-},"
enabled() { case "$automerge" in *",$1,"*) return 0 ;; *) return 1 ;; esac; }
auto_mergeable() {  # every file of pull request $1 is in an enabled category
  local f
  for f in $(gh pr view "$1" --json files --jq '.files[].path'); do
    case "$f" in
      Exploration/*|Exploration.lean) enabled exploration || return 1 ;;
      literature/*) enabled literature || return 1 ;;
      programmes/*/questions/*) enabled questions || return 1 ;;
      catalogue/*) enabled literature || enabled library || return 1 ;;
      Incognita/*|Incognita.lean) enabled library || return 1 ;;
      *) return 1 ;;
    esac
  done
}
merge_ready() {  # merge the open pull requests that are approved, green and auto-mergeable
  [ "$automerge" = ",," ] && return 0
  local pr ci verdict
  for pr in $(gh pr list --state open --json number --jq '.[].number'); do
    ci=$(gh pr view "$pr" --json statusCheckRollup \
      --jq '[.statusCheckRollup[] | select(.name == "Build and check") | .conclusion] | first')
    verdict=$(gh pr view "$pr" --json commits,comments --jq '
      ([.comments[] | select(.body | startswith("Verdict:"))] | sort_by(.createdAt) | last) as $v
      | if $v == null then "none" elif $v.createdAt < .commits[-1].committedDate then "stale"
        else ($v.body | split("\n") | first) end')
    if [ "$ci" = SUCCESS ] && [ "$verdict" = "Verdict: approve" ] && auto_mergeable "$pr"; then
      echo "== merging #$pr automatically"
      gh pr merge "$pr" --squash --delete-branch || echo "merge of #$pr failed" >&2
    fi
  done
}
pr_to_review() {  # an open pull request whose last commit has no later verdict
  gh pr list --state open --json number,commits,comments --jq '
    .[] | ([.comments[] | select(.body | startswith("Verdict:")) | .createdAt] | max) as $r
        | select($r == null or $r < .commits[-1].committedDate) | .number' | head -n 1
}

for i in $(seq 1 "$n"); do
  merge_ready
  git pull -q --ff-only origin main
  role="" target=""
  if pr=$(pr_to_review) && [ -n "$pr" ]; then
    role=review-pr target=$pr
  elif [ $((i % 10)) = 0 ] && [ -n "$(approved)" ]; then
    role=garden
  else
    q=$(for f in $(questions_in); do
          grep -q '^| Status | proposed' "$f" && grep -q '^| Reviewer verdict | <' "$f" && echo "$f"
        done | head -n 1)
    if [ -n "$q" ]; then
      role=review-question target=$q
    elif grep -q '^novelty = "unchecked"' catalogue/results.toml 2>/dev/null; then
      role=bibliographer
    elif [ $((i % 4)) = 2 ] && [ -n "$(approved)" ]; then
      role=bibliographer
    else
      open=$(for f in $(questions_in); do grep -q '^| Status | open' "$f" && echo "$f"; done | shuf -n 1 || true)
      prog=$(approved | shuf -n 1 || true)
      if [ -n "$open" ] && [ $((i % 2)) = 1 ]; then
        role=research target=$open
      elif [ -n "$prog" ] && [ $((i % 3)) != 0 ]; then
        role=formalise target=$prog
      elif [ -n "$prog" ]; then
        role=propose target=$prog
      fi
    fi
  fi
  if [ -z "$role" ]; then
    echo "nothing to do: no pull request to review and no approved programme"
    exit 0
  fi
  echo "== task $i/$n: $role ${target} ($(date -u +%FT%TZ))"
  bash scripts/agent.sh "$role" "$target" || echo "task failed: $role $target" >&2
done
