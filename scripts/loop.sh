#!/usr/bin/env bash
# Run n agent tasks, one after the other, each time the most useful one in the order of AGENTS.md:
# fix the agents' own pull requests, review them, review proposed questions, audit the attribution
# of new results, keep a stock of questions per programme (INCOGNITA_QUESTION_STOCK), then a rotation
# of research, check, bibliographer and formalisation; gardening every tenth task. See agents/README.md.
#
# Usage: scripts/loop.sh [n]        (run it in the main checkout, on branch main, never edited by hand)
set -euo pipefail

n=${1:-1}
root="$(git rev-parse --show-toplevel)"
cd "$root"

# Quota pacing, as in the Tau Ceti worker: before each task, read the Claude subscription usage with
# the worker's own pacer (`tauceti status --json`) and wait while a window is not under pace.
# INCOGNITA_PACE is the pacing curve, with the syntax of `tauceti --pace` (unset: the worker's
# default curve; "0:100": everything that remains; "off": no pacing). The worker must be installed.
tauceti_conf=${INCOGNITA_TAUCETI_CONF:-https://raw.githubusercontent.com/LeanMachineLearning/LMLExplore/main/tauceti.toml}
wait_for_quota() {
  [ "${INCOGNITA_PACE:-}" = off ] && return 0
  local q ok next s
  while true; do
    if [ -n "${INCOGNITA_PACE:-}" ]; then
      q=$(TAUCETI_PACE="$INCOGNITA_PACE" tauceti --conf "$tauceti_conf" status --json 2>/dev/null \
        | jq -c '.quota.claude' 2>/dev/null) || q=""
    else
      q=$(tauceti --conf "$tauceti_conf" status --json 2>/dev/null | jq -c '.quota.claude' 2>/dev/null) || q=""
    fi
    ok=$(printf '%s' "${q:-null}" | jq -r '
      if . == null or (.windows | length) == 0 then "unknown (\(.error // "no reading"))"
      elif .rate_limited then "rate limited"
      elif ([.windows[].status] | all(. == "under-pace" or . == "idle")) then "yes"
      else "over pace" end' 2>/dev/null || echo "unknown")
    [ "$ok" = yes ] && return 0
    next=$(printf '%s' "${q:-null}" | jq -r '.next_eligible // empty' 2>/dev/null || true)
    if [ -n "$next" ]; then s=$(( ${next%.*} - $(date +%s) + 60 )); else s=900; fi
    [ "$s" -lt 300 ] && s=300
    [ "$s" -gt 3600 ] && s=3600
    echo "== quota: $ok $(printf '%s' "${q:-null}" | jq -c '[.windows[]? | {name, used, budget, status}]' 2>/dev/null); waiting ${s}s"
    sleep "$s"
  done
}

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
# Only the pull requests of agents (branch agent/*) are reviewed and fixed by agents; humans review
# their own. A pull request labelled needs-human is left to a human.
agent_prs='.[] | select(.headRefName | startswith("agent/"))
               | select([.labels[].name] | index("needs-human") | not)'
escalate() {  # label needs-human: a "block" verdict, or three fix rounds without success
  gh label create needs-human --color B60205 \
    --description "An agent cannot go further: a human must decide" >/dev/null 2>&1 || true
  local pr
  for pr in $(gh pr list --state open --json number,headRefName,labels,comments --jq "$agent_prs"'
      | ([.comments[] | select(.body | startswith("Verdict:"))] | sort_by(.createdAt) | last) as $v
      | ([.comments[] | select(.body | startswith("Fix round"))] | length) as $f
      | select(($v != null and ($v.body | startswith("Verdict: block"))) or $f >= 3) | .number'); do
    gh pr edit "$pr" --add-label needs-human >/dev/null && echo "== #$pr needs a human"
  done
}
pr_to_fix() {  # changes requested on the last commit (and not answered yet), a failed build, or a conflict
  gh pr list --state open --json number,headRefName,labels,commits,comments,mergeable,statusCheckRollup \
    --jq "$agent_prs"'
      | ([.comments[] | select(.body | startswith("Verdict:"))] | sort_by(.createdAt) | last) as $v
      | ([.comments[] | select(.body | startswith("Fix round")) | .createdAt] | max) as $lf
      | select(
          ($v != null and $v.createdAt > .commits[-1].committedDate
             and ($v.body | startswith("Verdict: request_changes"))
             and ($lf == null or $lf < $v.createdAt))
          or ([.statusCheckRollup[]? | select(.name == "Build and check") | .conclusion] | first) == "FAILURE"
          or .mergeable == "CONFLICTING")
      | .number' | head -n 1
}
pr_to_review() {  # an agent pull request whose last commit has no later verdict
  gh pr list --state open --json number,headRefName,labels,commits,comments --jq "$agent_prs"'
      | ([.comments[] | select(.body | startswith("Verdict:")) | .createdAt] | max) as $r
      | select($r == null or $r < .commits[-1].committedDate) | .number' | head -n 1
}

# Question stock: an approved programme with fewer than INCOGNITA_QUESTION_STOCK (default 3) questions
# waiting (proposed or open, plus proposals still in open pull requests) gets a new proposal before
# anything else. The cap also bounds what waits for the owner during calibration.
stock=${INCOGNITA_QUESTION_STOCK:-3}
programme_short_of_questions() {  # the approved programme with the fewest waiting questions, if below the stock
  local p c f pending best="" bestc=""
  for p in $(approved); do
    c=0
    for f in programmes/"$p"/questions/Q*.md; do
      [ -f "$f" ] || continue
      grep -q -E '^\| Status \| (proposed|open)' "$f" && c=$((c + 1))
    done
    # proposals of this programme still in open pull requests (agent.sh writes "Target: `<P>`")
    pending=$(gh pr list --state open --json title,body \
      --jq '[.[] | select(.title | startswith("Propose Q"))] | map(.body) | .[]' 2>/dev/null \
      | grep -c -F "Target: \`$p\`" || true)
    c=$((c + ${pending:-0}))
    if [ "$c" -lt "$stock" ] && { [ -z "$bestc" ] || [ "$c" -lt "$bestc" ]; }; then best=$p; bestc=$c; fi
  done
  echo "$best"
}

for i in $(seq 1 "$n"); do
  merge_ready
  wait_for_quota
  git pull -q --ff-only origin main
  escalate
  role="" target=""
  if pr=$(pr_to_fix) && [ -n "$pr" ]; then
    role=fix-pr target=$pr
  elif pr=$(pr_to_review) && [ -n "$pr" ]; then
    role=review-pr target=$pr
  elif [ $((i % 10)) = 0 ] && [ -n "$(approved)" ]; then
    role=garden
  else
    q=$(for f in $(questions_in); do
          grep -q '^| Status | proposed' "$f" && grep -q '^| Reviewer verdict | <' "$f" && echo "$f"
        done | head -n 1)
    open=$(for f in $(questions_in); do grep -q '^| Status | open' "$f" && echo "$f"; done | shuf -n 1 || true)
    low=$(programme_short_of_questions)
    if [ -n "$q" ]; then
      role=review-question target=$q
    elif grep -q '^novelty = "unchecked"' catalogue/results.toml 2>/dev/null; then
      role=bibliographer
    elif [ -n "$low" ]; then
      role=propose target=$low
    else
      # Rotation over six tasks: research three times (formalise if no question is open), check
      # once (formalise if nothing is merged), bibliographer once, formalise once.
      prog=$(approved | shuf -n 1 || true)
      case $((i % 6)) in
        1|3|5) if [ -n "$open" ]; then role=research target=$open; else role=formalise target=$prog; fi ;;
        0) if grep -q '^confidence = "merged"' catalogue/results.toml 2>/dev/null; then role=check
           else role=formalise target=$prog; fi ;;
        2) role=bibliographer ;;
        4) role=formalise target=$prog ;;
      esac
      [ -z "$prog" ] && [ "$role" != bibliographer ] && [ "$role" != check ] && [ "$role" != research ] && role=""
    fi
  fi
  if [ -z "$role" ]; then
    echo "nothing to do: no pull request to review and no approved programme"
    exit 0
  fi
  echo "== task $i/$n: $role ${target} ($(date -u +%FT%TZ))"
  bash scripts/agent.sh "$role" "$target" || echo "task failed: $role $target" >&2
done
