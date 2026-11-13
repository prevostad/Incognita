#!/usr/bin/env bash
# Run n agent tasks, one after the other, each time the most useful one in the order of AGENTS.md:
# review pull requests, review proposed questions, research open questions or formalise known
# results (alternately), propose questions; gardening every tenth task. See agents/README.md.
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
pr_to_review() {  # an open pull request whose last commit has no later verdict
  gh pr list --state open --json number,commits,comments --jq '
    .[] | ([.comments[] | select(.body | startswith("Verdict:")) | .createdAt] | max) as $r
        | select($r == null or $r < .commits[-1].committedDate) | .number' | head -n 1
}

for i in $(seq 1 "$n"); do
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
