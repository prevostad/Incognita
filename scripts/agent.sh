#!/usr/bin/env bash
# Run one agent task in a fresh worktree. See agents/README.md.
#
# Usage: scripts/agent.sh <role> [target]
#   propose <Programme> | review-question <question file> | research <question file>
#   formalise <Programme> | review-pr <pull request number> | garden | bibliographer
#   fix-pr <pull request number> | check
#
# Requires: claude and gh logged in, and a main checkout already built once with
# `scripts/build.sh Incognita` (the worktrees share its .lake/packages).
set -euo pipefail

role=${1:?usage: scripts/agent.sh <role> [target]}
target=${2:-}
root="$(git rev-parse --show-toplevel)"
cd "$root"
prompt_file="agents/roles/$role.md"
[ -f "$prompt_file" ] || { echo "unknown role: $role" >&2; exit 2; }
if [ "$role" != garden ] && [ "$role" != bibliographer ] && [ "$role" != check ] && [ -z "$target" ]; then
  echo "$role needs a target" >&2
  exit 2
fi
[ -d "$root/.lake/packages" ] || { echo "build the main checkout first: scripts/build.sh Incognita" >&2; exit 1; }

author_model=${INCOGNITA_MODEL_AUTHOR:-opus}
reviewer_model=${INCOGNITA_MODEL_REVIEWER:-sonnet}
max_turns=${INCOGNITA_MAX_TURNS:-200}
case "$role" in
  review-question|review-pr|check) model=$reviewer_model ;;
  *) model=$author_model ;;
esac

stamp=$(date -u +%Y%m%d-%H%M%S)
branch="agent/$role-$stamp"
wt="$root/.agents/$role-$stamp"
mkdir -p "$root/.agents"
git fetch -q origin
park_after=${INCOGNITA_PARK_AFTER:-5}
prompt=$(sed -e "s|{TARGET}|$target|g" -e "s|{PARK_AFTER}|$park_after|g" "$prompt_file")

# Every role may read the web (search and fetch pages). No shell network access, no push, no gh:
# the script pushes and opens the pull request.
web_tools="WebSearch,WebFetch"
# Writing roles: files, builds and local git.
write_tools="Read,Edit,Write,Glob,Grep,$web_tools,Bash(lake build:*),Bash(lake exe audit:*),Bash(lake env lean:*),Bash(bash scripts/build.sh:*),Bash(bash scripts/check-build.sh:*),Bash(scripts/build.sh:*),Bash(scripts/check-build.sh:*),Bash(git add:*),Bash(git commit:*),Bash(git status:*),Bash(git diff:*),Bash(git log:*),Bash(ls:*),Bash(grep:*)"
# Reviewers: read only.
read_tools="Read,Glob,Grep,$web_tools,Bash(git diff:*),Bash(git log:*),Bash(ls:*),Bash(grep:*)"

# Writing roles end by summarising their pull request for the human who merges it.
summary_instructions='

Finally, write the file `.agents/summary.md` (it is not committed; the script puts it in the pull
request description, and CI turns it into a PDF). Sections, in this order:
## Results — each result proved or refuted in this pull request, as a precise mathematical
statement (LaTeX between $...$ or $$...$$), followed by its Lean name; "None" if there is none.
## Frozen statements — frozen statements added (with their question), or "None".
## Sources read — the references read for this work, as [KEY, part].
## Not done — what remains, and any doubt about the statements.
Keep it short: it is what a human reads before merging.'

# Remove the worktree first, then the local branches (a branch cannot be deleted while a worktree
# uses it). A pushed branch lives on in origin; an unpushed one is kept by disabling this trap.
cleanup() {
  git -C "$root" worktree remove --force "$wt" 2>/dev/null || true
  git -C "$root" branch -q -D "pr-$target-$stamp" 2>/dev/null || true
  git -C "$root" branch -q -D "$branch" 2>/dev/null || true
}
trap cleanup EXIT

share_packages() {
  mkdir -p "$wt/.lake"
  ln -s "$root/.lake/packages" "$wt/.lake/packages"
}

if [ "$role" = review-pr ]; then
  git fetch -q origin "pull/$target/head:pr-$target-$stamp"
  git worktree add -q "$wt" "pr-$target-$stamp"
  share_packages
  mkdir -p "$wt/.agents"
  gh pr diff "$target" > "$wt/.agents/pr.diff"
  gh pr view "$target" --json title,body --jq '.title + "\n\n" + .body' > "$wt/.agents/pr.txt"
  review=$(cd "$wt" && claude -p "$prompt" --model "$model" --max-turns "$max_turns" \
    --allowedTools "$read_tools")
  case "$review" in
    Verdict:*) ;;
    *) echo "the review does not start with a verdict; not posted:" >&2; echo "$review" >&2; exit 1 ;;
  esac
  printf '%s\n\n---\n:robot: Automated review by `%s` (role review-pr, scripts/agent.sh).\n' \
    "$review" "$model" > "$wt/.agents/review.md"
  gh pr comment "$target" --body-file "$wt/.agents/review.md"
  exit 0
fi

# Human-owned paths may not change. New frozen statements (and their import in Statements.lean)
# are allowed for the roles that create them, and for fix-pr on a pull request that adds them.
check_paths() {
  local status=0 st path
  while IFS=$'\t' read -r st path; do
    case "$path" in
      README.md|AGENTS.md|CLAUDE.md|CONTRIBUTING.md|lakefile.toml|lean-toolchain|lake-manifest.json \
        |templates/*|agents/*|docs/*|scripts/*|.github/*|programmes/*/PROGRAMME.md)
        echo "human-owned path changed: $path" >&2; status=1 ;;
      programmes/*/questions/*) ;;
      literature/*|catalogue/*) ;;
      programmes/*/*) echo "human-owned path changed: $path" >&2; status=1 ;;
      Statements.lean)
        case "$role" in review-question|formalise|fix-pr) ;; *) echo "Statements.lean changed by $role" >&2; status=1 ;; esac ;;
      Statements/*)
        case "$st:$role" in
          A:review-question|A:formalise|A:fix-pr) ;;
          *) echo "frozen statement changed ($st) by $role: $path" >&2; status=1 ;;
        esac ;;
    esac
    if [ "$role" = bibliographer ]; then
      case "$path" in
        literature/*|catalogue/*|programmes/*/questions/*) ;;
        *) echo "the bibliographer may not change $path" >&2; status=1 ;;
      esac
    fi
  done < <(git diff --name-status origin/main...HEAD)
  return "$status"
}

summary_of() {
  if [ -f "$wt/.agents/summary.md" ]; then cat "$wt/.agents/summary.md"; else echo "(the agent wrote no summary)"; fi
}

# fix-pr: work on the branch of an agent's pull request, push to it, comment.
if [ "$role" = fix-pr ]; then
  head=$(gh pr view "$target" --json headRefName --jq .headRefName)
  case "$head" in
    agent/*) ;;
    *) echo "fix-pr only fixes pull requests of agents (branch agent/*), not $head" >&2; exit 2 ;;
  esac
  git fetch -q origin "$head"
  remote_sha=$(git rev-parse "origin/$head")
  branch="fix-pr-$target-$stamp"
  git worktree add -q -b "$branch" "$wt" "origin/$head"
  share_packages
  mkdir -p "$wt/.agents"
  gh pr view "$target" --json title,body --jq '.title + "\n\n" + .body' > "$wt/.agents/pr.txt"
  gh pr view "$target" --json comments \
    --jq '.comments[] | "### " + .createdAt + "\n\n" + .body + "\n"' > "$wt/.agents/reviews.md"
  gh pr checks "$target" > "$wt/.agents/ci.txt" 2>&1 || true
  run=$(gh run list --branch "$head" --workflow ci.yml --limit 1 --json databaseId,conclusion \
    --jq '.[0] | select(.conclusion == "failure") | .databaseId' 2>/dev/null || true)
  if [ -n "$run" ]; then
    gh run view "$run" --log-failed 2>/dev/null | tail -n 200 > "$wt/.agents/ci-log.txt" || true
  fi
  if [ "$(git -C "$wt" merge-base HEAD origin/main)" != "$(git rev-parse origin/main)" ]; then
    echo "The branch is behind origin/main: rebase it." > "$wt/.agents/rebase.txt"
  fi
  (cd "$wt" && claude -p "$prompt$summary_instructions" --model "$model" --max-turns "$max_turns" \
    --permission-mode acceptEdits \
    --allowedTools "$write_tools,Bash(git rebase:*),Bash(git show:*),Bash(git merge-base:*)")
  cd "$wt"
  if [ "$(git rev-parse HEAD)" = "$remote_sha" ]; then
    printf 'Fix round: no change.\n\n%s\n\n---\n:robot: `%s` (role fix-pr, scripts/agent.sh).\n' \
      "$(summary_of)" "$model" > "$wt/.agents/fix.md"
    gh pr comment "$target" --body-file "$wt/.agents/fix.md"
    exit 0
  fi
  if ! check_paths; then
    echo "branch $branch kept locally for inspection; not pushed" >&2
    trap - EXIT
    exit 1
  fi
  git push -q --force-with-lease="refs/heads/$head:$remote_sha" origin "HEAD:refs/heads/$head"
  printf 'Fix round: pushed.\n\n%s\n\n---\n:robot: `%s` (role fix-pr, scripts/agent.sh).\n' \
    "$(summary_of)" "$model" > "$wt/.agents/fix.md"
  gh pr comment "$target" --body-file "$wt/.agents/fix.md"
  exit 0
fi

git worktree add -q -b "$branch" "$wt" origin/main
share_packages
mkdir -p "$wt/.agents"
(cd "$wt" && claude -p "$prompt$summary_instructions" --model "$model" --max-turns "$max_turns" \
  --permission-mode acceptEdits --allowedTools "$write_tools")

cd "$wt"
if [ -z "$(git log --oneline origin/main..HEAD)" ]; then
  echo "no commit: nothing to push"
  exit 0
fi
if ! check_paths; then
  echo "branch $branch kept locally for inspection; not pushed" >&2
  trap - EXIT
  exit 1
fi

summary=$(summary_of)
git push -q -u origin "$branch"
gh pr create --base main --head "$branch" --title "$(git log -1 --format=%s)" --body "$(cat <<EOF
Role: \`$role\`. Target: \`${target:-none}\`. Model: \`$model\`.

$summary

Opened by \`scripts/agent.sh\` (see agents/README.md). CI attaches a PDF of this summary, with the
Lean statements of the pull request, to its run (artifact \`pr-summary\`).

🤖 Generated with [Claude Code](https://claude.com/claude-code)
EOF
)"
