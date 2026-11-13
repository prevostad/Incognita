#!/usr/bin/env bash
# Run one agent task in a fresh worktree. See agents/README.md.
#
# Usage: scripts/agent.sh <role> [target]
#   propose <Programme> | review-question <question file> | research <question file>
#   formalise <Programme> | review-pr <pull request number> | garden
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
if [ "$role" != garden ] && [ -z "$target" ]; then
  echo "$role needs a target" >&2
  exit 2
fi
[ -d "$root/.lake/packages" ] || { echo "build the main checkout first: scripts/build.sh Incognita" >&2; exit 1; }

author_model=${INCOGNITA_MODEL_AUTHOR:-opus}
reviewer_model=${INCOGNITA_MODEL_REVIEWER:-sonnet}
max_turns=${INCOGNITA_MAX_TURNS:-200}
case "$role" in
  review-question|review-pr) model=$reviewer_model ;;
  *) model=$author_model ;;
esac

stamp=$(date -u +%Y%m%d-%H%M%S)
branch="agent/$role-$stamp"
wt="$root/.agents/$role-$stamp"
mkdir -p "$root/.agents"
git fetch -q origin
prompt=$(sed "s|{TARGET}|$target|g" "$prompt_file")

# Writing roles: files, builds and local git only (no push, no gh, no network).
write_tools="Read,Edit,Write,Glob,Grep,Bash(lake build:*),Bash(lake exe audit:*),Bash(lake env lean:*),Bash(bash scripts/build.sh:*),Bash(bash scripts/check-build.sh:*),Bash(scripts/build.sh:*),Bash(scripts/check-build.sh:*),Bash(git add:*),Bash(git commit:*),Bash(git status:*),Bash(git diff:*),Bash(git log:*),Bash(ls:*),Bash(grep:*)"
# Reviewers: read only.
read_tools="Read,Glob,Grep,Bash(git diff:*),Bash(git log:*),Bash(ls:*),Bash(grep:*)"

cleanup() { git -C "$root" worktree remove --force "$wt" 2>/dev/null || true; }
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
  git branch -q -D "pr-$target-$stamp" || true
  exit 0
fi

git worktree add -q -b "$branch" "$wt" origin/main
share_packages
(cd "$wt" && claude -p "$prompt" --model "$model" --max-turns "$max_turns" \
  --permission-mode acceptEdits --allowedTools "$write_tools")

cd "$wt"
if [ -z "$(git log --oneline origin/main..HEAD)" ]; then
  echo "no commit: nothing to push"
  git -C "$root" branch -q -D "$branch" || true
  exit 0
fi

# Human-owned paths may not change. New frozen statements (and their import in Statements.lean)
# are allowed for the roles that create them.
status=0
while IFS=$'\t' read -r st path; do
  case "$path" in
    README.md|AGENTS.md|CLAUDE.md|CONTRIBUTING.md|lakefile.toml|lean-toolchain|lake-manifest.json \
      |templates/*|agents/*|docs/*|scripts/*|.github/*|programmes/*/PROGRAMME.md)
      echo "human-owned path changed: $path" >&2; status=1 ;;
    programmes/*/questions/*) ;;
    programmes/*/*) echo "human-owned path changed: $path" >&2; status=1 ;;
    Statements.lean)
      case "$role" in review-question|formalise) ;; *) echo "Statements.lean changed by $role" >&2; status=1 ;; esac ;;
    Statements/*)
      if [ "$st" != A ] || { [ "$role" != review-question ] && [ "$role" != formalise ]; }; then
        echo "frozen statement changed ($st) by $role: $path" >&2; status=1
      fi ;;
  esac
done < <(git diff --name-status origin/main...HEAD)
if [ "$status" != 0 ]; then
  echo "branch $branch kept locally for inspection; not pushed" >&2
  trap - EXIT
  exit 1
fi

git push -q -u origin "$branch"
gh pr create --base main --head "$branch" --title "$(git log -1 --format=%s)" --body "$(cat <<EOF
Role: \`$role\`. Target: \`${target:-none}\`. Model: \`$model\`.

Opened by \`scripts/agent.sh\` (see agents/README.md).

🤖 Generated with [Claude Code](https://claude.com/claude-code)
EOF
)"
