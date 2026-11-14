#!/usr/bin/env bash
# The agent-side half of one task, run AS THE AGENT USER inside the sandbox of scripts/agent.sh
# (systemd-run --uid=incognita-agent). scripts/agent.sh copies this file from the loop's clone of
# main into the task's input directory, so the agent cannot change it. See agents/README.md.
#
#   agent-side.sh prepare <task-dir> <base-sha> <owner/repo> <main-ref> <head-ref>
#       reset the agent's clone (~/work): git configuration and hooks, fetch main and the PR head
#       from <task-dir>/in.bundle (refs <main-ref>, <head-ref>) as origin/main and origin/pr-head, check out <base-sha> on the branch incognita-task, remove
#       untracked files (except .lake), copy <task-dir>/agents/ to .agents/, reset ~/.claude from
#       the template.
#   agent-side.sh collect <out-dir> <main-sha> <head-sha|->
#       write <out-dir>/head (HEAD), <out-dir>/count (new commits, not in main nor in the PR head),
#       <out-dir>/out.bundle (those commits, as refs/incognita/out), and the first 200 000 bytes of
#       .agents/summary.md and .agents/report.md, if they are regular files.
set -euo pipefail

work=$HOME/work
template=${INCOGNITA_TEMPLATE:-/srv/incognita/template}
export GIT_CONFIG_NOSYSTEM=1 GIT_TERMINAL_PROMPT=0
# Never run hooks or a file system monitor configured by an earlier session.
g() { git -c core.hooksPath=/dev/null -c core.fsmonitor=false -c core.pager=cat "$@"; }

prepare() {
  local task_dir=$1 base=$2 slug=$3 ref_main=$4 ref_head=$5
  [[ "$base" =~ ^[0-9a-f]{40}$ ]] || { echo "bad base $base" >&2; exit 2; }
  [[ "$ref_main" =~ ^refs/incognita/bundle/[A-Za-z0-9._-]+$ ]] && [[ "$ref_head" =~ ^refs/incognita/bundle/[A-Za-z0-9._-]+$ ]] \
    || { echo "bad bundle refs" >&2; exit 2; }
  [ -d "$work/.git" ] && [ ! -L "$work" ] && [ ! -L "$work/.git" ] || { echo "$work is not a clone" >&2; exit 2; }
  cd "$work"
  # The repository configuration and hooks are rewritten: a session may have edited them.
  rm -rf .git/hooks .git/info/attributes .git/config
  mkdir -p .git/hooks
  cat > .git/config <<EOF
[core]
	repositoryformatversion = 0
	filemode = true
	bare = false
	logallrefupdates = true
	hooksPath = /dev/null
	fsmonitor = false
[remote "origin"]
	url = https://github.com/$slug.git
	fetch = +refs/heads/*:refs/remotes/origin/*
EOF
  cat > "$HOME/.gitconfig" <<'EOF'
[user]
	name = Incognita agent
	email = incognita-agent@users.noreply.github.com
[advice]
	detachedHead = false
[rebase]
	autoStash = false
[commit]
	gpgSign = false
EOF
  g rebase --abort >/dev/null 2>&1 || true
  g merge --abort >/dev/null 2>&1 || true
  g cherry-pick --abort >/dev/null 2>&1 || true
  rm -rf .git/rebase-merge .git/rebase-apply .git/MERGE_HEAD .git/CHERRY_PICK_HEAD
  g fetch -q --no-tags -f "$task_dir/in.bundle" \
    "+$ref_main:refs/remotes/origin/main" "+$ref_head:refs/remotes/origin/pr-head"
  g checkout -q -f -B incognita-task "$base"
  g clean -q -ffdx -e /.lake/
  # Other local branches of earlier tasks are dropped.
  g for-each-ref --format='%(refname:short)' refs/heads | grep -vx incognita-task \
    | while read -r b; do g branch -q -D "$b" || true; done
  g update-ref -d refs/incognita/out 2>/dev/null || true
  mkdir -p .agents
  cp -R "$task_dir/agents/." .agents/
  # Claude Code's configuration, from the template (nothing kept from an earlier session).
  rm -rf "$HOME/.claude" "$HOME/.claude.json" "$HOME/.claude.json.backup"
  if [ -d "$template/claude" ]; then cp -R "$template/claude" "$HOME/.claude"; else mkdir -p "$HOME/.claude"; fi
  if [ -f "$template/claude.json" ]; then cp "$template/claude.json" "$HOME/.claude.json"; fi
  echo "prepared $(g rev-parse HEAD)"
}

copy_capped() {  # src dst: the first 200 000 bytes of a regular file (not a link, not a FIFO)
  if [ -f "$1" ] && [ ! -L "$1" ]; then timeout 20 head -c 200000 -- "$1" > "$2" || true; fi
}

collect() {
  local out=$1 main=$2 head_sha=$3 head n
  [ -d "$out" ] && [ ! -L "$out" ] || { echo "no output directory $out" >&2; exit 2; }
  cd "$work"
  head=$(g rev-parse --verify -q 'HEAD^{commit}') || { echo none > "$out/head"; echo 0 > "$out/count"; exit 0; }
  echo "$head" > "$out/head"
  local negs=("^$main")
  [ "$head_sha" != - ] && negs+=("^$head_sha")
  n=$(g rev-list --count "$head" "${negs[@]}")
  echo "$n" > "$out/count"
  if [ "$n" -gt 0 ]; then
    g update-ref refs/incognita/out "$head"
    g bundle create -q "$out/out.bundle" refs/incognita/out "${negs[@]}"
  fi
  g status --porcelain=v1 --untracked-files=normal -- . ':!.agents' 2>/dev/null | head -n 50 > "$out/uncommitted" || true
  copy_capped .agents/summary.md "$out/summary.md"
  copy_capped .agents/report.md "$out/report.md"
  echo "collected $head ($n new commits)"
}

case "${1:-}" in
  prepare) shift; prepare "$@" ;;
  collect) shift; collect "$@" ;;
  *) echo "usage: agent-side.sh prepare <task-dir> <base> <owner/repo> <main-ref> <head-ref> | collect <out> <main> <head|->" >&2; exit 2 ;;
esac
