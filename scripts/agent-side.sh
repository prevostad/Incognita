#!/usr/bin/env bash
# The agent-side half of one task, run AS THE AGENT USER inside the sandbox of scripts/agent.sh
# (systemd-run --uid=incognita-agent). scripts/agent.sh copies this file from the loop's clone of
# main into the task's input directory, so the agent cannot change it. See agents/README.md.
#
#   agent-side.sh prepare <task-dir> <base-sha> <owner/repo> <main-ref> <head-ref>
#       reset the agent's home (nothing kept from an earlier session but ~/work, ~/.elan and the
#       old Claude Code install of ~/.local), the shell files from /etc/skel, ~/.claude from the
#       template; reset the agent's clone (~/work): git configuration and hooks, fetch main and the
#       PR head from <task-dir>/in.bundle (refs <main-ref>, <head-ref>) as origin/main and
#       origin/pr-head, check out <base-sha> on the branch incognita-task, remove untracked files
#       (except .lake, where every CLAUDE*.md, AGENTS*.md and .claude is removed), copy
#       <task-dir>/agents/ to .agents/.
#   agent-side.sh collect <out-dir> <main-sha> <head-sha|->
#       write <out-dir>/head (HEAD), <out-dir>/count (new commits, not in main nor in the PR head),
#       <out-dir>/out.bundle (those commits, as refs/incognita/out), <out-dir>/untracked (at most
#       50 untracked paths, for the log), and the first 200 000 bytes of .agents/summary.md and
#       .agents/report.md, if they are regular files.
#
# Git runs here on a clone the session controlled: no configuration but the one written below
# (no global or system file, no hooks, no attributes file, no file system monitor), and only
# plumbing that runs no filter (rev-parse, rev-list, update-ref, bundle; never `git status`).
set -euo pipefail

work=$HOME/work
template=${INCOGNITA_TEMPLATE:-/srv/incognita/template}
export GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_SYSTEM=/dev/null GIT_CONFIG_NOSYSTEM=1 GIT_TERMINAL_PROMPT=0
unset GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES GIT_CEILING_DIRECTORIES
g() { git -c core.hooksPath=/dev/null -c core.fsmonitor=false -c core.attributesFile=/dev/null \
        -c core.pager=cat -c core.untrackedCache=false "$@"; }

check_clone() {
  [ -d "$work/.git" ] && [ ! -L "$work" ] && [ ! -L "$work/.git" ] || { echo "$work is not a clone" >&2; exit 2; }
}

# reset_git [<owner/repo>]: the repository's configuration from a fixed template, no hooks, no
# attributes or alternates of the session.
reset_git() {
  local slug=${1:-}
  cd "$work"
  rm -rf .git/hooks .git/info/attributes .git/config .git/objects/info/alternates
  mkdir -p .git/hooks
  {
    printf '[core]\n\trepositoryformatversion = 0\n\tfilemode = true\n\tbare = false\n'
    printf '\tlogallrefupdates = true\n\thooksPath = /dev/null\n\tfsmonitor = false\n'
    if [ -n "$slug" ]; then
      printf '[remote "origin"]\n\turl = https://github.com/%s.git\n' "$slug"
      printf '\tfetch = +refs/heads/*:refs/remotes/origin/*\n'
    fi
  } > .git/config
}

# clean_home: nothing of an earlier session survives in the home but the clone, the toolchain
# (read-only in the sessions) and the old Claude Code install (~/.local/{bin,share}/claude, no
# longer on PATH: the sessions run /opt/incognita/bin/claude). Shell files come back from /etc/skel.
clean_home() {
  local f
  cd "$HOME"
  for f in "$HOME"/* "$HOME"/.[!.]* "$HOME"/..?*; do
    [ -e "$f" ] || [ -L "$f" ] || continue
    case "${f##*/}" in work|.elan|.local) ;; *) rm -rf -- "$f" ;; esac
  done
  if [ -L "$HOME/.local" ] || [ ! -d "$HOME/.local" ]; then rm -rf -- "$HOME/.local"
  else
    for f in "$HOME/.local"/* "$HOME/.local"/.[!.]* "$HOME/.local"/..?*; do
      [ -e "$f" ] || [ -L "$f" ] || continue
      case "${f##*/}" in bin|share) [ -L "$f" ] && rm -rf -- "$f" ;; *) rm -rf -- "$f" ;; esac
    done
    for f in "$HOME/.local/bin" "$HOME/.local/share"; do
      [ -d "$f" ] && find "$f" -mindepth 1 -maxdepth 1 ! -name claude -exec rm -rf -- {} +
    done
  fi
  for f in .bashrc .profile .bash_logout; do
    if [ -f "/etc/skel/$f" ]; then cp "/etc/skel/$f" "$HOME/$f"; fi
  done
  # Claude Code's configuration, from the template.
  if [ -d "$template/claude" ]; then cp -R "$template/claude" "$HOME/.claude"; else mkdir -p "$HOME/.claude"; fi
  if [ -f "$template/claude.json" ]; then cp "$template/claude.json" "$HOME/.claude.json"; fi
  # The identity of the session's commits (the session's git reads this file; this script does not).
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
}

prepare() {
  local task_dir=$1 base=$2 slug=$3 ref_main=$4 ref_head=$5
  [[ "$base" =~ ^[0-9a-f]{40}$ ]] || { echo "bad base $base" >&2; exit 2; }
  [[ "$slug" =~ ^[A-Za-z0-9._-]+/[A-Za-z0-9._-]+$ ]] || { echo "bad repository $slug" >&2; exit 2; }
  [[ "$ref_main" =~ ^refs/incognita/bundle/[A-Za-z0-9._-]+$ ]] && [[ "$ref_head" =~ ^refs/incognita/bundle/[A-Za-z0-9._-]+$ ]] \
    || { echo "bad bundle refs" >&2; exit 2; }
  check_clone
  clean_home
  reset_git "$slug"
  g rebase --abort >/dev/null 2>&1 || true
  g merge --abort >/dev/null 2>&1 || true
  g cherry-pick --abort >/dev/null 2>&1 || true
  rm -rf .git/rebase-merge .git/rebase-apply .git/MERGE_HEAD .git/CHERRY_PICK_HEAD
  g fetch -q --no-tags -f "$task_dir/in.bundle" \
    "+$ref_main:refs/remotes/origin/main" "+$ref_head:refs/remotes/origin/pr-head"
  g checkout -q -f -B incognita-task "$base"
  g clean -q -ffdx -e /.lake/
  # No instructions for Claude Code in the build directory: the loop restored it from its own copy
  # (scripts/lib.sh restore_agent_lake: nothing planted by a session survives); the dependencies'
  # own CLAUDE*.md, AGENTS*.md and .claude/ are removed too, and hidden from git
  # (skip-worktree), so that lake does not warn that their repositories have local changes.
  if [ -d .lake ] && [ ! -L .lake ]; then
    local pkg
    for pkg in .lake/packages/*/; do
      pkg=${pkg%/}
      [ -d "$pkg/.git" ] && [ ! -L "$pkg" ] && [ ! -L "$pkg/.git" ] || continue
      ( cd "$pkg" && g ls-files -z -- 'CLAUDE*.md' '*/CLAUDE*.md' 'AGENTS*.md' '*/AGENTS*.md' '.claude/*' '*/.claude/*' \
          | xargs -0 -r git -c core.hooksPath=/dev/null -c core.fsmonitor=false update-index --skip-worktree -- ) || true
    done
    find .lake \( -name 'CLAUDE*.md' -o -name 'AGENTS*.md' -o -name '.claude' \) -prune -exec rm -rf -- {} + 2>/dev/null || true
  fi
  # Other local branches of earlier tasks are dropped.
  g for-each-ref --format='%(refname:short)' refs/heads | { grep -vx incognita-task || true; } \
    | while read -r b; do g branch -q -D "$b" || true; done
  g update-ref -d refs/incognita/out 2>/dev/null || true
  mkdir -p .agents
  cp -R "$task_dir/agents/." .agents/
  echo "prepared $(g rev-parse HEAD)"
}

copy_capped() {  # src dst: the first 200 000 bytes of a regular file (not a link, not a FIFO)
  if [ -f "$1" ] && [ ! -L "$1" ]; then timeout 20 head -c 200000 -- "$1" > "$2" || true; fi
}

collect() {
  local out=$1 main=$2 head_sha=$3 head n
  [ -d "$out" ] && [ ! -L "$out" ] || { echo "no output directory $out" >&2; exit 2; }
  [[ "$main" =~ ^[0-9a-f]{40}$ ]] && { [ "$head_sha" = - ] || [[ "$head_sha" =~ ^[0-9a-f]{40}$ ]]; } \
    || { echo "bad main or head" >&2; exit 2; }
  check_clone
  # The session may have changed the repository's configuration or hooks: rewritten first.
  reset_git
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
  # For the log only: untracked paths are listed, never hashed (no filter can run).
  { g ls-files --others --exclude-standard -- . ':!.agents' ':!.lake' 2>/dev/null || true; } | head -n 50 > "$out/untracked"
  copy_capped .agents/summary.md "$out/summary.md"
  copy_capped .agents/report.md "$out/report.md"
  echo "collected $head ($n new commits)"
}

case "${1:-}" in
  prepare) shift; prepare "$@" ;;
  collect) shift; collect "$@" ;;
  *) echo "usage: agent-side.sh prepare <task-dir> <base> <owner/repo> <main-ref> <head-ref> | collect <out> <main> <head|->" >&2; exit 2 ;;
esac
