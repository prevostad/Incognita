#!/usr/bin/env bash
# The agent-side half of one task, run AS THE AGENT USER inside the sandbox of scripts/agent.sh
# (systemd-run --uid=incognita-agent). scripts/agent.sh copies this file from the loop's clone of
# main into the task's input directory, so the agent cannot change it. See agents/README.md.
#
#   agent-side.sh prepare <task-dir> <base-sha> <owner/repo> <main-ref> <head-ref>
#       reset the agent's home (nothing kept from an earlier session but ~/work/.lake, restored by
#       the loop just before, and ~/.elan, read-only in the sessions), the shell files from
#       /etc/skel, ~/.claude from the template; rebuild the agent's clone (~/work) from scratch:
#       everything but .lake removed (the old repository included), `git init`, a fixed
#       configuration, fetch main and the PR head from <task-dir>/in.bundle (refs <main-ref>,
#       <head-ref>) as origin/main and origin/pr-head, check out <base-sha> on the branch
#       incognita-task (the working tree is exactly that commit); in .lake, every CLAUDE*.md,
#       AGENTS*.md and .claude is removed; copy <task-dir>/agents/ to .agents/.
#   agent-side.sh collect <out-dir> <main-sha> <head-sha|->
#       write <out-dir>/head (HEAD), <out-dir>/count (new commits, not in main nor in the PR head),
#       <out-dir>/out.bundle (those commits, as refs/incognita/out), <out-dir>/untracked (at most
#       50 untracked paths, for the log), and the first 200 000 bytes of .agents/summary.md and
#       .agents/report.md, if they are regular files.
#   agent-side.sh notes <out-dir>
#       the first 200 000 bytes of .agents/report.md, if it is a regular file: the report so far of
#       a reviewer stopped before its verdict, handed to the next reviewer (AGENTS.md 5.4). Git is
#       not run.
#
# Git runs here on a repository the session controlled (collect) or on a new one (prepare): no
# configuration but the one written below (no global or system file, no hooks, no attributes file,
# no file system monitor, no replace objects, no grafts, no common directory elsewhere), and in
# collect only plumbing that runs no filter (rev-parse, rev-list, update-ref, bundle; never
# `git status`).
set -euo pipefail

work=$HOME/work
template=${INCOGNITA_TEMPLATE:-/srv/incognita/template}
export GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_SYSTEM=/dev/null GIT_CONFIG_NOSYSTEM=1 GIT_TERMINAL_PROMPT=0 \
  GIT_NO_REPLACE_OBJECTS=1
unset GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES \
  GIT_CEILING_DIRECTORIES GIT_COMMON_DIR GIT_NAMESPACE GIT_REPLACE_REF_BASE GIT_GRAFT_FILE GIT_SHALLOW_FILE \
  GIT_CONFIG GIT_CONFIG_PARAMETERS GIT_CONFIG_COUNT GIT_TEMPLATE_DIR GIT_ATTR_SOURCE GIT_EXEC_PATH
g() { git -c core.hooksPath=/dev/null -c core.fsmonitor=false -c core.attributesFile=/dev/null \
        -c core.pager=cat -c core.untrackedCache=false "$@"; }

check_clone() {
  [ -d "$work/.git" ] && [ ! -L "$work" ] && [ ! -L "$work/.git" ] || { echo "$work is not a clone" >&2; exit 2; }
}

# write_config [<owner/repo>]: the repository's configuration from a fixed template (no filter
# driver can be configured: the global and system files are /dev/null).
write_config() {
  local slug=${1:-}
  {
    printf '[core]\n\trepositoryformatversion = 0\n\tfilemode = true\n\tbare = false\n'
    printf '\tlogallrefupdates = true\n\thooksPath = /dev/null\n\tfsmonitor = false\n'
    if [ -n "$slug" ]; then
      printf '[remote "origin"]\n\turl = https://github.com/%s.git\n' "$slug"
      printf '\tfetch = +refs/heads/*:refs/remotes/origin/*\n'
    fi
  } > "$work/.git/config"
}

# reset_git (collect): the session's repository with the fixed configuration again, and without
# what would make git read another configuration, other objects or other history (a common
# directory elsewhere, a per-worktree configuration, grafts, a shallow file, replace refs,
# alternates), hooks or attributes.
reset_git() {
  cd "$work"
  rm -rf .git/hooks .git/info/attributes .git/config .git/config.worktree .git/commondir .git/info/grafts \
    .git/shallow .git/refs/replace .git/objects/info/alternates .git/objects/info/http-alternates
  write_config
}

# clean_home: nothing of an earlier session survives in the home but the clone (rebuilt below,
# except its .lake) and the toolchain (read-only in the sessions); ~/.local goes too (Claude Code is
# /opt/incognita/bin/claude, root-owned). Shell files come back from /etc/skel.
clean_home() {
  local f
  cd "$HOME"
  for f in "$HOME"/* "$HOME"/.[!.]* "$HOME"/..?*; do
    [ -e "$f" ] || [ -L "$f" ] || continue
    case "${f##*/}" in work|.elan) ;; *)
      if [ -d "$f" ] && [ ! -L "$f" ]; then chmod -R u+rwX -- "$f" 2>/dev/null || true; fi
      rm -rf -- "$f" ;;
    esac
  done
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
  [ -d "$work" ] && [ ! -L "$work" ] || { echo "$work is not a directory" >&2; exit 2; }
  clean_home
  cd "$work"
  # The session's clone is dropped whole, its repository included (.git, or a .git file pointing
  # elsewhere, with its configuration, index, hooks, replace refs, grafts...): only the build
  # directory is kept, which the loop restored from its own copy just before
  # (scripts/lib.sh restore_agent_lake: nothing planted by a session survives there).
  if [ -L .lake ] || { [ -e .lake ] && [ ! -d .lake ]; }; then rm -f -- .lake; fi
  find . -mindepth 1 -maxdepth 1 ! -name .lake ! -type l -type d -exec chmod -R u+rwX -- {} + 2>/dev/null || true
  find . -mindepth 1 -maxdepth 1 ! -name .lake -exec rm -rf -- {} +
  # A new repository: no template (no hooks), the fixed configuration, the objects of the bundle.
  g init -q --template= -b incognita-task .
  write_config "$slug"
  g fetch -q --no-tags -f "$task_dir/in.bundle" \
    "+$ref_main:refs/remotes/origin/main" "+$ref_head:refs/remotes/origin/pr-head"
  g checkout -q -f -B incognita-task "$base"
  # The working tree is exactly the commit: no index entry marked skip-worktree or
  # assume-unchanged, no untracked file (outside the ignored .lake).
  local odd
  odd=$(g ls-files -v | grep -v '^H ' | head -n 3 || true)
  [ -z "$odd" ] || { echo "index entries not plain after checkout: $odd" >&2; exit 2; }
  odd=$(g ls-files --others --exclude-standard | head -n 3 || true)
  [ -z "$odd" ] || { echo "untracked files after checkout: $odd" >&2; exit 2; }
  [ "$(g rev-parse HEAD)" = "$base" ] && [ "$(g rev-parse --git-common-dir)" = .git ] \
    || { echo "the new repository is not at $base" >&2; exit 2; }
  # No instructions for Claude Code in the build directory: the dependencies' own CLAUDE*.md,
  # AGENTS*.md and .claude/ are removed too. Those tracked by a dependency are hidden from its git
  # (skip-worktree in the dependency's index, set here on every task: the loop's restore brings
  # back its own index first), so that lake does not warn that their repositories have local
  # changes.
  if [ -d .lake ]; then
    local pkg
    for pkg in .lake/packages/*/; do
      pkg=${pkg%/}
      [ -d "$pkg/.git" ] && [ ! -L "$pkg" ] && [ ! -L "$pkg/.git" ] || continue
      ( cd "$pkg" && g ls-files -z -- 'CLAUDE*.md' '*/CLAUDE*.md' 'AGENTS*.md' '*/AGENTS*.md' '.claude/*' '*/.claude/*' \
          | xargs -0 -r git -c core.hooksPath=/dev/null -c core.fsmonitor=false update-index --skip-worktree -- ) || true
    done
    find .lake \( -name 'CLAUDE*.md' -o -name 'AGENTS*.md' -o -name '.claude' \) -prune -exec rm -rf -- {} + 2>/dev/null || true
  fi
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
  # The session may have changed the repository's configuration, hooks, common directory...:
  # reset first.
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

notes() {
  local out=$1
  [ -d "$out" ] && [ ! -L "$out" ] || { echo "no output directory $out" >&2; exit 2; }
  cd "$work" || exit 2
  copy_capped .agents/report.md "$out/report.md"
  echo "notes collected"
}

case "${1:-}" in
  prepare) shift; prepare "$@" ;;
  collect) shift; collect "$@" ;;
  notes) shift; notes "$@" ;;
  *) echo "usage: agent-side.sh prepare <task-dir> <base> <owner/repo> <main-ref> <head-ref> | collect <out> <main> <head|-> | notes <out>" >&2; exit 2 ;;
esac
