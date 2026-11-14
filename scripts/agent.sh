#!/usr/bin/env bash
# Run one agent task: one `claude -p` session as the isolated user incognita-agent. See
# agents/README.md ("How a task runs").
#
# Usage: scripts/agent.sh <role> [target]
#   write-paper <Roadmap>          formalize-statements <Paper>     prove <Paper>
#   referee-scope <PR>             referee-proofs <PR>              review-statements <PR>
#   review-pr <PR>                 revise <PR> | revise <Paper>     fix-pr <PR> | fix-pr main
#   bibliographer [<Paper>|-]      garden                           propose-roadmap <Roadmap> | -
#   review-roadmap <PR>
#
# Run by the user `lean` in its clone of main (never edited by hand), normally from scripts/loop.sh.
# The loop never runs git or lake inside the agent's clone, and never opens a file the agent wrote
# as itself: inputs go in as a git bundle, outputs come back as files of the agent user, read
# through `sudo -u incognita-agent` (out_read), then are checked here (path whitelist), squashed
# into one commit and pushed with the loop's own GitHub token.
#
# Environment from the loop: INCOGNITA_HEAD (the PR head the task was chosen for), INCOGNITA_TASK_TIMEOUT
# (seconds), INCOGNITA_NOTE (extra situation line for task.md), and the variables of scripts/lib.sh.
# Exit: 0 task done (whatever the outcome; recorded in the state), 1 error, 2 usage,
# 3 Claude is logged out (stop the night), 4 rate limited (reset time in state/rate-limit-until),
# 5 the infrastructure failed before the session (not counted against the target), 7 the agent's
# ~/work could not be prepared even after one repair (stop the night).
set -u -o pipefail
umask 022
# shellcheck source=scripts/lib.sh
. "$(dirname "${BASH_SOURCE[0]}")/lib.sh"
die() { log "fatal: $*"; exit 5; }   # before the session: an infrastructure failure

role=${1:-}
target=${2:--}
is_role "$role" || { echo "usage: scripts/agent.sh <role> [target]; roles: $ROLES" >&2; exit 2; }
init_state || die "cannot create $INCOGNITA_STATE"
owner_login >/dev/null || die "gh is not logged in (gh api user failed)"
DEADLINE=$(deadline_epoch) || exit 2
# Hard requirement: a session never runs without the isolation of D11 (its tools run LaTeX, Python
# and Lean code written by the agent).
if ! is_dry; then
  id -u "$INCOGNITA_AGENT_USER" >/dev/null 2>&1 \
    || die "no user $INCOGNITA_AGENT_USER: run scripts/server/setup-agent-user.sh first"
  [ "$(id -un)" != "$INCOGNITA_AGENT_USER" ] || die "run this as the loop's user, not as $INCOGNITA_AGENT_USER"
  command -v systemd-run >/dev/null || die "systemd-run is missing"
  sudo -n true 2>/dev/null || die "the loop's user needs sudo without password (systemd-run, rsync)"
  [ -d "$INCOGNITA_EXCHANGE/in" ] && [ -d "$INCOGNITA_EXCHANGE/out" ] \
    || die "$INCOGNITA_EXCHANGE/{in,out} missing: run scripts/server/setup-agent-user.sh"
  [ -x "$AGENT_CLAUDE" ] && [ "$(stat -c %U "$AGENT_CLAUDE" 2>/dev/null)" = root ] \
    || die "no root-owned $AGENT_CLAUDE: run scripts/server/setup-agent-user.sh"
fi

# ---------------------------------------------------------------- parameters of the role
upper=$(printf '%s' "$role" | tr 'a-z-' 'A-Z_')
if is_review_role "$role"; then
  model=$INCOGNITA_MODEL_REVIEWER timeout_s=$INCOGNITA_TIMEOUT_REVIEW
else
  model=$INCOGNITA_MODEL_AUTHOR timeout_s=$INCOGNITA_TIMEOUT_WRITE
fi
v=INCOGNITA_MODEL_$upper; [ -n "${!v:-}" ] && model=${!v}
v=INCOGNITA_TIMEOUT_$upper; [ -n "${!v:-}" ] && timeout_s=${!v}
[ -n "${INCOGNITA_TASK_TIMEOUT:-}" ] && [ "$INCOGNITA_TASK_TIMEOUT" -lt "$timeout_s" ] && timeout_s=$INCOGNITA_TASK_TIMEOUT
effort=$INCOGNITA_EFFORT
turns=$INCOGNITA_MAX_TURNS

web="WebSearch,WebFetch"
read_tools="Read,Glob,Grep,$web,Bash(ls:*),Bash(grep:*),Bash(wc:*),Bash(git diff:*),Bash(git log:*),Bash(git show:*),Bash(git status:*)"
lean_tools="Bash(lake build:*),Bash(lake env lean:*),Bash(lake lint:*),Bash(lake exe audit:*),Bash(lake exe mk_all:*),Bash(bash scripts/build.sh:*),Bash(bash scripts/check-build.sh:*),Bash(scripts/build.sh:*),Bash(scripts/check-build.sh:*)"
# LaTeX and Python (numerical experiments) run arbitrary code: acceptable ONLY because every session
# runs as incognita-agent under systemd-run (scripts/lib.sh, run_sandboxed). Never give these tools
# to a session that is not isolated.
exec_tools="Bash(latexmk:*),Bash(pdflatex:*),Bash(bibtex:*),Bash(python3:*)"
write_tools="$read_tools,Edit,Write,$lean_tools,$exec_tools,Bash(git add:*),Bash(git commit:*),Bash(git rm:*),Bash(git mv:*),Bash(mkdir:*)"
rebase_tools="Bash(git rebase origin/main),Bash(git rebase --continue),Bash(git rebase --abort),Bash(git merge-base:*)"
case "$role" in
  referee-scope) tools=$read_tools ;;
  # Numerical experiments in .agents/scratch/ (a reviewer's files are never collected).
  referee-proofs) tools="$read_tools,$exec_tools,Write,Bash(mkdir:*)" ;;
  review-statements|review-pr) tools="$read_tools,$lean_tools" ;;
  fix-pr|revise) tools="$write_tools,$rebase_tools" ;;
  *) tools=$write_tools ;;
esac

stamp=$(date +%Y%m%d-%H%M%S)
task="$stamp-$role"
if is_dry; then
  in=$(mktemp -d); out=$(mktemp -d)
else
  in=$INCOGNITA_EXCHANGE/in/$task; out=$INCOGNITA_EXCHANGE/out/$task
fi
tmp=$(mktemp -d)
cleanup() {
  stop_sandbox
  rm -rf "$tmp"
  if is_dry; then rm -rf "$in" "$out"
  else
    rm -rf "$in" 2>/dev/null
    [[ "$task" =~ ^[0-9]{8}-[0-9]{6}-[a-z-]+$ ]] && sudo -n rm -rf "$INCOGNITA_EXCHANGE/out/$task" 2>/dev/null
    repo_git update-ref -d "refs/incognita/tasks/$task" 2>/dev/null
    repo_git update-ref -d "refs/incognita/bundle/$task-main" 2>/dev/null
    repo_git update-ref -d "refs/incognita/bundle/$task-head" 2>/dev/null
  fi
  return 0
}
trap cleanup EXIT
trap 'log "interrupted"; exit 130' INT TERM

finish() {  # ok|fail|skip <outcome...>: record and exit 0
  local kind=$1; shift
  record_attempt "$role" "$target" "$kind" "$@"
  record_event task "$role" "$target" "$kind $* ${session_info:-}"
  log "== $role $target: $kind $*"
  exit 0
}
session_info=""

# ---------------------------------------------------------------- what the task works on
M=$(sync_main) || die "cannot update the loop's clone of main"
prs_json=$tmp/prs.json
fetch_open_prs > "$prs_json" || die "cannot list the open pull requests (unknown, not empty)"

pr="" H="" branch="" pr_role="" pr_target="" kind="" paper="" roadmap="" base="$M" eff_role=$role
pr_title="" pr_labels="" pr_draft=false
paper_of_ref() {  # ref: the paper directories a PR adds or changes (merge-base(main, ref)..ref)
  repo_git diff --name-only --no-renames "$(repo_git merge-base "$M" "$1")" "$1" -- papers \
    | sed -n -E 's#^papers/([^/]+)/.*#\1#p' | sort -u
}
case "$role:$target" in
  fix-pr:main)
    eff_role=fix-main ;;
  referee-*:*|review-*:*|fix-pr:*|revise:[0-9]*)
    [[ "$target" =~ ^[0-9]+$ ]] || { echo "$role needs a pull request number" >&2; exit 2; }
    pr=$target
    info=$(ghr pr view "$pr" --json number,title,body,headRefName,headRefOid,isCrossRepository,state,isDraft,labels,author,baseRefName) \
      || die "cannot read pull request #$pr"
    [ "$(jq -r .state <<<"$info")" = OPEN ] || finish skip "not-open"
    [ "$(jq -r .isCrossRepository <<<"$info")" = false ] || finish skip "fork"
    [ "$(jq -r .author.login <<<"$info")" = "$OWNER" ] || finish skip "not-opened-by-the-loop"
    [ "$(jq -r .baseRefName <<<"$info")" = main ] || finish skip "base-not-main"
    branch=$(jq -r .headRefName <<<"$info")
    case "$branch" in agent/*) ;; *) finish skip "not-an-agent-branch" ;; esac
    H=$(jq -r .headRefOid <<<"$info")
    if [ -n "${INCOGNITA_HEAD:-}" ] && [ "$INCOGNITA_HEAD" != "$H" ]; then finish skip "moved"; fi
    fetch_pr_head "$pr" "$H" || finish skip "head-moved-or-fetch-failed"
    pr_title=$(jq -r .title <<<"$info")
    pr_draft=$(jq -r .isDraft <<<"$info")
    pr_labels=$(jq -r '[.labels[].name] | join(",")' <<<"$info")
    line=$(jq -r '.body // "" | split("\n")[0]' <<<"$info")
    pr_role=$(printf '%s' "$line" | sed -n -E 's/^Role: `([a-z-]+)`\. Target: `([^`]*)`\..*/\1/p')
    pr_target=$(printf '%s' "$line" | sed -n -E 's/^Role: `([a-z-]+)`\. Target: `([^`]*)`\..*/\2/p')
    [ -n "$pr_role" ] || finish skip "no-role-line"
    kind=$(pr_kind "$pr_role")
    [ "$kind" = scripted ] && finish skip "a-scripted-pull-request-of-the-loop"
    case "$role" in
      referee-scope|referee-proofs|revise) [ "$kind" = paper ] || finish skip "not-a-paper-pr" ;;
      review-statements) [ "$kind" = statements ] || finish skip "not-a-statements-pr" ;;
      review-roadmap) [ "$kind" = roadmap ] || finish skip "not-a-roadmap-pr" ;;
      review-pr) [ "$kind" = generic ] || finish skip "not-a-generic-pr" ;;
    esac
    paper=$(paper_of_ref "$H" | head -n 1)
    case "$pr_role" in
      prove|formalize-statements) paper=$(paper_of_num "$(paper_num "$pr_target")") || paper=$pr_target ;;
      revise) [[ "$pr_target" =~ ^P[0-9]+- ]] && paper=$pr_target ;;
      bibliographer) [[ "$pr_target" =~ ^P[0-9]{3}- ]] && paper=$pr_target ;;
    esac
    base=$H
    if [ "$role" = fix-pr ]; then
      case "$pr_role" in
        fix-pr) eff_role=fix-main ;;
        revise) eff_role=revise ;;
        *) eff_role=$pr_role ;;
      esac
    fi
    [ "$role" = revise ] && eff_role=revise
    [ "$kind" = paper ] && [ "$pr_role" = write-paper ] && roadmap=$pr_target
    ;;
  revise:*)   # a disputed paper on main: a new version in a new PR
    [[ "$target" =~ ^P[0-9]+-[A-Za-z0-9-]+$ ]] || { echo "revise needs a PR number or a paper" >&2; exit 2; }
    paper=$target ;;
  write-paper:*)
    [[ "$target" =~ ^[A-Za-z0-9_-]+$ ]] || { echo "write-paper needs a roadmap" >&2; exit 2; }
    roadmap=$target ;;
  propose-roadmap:*)
    [ "$target" = - ] || [[ "$target" =~ ^[A-Za-z0-9_-]+$ ]] || { echo "propose-roadmap needs a roadmap or -" >&2; exit 2; }
    [ "$target" = - ] || roadmap=$target ;;
  formalize-statements:*|prove:*)
    [[ "$target" =~ ^[A-Za-z0-9_-]+$ ]] || { echo "$role needs a paper" >&2; exit 2; }
    paper=$(paper_of_num "$(paper_num "$target")") || paper=$target ;;
  bibliographer:*)
    # A paper that waits for the bibliographer (its source notes, or its attribution audit).
    if [ "$target" != - ]; then
      [[ "$target" =~ ^P[0-9]{3}-[A-Za-z0-9-]+$ ]] && [ -n "$(ls_main "papers/$target")" ] \
        || { echo "bibliographer needs a paper on main or -" >&2; exit 2; }
      paper=$target
    fi ;;
esac
[ -z "$roadmap" ] && [ -n "$paper" ] && roadmap=$(meta_get "$paper" roadmap)
if [ -z "$roadmap" ] && [ -n "$paper" ] && [ -n "$H" ]; then
  roadmap=$(repo_git show "$H:papers/$paper/META.toml" 2>/dev/null \
    | sed -n -E 's/^roadmap[[:space:]]*=[[:space:]]*"([^"]*)".*/\1/p' | head -n 1)
fi
# A roadmap name goes into paths: only a roadmap directory of main (S4).
if [ -n "$roadmap" ] && ! valid_roadmap "$roadmap"; then
  log "the roadmap \"$(printf '%s' "$roadmap" | one_line 80)\" is not a roadmap of main: ignored"
  case "$role" in write-paper|propose-roadmap) finish skip "not-a-roadmap" ;; esac
  roadmap=""
fi

# The agent's .lake follows main's toolchain and manifest (it may rebuild main: before the context
# files, so that the deadline written in task.md holds).
if ! is_dry; then
  set_activity "prepare $role $target"
  sync_agent_lake || log "warning: the agent's .lake could not be re-synced; the session may rebuild"
fi

# ---------------------------------------------------------------- context files (.agents/)
ctx=$in/agents
if ! is_dry; then
  mkdir -p "$in" || die "cannot create $in (run scripts/server/setup-agent-user.sh)"
fi
mkdir -p "$ctx"
open_prs_md "$prs_json" > "$ctx/open-prs.md"
files="task.md open-prs.md"

meta_lines_at() {  # ref roadmap: "paper<TAB>directions<TAB>kind" of the papers of a roadmap at ref
  local ref=$1 r=$2 p m
  for p in $(repo_git ls-tree --name-only "$ref:papers" 2>/dev/null | grep -E '^P[0-9]+-'); do
    m=$(repo_git show "$ref:papers/$p/META.toml" 2>/dev/null) || continue
    printf '%s\n' "$m" | grep -Eq "^roadmap[[:space:]]*=[[:space:]]*\"$r\"" || continue
    printf '%s\t%s\t%s\n' "$p" "$(printf '%s\n' "$m" | sed -n -E 's/^directions[[:space:]]*=[[:space:]]*(.*)/\1/p' | head -n 1)" \
      "$(printf '%s\n' "$m" | sed -n -E 's/^kind[[:space:]]*=[[:space:]]*"([a-z]+)".*/\1/p' | head -n 1)"
  done
}

rounds=0 fixes=0
if [ -n "$pr" ]; then
  mb=$(repo_git merge-base "$M" "$H")
  repo_git diff --no-renames "$mb" "$H" | head -c 3000000 > "$ctx/pr.diff"
  { printf '%s\n\n' "$pr_title"; jq -r '.body // ""' <<<"$info"; } > "$ctx/pr.txt"
  files="$files pr.diff pr.txt"
  if comments=$(trusted_comments "$pr"); then
    if [ "$(jq 'length' <<<"$comments")" -gt 0 ]; then
      { echo "# Earlier reports on this pull request (written by the loop's sessions, oldest first)"
        echo
        jq -r --arg h "$H" '.[] | "## \(.kind) on `\(.sha[0:12])`\(if .sha == $h then " (the current head)" else "" end), \(.created_at)\n\n\(.body)\n"' <<<"$comments"
      } | head -c 400000 > "$ctx/reports.md"
      files="$files reports.md"
    fi
    # A referee re-checks what changed since its last report (D2): for a paper, its directory only
    # (a rebase on main changes much more).
    if is_review_role "$role"; then
      prev=$(jq -r --arg k "$role" --arg h "$H" '[.[] | select(.kind == $k and .sha != $h)] | last | .sha // empty' <<<"$comments")
      if [ -n "$prev" ] && { repo_git cat-file -e "$prev^{commit}" 2>/dev/null || repo_git fetch -q origin "$prev" 2>/dev/null; }; then
        if [ "$kind" = paper ] && [ -n "$paper" ]; then
          repo_git diff --no-renames "$prev" "$H" -- "papers/$paper/" | head -c 2000000 > "$ctx/revision.diff"
        else
          repo_git diff --no-renames "$prev" "$H" | head -c 2000000 > "$ctx/revision.diff"
        fi
        files="$files revision.diff"
      fi
    fi
  else
    die "cannot read the comments of #$pr"
  fi
  # Rounds since the owner last reopened the pull request (after its last `rejected` comment).
  rounds=$(jq "$SINCE_REJECTED_JQ"' since_rejected | [.[] | select(.kind == "revise")] | length' <<<"$comments")
  fixes=$(jq "$SINCE_REJECTED_JQ"' since_rejected | [.[] | select(.kind == "fix-pr" or .kind == "fix-pr-nochange" or .kind == "revise-fix" or .kind == "revise-fix-nochange")] | length' <<<"$comments")
fi
# revise on a paper PR: a revision round answers a referee's `major` on the head (it counts towards
# INCOGNITA_REVISION_ROUNDS, comment kind `revise`); otherwise it is a repair (failed build,
# conflict, incomplete draft: kind `revise-fix`, counted as a fix round). A `reject` on the head
# of a pull request the owner reopened is answered like a `major`.
referee_round=0
if [ "$role" = revise ] && [ -n "$pr" ]; then
  sts=$(statuses_of "$H") || sts=""
  case "$(verdict_in "$sts" "Referee scope" referee-scope) $(verdict_in "$sts" "Referee proofs" referee-proofs)" in
    *major*|*minor*|*reject*) referee_round=1 ;;
  esac
fi
ci_state=""
if [ -n "$H" ]; then
  ci_state=$(jq -r --argjson n "$pr" --arg role "$pr_role" "$CI_JQ"'
    .[] | select(.number == $n) | ci_of($role)' "$prs_json")
  case "$ci_state" in
    FAILURE|TIMED_OUT|STARTUP_FAILURE|ERROR)
      ci_failed_log "$H" | tail -c 150000 > "$ctx/ci-log.txt" && files="$files ci-log.txt" ;;
  esac
elif [ "$eff_role" = fix-main ]; then
  ci_failed_log "$M" | tail -c 150000 > "$ctx/ci-log.txt" && files="$files ci-log.txt"
fi
# Papers closed with the label `rejected`: "number head" lines, heads fetched (cached per task).
rejected_prs() {
  if [ ! -f "$tmp/rejected.txt" ]; then
    ghr pr list --state closed --label rejected --limit 200 --json number,headRefOid \
      --jq '.[] | "\(.number) \(.headRefOid)"' 2>/dev/null | while read -r n h; do
        repo_git cat-file -e "$h^{commit}" 2>/dev/null \
          || repo_git fetch -q origin "+refs/pull/$n/head:refs/incognita/pr/$n" 2>/dev/null || continue
        echo "$n $h"
      done > "$tmp/rejected.txt"
  fi
  cat "$tmp/rejected.txt"
}
# rejected_reports <roadmap>: the trusted reports on the rejected papers of the roadmap (D2: their
# D and C items count as covered; writers and scope referees read why they failed).
rejected_reports() {
  local n h c
  rejected_prs | while read -r n h; do
    [ -n "$(meta_lines_at "$h" "$1")" ] || continue
    c=$(trusted_comments "$n") || continue
    printf '## Rejected pull request #%s (%s)\n\n' "$n" "$(meta_lines_at "$h" "$1" | cut -f1 | tr '\n' ' ')"
    jq -r '.[] | select(.kind == "referee-scope" or .kind == "referee-proofs" or .kind == "rejected")
      | "### \(.kind) on `\(.sha[0:12])`, \(.created_at)\n\n\(.body)\n"' <<<"$c" | head -c 100000
  done
}
if [ "$role" = write-paper ]; then
  : > "$tmp/taken"
  papers_on_main >> "$tmp/taken"
  { echo "# Papers of the roadmap $roadmap and the directions they serve"
    echo
    echo "## On main"
    meta_lines_at origin/main "$roadmap" | awk -F'\t' '{print "- " $1 " (" $3 "): " $2}'
    echo
    echo "## In open pull requests"
    jq -r '.[] | select(.isCrossRepository == false) | "\(.number) \(.headRefOid)"' "$prs_json" \
      | while read -r n h; do
          fetch_pr_head "$n" "$h" 2>/dev/null || continue
          repo_git ls-tree --name-only "refs/incognita/pr/$n:papers" 2>/dev/null | grep -E '^P[0-9]+-' >> "$tmp/taken"
          meta_lines_at "refs/incognita/pr/$n" "$roadmap" | awk -F'\t' -v n="$n" '{print "- #" n " " $1 " (" $3 "): " $2}'
        done
    echo
    echo "## Rejected (closed with the label rejected)"
    echo
    echo "Their D and C items count as covered (no new paper on them unless the owner reopens one)."
    echo "Their F items (known results to formalise), and the items of a rejected \`definitions\` paper,"
    echo "stay open: a new paper on one of them answers the reports of the rejected paper (\`reports.md\`)."
    echo
    rejected_prs | while read -r n h; do
        repo_git ls-tree --name-only "$h:papers" 2>/dev/null | grep -E '^P[0-9]+-' >> "$tmp/taken"
        meta_lines_at "$h" "$roadmap" | awk -F'\t' -v n="$n" '{print "- #" n " " $1 " (" $3 "): " $2}'
      done
  } > "$ctx/papers.md" 2>/dev/null
  files="$files papers.md"
  # The number of the new paper: one more than every number on main, in open PRs and rejected.
  last=$(awk "$AWK_NUM"' num($0) >= 0 { print num($0) }' "$tmp/taken" | sort -n | tail -n 1)
  paper_number=$(printf 'P%03d' $(( ${last:--1} + 1 )))
fi
# The items of the roadmap on main (directions, known results, candidate directions; computed by
# scripts/certify.py items), for writers and proposers.
if { [ "$role" = write-paper ] || [ "$role" = propose-roadmap ]; } && [ -n "$roadmap" ]; then
  { echo "# Items of the roadmap $roadmap on main (computed by scripts/certify.py items)"
    echo
    echo "One line per item: open (no paper on main serves it: check papers.md for open and rejected"
    echo "pull requests), closed (pending owner decision, on hold, closed, or in a proposed extension),"
    echo "covered (the papers on main that serve it), dropped (a candidate direction)."
    echo
    certify_py items "$roadmap" 2>&1 | sed 's/^/- /'
  } > "$ctx/items.md"
  files="$files items.md"
fi
# The roadmaps, for a proposer: status, domain, KNOWN.md reviewed or not, free items.
if [ "$role" = propose-roadmap ]; then
  { echo "# Roadmaps on main"
    echo
    echo "| Roadmap | Status | Domain | KNOWN.md | Extensions | Free items |"
    echo "|---|---|---|---|---|---|"
    for r in $(ls_main roadmaps); do
      valid_roadmap "$r" || continue
      rm_text=$(show_main "roadmaps/$r/ROADMAP.md") || continue
      st=$(printf '%s\n' "$rm_text" | sed -n -E 's/^\| Status \| \*\*([a-z]+)\*\*.*/\1/p' | head -n 1)
      dom=$(printf '%s\n' "$rm_text" | sed -n -E 's/^\| Domain \| `?([a-z0-9-]+)`?.*/\1/p' | head -n 1)
      kn=$(show_main "roadmaps/$r/KNOWN.md" | head -n 1)
      ext=$(ls_main "roadmaps/$r/extensions" | tr '\n' ' ')
      fr=$(certify_py items "$r" --free 2>/dev/null | cut -d' ' -f1 | tr '\n' ' ')
      echo "| $r | ${st:-?} | ${dom:-?} | ${kn:-?} | ${ext:--} | ${fr:-none} |"
    done
    echo
    echo "Domains of the approved roadmaps (a proposal inside one of them is approved after a veto"
    echo "window; a new domain needs the owner's explicit approval): $(for r in $(ls_main roadmaps); do
        show_main "roadmaps/$r/ROADMAP.md" | grep -q '^| Status | \*\*approved' || continue
        show_main "roadmaps/$r/ROADMAP.md" | sed -n -E 's/^\| Domain \| `?([a-z0-9-]+)`?.*/\1/p' | head -n 1
      done | sort -u | tr '\n' ' ')"
  } > "$ctx/roadmaps.md"
  files="$files roadmaps.md"
fi
if [ "$role" = write-paper ] || [ "$role" = referee-scope ]; then
  if [ -n "$roadmap" ]; then
    rejected_reports "$roadmap" > "$tmp/rejected.md" 2>/dev/null
    if [ -s "$tmp/rejected.md" ]; then
      { [ -s "$ctx/reports.md" ] && { cat "$ctx/reports.md"; echo; }
        echo "# Reports on the rejected papers of the roadmap $roadmap"
        echo
        cat "$tmp/rejected.md"
      } | head -c 600000 > "$tmp/reports-all.md"
      mv "$tmp/reports-all.md" "$ctx/reports.md"
      in_list reports.md "$files" || files="$files reports.md"
    fi
  fi
fi
# The bibliographer's paper: the scope referees' reports on the pull request that added it (its
# merge commit on main ends with "(#<n>)").
if [ "$role" = bibliographer ] && [ -n "$paper" ]; then
  merged_pr=$(repo_git log --diff-filter=A --format=%s origin/main -- "papers/$paper/META.toml" | tail -n 1 \
    | sed -n -E 's/.*\(#([0-9]+)\)$/\1/p')
  if [ -n "$merged_pr" ] && c=$(trusted_comments "$merged_pr"); then
    { echo "# Reports of referee-scope on pull request #$merged_pr, which added \`$paper\` (oldest first)"
      echo
      jq -r '.[] | select(.kind == "referee-scope") | "## referee-scope on `\(.sha[0:12])`, \(.created_at)\n\n\(.body)\n"' <<<"$c"
    } | head -c 400000 > "$ctx/reports.md"
    files="$files reports.md"
  fi
fi
# Entries of KNOWN.md kept outside the repository (CONTRIBUTING.md §2): the owner's private file
# $INCOGNITA_PRIVATE_KNOWN/<Roadmap>.md, if any, given to the sessions of that roadmap.
if [ -n "$roadmap" ] && [ -n "${INCOGNITA_PRIVATE_KNOWN:-}" ] && [ -f "$INCOGNITA_PRIVATE_KNOWN/$roadmap.md" ]; then
  head -c 400000 "$INCOGNITA_PRIVATE_KNOWN/$roadmap.md" > "$ctx/known-private.md" && files="$files known-private.md"
fi
# The owner's answers on the issue "Questions for the owner" (L13): the same questions are not
# asked again.
qn=$(ghr issue list --state open --limit 200 --author "$OWNER" --json number,title \
  --jq 'map(select(.title == "Questions for the owner")) | first | .number // empty' 2>/dev/null) || qn=""
if [ -n "$qn" ] && raw=$(ghr api --paginate "repos/$GH_REPO/issues/$qn/comments?per_page=100" 2>/dev/null); then
  owner_answers_md "$raw" | tail -c 200000 > "$ctx/owner-answers.md"
  if [ -s "$ctx/owner-answers.md" ]; then files="$files owner-answers.md"; else rm -f "$ctx/owner-answers.md"; fi
fi

situation=""
add_situation() { situation="$situation- $*
"; }
[ -n "${INCOGNITA_NOTE:-}" ] && add_situation "$INCOGNITA_NOTE"
case "$ci_state" in FAILURE|TIMED_OUT|STARTUP_FAILURE|ERROR) add_situation "The build failed on the head (check \"Build and check\" of the workflow CI, or \"Compile papers\" of the workflow Papers): see \`ci-log.txt\`." ;; esac
if [ -n "$H" ] && ! is_review_role "$role" && ! repo_git merge-base --is-ancestor "$M" "$H"; then
  add_situation "The branch is behind \`origin/main\`. If it conflicts, or for a Lean change, rebase it: \`git rebase origin/main\`."
fi
case ",$pr_labels," in *,incomplete,*) add_situation "This pull request is a draft labelled \`incomplete\`: an earlier session stopped before the end. Continue its work." ;; esac
if [ "$role" = revise ] && [ -n "$pr" ]; then
  if [ "$referee_round" = 1 ]; then
    add_situation "Revision round $(( rounds + 1 )) of $INCOGNITA_REVISION_ROUNDS: address the referees' latest reports (\`reports.md\`)."
  else
    add_situation "Repair of a paper pull request (failed build, conflict with \`main\`, or an incomplete draft), not a revision round: no referee asked for changes on this head."
  fi
fi
[ "$role" = fix-pr ] && [ -n "$pr" ] && add_situation "Fix round $(( fixes + 1 )); the pull request was opened by the role \`$pr_role\` (target \`$pr_target\`): keep its purpose, and its paths (AGENTS.md §2, line \`$eff_role\`)."
[ "$eff_role" = fix-main ] && [ -z "$pr" ] && add_situation "The build of \`main\` is red (see \`ci-log.txt\`): repair it with the smallest change; a new pull request \"fix main\" is opened."
if [ "$role" = revise ] && [ -z "$pr" ]; then
  cur_version=$(show_main "papers/$paper/META.toml" | sed -n -E 's/^version[[:space:]]*=[[:space:]]*([0-9]+).*/\1/p' | head -n 1)
  de=$(disputed_entries "$paper" | tr '\n' ' ')
  [ -n "$de" ] && add_situation "The paper \`$paper\` is disputed: write its next version for the errata entries $de(\`papers/$paper/errata.md\`), on a new pull request: \`version = $(( ${cur_version:-1} + 1 ))\` in META.toml."
  dc=$(certify_py depchecks 2>/dev/null | awk -v p="$paper" '$1 == p { printf "%s ", $2 }')
  [ -n "$dc" ] && add_situation "Dependency check (AGENTS.md section 5.6): library papers this paper depends on have a new version since it cited them: $dc. For each, compare the nodes this paper uses (\`depends_on\` in META.toml) with the new version. Not affected: add a line to \`papers/$paper/dependency-checks.md\` and update \`depends_on\` to the new version (paper.tex unchanged, same version). Affected: add an entry \`E<k>\` to \`papers/$paper/errata.md\` and write the next version (\`version = $(( ${cur_version:-1} + 1 ))\`), with the line \`Revised in …\` under it."
fi
if [ "$role" = write-paper ] || [ "$role" = revise ]; then
  add_situation "Before compiling, \`python3 scripts/certify.py bib\` writes \`papers/library.bib\` (generated, never committed: the keys \`INC-P<nnn>\` of the library); before the last commit, \`python3 scripts/certify.py check\`$( [ "$role" = revise ] && echo " --base origin/main")."
fi
if [ "$role" = write-paper ]; then
  add_situation "A new paper has \`version = 1\` and lists in \`depends_on\` the results of library papers it uses (each cited as \`\\cite[...]{INC-P<nnn>}\`)."
fi
if [ "$role" = bibliographer ] && [ -n "$paper" ]; then
  add_situation "The paper \`$paper\` waits for you: its source notes (an external paper), or its attribution audit (a verified internal paper)$( in_list reports.md "$files" && echo "; the scope referees' reports on it are in \`reports.md\` (read them only at step 3.4)")."
fi
if [ "$role" = formalize-statements ] && [ -n "$paper" ]; then
  fe=$(freeze_entries "$paper" | tr '\n' ' ')
  if [ -n "$fe" ]; then
    add_situation "Entries to resolve: $fe(\`papers/$paper/errata.md\` revised in a new version, or \`statement-corrections.md\`): freeze the corrected statements under new names and add the \`Resolved by\` lines (AGENTS.md §6.6)."
  elif [ -n "$(locks_of "$paper")" ]; then
    add_situation "The paper already has frozen statements: freeze only what is missing."
  fi
fi
if [ "$role" = prove ] || [ "$role" = formalize-statements ]; then
  st=$(audit_status 2>/dev/null | awk -v n="$(paper_num "$paper")" "$AWK_NUM"' num($1) == n + 0')
  [ -n "$st" ] && add_situation "Frozen statements of this paper (\`lake exe audit --status\` on main):
$(printf '%s\n' "$st" | sed 's/^/  - /')"
fi
in_list owner-answers.md "$files" && add_situation "The owner's answers to earlier questions are in \`owner-answers.md\`: never ask again what is answered there."
[ -n "$situation" ] || situation="- Nothing special.
"
if is_review_role "$role"; then
  case "$role" in
    referee-*) vlist='accept|major|reject' ;;
    *) vlist='approve|request_changes|reject' ;;
  esac
  vrule=""
  case "$role" in referee-*) vrule="
- The verdict is computed from your defect table: \`reject\` if any F, \`major\` if any G or L, otherwise \`accept\` (P defects only). The script reads \`minor\` as \`major\`." ;; esac
  scratch=""
  [ "$role" = referee-proofs ] && scratch=" (numerical experiments only in \`.agents/scratch/\`, never collected)"
  contract="- You change no file of the repository and make no commit$scratch: your final answer is your report.
- Its first line is exactly \`Verdict: <$vlist>\`; the script reads the first line that starts with \`Verdict: \`.$vrule
- The script posts the report on pull request #$pr as a comment and sets the commit status of the head \`${H:0:12}\` from the verdict.
- A question only the owner can answer goes on its own line, starting with \`Ask-owner: \`; the script forwards it."
else
  contract="- Commit your work on the current branch (\`incognita-task\`). You cannot push: the script pushes.
- The script pushes your commits as ONE commit (their sum): what a commit adds and a later one removes is never published.
- Then write \`.agents/summary.md\` (not committed): it becomes $( [ -n "$pr" ] && echo "the comment of this round on the pull request" || echo "the description of the new pull request" ).
- The script refuses the whole result if a commit changes a path your role may not change (see AGENTS.md;
  human-owned paths, dot-files, \`CLAUDE.md\`/\`AGENTS.md\`, symbolic links, files over 1 MB, a frozen
  statement that is not an addition, generated files such as \`papers/library.bib\`), and keeps nothing that is not committed."
fi
# The session ends at task_end: the role's timeout from now, and never later than 2 minutes before
# the deadline; the preparation below eats into it, so that task.md stays true.
task_end=$(( $(now) + timeout_s ))
[ "$DEADLINE" != 0 ] && [ "$task_end" -gt $(( DEADLINE - 120 )) ] && task_end=$(( DEADLINE - 120 ))
end_local=$(date -d "@$task_end" '+%H:%M' 2>/dev/null || echo "?")
{
  echo "# Task (written by scripts/agent.sh)"
  echo
  echo "- Role: \`$role\`"
  echo "- Target: \`$target\`"
  [ -n "$pr" ] && echo "- Pull request: #$pr, head \`$H\` (branch \`$branch\`), opened by the role \`$pr_role\` for \`$pr_target\`"
  [ -n "$paper" ] && echo "- Paper: \`$paper\` (\`papers/$paper/\`, Lean prefix \`$(printf '%s' "$paper" | sed -E 's/^(P[0-9]+).*/\1/')\`)"
  [ -n "${paper_number:-}" ] && echo "- Paper: \`$paper_number\`, a new directory \`papers/$paper_number-<slug>/\` (choose the slug; Lean prefix \`$paper_number\`)"
  [ -n "$roadmap" ] && echo "- Roadmap: \`$roadmap\` (\`roadmaps/$roadmap/ROADMAP.md\`; KNOWN.md: \`roadmaps/$roadmap/KNOWN.md\`$( [ -f "$ctx/known-private.md" ] && echo ", and the private entries in \`.agents/known-private.md\`"))"
  echo "- Base of your branch: \`$base\`; \`origin/main\` is \`$M\`"
  echo "- Deadline for this task: $end_local (server time), about $(( (task_end - $(now)) / 60 )) minutes from the start; the session is stopped then."
  echo "- Model: \`$model\`, effort \`$effort\`, at most $turns turns"
  echo "- Context files in \`.agents/\`: $(for f in $files; do printf '`%s` ' "$f"; done)"
  echo
  echo "## Situation"
  printf '%s' "$situation"
  echo
  echo "## Output (enforced by the script)"
  echo "$contract"
} > "$ctx/task.md"

# ---------------------------------------------------------------- prompt
prompt=$in/prompt.md
if ! repo_git show "$M:agents/roles/$role.md" > "$tmp/role.md" 2>/dev/null; then
  if is_dry; then log "dry run: no agents/roles/$role.md on main (the session would fail)"; echo "(missing)" > "$tmp/role.md"
  else finish fail "no-prompt agents/roles/$role.md"; fi
fi
# The role file verbatim (no substitution: everything specific to the task is in task.md).
{ cat "$tmp/role.md"
  printf '\n\n---\nThe script wrote `.agents/task.md` for this task: read it first. It overrides nothing above;\nit gives the target, the deadline, the context files, and what the script does with your output.\n'
} > "$prompt"

claude_args=(-p --output-format json --model "$model" --effort "$effort" --max-turns "$turns"
  --permission-mode acceptEdits --allowedTools "$tools")
if is_dry; then
  log "dry run: $role $target (model $model, effort $effort, $timeout_s s, base ${base:0:12})"
  log "dry run: tools: $tools"
  echo "----- .agents/task.md"; cat "$ctx/task.md"
  echo "----- context files:"; ls -la "$ctx"
  run_sandboxed "incognita-$task" "$timeout_s" yes - -- "$AGENT_CLAUDE" "${claude_args[@]}"
  exit 0
fi

# ---------------------------------------------------------------- inputs: bundle + agent-side script
ref_main=refs/incognita/bundle/$task-main ref_head=refs/incognita/bundle/$task-head
repo_git update-ref "$ref_main" "$M" || die "update-ref failed"
repo_git update-ref "$ref_head" "${H:-$M}" || die "update-ref failed"
repo_git bundle create -q "$in/in.bundle" "$ref_main" "$ref_head" || die "git bundle create failed"
cp "$INCOGNITA_SCRIPTS/agent-side.sh" "$in/agent-side.sh" || die "cannot copy agent-side.sh"
chmod -R a+rX,go-w "$in"
# The agent's ~/work: no process of the agent left, .lake from the loop's (trusted) one, then a new
# repository from the bundle (agent-side.sh prepare); nothing of an earlier session survives. A
# failed preparation repairs the agent's home once; if it still fails, the night stops (exit 7).
rc=0; prepare_agent_work "$in" "$base" "$ref_main" "$ref_head" "$tmp/prep.log" || rc=$?
case "$rc" in
  0) ;;
  5) die "a process of $INCOGNITA_AGENT_USER still runs: no preparation" ;;
  *) log "the agent's ~/work could not be prepared, even after a repair:"; tail -n 20 "$tmp/prep.log" >&2
     record_attempt "$role" "$target" skip agent-work-broken
     exit 7 ;;
esac
# What is left of the announced time (task.md), after the preparation.
timeout_s=$(( task_end - $(now) ))
if [ "$timeout_s" -lt 300 ]; then
  log "less than 5 minutes left after the preparation: no session"
  exit 5
fi

# ---------------------------------------------------------------- the session
set_activity "$role $target (claude, until $end_local)"
log "== session: $role $target, model $model, ${timeout_s}s${pr:+, PR #$pr head ${H:0:12}}"
t0=$(now)
# In the background, then `wait`: a TERM (night.sh stopping) runs our trap at once, which stops the
# unit (stop_sandbox), instead of waiting for the end of the session. Both outputs are capped (and
# drained beyond the cap, so that the session never gets a broken pipe).
SANDBOX_UNIT="incognita-$task"
{ run_sandboxed "incognita-$task" "$timeout_s" yes - -- "$AGENT_CLAUDE" "${claude_args[@]}" \
    < "$prompt" 2> >(head -c 2000000 > "$tmp/session.err"; cat > /dev/null; : > "$tmp/err.done")
  echo $? > "$tmp/rc"
} | { head -c 8000000 > "$tmp/result.json"; cat > /dev/null; } &
wait $!
SANDBOX_UNIT=""
for _ in $(seq 1 20); do [ -e "$tmp/err.done" ] && break; sleep 0.5; done
rc=$(cat "$tmp/rc" 2>/dev/null || echo 1)
elapsed=$(( $(now) - t0 ))
counter_inc tasks-total >/dev/null

if jq -e 'type == "object"' "$tmp/result.json" >/dev/null 2>&1; then
  is_error=$(jq -r '.is_error // false' "$tmp/result.json")
  subtype=$(jq -r '.subtype // "unknown"' "$tmp/result.json")
  jq -r '.result // ""' "$tmp/result.json" > "$tmp/result.txt"
  session_info="(turns $(jq -r '.num_turns // "?"' "$tmp/result.json"), ${elapsed}s, \$$(jq -r '.total_cost_usd // "?"' "$tmp/result.json"))"
else
  is_error=true subtype=no-json
  [ "$elapsed" -ge $(( timeout_s - 30 )) ] && subtype=timeout
  : > "$tmp/result.txt"
  session_info="(exit $rc, ${elapsed}s)"
fi
log "session ended: is_error=$is_error subtype=$subtype $session_info"
errtext=$( { head -c 4000 "$tmp/result.txt"; tail -c 4000 "$tmp/session.err"; } 2>/dev/null)

if [ "$is_error" = true ]; then
  if printf '%s' "$errtext" | grep -qiE 'invalid api key|not logged in|please run /login|oauth token (has )?expired|authentication_error|401 unauthorized|invalid bearer token|credit balance'; then
    record_event stop "$role" "$target" "claude logged out"
    log "Claude is logged out (or the token in $INCOGNITA_AGENT_ENV is invalid)"
    record_attempt "$role" "$target" skip logged-out
    exit 3
  fi
  if printf '%s' "$errtext" | grep -qiE 'usage limit|rate.?limit|limit reached|hit your limit|too many requests|\b429\b|overloaded|\b529\b'; then
    reset=$(printf '%s' "$errtext" | grep -oE '\|[0-9]{10}' | head -n 1 | tr -d '|')
    printf '%s' "$errtext" | grep -qiE 'overloaded|\b529\b' && [ -z "$reset" ] && reset=$(( $(now) + 600 ))
    if [ -z "$reset" ]; then
      when=$(printf '%s' "$errtext" | grep -oiE 'resets? (at )?[0-9]{1,2}(:[0-9]{2})? ?(am|pm)?' | head -n 1 | sed -E 's/^[Rr]esets? (at )?//')
      [ -n "$when" ] && reset=$(date -d "$when" +%s 2>/dev/null)
      [ -n "$reset" ] && [ "$reset" -le "$(now)" ] && reset=$(( reset + 86400 ))
    fi
    [ -n "$reset" ] || reset=$(( $(now) + 1800 ))
    printf '%s\n' "$reset" > "$INCOGNITA_STATE/rate-limit-until"
    record_event quota "$role" "$target" "rate limited until $(date -d "@$reset" '+%H:%M')"
    record_attempt "$role" "$target" skip rate-limited
    log "rate limited until $(date -d "@$reset" '+%F %T')"
    exit 4
  fi
fi

# forward_questions <file> <origin> <sha>: the lines "Ask-owner: ..." of a report or summary go to the
# pinned issue "Questions for the owner" (AGENTS.md §1, §5.4).
forward_questions() {
  grep -qE '^(- )?Ask-owner:' "$1" 2>/dev/null || return 0
  local q
  q=$(pinned_issue "Questions for the owner") || return 1
  { printf 'From %s (`%s` on `%s`):\n\n' "$2" "$role" "${3:0:12}"
    grep -E '^(- )?Ask-owner:' "$1" | sed -E 's/^- //' | sanitize 20000; } > "$tmp/ask.md"
  post_comment "$q" ask-owner "$3" "$tmp/ask.md" >/dev/null
  record_event ask-owner "$role" "$target" "$(grep -E '^(- )?Ask-owner:' "$1" | head -n 3 | one_line 400)"
}

footer() {  # the line under every comment
  printf '\n---\n:robot: `%s` (role `%s`, head `%s`, scripts/agent.sh)%s\n' "$model" "$role" "${1:0:12}" "${2:-}"
}

# ---------------------------------------------------------------- reviewers: verdict, comment, statuses
if is_review_role "$role"; then
  report=$tmp/result.txt
  verdict=$(grep -m1 -E '^Verdict: ' "$report" | sed -E 's/^Verdict: *`?([a-z_]+).*/\1/')
  case "$role:$verdict" in
    referee-*:accept|referee-*:major|referee-*:reject) ;;
    referee-*:minor) verdict=major ;;   # reject if any F, major if any G or L, accept if P only
    review-*:approve|review-*:request_changes|review-*:reject) ;;
    *)
      n=$(counter_inc "review-fail $pr")
      log "no valid verdict (\"$verdict\"; $subtype); $n reviews of #$pr without a verdict"
      [ "$n" -ge "$INCOGNITA_REVIEW_FAIL_LIMIT" ] && escalate "$pr" "$n reviews without a verdict"
      finish fail "no-verdict ($subtype)" ;;
  esac
  sanitize 60000 < "$report" > "$tmp/body.md"
  footer "$H" >> "$tmp/body.md"
  url=$(post_comment "$pr" "$role" "$H" "$tmp/body.md") || finish fail "comment-failed"
  desc="role=$role verdict=$verdict pr=$pr"
  case "$role" in
    review-pr|review-statements|review-roadmap)
      if [ "$verdict" = approve ]; then st=success; else st=failure; fi
      set_status "$H" "Incognita review" "$st" "$desc" ;;
    referee-scope)
      if [ "$verdict" = accept ]; then st=success; else st=failure; fi
      set_status "$H" "Referee scope" "$st" "$desc"
      if [ "$verdict" = accept ]; then
        set_status "$H" "Incognita review" pending "role=referees verdict=pending pr=$pr (referee-proofs next)"
      else
        set_status "$H" "Incognita review" failure "role=referees verdict=$verdict pr=$pr"
      fi ;;
    referee-proofs)
      if [ "$verdict" = accept ]; then st=success; else st=failure; fi
      set_status "$H" "Referee proofs" "$st" "$desc"
      sts=$(statuses_of "$H") || sts=""
      if [ "$verdict" = accept ] && [ "$(verdict_in "$sts" "Referee scope" referee-scope)" = accept ]; then
        set_status "$H" "Incognita review" success "role=referees verdict=accept pr=$pr"
      else
        set_status "$H" "Incognita review" failure "role=referees verdict=$verdict pr=$pr"
      fi ;;
  esac
  counter_set "review-fail $pr" 0
  # Questions for the owner.
  forward_questions "$report" "#$pr" "$H"
  # Papers: a rejection, or a G after the last revision round, closes the PR (D2).
  if [ "$kind" = paper ]; then
    why=""
    [ "$verdict" = reject ] && why="$role: reject"
    [ "$verdict" = major ] && [ "$rounds" -ge "$INCOGNITA_REVISION_ROUNDS" ] && why="$role: major after $rounds revision rounds"
    [ -n "$why" ] && close_rejected "$pr" "$H" "$why" "$(printf '%s' "$pr_title" | one_line 120)"
  elif [ "$verdict" = reject ] && [ "$kind" = roadmap ]; then
    close_rejected "$pr" "$H" "$role: reject" "$(printf '%s' "$pr_title" | one_line 120)"
  elif [ "$verdict" = reject ]; then
    escalate "$pr" "$role: reject"
  fi
  finish ok "verdict $verdict $url"
fi

# ---------------------------------------------------------------- writers: collect, check, push
sudo -n install -d -o "$INCOGNITA_AGENT_USER" -g "$(id -gn)" -m 750 "$out" || finish fail "no-output-dir"
if ! run_sandboxed "incognita-$task-collect" 900 no "$out" -- bash "$in/agent-side.sh" collect "$out" "$M" "${H:--}" \
    </dev/null >"$tmp/collect.log" 2>&1; then
  log "the collection failed:"; tail -n 20 "$tmp/collect.log" >&2
  finish fail "collect-failed ($subtype)"
fi
# Every output is read as the agent user, regular files only (out_read): never opened by the loop.
# The collection writes regular files only: anything else there is an attack, and nothing is kept.
odd=$(out_irregular "$out")
if [ -n "$odd" ]; then
  log "refused: entries that are not regular files in $out: $(printf '%s' "$odd" | tr '\n' ' ')"
  record_event refused "$role" "$target" "non-regular entries in the output directory"
  finish fail "non-regular-output"
fi
count=$(out_read "$out/count" 20 | tr -dc 0-9)
newhead=$(out_read "$out/head" 41 | tr -dc 0-9a-f)
untracked=$(out_read "$out/untracked" 4000 | head -n 20 | tr '\n' ' ')
[ -n "$untracked" ] && log "untracked files left by the session (dropped): $(printf '%s' "$untracked" | one_line 300)"
summary=$tmp/summary.md
out_read "$out/summary.md" 200000 | sanitize 60000 > "$summary"
[ -s "$summary" ] || echo "(The agent wrote no summary.)" > "$summary"
# Questions of a writing session, whatever its outcome (a writer may stop without a commit to ask).
forward_questions "$summary" "$( [ -n "$pr" ] && echo "#$pr" || echo "the task $task ($role $target)" )" "${H:-$M}"

failed_session=false
[ "$is_error" = true ] || [ "$subtype" != success ] && failed_session=true

# Comment kind of this round on a PR: `revise` (a revision round, counted by the loop), `revise-fix`
# (a repair of a paper PR) or `fix-pr`; `<kind>-nochange` when nothing was pushed.
ckind=$role
[ "$role" = revise ] && [ "$referee_round" != 1 ] && ckind=revise-fix
is_fix_round() { [ "$ckind" = fix-pr ] || [ "$ckind" = revise-fix ]; }

if [ "${count:-0}" -eq 0 ] || ! [[ "$newhead" =~ ^[0-9a-f]{40}$ ]]; then
  # A writer that found no open item says so (line "No open item in <Roadmap>."): the roadmap is
  # exhausted until its items change, and the loop proposes an extension (AGENTS.md section 4).
  if [ "$role" = write-paper ] && [ -n "$roadmap" ] && grep -qE '^(- )?No open item' "$summary" \
      && h=$(certify_py items-hash "$roadmap" 2>/dev/null); then
    mark_set "exhausted $roadmap $h"
    record_event exhausted "$role" "$roadmap" "no open item"
  fi
  if [ -n "$pr" ]; then
    { printf '%s round: no change (%s).\n\n' "$( [ "$ckind" = revise ] && echo Revision || echo Fix )" "$subtype"; cat "$summary"; footer "$H"; } > "$tmp/body.md"
    post_comment "$pr" "$ckind-nochange" "$H" "$tmp/body.md" >/dev/null
    is_fix_round && counter_inc "fix-rounds $pr" >/dev/null
  fi
  # A session that ended normally without a commit is not a failure of its target (never parked).
  [ "$failed_session" = true ] && finish fail "no-commit ($subtype)"
  finish skip no-commit "($subtype)"
fi

out_copy "$out/out.bundle" "$INCOGNITA_BUNDLE_MAX" "$tmp/out.bundle" || finish fail "bundle-unreadable-or-too-large"
repo_git -c transfer.fsckObjects=true -c fetch.fsckObjects=true fetch -q --no-tags "$tmp/out.bundle" \
  "+refs/incognita/out:refs/incognita/tasks/$task" || finish fail "bundle-fetch-failed"
new=$(repo_git rev-parse "refs/incognita/tasks/$task") || finish fail "bundle-without-ref"
[ "$new" = "$newhead" ] || finish fail "bundle-head-mismatch"
nb=$(repo_git rev-list --count "$new" "^$M" ${H:+"^$H"})
[ "$nb" -le 300 ] || finish fail "too-many-commits ($nb)"
cbase=$(repo_git merge-base "$M" "$new") || finish fail "no-merge-base"
paths_ok() {
  check_paths "$eff_role" "$paper" "$cbase" "$new" || return 1
  # write-paper: the new directory has the number given in task.md.
  if [ -n "${paper_number:-}" ]; then
    local d
    d=$(repo_git diff --name-only --no-renames "$cbase" "$new" -- papers | sed -n -E 's#^papers/([^/]+)/.*#\1#p' | sort -u)
    case "$d" in "$paper_number"-*) ;; *) log "refused: the paper directory must be papers/$paper_number-<slug>/, not papers/$d/"; return 1 ;; esac
  fi
  return 0
}
if ! paths_ok 2> "$tmp/paths.log"; then
  cat "$tmp/paths.log" >&2
  record_event refused "$role" "$target" "$(one_line 400 < "$tmp/paths.log")"
  repo_git update-ref "refs/incognita/refused/$task" "$new"   # kept for inspection (never pushed)
  if [ -n "$pr" ]; then
    { echo "The script refused this session's commits (not pushed):"; echo; sed 's/^/    /' "$tmp/paths.log" | sanitize 10000; footer "$H"; } > "$tmp/body.md"
    post_comment "$pr" "$ckind-nochange" "$H" "$tmp/body.md" >/dev/null
    is_fix_round && counter_inc "fix-rounds $pr" >/dev/null
  fi
  finish fail "refused-paths (kept as refs/incognita/refused/$task)"
fi

# One commit per round (S3): the checked sum of the session's commits, on top of the PR head (or,
# when the round rebased the branch, of its base), so that no intermediate commit is published.
sq_parent=$(squash_parent "$M" "$new" "$H") || finish fail "no-squash-parent"
{ repo_git log -1 --format=%s "$new"
  echo
  echo "One commit for the session's commits (scripts/agent.sh):"
  repo_git log --reverse --format='- %s' "$sq_parent..$new" | head -n 100
} | sanitize 20000 > "$tmp/squash-msg"
# The author is the bot identity (squash_onto); the session in trailers.
printf '\nIncognita-Model: %s\nIncognita-Agent-Role: %s\n' "$model" "$role" >> "$tmp/squash-msg"
sq=$(squash_onto "$sq_parent" "$new" "$tmp/squash-msg") || finish fail "squash-failed"
[ "$(repo_git rev-parse "$sq^{tree}")" = "$(repo_git rev-parse "$new^{tree}")" ] || finish fail "squash-tree-mismatch"

if [ -n "$pr" ]; then
  # fix-pr / revise: push to the PR branch, only if it is still at H.
  if ! repo_git push -q --force-with-lease="refs/heads/$branch:$H" origin "$sq:refs/heads/$branch"; then
    finish fail "push-rejected (the branch moved)"
  fi
  if [ "$ckind" = revise ]; then
    title="Revision round $(( rounds + 1 )) of $INCOGNITA_REVISION_ROUNDS: pushed \`${sq:0:12}\`."
  else
    title="Fix round: pushed \`${sq:0:12}\`."
    counter_inc "fix-rounds $pr" >/dev/null
  fi
  [ "$failed_session" = true ] && title="$title The session stopped before the end ($subtype): the pull request is marked \`incomplete\`."
  { printf '%s\n\n' "$title"; cat "$summary"; footer "$sq"; } > "$tmp/body.md"
  post_comment "$pr" "$ckind" "$sq" "$tmp/body.md" >/dev/null
  if [ "$failed_session" = true ]; then
    ensure_labels
    gh pr edit "$pr" --add-label incomplete >/dev/null 2>&1
    [ "$pr_draft" = true ] || gh pr ready "$pr" --undo >/dev/null 2>&1
    finish fail "pushed-incomplete #$pr ($subtype)"
  fi
  case ",$pr_labels," in
    *,incomplete,*) gh pr edit "$pr" --remove-label incomplete >/dev/null 2>&1; gh pr ready "$pr" >/dev/null 2>&1 ;;
  esac
  finish ok "pushed #$pr ${sq:0:12}"
fi

# A new pull request.
if [ "$eff_role" = fix-main ]; then bname="agent/fix-main-$stamp"; else bname="agent/$role-$stamp"; fi
repo_git push -q origin "$sq:refs/heads/$bname" || finish fail "push-failed"
title=$(repo_git log -1 --format=%s "$new" | one_line 120)
[ -n "$title" ] || title="$role $target"
{ printf 'Role: `%s`. Target: `%s`. Model: `%s`.\n\n' "$role" "$target" "$model"
  if [ "$failed_session" = true ]; then
    printf '> **Incomplete**: the session stopped before the end (`%s`). Its work is kept in this draft; an agent continues it.\n\n' "$subtype"
  fi
  cat "$summary"
  printf '\n\nOpened by `scripts/agent.sh` (see agents/README.md).\n\n🤖 Generated with [Claude Code](https://claude.com/claude-code)\n'
} > "$tmp/prbody.md"
draft=()
[ "$failed_session" = true ] && { ensure_labels; draft=(--draft --label incomplete); }
# Not retried blindly: a creation that timed out may have worked (then the PR of the branch is used).
create_pr() {
  local i url
  for i in 1 2 3; do
    url=$(gh pr create --base main --head "$bname" --title "$title" --body-file "$tmp/prbody.md" "${draft[@]}") \
      && { printf '%s\n' "$url"; return 0; }
    sleep $(( i * 5 ))
    url=$(gh pr list --state open --head "$bname" --json url --jq '.[0].url // empty' 2>/dev/null) \
      && [ -n "$url" ] && { printf '%s\n' "$url"; return 0; }
  done
  return 1
}
url=$(create_pr) || finish fail "pr-create-failed (branch $bname pushed)"
n=${url##*/}
if [ "$failed_session" = true ]; then finish ok "draft #$n ($subtype)"; fi
finish ok "pr #$n"
