#!/usr/bin/env bash
# Run one agent task: one `claude -p` session as the isolated user incognita-agent. See
# agents/README.md ("How a task runs").
#
# Usage: scripts/agent.sh <role> [target]
#   write-paper <Roadmap>          formalize-statements <Paper>     prove <Paper>
#   referee-scope <PR>             referee-proofs <PR>              review-statements <PR>
#   review-pr <PR>                 revise <PR> | revise <Paper>     fix-pr <PR> | fix-pr main
#   bibliographer                  garden
#
# Run by the user `lean` in its clone of main (never edited by hand), normally from scripts/loop.sh.
# The loop never runs git or lake inside the agent's clone: inputs go in as a git bundle, outputs
# come back as a git bundle written by the agent user, then are checked here (path whitelist) and
# pushed with the loop's own GitHub token.
#
# Environment from the loop: INCOGNITA_HEAD (the PR head the task was chosen for), INCOGNITA_TASK_TIMEOUT
# (seconds), INCOGNITA_NOTE (extra situation line for task.md), and the variables of scripts/lib.sh.
# Exit: 0 task done (whatever the outcome; recorded in the state), 1 error, 2 usage,
# 3 Claude is logged out (stop the night), 4 rate limited (reset time in state/rate-limit-until).
set -u -o pipefail
umask 022
# shellcheck source=scripts/lib.sh
. "$(dirname "${BASH_SOURCE[0]}")/lib.sh"

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
  referee-proofs) tools="$read_tools,$exec_tools" ;;
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
    case "$role" in
      referee-scope|referee-proofs|revise) [ "$kind" = paper ] || finish skip "not-a-paper-pr" ;;
      review-statements) [ "$kind" = statements ] || finish skip "not-a-statements-pr" ;;
      review-pr) [ "$kind" = generic ] || finish skip "not-a-generic-pr" ;;
    esac
    paper=$(paper_of_ref "$H" | head -n 1)
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
  formalize-statements:*|prove:*)
    [[ "$target" =~ ^[A-Za-z0-9_-]+$ ]] || { echo "$role needs a paper" >&2; exit 2; }
    paper=$(paper_of_num "$(paper_num "$target")") || paper=$target ;;
esac
[ -z "$roadmap" ] && [ -n "$paper" ] && roadmap=$(meta_get "$paper" roadmap)
if [ -z "$roadmap" ] && [ -n "$paper" ] && [ -n "$H" ]; then
  roadmap=$(repo_git show "$H:papers/$paper/META.toml" 2>/dev/null \
    | sed -n -E 's/^roadmap[[:space:]]*=[[:space:]]*"([^"]*)".*/\1/p' | head -n 1)
fi

# ---------------------------------------------------------------- context files (.agents/)
ctx=$in/agents
if ! is_dry; then
  mkdir -p "$in" || die "cannot create $in (run scripts/server/setup-agent-user.sh)"
fi
mkdir -p "$ctx"
open_prs_md "$prs_json" > "$ctx/open-prs.md"
files="task.md open-prs.md"

meta_lines_at() {  # ref roadmap: "paper<TAB>directions" of the papers of a roadmap at ref
  local ref=$1 r=$2 p m
  for p in $(repo_git ls-tree --name-only "$ref:papers" 2>/dev/null | grep -E '^P[0-9]+-'); do
    m=$(repo_git show "$ref:papers/$p/META.toml" 2>/dev/null) || continue
    printf '%s\n' "$m" | grep -Eq "^roadmap[[:space:]]*=[[:space:]]*\"$r\"" || continue
    printf '%s\t%s\n' "$p" "$(printf '%s\n' "$m" | sed -n -E 's/^directions[[:space:]]*=[[:space:]]*(.*)/\1/p' | head -n 1)"
  done
}

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
    # A referee re-checks what changed since its last report (D2).
    if is_review_role "$role"; then
      prev=$(jq -r --arg k "$role" --arg h "$H" '[.[] | select(.kind == $k and .sha != $h)] | last | .sha // empty' <<<"$comments")
      if [ -n "$prev" ] && { repo_git cat-file -e "$prev^{commit}" 2>/dev/null || repo_git fetch -q origin "$prev" 2>/dev/null; }; then
        repo_git diff --no-renames "$prev" "$H" | head -c 2000000 > "$ctx/revision.diff"
        files="$files revision.diff"
      fi
    fi
  else
    die "cannot read the comments of #$pr"
  fi
  rounds=$(jq '[.[] | select(.kind == "revise")] | length' <<<"$comments")
  fixes=$(jq '[.[] | select(.kind == "fix-pr" or .kind == "fix-pr-nochange")] | length' <<<"$comments")
fi
ci_state=""
if [ -n "$H" ]; then
  ci_state=$(jq -r --argjson n "$pr" '.[] | select(.number == $n)
    | ([.statusCheckRollup[]? | select(.name == "Build and check")] | last) as $c
    | if $c == null then "NONE" elif ($c.conclusion // "") != "" then $c.conclusion else $c.status end' "$prs_json")
  case "$ci_state" in
    FAILURE|TIMED_OUT|STARTUP_FAILURE|ERROR)
      ci_failed_log "$H" | tail -c 150000 > "$ctx/ci-log.txt" && files="$files ci-log.txt" ;;
  esac
elif [ "$eff_role" = fix-main ]; then
  ci_failed_log "$M" | tail -c 150000 > "$ctx/ci-log.txt" && files="$files ci-log.txt"
fi
if [ "$role" = write-paper ]; then
  { echo "# Papers of the roadmap $roadmap and the directions they serve"
    echo
    echo "## On main"
    meta_lines_at origin/main "$roadmap" | awk -F'\t' '{print "- " $1 ": " $2}'
    echo
    echo "## In open pull requests"
    jq -r '.[] | select(.isCrossRepository == false) | "\(.number) \(.headRefOid)"' "$prs_json" \
      | while read -r n h; do
          fetch_pr_head "$n" "$h" 2>/dev/null || continue
          meta_lines_at "refs/incognita/pr/$n" "$roadmap" | awk -F'\t' -v n="$n" '{print "- #" n " " $1 ": " $2}'
        done
    echo
    echo "## Rejected (closed with the label rejected): these directions count as covered"
    ghr pr list --state closed --label rejected --limit 200 --json number,headRefOid,title \
      --jq '.[] | "\(.number) \(.headRefOid)"' 2>/dev/null | while read -r n h; do
        repo_git cat-file -e "$h^{commit}" 2>/dev/null || repo_git fetch -q origin "+refs/pull/$n/head:refs/incognita/pr/$n" 2>/dev/null || continue
        meta_lines_at "$h" "$roadmap" | awk -F'\t' -v n="$n" '{print "- #" n " " $1 ": " $2}'
      done
  } > "$ctx/papers.md" 2>/dev/null
  files="$files papers.md"
fi

situation=""
add_situation() { situation="$situation- $*
"; }
[ -n "${INCOGNITA_NOTE:-}" ] && add_situation "$INCOGNITA_NOTE"
case "$ci_state" in FAILURE|TIMED_OUT|STARTUP_FAILURE|ERROR) add_situation "The build (CI \"Build and check\") failed on the head: see \`ci-log.txt\`." ;; esac
if [ -n "$H" ] && ! repo_git merge-base --is-ancestor "$M" "$H"; then
  add_situation "The branch is behind \`origin/main\`. If it conflicts, or for a Lean change, rebase it: \`git rebase origin/main\`."
fi
case ",$pr_labels," in *,incomplete,*) add_situation "This pull request is a draft labelled \`incomplete\`: an earlier session stopped before the end. Continue its work." ;; esac
[ "$role" = revise ] && [ -n "$pr" ] && add_situation "Revision round $(( rounds + 1 )) of $INCOGNITA_REVISION_ROUNDS: address the referees' latest reports (\`reports.md\`)."
[ "$role" = fix-pr ] && [ -n "$pr" ] && add_situation "Fix round $(( fixes + 1 )); the pull request was opened by the role \`$pr_role\` (target \`$pr_target\`): keep its purpose."
[ "$eff_role" = fix-main ] && [ -z "$pr" ] && add_situation "The build of \`main\` is red (see \`ci-log.txt\`): repair it with the smallest change; a new pull request \"fix main\" is opened."
[ "$role" = revise ] && [ -z "$pr" ] && add_situation "The paper \`$paper\` is disputed (see \`papers/$paper/errata.md\`): write its next version."
if [ "$role" = prove ] || [ "$role" = formalize-statements ]; then
  st=$(audit_status 2>/dev/null | awk -v n="$(paper_num "$paper")" '{ k = $1; sub(/^P0*/, "", k); sub(/[^0-9].*/, "", k); if (k == n) print }')
  [ -n "$st" ] && add_situation "Frozen statements of this paper (\`lake exe audit --status\` on main):
$(printf '%s\n' "$st" | sed 's/^/  - /')"
fi
[ -n "$situation" ] || situation="- Nothing special.
"
if is_review_role "$role"; then
  case "$role" in
    referee-*) vlist='accept|major|reject' ;;
    *) vlist='approve|request_changes|reject' ;;
  esac
  contract="- You change no file and make no commit: your final answer is your report.
- Its first line is exactly \`Verdict: <$vlist>\`; the script reads the first line that starts with \`Verdict: \`.
- The script posts the report on pull request #$pr as a comment and sets the commit status of the head \`${H:0:12}\` from the verdict.
- A question only the owner can answer goes on its own line, starting with \`Ask-owner: \`; the script forwards it."
else
  contract="- Commit your work on the current branch (\`incognita-task\`). You cannot push: the script pushes.
- Then write \`.agents/summary.md\` (not committed): it becomes the pull request's description${pr:+ comment}.
- The script refuses the whole result if a commit changes a path your role may not change (see AGENTS.md;
  human-owned paths, dot-files, \`CLAUDE.md\`/\`AGENTS.md\`, symbolic links, files over 1 MB, a frozen
  statement that is not an addition), and keeps nothing that is not committed."
fi
end_local=$(date -d "@$(( $(now) + timeout_s ))" '+%H:%M' 2>/dev/null || echo "?")
cat > "$ctx/task.md" <<EOF
# Task (written by scripts/agent.sh)

- Role: \`$role\`
- Target: \`$target\`
$( [ -n "$pr" ] && echo "- Pull request: #$pr, head \`$H\` (branch \`$branch\`), opened by the role \`$pr_role\` for \`$pr_target\`" )
$( [ -n "$paper" ] && echo "- Paper: \`$paper\` (\`papers/$paper/\`)" )
$( [ -n "$roadmap" ] && echo "- Roadmap: \`$roadmap\` (\`roadmaps/$roadmap/ROADMAP.md\`, \`roadmaps/$roadmap/KNOWN.md\`)" )
- Base of your branch: \`$base\`; \`origin/main\` is \`$M\`
- Deadline for this task: $end_local (server time), $(( timeout_s / 60 )) minutes from the start; the session is stopped then.
- Model: \`$model\`, effort \`$effort\`, at most $turns turns
- Context files in \`.agents/\`: $(for f in $files; do printf '`%s` ' "$f"; done)

## Situation
$situation
## Output (enforced by the script)
$contract
EOF
sed -i '/^$/N;/^\n$/D' "$ctx/task.md" 2>/dev/null || true

# ---------------------------------------------------------------- prompt
prompt=$in/prompt.md
if ! repo_git show "$M:agents/roles/$role.md" > "$tmp/role.md" 2>/dev/null; then
  finish fail "no-prompt agents/roles/$role.md"
fi
{ sed -e "s|{TARGET}|$target|g" "$tmp/role.md"
  printf '\n\n---\nThe script wrote `.agents/task.md` for this task: read it first. It overrides nothing above;\nit gives the target, the deadline, the context files, and what the script does with your output.\n'
} > "$prompt"

if is_dry; then
  log "dry run: $role $target (model $model, effort $effort, $timeout_s s, base ${base:0:12})"
  log "dry run: tools: $tools"
  echo "----- .agents/task.md"; cat "$ctx/task.md"
  echo "----- context files:"; ls -la "$ctx"
  run_sandboxed "incognita-$task" "$timeout_s" yes - -- \
    "$INCOGNITA_AGENT_HOME/.local/bin/claude" -p --output-format json --model "$model" --effort "$effort" \
    --max-turns "$turns" --permission-mode acceptEdits --allowedTools "$tools"
  exit 0
fi

# ---------------------------------------------------------------- inputs: bundle + agent-side script
ref_main=refs/incognita/bundle/$task-main ref_head=refs/incognita/bundle/$task-head
repo_git update-ref "$ref_main" "$M" || die "update-ref failed"
repo_git update-ref "$ref_head" "${H:-$M}" || die "update-ref failed"
repo_git bundle create -q "$in/in.bundle" "$ref_main" "$ref_head" || die "git bundle create failed"
cp "$INCOGNITA_SCRIPTS/agent-side.sh" "$in/agent-side.sh" || die "cannot copy agent-side.sh"
chmod -R a+rX,go-w "$in"

sync_agent_lake || log "warning: the agent's .lake could not be re-synced; the session may rebuild"

set_activity "prepare $role $target"
if ! run_sandboxed "incognita-$task-prep" 900 no - -- bash "$in/agent-side.sh" prepare "$in" "$base" "$GH_REPO" \
    "$ref_main" "$ref_head" </dev/null >"$tmp/prep.log" 2>&1; then
  log "the preparation failed:"; tail -n 20 "$tmp/prep.log" >&2
  finish fail "prepare-failed"
fi

# ---------------------------------------------------------------- the session
set_activity "$role $target (claude, until $end_local)"
log "== session: $role $target, model $model, ${timeout_s}s${pr:+, PR #$pr head ${H:0:12}}"
t0=$(now)
run_sandboxed "incognita-$task" "$timeout_s" yes - -- \
  "$INCOGNITA_AGENT_HOME/.local/bin/claude" -p --output-format json --model "$model" --effort "$effort" \
  --max-turns "$turns" --permission-mode acceptEdits --allowedTools "$tools" \
  < "$prompt" 2> "$tmp/session.err" | head -c 8000000 > "$tmp/result.json"
rc=${PIPESTATUS[0]}
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

footer() {  # the line under every comment
  printf '\n---\n:robot: `%s` (role `%s`, head `%s`, scripts/agent.sh)%s\n' "$model" "$role" "${1:0:12}" "${2:-}"
}

# ---------------------------------------------------------------- reviewers: verdict, comment, statuses
if is_review_role "$role"; then
  report=$tmp/result.txt
  verdict=$(grep -m1 -E '^Verdict: ' "$report" | sed -E 's/^Verdict: *`?([a-z_]+).*/\1/')
  case "$role:$verdict" in
    referee-*:accept|referee-*:major|referee-*:reject) ;;
    referee-*:minor) verdict=major ;;   # D2: L and P need no new round, but a "minor" verdict is a G
    review-*:approve|review-*:request_changes|review-*:reject) ;;
    *)
      n=$(counter_inc "review-fail $pr")
      log "no valid verdict (\"$verdict\"; $subtype); $n reviews of #$pr without a verdict"
      if [ "$n" -ge "$INCOGNITA_REVIEW_FAIL_LIMIT" ] && [ "$kind" != paper ]; then
        escalate "$pr" "$n reviews without a verdict"
      fi
      finish fail "no-verdict ($subtype)" ;;
  esac
  sanitize 60000 < "$report" > "$tmp/body.md"
  footer "$H" >> "$tmp/body.md"
  url=$(post_comment "$pr" "$role" "$H" "$tmp/body.md") || finish fail "comment-failed"
  desc="role=$role verdict=$verdict pr=$pr"
  case "$role" in
    review-pr|review-statements)
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
  if grep -qE '^Ask-owner:' "$report"; then
    if q=$(pinned_issue "Questions for the owner"); then
      { printf 'From #%s (`%s` on `%s`):\n\n' "$pr" "$role" "${H:0:12}"
        grep -E '^Ask-owner:' "$report" | sanitize 20000; } > "$tmp/ask.md"
      post_comment "$q" ask-owner "$H" "$tmp/ask.md" >/dev/null
      record_event ask-owner "$role" "$pr" "$(grep -E '^Ask-owner:' "$report" | head -n 3 | one_line 400)"
    fi
  fi
  # Papers: a rejection, or a G after the last revision round, closes the PR (D2).
  if [ "$kind" = paper ]; then
    why=""
    [ "$verdict" = reject ] && why="$role: reject"
    [ "$verdict" = major ] && [ "$rounds" -ge "$INCOGNITA_REVISION_ROUNDS" ] && why="$role: major after $rounds revision rounds"
    [ -n "$why" ] && close_rejected "$pr" "$H" "$why" "$(printf '%s' "$pr_title" | one_line 120)"
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
count=$(head -c 20 "$out/count" 2>/dev/null | tr -dc 0-9)
newhead=$(head -c 41 "$out/head" 2>/dev/null | tr -dc 0-9a-f)
[ -s "$out/uncommitted" ] && log "uncommitted changes left by the session (dropped): $(head -c 300 "$out/uncommitted" | tr '\n' ' ')"
summary=$tmp/summary.md
if [ -s "$out/summary.md" ]; then sanitize 60000 < "$out/summary.md" > "$summary"
else echo "(The agent wrote no summary.)" > "$summary"; fi

failed_session=false
[ "$is_error" = true ] || [ "$subtype" != success ] && failed_session=true

if [ "${count:-0}" -eq 0 ] || ! [[ "$newhead" =~ ^[0-9a-f]{40}$ ]]; then
  if [ -n "$pr" ]; then
    kindc=$role-nochange
    { printf '%s round: no change (%s).\n\n' "$( [ "$role" = revise ] && echo Revision || echo Fix )" "$subtype"; cat "$summary"; footer "$H"; } > "$tmp/body.md"
    post_comment "$pr" "$kindc" "$H" "$tmp/body.md" >/dev/null
    [ "$role" = fix-pr ] && counter_inc "fix-rounds $pr" >/dev/null
  fi
  finish fail "no-commit ($subtype)"
fi

repo_git -c transfer.fsckObjects=true -c fetch.fsckObjects=true fetch -q --no-tags "$out/out.bundle" \
  "+refs/incognita/out:refs/incognita/tasks/$task" || finish fail "bundle-fetch-failed"
new=$(repo_git rev-parse "refs/incognita/tasks/$task") || finish fail "bundle-without-ref"
[ "$new" = "$newhead" ] || finish fail "bundle-head-mismatch"
nb=$(repo_git rev-list --count "$new" "^$M" ${H:+"^$H"})
[ "$nb" -le 300 ] || finish fail "too-many-commits ($nb)"
cbase=$(repo_git merge-base "$M" "$new") || finish fail "no-merge-base"
if ! check_paths "$eff_role" "$paper" "$cbase" "$new" 2> "$tmp/paths.log"; then
  cat "$tmp/paths.log" >&2
  record_event refused "$role" "$target" "$(one_line 400 < "$tmp/paths.log")"
  repo_git update-ref "refs/incognita/refused/$task" "$new"   # kept for inspection
  if [ -n "$pr" ]; then
    { echo "The script refused this session's commits (not pushed):"; echo; sed 's/^/    /' "$tmp/paths.log" | sanitize 10000; footer "$H"; } > "$tmp/body.md"
    post_comment "$pr" "$role-nochange" "$H" "$tmp/body.md" >/dev/null
    [ "$role" = fix-pr ] && counter_inc "fix-rounds $pr" >/dev/null
  fi
  finish fail "refused-paths (kept as refs/incognita/refused/$task)"
fi

if [ -n "$pr" ]; then
  # fix-pr / revise: push to the PR branch, only if it is still at H.
  if ! repo_git push -q --force-with-lease="refs/heads/$branch:$H" origin "$new:refs/heads/$branch"; then
    finish fail "push-rejected (the branch moved)"
  fi
  if [ "$role" = revise ]; then
    title="Revision round $(( rounds + 1 )) of $INCOGNITA_REVISION_ROUNDS: pushed \`${new:0:12}\`."
    ckind=revise
  else
    title="Fix round: pushed \`${new:0:12}\`."
    ckind=fix-pr
    counter_inc "fix-rounds $pr" >/dev/null
  fi
  [ "$failed_session" = true ] && title="$title The session stopped before the end ($subtype): the pull request is marked \`incomplete\`."
  { printf '%s\n\n' "$title"; cat "$summary"; footer "$new"; } > "$tmp/body.md"
  post_comment "$pr" "$ckind" "$new" "$tmp/body.md" >/dev/null
  if [ "$failed_session" = true ]; then
    ensure_labels
    gh pr edit "$pr" --add-label incomplete >/dev/null 2>&1
    [ "$pr_draft" = true ] || gh pr ready "$pr" --undo >/dev/null 2>&1
    finish fail "pushed-incomplete #$pr ($subtype)"
  fi
  case ",$pr_labels," in
    *,incomplete,*) gh pr edit "$pr" --remove-label incomplete >/dev/null 2>&1; gh pr ready "$pr" >/dev/null 2>&1 ;;
  esac
  finish ok "pushed #$pr ${new:0:12}"
fi

# A new pull request.
if [ "$eff_role" = fix-main ]; then bname="agent/fix-main-$stamp"; else bname="agent/$role-$stamp"; fi
repo_git push -q origin "$new:refs/heads/$bname" || finish fail "push-failed"
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
url=$(ghr pr create --base main --head "$bname" --title "$title" --body-file "$tmp/prbody.md" "${draft[@]}") \
  || finish fail "pr-create-failed (branch $bname pushed)"
n=${url##*/}
if [ "$failed_session" = true ]; then finish ok "draft #$n ($subtype)"; fi
finish ok "pr #$n"
