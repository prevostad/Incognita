#!/usr/bin/env bash
# Shared functions of the Incognita loop: scripts/night.sh, scripts/loop.sh, scripts/agent.sh.
# Sourced, never executed. No `set -e`: callers check every call. See agents/README.md.
#
# Conventions: functions print their result on stdout and log on stderr; a failed `gh` call
# returns non-zero and means "unknown", never "empty".

# ---------------------------------------------------------------- configuration
INCOGNITA_SCRIPTS=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
: "${INCOGNITA_REPO:=$(git -C "$INCOGNITA_SCRIPTS" rev-parse --show-toplevel 2>/dev/null || dirname "$INCOGNITA_SCRIPTS")}"
: "${INCOGNITA_HOME:=$HOME/.incognita}"
INCOGNITA_STATE=$INCOGNITA_HOME/state
INCOGNITA_LOGS=$INCOGNITA_HOME/logs
: "${INCOGNITA_AGENT_USER:=incognita-agent}"
: "${INCOGNITA_AGENT_HOME:=/home/$INCOGNITA_AGENT_USER}"
: "${INCOGNITA_EXCHANGE:=/srv/incognita}"
: "${INCOGNITA_AGENT_ENV:=/etc/incognita/agent.env}"
: "${INCOGNITA_AGENT_MEMORY:=6G}"
: "${INCOGNITA_MODEL_AUTHOR:=opus}"
: "${INCOGNITA_MODEL_REVIEWER:=sonnet}"
: "${INCOGNITA_EFFORT:=high}"
: "${INCOGNITA_MAX_TURNS:=200}"
: "${INCOGNITA_TIMEOUT_REVIEW:=1800}"       # seconds; reviews and referees
: "${INCOGNITA_TIMEOUT_WRITE:=5400}"        # seconds; writing roles
: "${INCOGNITA_MIN_REVIEW:=900}"            # a task is started only with at least this much time...
: "${INCOGNITA_MIN_WRITE:=2400}"            # ...left before the deadline (seconds)
: "${INCOGNITA_AUTOMERGE=papers,literature,proofs,exploration,directions}"   # D15; add `statements` later
: "${INCOGNITA_PAPERS_IN_REVIEW:=3}"
: "${INCOGNITA_PAPERS_MAX:=6}"
: "${INCOGNITA_ACCEPTED_UNVERIFIED_MAX:=2}"
: "${INCOGNITA_MAX_FAILS:=2}"               # failed attempts per (role, target) per night
: "${INCOGNITA_FIX_LIMIT:=3}"               # fix rounds on a non-paper PR, then needs-human
: "${INCOGNITA_REVIEW_FAIL_LIMIT:=3}"       # reviews without a verdict on a PR, then needs-human
: "${INCOGNITA_REVISION_ROUNDS:=2}"         # revision rounds of a paper, then rejected
: "${INCOGNITA_PARK_AFTER:=4}"              # failed attempts on a target (all nights), then parked
: "${INCOGNITA_ROTATION_EVERY:=6}"          # every n Claude tasks, one garden or bibliographer task
: "${INCOGNITA_IDLE_SLEEP:=1200}"
: "${INCOGNITA_VETO_NIGHTS:=2}"             # nights of veto before a roadmap proposal is approved
: "${INCOGNITA_PROPOSE_EVERY:=7}"           # nights between two periodic roadmap proposals (0: never)
: "${INCOGNITA_ROADMAPS_WAITING_MAX:=2}"    # approved roadmaps whose KNOWN.md waits for the owner
: "${INCOGNITA_DRY_RUN:=0}"
: "${INCOGNITA_BOT_NAME:=Incognita agents}"
: "${INCOGNITA_BOT_EMAIL:=incognita-agents@users.noreply.github.com}"

if [ -z "${INCOGNITA_GH_REPO:-}" ]; then
  INCOGNITA_GH_REPO=$(git -C "$INCOGNITA_REPO" remote get-url origin 2>/dev/null \
    | sed -n -E 's#^(https://github\.com/|git@github\.com:)([^/]+/[^/.]+)(\.git)?/?$#\2#p')
  : "${INCOGNITA_GH_REPO:=prevostad/Incognita}"
fi
export GH_REPO=$INCOGNITA_GH_REPO
export GH_PROMPT_DISABLED=1 GH_NO_UPDATE_NOTIFIER=1

ROLES="write-paper referee-scope referee-proofs revise formalize-statements review-statements prove review-pr fix-pr bibliographer garden propose-roadmap review-roadmap"
REVIEW_ROLES="referee-scope referee-proofs review-statements review-pr review-roadmap"
ROOT_FILES="Incognita.lean Statements.lean Exploration.lean"

# ---------------------------------------------------------------- small helpers
log() { printf '%s %s\n' "$(date '+%F %T')" "$*" >&2; }
die() { log "fatal: $*"; exit 1; }
now() { date +%s; }
is_dry() { [ "$INCOGNITA_DRY_RUN" = 1 ]; }
in_list() { case " $2 " in *" $1 "*) return 0 ;; *) return 1 ;; esac; }
is_review_role() { in_list "$1" "$REVIEW_ROLES"; }
is_role() { in_list "$1" "$ROLES"; }
key_of() { printf '%s' "$*" | tr -c 'A-Za-z0-9._-' '_'; }
repo_git() { git -C "$INCOGNITA_REPO" -c core.hooksPath=/dev/null -c core.fsmonitor=false "$@"; }

# Write the current activity for the heartbeat.
set_activity() { mkdir -p "$INCOGNITA_HOME" && printf '%s\n' "$*" > "$INCOGNITA_HOME/activity" 2>/dev/null; }

# ---------------------------------------------------------------- deadline
# INCOGNITA_DEADLINE_EPOCH wins; else INCOGNITA_DEADLINE (HH:MM, local) is its next occurrence.
# Without either there is no deadline (manual runs).
deadline_epoch() {
  if [ -n "${INCOGNITA_DEADLINE_EPOCH:-}" ]; then echo "$INCOGNITA_DEADLINE_EPOCH"; return 0; fi
  if [ -z "${INCOGNITA_DEADLINE:-}" ]; then echo 0; return 0; fi
  case "$INCOGNITA_DEADLINE" in
    [0-2][0-9]:[0-5][0-9]) ;;
    *) log "INCOGNITA_DEADLINE must be HH:MM, not $INCOGNITA_DEADLINE"; return 1 ;;
  esac
  local t
  t=$(date -d "today $INCOGNITA_DEADLINE" +%s) || return 1
  [ "$t" -le "$(now)" ] && { t=$(date -d "tomorrow $INCOGNITA_DEADLINE" +%s) || return 1; }
  echo "$t"
}
remaining() {  # seconds left before the deadline (a large number without deadline)
  local d=${DEADLINE:-0}
  if [ "$d" = 0 ]; then echo 999999999; else echo $(( d - $(now) )); fi
}
sleep_bounded() {  # sleep $1 seconds, but never past the deadline
  local s=$1 r
  r=$(remaining)
  [ "$r" -lt "$s" ] && s=$r
  [ "$s" -gt 0 ] && sleep "$s"
  return 0
}

# ---------------------------------------------------------------- state (~/.incognita/state)
init_state() {
  mkdir -p "$INCOGNITA_STATE/lifetime" "$INCOGNITA_STATE/parked" "$INCOGNITA_STATE/marks" \
    "$INCOGNITA_STATE/audit" "$INCOGNITA_LOGS" "$INCOGNITA_HOME/work" || return 1
  : "${INCOGNITA_NIGHT:=$(date +%F)}"
  export INCOGNITA_NIGHT
  NIGHT_DIR=$INCOGNITA_STATE/nights/$INCOGNITA_NIGHT
  mkdir -p "$NIGHT_DIR/attempts"
  # The first night, for the periodic roadmap proposals (a dry run records nothing).
  is_dry || [ -f "$INCOGNITA_STATE/first-night" ] || printf '%s\n' "$INCOGNITA_NIGHT" > "$INCOGNITA_STATE/first-night"
}
# days_between <YYYY-MM-DD> <YYYY-MM-DD>: whole days from the first date to the second.
days_between() {
  local a b
  a=$(date -u -d "$1" +%s 2>/dev/null) && b=$(date -u -d "$2" +%s 2>/dev/null) || { echo 0; return; }
  echo $(( (b - a) / 86400 ))
}
counter_get() { cat "$INCOGNITA_STATE/lifetime/$(key_of "$1")" 2>/dev/null || echo 0; }
counter_inc() {
  local f n
  f=$INCOGNITA_STATE/lifetime/$(key_of "$1")
  n=$(( $(counter_get "$1") + ${2:-1} ))
  printf '%s\n' "$n" > "$f"
  echo "$n"
}
counter_set() { printf '%s\n' "$2" > "$INCOGNITA_STATE/lifetime/$(key_of "$1")"; }
mark_set() { : > "$INCOGNITA_STATE/marks/$(key_of "$1")"; }
mark_has() { [ -e "$INCOGNITA_STATE/marks/$(key_of "$1")" ]; }
is_parked() { [ -e "$INCOGNITA_STATE/parked/$(key_of "$1 $2")" ]; }

# record_attempt <role> <target> <ok|fail|skip> <outcome...>
record_attempt() {
  local role=$1 target=$2 kind=$3; shift 3
  is_dry && return 0   # a dry run leaves the state alone
  printf '%s %s %s\n' "$(now)" "$kind" "$*" >> "$NIGHT_DIR/attempts/$(key_of "$role $target")"
  if [ "$kind" = fail ]; then
    local n
    n=$(counter_inc "fail $role $target")
    if [ "$n" -ge "$INCOGNITA_PARK_AFTER" ] && ! [[ "$target" =~ ^[0-9]+$ ]]; then
      : > "$INCOGNITA_STATE/parked/$(key_of "$role $target")"
      log "parked: $role $target ($n failed attempts in all; remove $INCOGNITA_STATE/parked/$(key_of "$role $target") to retry)"
      record_event parked "$role" "$target" "$n failures"
    fi
  elif [ "$kind" = ok ]; then
    counter_set "fail $role $target" 0
  fi
}
night_fails() {
  local f
  f=$NIGHT_DIR/attempts/$(key_of "$1 $2")
  [ -f "$f" ] || { echo 0; return; }
  awk '$2 == "fail"' "$f" | wc -l | tr -d ' '
}
# record_event <kind> <role> <target> <detail...>   (TSV, for the night report)
record_event() {
  is_dry && return 0
  local kind=$1 role=${2:--} target=${3:--}; shift 3 || shift $#
  local detail
  detail=$(printf '%s' "$*" | tr '\t\n\r' '   ' | cut -c1-500)
  printf '%s\t%s\t%s\t%s\t%s\n' "$(date '+%F %T')" "$kind" "$role" "$target" "$detail" \
    >> "$NIGHT_DIR/events.tsv"
}

# ---------------------------------------------------------------- GitHub
# gh with three tries; prints stdout; non-zero = unknown.
ghr() {
  local i out rc=1
  for i in 1 2 3; do
    if out=$(gh "$@"); then printf '%s\n' "$out"; return 0; fi
    rc=$?
    [ "$i" -lt 3 ] && sleep $(( i * 5 ))
  done
  log "gh failed ($rc): gh $*"
  return "$rc"
}
owner_login() {  # the loop's GitHub account; trusted comments and statuses are its own
  if [ -z "${OWNER:-}" ]; then
    OWNER=$(ghr api user --jq .login) || return 1
    [ -n "$OWNER" ] || return 1
    export OWNER
  fi
  echo "$OWNER"
}
ensure_label() {  # name color description
  is_dry && return 0
  gh label create "$1" --color "$2" --description "$3" >/dev/null 2>&1 || true
}
ensure_labels() {
  ensure_label incomplete FBCA04 "A session stopped before the end: its work is kept, an agent continues it"
  ensure_label rejected B60205 "Paper rejected by the referees (reports kept); the owner may reopen it"
  ensure_label needs-human B60205 "The agents cannot go further: the owner decides"
  ensure_label veto B60205 "The owner vetoes this roadmap proposal (or comments: veto)"
}

# certify_py <args...>: scripts/certify.py of the loop's own clone (never the agent's copy), on the
# loop's clone by default (pass --repo first to read another tree).
certify_py() {
  case "${1:-}" in --repo) python3 "$INCOGNITA_SCRIPTS/certify.py" "$@" ;;
                   *) python3 "$INCOGNITA_SCRIPTS/certify.py" --repo "$INCOGNITA_REPO" "$@" ;; esac
}

# owner_words <comments-json>: "<veto|approve> <created_at>" of the latest comment written by the
# owner himself (OWNER, without the loop's marker) whose first word is veto or approve.
owner_words() {
  printf '%s' "$1" | jq -rs --arg o "$OWNER" '
    add // [] | map(select(.user.login == $o and ((.body // "") | startswith("<!-- incognita:") | not))
      | {w: ((.body // "") | ascii_downcase | capture("^\\s*(?<w>veto|approve)\\b").w? // empty), created_at})
    | map(select(.w != null)) | sort_by(.created_at) | last | if . == null then empty else "\(.w) \(.created_at)" end'
}

# Agent text posted to GitHub: control and bidi characters removed, tokens redacted, `<!--`
# escaped, `@` followed by a zero-width space, closing keywords neutralised, truncated.
# sanitize [max-chars] < in > out
sanitize() {
  python3 -I -c '
import re, sys
limit = int(sys.argv[1])
t = sys.stdin.buffer.read().decode("utf-8", "replace")
t = "".join(c for c in t if c in "\n\t" or (ord(c) >= 32 and ord(c) != 127
            and not (0x202A <= ord(c) <= 0x202E) and not (0x2066 <= ord(c) <= 0x2069)))
t = re.sub(r"sk-ant-[A-Za-z0-9_\-]{8,}", "[redacted]", t)
t = t.replace("<!--", "&lt;!--")
t = t.replace("@", "@​")
t = re.sub(r"(?i)\b(close[sd]?|fix(?:e[sd])?|resolve[sd]?)(\s*:?\s+)(?=(?:[\w.-]+/[\w.-]+)?#\d|https?://)",
           lambda m: m.group(1) + "​" + m.group(2), t)
if len(t) > limit:
    t = t[:limit] + "\n\n[truncated by the script at %d characters]\n" % limit
sys.stdout.write(t)
' "${1:-60000}"
}
one_line() { sanitize "${1:-200}" | tr '\n\r\t' '   ' | sed -e 's/  */ /g' -e 's/^ //' -e 's/ $//'; }

# post_comment <issue-or-pr> <kind> <sha> <body-file>: a trusted comment, marker on the first line.
# The body must already be sanitised where it comes from an agent.
post_comment() {
  local n=$1 kind=$2 sha=$3 body=$4 f
  f=$(mktemp) || return 1
  { printf '<!-- incognita:%s:%s -->\n' "$kind" "$sha"; cat "$body"; } > "$f"
  if is_dry; then log "dry run: would comment on #$n ($kind)"; rm -f "$f"; return 0; fi
  ghr api -X POST "repos/$GH_REPO/issues/$n/comments" -F "body=@$f" --jq .html_url
  local rc=$?
  rm -f "$f"
  return $rc
}

# trusted_comments <pr>: JSON array of the comments by OWNER whose first line is a marker, with
# fields kind, sha, body (marker removed), created_at. trusted_of <raw comments> does the same on
# comments already fetched (`gh api --paginate .../comments`).
TRUSTED_JQ='
    add // [] | map(select(.user.login == $o)
      | (.body | split("\n")) as $l
      | ($l[0] | capture("^<!-- incognita:(?<kind>[a-z-]+):(?<sha>[0-9a-f]{40}) -->$")) as $m
      | {kind: $m.kind, sha: $m.sha, created_at, url: .html_url, body: ($l[1:] | join("\n"))})
    | sort_by(.created_at)'
trusted_of() { printf '%s' "$1" | jq -s --arg o "$OWNER" "$TRUSTED_JQ"; }
trusted_comments() {
  local raw
  raw=$(ghr api --paginate "repos/$GH_REPO/issues/$1/comments?per_page=100") || return 1
  trusted_of "$raw"
}

# statuses_of <sha>: one line per context: context<TAB>state<TAB>trusted<TAB>description, for the
# latest status of each context; trusted = created by OWNER (a workflow's status is not trusted).
statuses_of() {
  local raw
  raw=$(ghr api --paginate "repos/$GH_REPO/commits/$1/statuses?per_page=100") || return 1
  printf '%s' "$raw" | jq -rs --arg o "$OWNER" '
    add // [] | group_by(.context) | map(max_by(.created_at))
    | .[] | [.context, .state, (if .creator.login == $o then "yes" else "no" end),
             (.description // "" | gsub("[\t\n]"; " "))] | @tsv'
}
# verdict_in <statuses-text> <context> <role-regex>: the verdict of a trusted status, or "none".
verdict_in() {
  printf '%s\n' "$1" | awk -F'\t' -v c="$2" -v r="$3" '
    $1 == c && $3 == "yes" {
      if (match($4, /role=[a-z-]+/)) role = substr($4, RSTART + 5, RLENGTH - 5); else role = ""
      if (match($4, /verdict=[a-z_]+/)) v = substr($4, RSTART + 8, RLENGTH - 8); else v = ""
      if (role ~ ("^(" r ")$") && v != "") { print v; found = 1 }
    }
    END { if (!found) print "none" }'
}
set_status() {  # sha context state description
  if is_dry; then log "dry run: would set status $2=$3 on ${1:0:12} ($4)"; return 0; fi
  ghr api -X POST "repos/$GH_REPO/statuses/$1" -f state="$3" -f context="$2" \
    -f description="${4:0:139}" >/dev/null
}

# pinned_issue <title>: number of the open issue with this title opened by OWNER; created and
# pinned if missing.
pinned_issue() {
  local title=$1 n
  n=$(ghr issue list --state open --limit 200 --author "$OWNER" --json number,title \
      --jq "map(select(.title == \"$title\")) | first | .number // empty") || return 1
  if [ -z "$n" ]; then
    is_dry && { log "dry run: would create the issue \"$title\""; echo 0; return 0; }
    local url
    url=$(ghr issue create --title "$title" \
      --body "Written by the Incognita loop (scripts/night.sh, scripts/agent.sh). One comment per entry.") \
      || return 1
    n=${url##*/}
    gh issue pin "$n" >/dev/null 2>&1 || log "could not pin issue #$n"
  fi
  echo "$n"
}

# close_rejected <pr> <sha> <reason> [title]: a paper PR closed with the label `rejected` (D2).
close_rejected() {
  local n=$1 sha=$2 why=$3 title=${4:-} f
  if is_dry; then log "dry run: would close #$n as rejected ($why)"; return 0; fi
  ensure_labels
  f=$(mktemp)
  printf 'Closed by the script: %s. The reports stay above; the owner may reopen the pull request.\n' "$why" > "$f"
  post_comment "$n" rejected "$sha" "$f" >/dev/null
  rm -f "$f"
  gh pr edit "$n" --add-label rejected >/dev/null 2>&1
  gh pr close "$n" >/dev/null 2>&1 || return 1
  record_event rejected - "$n" "$title — $why"
  log "closed #$n as rejected: $why"
}
escalate() {  # <pr> <reason>: label needs-human (non-paper PRs), once
  if is_dry; then log "dry run: would label #$1 needs-human ($2)"; return 0; fi
  ensure_labels
  gh pr edit "$1" --add-label needs-human >/dev/null 2>&1 || return 1
  record_event needs-human - "$1" "$2"
  log "#$1 needs a human: $2"
}

# The open pull requests (all of them; filters are applied by the callers).
PR_FIELDS=number,title,body,headRefName,headRefOid,isCrossRepository,isDraft,labels,mergeable,statusCheckRollup,author,createdAt,updatedAt,baseRefName
fetch_open_prs() { ghr pr list --state open --limit 200 --json "$PR_FIELDS"; }

# The build of a PR head, from its statusCheckRollup (a PR object). Two checks count: "Build and
# check" (job of the workflow CI, a required check of main) and "Compile papers" (job of the
# workflow Papers, path-filtered, so never a required check). Paper PRs (roles write-paper, revise)
# need both; any other PR needs "Build and check", and "Compile papers" too when it ran (it touched
# papers/). Result: SUCCESS, a failure (FAILURE, TIMED_OUT, STARTUP_FAILURE, ERROR), NONE (a needed
# check is missing) or the state of a check still running or cancelled.
CI_JQ='
  def ci_of($role):
    ([.statusCheckRollup[]? | select(.name == "Build and check" or .name == "Compile papers")]
     | group_by(.name) | map(last)) as $present
    | ([$present[].name]
       + (if ($role == "write-paper" or $role == "revise") then ["Build and check", "Compile papers"]
          else ["Build and check"] end) | unique) as $names
    | [$names[] as $nm | ([$present[] | select(.name == $nm)] | first) as $c
       | if $c == null then "NONE"
         elif ($c.conclusion // "") != "" then $c.conclusion else ($c.status // "NONE") end] as $v
    | def bad: . == "FAILURE" or . == "TIMED_OUT" or . == "STARTUP_FAILURE" or . == "ERROR";
      def good: . == "SUCCESS" or . == "NEUTRAL" or . == "SKIPPED";
      if any($v[]; bad) then ([$v[] | select(bad)] | first)
      elif all($v[]; good) then "SUCCESS"
      elif any($v[]; . == "NONE") then "NONE"
      else ([$v[] | select(good | not)] | first) end;'

# jq: one row per agent PR (same repository, branch agent/*, opened by OWNER, with a Role line):
# number H branch draft mergeable role target labels ci
AGENT_ROWS_JQ=$CI_JQ'
  .[] | select(.isCrossRepository == false and (.headRefName | startswith("agent/"))
               and .author.login == $o and .baseRefName == "main")
  | ((.body // "") | split("\n")[0]
     | capture("^Role: `(?<role>[a-z-]+)`\\. Target: `(?<target>[^`]*)`\\.")) as $r
  | [.number, .headRefOid, .headRefName, (if .isDraft then "draft" else "ready" end),
     (.mergeable // "UNKNOWN"), $r.role, (if $r.target == "" then "-" else $r.target end),
     ([.labels[].name] | join(",") | if . == "" then "-" else . end),
     ci_of($r.role)]
  | @tsv'
agent_rows() { jq -r --arg o "$OWNER" "$AGENT_ROWS_JQ" "$1"; }

# Busy targets: "role target" of every open same-repository PR (agents' work in progress).
busy_pairs() {
  jq -r '.[] | select(.isCrossRepository == false)
    | ((.body // "") | split("\n")[0]
       | capture("^Role: `(?<role>[a-z-]+)`\\. Target: `(?<target>[^`]*)`\\.")) | "\(.role) \(.target)"' "$1"
}
open_prs_md() {  # the context file .agents/open-prs.md
  jq -r '.[] | select(.isCrossRepository == false)
    | "- #\(.number)\(if .isDraft then " (draft)" else "" end): \((.body // "") | split("\n")[0]) — \(.title)"' "$1"
}

# ---------------------------------------------------------------- CI
# ci_runs_of <sha> [event] [workflows]: the runs on this commit of the workflows named by the regex
# <workflows> (default: CI and Papers, the two workflows whose checks count), newest first.
ci_runs_of() {
  local q="head_sha=$1&per_page=50" w=${3:-CI|Papers}
  [ -n "${2:-}" ] && q="$q&event=$2"
  ghr api "repos/$GH_REPO/actions/runs?$q" \
    --jq "[.workflow_runs[] | select(.name | test(\"^($w)\$\"))] | sort_by(.created_at) | reverse"
}
# ci_effective <sha> <rollup-state>: success | pending | failed. A failure is rerun once (failed
# jobs of the failed run); a cancelled or missing run older than 2 h is rerun once. Unknown is
# "pending". <rollup-state> is the ci column of the rows (CI_JQ).
ci_effective() {
  local sha=$1 st=$2 runs id attempt age
  case "$st" in
    SUCCESS) echo success; return 0 ;;
    IN_PROGRESS|QUEUED|PENDING|WAITING|REQUESTED|EXPECTED) echo pending; return 0 ;;
  esac
  runs=$(ci_runs_of "$sha") || { echo pending; return 0; }
  # The run to look at: the newest failed one if any, else the newest.
  id=$(printf '%s' "$runs" | jq -r '([.[] | select(.conclusion == "failure" or .conclusion == "timed_out" or .conclusion == "startup_failure")] + .) | .[0].id // empty')
  attempt=$(printf '%s' "$runs" | jq -r --arg id "$id" '[.[] | select((.id | tostring) == $id)] | .[0].run_attempt // 0')
  case "$st" in
    FAILURE|TIMED_OUT|STARTUP_FAILURE|ERROR)
      if [ -n "$id" ] && [ "$attempt" -le 1 ] && ! mark_has "rerun $sha $id"; then
        if is_dry; then log "dry run: would rerun the failed jobs of run $id (${sha:0:12})"
        else
          mark_set "rerun $sha $id"
          gh run rerun "$id" --failed >/dev/null 2>&1 && log "CI of ${sha:0:12} failed: rerun $id" \
            && record_event ci-rerun - - "${sha:0:12} run $id"
        fi
        echo pending; return 0
      fi
      echo failed; return 0 ;;
  esac
  # cancelled, skipped, stale, missing...
  if [ -n "$id" ]; then
    age=$(( $(now) - $(date -d "$(printf '%s' "$runs" | jq -r '.[0].updated_at')" +%s 2>/dev/null || now) ))
    if [ "$age" -gt 7200 ] && ! mark_has "rerun-cancelled $sha"; then
      if ! is_dry; then
        mark_set "rerun-cancelled $sha"
        gh run rerun "$id" >/dev/null 2>&1 && log "CI of ${sha:0:12} cancelled 2 h ago: rerun $id"
      fi
    fi
  fi
  echo pending
}
# main_red <M>: 0 if the build of main's head M failed on a push run after one rerun.
main_red() {
  local m=$1 runs st attempt id
  runs=$(ci_runs_of "$m" push CI) || return 1
  st=$(printf '%s' "$runs" | jq -r '.[0].conclusion // "none"')
  attempt=$(printf '%s' "$runs" | jq -r '.[0].run_attempt // 0')
  id=$(printf '%s' "$runs" | jq -r '.[0].id // empty')
  case "$st" in
    failure|timed_out|startup_failure)
      if [ "$attempt" -le 1 ] && ! mark_has "rerun $m"; then
        is_dry || { mark_set "rerun $m"; gh run rerun "$id" --failed >/dev/null 2>&1 \
          && log "CI of main failed: rerun $id"; }
        return 1
      fi
      return 0 ;;
  esac
  return 1
}
ci_failed_log() {  # sha [workflows] → the end of the logs of the failed jobs of its failed runs
  local runs id name found=1
  runs=$(ci_runs_of "$1" "" "${2:-CI|Papers}") || return 1
  while IFS=$'\t' read -r id name; do
    [ -n "$id" ] || continue
    printf '===== workflow %s, run %s: failed jobs\n' "$name" "$id"
    gh run view "$id" --log-failed 2>/dev/null | tail -n 400
    found=0
  done < <(printf '%s' "$runs" | jq -r 'group_by(.name) | map(.[0]) | .[]
    | select(.conclusion == "failure" or .conclusion == "timed_out" or .conclusion == "startup_failure")
    | [.id, .name] | @tsv')
  return $found
}

# ---------------------------------------------------------------- the loop's own clone (trusted)
sync_main() {  # fetch and fast-forward the loop's clone; prints origin/main
  repo_git fetch -q --prune origin || return 1
  local cur
  cur=$(repo_git rev-parse --abbrev-ref HEAD) || return 1
  [ "$cur" = main ] || { log "the loop's clone is on $cur, not main"; return 1; }
  repo_git merge -q --ff-only origin/main >/dev/null || { log "cannot fast-forward main"; return 1; }
  repo_git rev-parse origin/main
}
fetch_pr_head() {  # pr sha: fetch refs/pull/N/head into refs/incognita/pr/N and check it is sha
  repo_git -c transfer.fsckObjects=true fetch -q --no-tags origin "+refs/pull/$1/head:refs/incognita/pr/$1" \
    || return 1
  [ "$(repo_git rev-parse "refs/incognita/pr/$1")" = "$2" ]
}
show_main() { repo_git show "origin/main:$1" 2>/dev/null; }
ls_main() { repo_git ls-tree --name-only "origin/main:$1" 2>/dev/null; }

# Roadmaps: approved, with KNOWN.md reviewed by the owner (first line "Reviewed by owner: <date>").
roadmaps_writable() {
  local r
  for r in $(ls_main roadmaps); do
    show_main "roadmaps/$r/ROADMAP.md" | grep -q '^| Status | \*\*approved' || continue
    show_main "roadmaps/$r/KNOWN.md" | head -n 1 | grep -Eq '^Reviewed by owner:[[:space:]]*[0-9]' || continue
    echo "$r"
  done
}
papers_on_main() { ls_main papers | grep -E '^P[0-9]+-' | sort -V; }
meta_get() {  # paper key: a simple TOML string value of papers/<paper>/META.toml on main
  show_main "papers/$1/META.toml" | sed -n -E "s/^$2[[:space:]]*=[[:space:]]*\"([^\"]*)\".*/\1/p" | head -n 1
}
paper_num() { printf '%s' "$1" | sed -n -E 's/^P0*([0-9]+).*/\1/p'; }
paper_of_num() {  # number → the paper directory on main with this number
  local p
  for p in $(papers_on_main); do [ "$(paper_num "$p")" = "$1" ] && { echo "$p"; return 0; }; done
  return 1
}
locks_of() {  # paper: lock files of its frozen statements (any Statements/ dir with its number)
  local d n
  n=$(paper_num "$1")
  for d in $(ls_main Statements); do
    [ "$(paper_num "$d")" = "$n" ] || continue
    ls_main "Statements/$d" | grep '\.lock$' | sed "s#^#Statements/$d/#"
  done
}

# Errata and statement corrections (AGENTS.md §6.6; papers/README.md). An entry starts with a line
# "## E<k> ..." (errata.md) or "## SC<n> ..." (statement-corrections.md); later roles add, under it,
# a line "Revised in ..." (revise: a new version of the paper exists) and a line "Resolved by ..."
# (formalize-statements: the corrected statements are frozen, or nothing needs freezing), possibly
# as list items ("- Resolved by ..."). An optional line "- Frozen statement: <Lean name>" names the
# frozen statement the entry is about.
# entry_flags < file: one line per entry: "<id> <revised 0|1> <resolved 0|1> <frozen statement|->".
entry_flags() {
  awk '
    function flush() { if (id != "") print id, rev, res, (fs == "" ? "-" : fs) }
    /^## (E|SC)[0-9]+([^0-9]|$)/ { flush(); id = $2; sub(/[^A-Z0-9].*$/, "", id); rev = 0; res = 0; fs = ""; next }
    /^## / { flush(); id = ""; next }
    id != "" && /^(- )?Revised in / { rev = 1 }
    id != "" && /^(- )?Resolved by / { res = 1 }
    id != "" && /^- Frozen statement:/ {
      fs = $0; sub(/^- Frozen statement:[ \t]*/, "", fs); gsub(/`/, "", fs); sub(/[ \t].*$/, "", fs) }
    END { flush() }'
}
# disputed_entries <paper>: errata entries of the paper on main neither revised nor resolved.
disputed_entries() { show_main "papers/$1/errata.md" | entry_flags | awk '$2 == 0 && $3 == 0 { print $1 }'; }
# freeze_entries <paper>: entries waiting for a statements PR: errata revised but not resolved, and
# statement corrections not resolved.
freeze_entries() {
  { show_main "papers/$1/errata.md" | entry_flags | awk '$2 == 1 && $3 == 0 { print $1 }'
    show_main "papers/$1/statement-corrections.md" | entry_flags | awk '$3 == 0 { print $1 }'; }
}
# superseded <paper>: short Lean names of frozen statements replaced by a resolved entry.
superseded() {
  { show_main "papers/$1/errata.md"; echo; show_main "papers/$1/statement-corrections.md"; } \
    | entry_flags | awk '$3 == 1 && $4 != "-" { n = $4; sub(/^Incognita\.Statements\.[^.]*\./, "", n); print n }' | sort -u
}

# Audit status of main (lines "<P> <name> open|proved|refuted"), from the loop's own clone of
# main only (trusted after merge), cached per commit. Interface: `lake exe audit --status`.
audit_status() {
  local m f tmp
  m=$(repo_git rev-parse origin/main) || return 1
  f=$INCOGNITA_STATE/audit/$m.txt
  if [ ! -f "$f" ]; then
    if [ -z "$(repo_git ls-tree -r --name-only origin/main -- Statements | grep '\.lock$')" ]; then
      : > "$f"
    else
      [ "$(repo_git rev-parse HEAD)" = "$m" ] || { log "audit: the clone is not at origin/main"; return 1; }
      is_dry && { log "dry run: no audit build"; return 1; }
      set_activity "audit build of main ${m:0:12}"
      tmp=$(mktemp)
      log "audit: building main ${m:0:12} in the loop's clone"
      if (cd "$INCOGNITA_REPO" && timeout -k 60 3600 bash scripts/build.sh Incognita Statements >"$tmp.log" 2>&1 \
          && timeout -k 60 1200 lake exe audit --status >"$tmp" 2>>"$tmp.log"); then
        grep -E '^[^ ]+ [^ ]+ (open|proved|refuted)$' "$tmp" > "$f"
      else
        log "audit: build or audit of main failed (see $tmp.log)"
        rm -f "$tmp"; return 1
      fi
      rm -f "$tmp" "$tmp.log"
    fi
  fi
  cat "$f"
}

# ---------------------------------------------------------------- paths (D12)

# paper_file <path> <paper|""> <regex>: is <path> papers/<paper>/<f> with <f> matching <regex>
# (any paper directory when <paper> is empty)?
paper_file() {
  local p=${2:-[^/]+}
  [[ "$1" =~ ^papers/${p}/(${3})$ ]]
}
# role_allows <role> <paper> <path> <status>: may this role make this change? This is the table
# of AGENTS.md §2, line for line (keep them identical; scripts/test-lib.sh tests every line).
# <paper> is the paper directory of the task (empty for write-paper: check_paths checks that the
# PR adds exactly one new directory). <status>: A, M or D (git diff --raw --no-renames). fix-pr
# uses the line of the role that opened the PR; fix-main is fix-pr on main. Reviewers: nothing.
role_allows() {
  local role=$1 paper=$2 path=$3 st=$4
  # Lean drafts: every writing role but the bibliographer.
  case "$path" in
    Exploration/*|Exploration.lean)
      case "$role" in write-paper|revise|formalize-statements|prove|garden|fix-main) return 0 ;; esac
      return 1 ;;
  esac
  # Nothing is ever deleted under papers/.
  case "$path" in papers/*) [ "$st" = D ] && return 1 ;; esac
  case "$role" in
    write-paper)
      paper_file "$path" "" 'paper\.tex|refs\.bib|META\.toml|notebook/.+' && return 0
      case "$path" in literature/*|papers/library.bib) [ "$st" != D ] && return 0 ;; esac ;;
    revise)
      [ -n "$paper" ] && paper_file "$path" "$paper" 'paper\.tex|refs\.bib|META\.toml|notebook/.+|errata\.md|dependency-checks\.md' && return 0
      case "$path" in literature/*|papers/library.bib) [ "$st" != D ] && return 0 ;; esac ;;
    propose-roadmap)
      # One new roadmap (ROADMAP.md and KNOWN.md of a new directory) or one new extension of an
      # approved roadmap; check_paths checks the whole proposal (scripts/certify.py proposal).
      case "$path" in
        roadmaps/*/ROADMAP.md|roadmaps/*/KNOWN.md)
          [ "$st" = A ] && [[ "$path" =~ ^roadmaps/[A-Z][A-Za-z0-9]+/(ROADMAP|KNOWN)\.md$ ]] && return 0 ;;
        roadmaps/*/extensions/*)
          [ "$st" = A ] && [[ "$path" =~ ^roadmaps/[A-Za-z0-9]+/extensions/X[0-9]+\.md$ ]] && return 0 ;;
        literature/*) [ "$st" != D ] && return 0 ;;
      esac ;;
    formalize-statements)
      case "$path" in
        Statements/*) [ "$st" = A ] && [[ "$path" =~ ^Statements/P[0-9]{3}/.+\.(lean|lock)$ ]] && return 0 ;;
        Statements.lean|Incognita.lean) return 0 ;;
        Incognita/*|catalogue/definitions/*) [ "$st" != D ] && return 0 ;;
      esac
      [ -n "$paper" ] && paper_file "$path" "$paper" 'blueprint\.md|errata\.md|statement-corrections\.md' && return 0 ;;
    prove)
      case "$path" in
        Incognita.lean) return 0 ;;
        Incognita/*) [ "$st" != D ] && return 0 ;;
        catalogue/results/*) [ "$st" = A ] && [[ "$path" =~ ^catalogue/results/P[0-9]{3}-[^/]+\.toml$ ]] && return 0 ;;
      esac
      [ -n "$paper" ] && paper_file "$path" "$paper" 'blueprint\.md|formalisation\.tex|errata\.md|statement-corrections\.md' && return 0 ;;
    bibliographer)
      case "$path" in literature/*|catalogue/attribution/*) [ "$st" != D ] && return 0 ;; esac
      paper_file "$path" "" 'refs\.bib' && return 0 ;;
    garden)
      case "$path" in
        Incognita.lean) return 0 ;;
        Incognita/*|catalogue/relations.toml|catalogue/garden.md) [ "$st" != D ] && return 0 ;;
        # Dropped lines under candidate directions (the file exists: entries come from the loop).
        roadmaps/*/directions.md) [ "$st" = M ] && [[ "$path" =~ ^roadmaps/[A-Za-z0-9]+/directions\.md$ ]] && return 0 ;;
      esac
      # A failed re-check: an erratum or a statement correction of the paper re-checked.
      paper_file "$path" "" 'errata\.md|statement-corrections\.md' && return 0 ;;
    fix-main)
      case "$path" in
        Incognita.lean|Statements.lean) return 0 ;;
        Incognita/*|papers/library.bib) [ "$st" != D ] && return 0 ;;
      esac ;;
  esac
  return 1
}

# check_paths <role> <paper> <base> <new>: 0 if every change of base..new is allowed; reasons on
# stderr. <role> is the role whose rules apply (fix-pr: the role that opened the PR; fix-main).
check_paths() {
  local role=$1 paper=$2 base=$3 new=$4 bad=0 raw meta path omode nmode osha nsha st size f
  raw=$(mktemp) || return 1
  if ! repo_git -c core.quotePath=false diff --raw -z --no-renames --no-abbrev "$base" "$new" > "$raw"; then
    rm -f "$raw"; log "check_paths: git diff failed"; return 1
  fi
  local papers_touched=""
  while IFS= read -r -d '' meta && IFS= read -r -d '' path; do
    read -r omode nmode osha nsha st <<< "${meta#:}"
    : "$omode" "$osha"
    case "$nmode" in 120000|160000) log "refused: $path is a symlink or submodule"; bad=1; continue ;; esac
    case "/$path" in */.*) log "refused: $path (a path component starts with a dot)"; bad=1; continue ;; esac
    case "${path##*/}" in
      CLAUDE.md|AGENTS.md|CONTRIBUTING.md|README.md|lakefile.lean|.gitmodules) log "refused: $path (human-owned, anywhere)"; bad=1; continue ;;
    esac
    if [ "$st" != D ]; then
      size=$(repo_git cat-file -s "$nsha" 2>/dev/null || echo 0)
      [ "$size" -gt 1048576 ] && { log "refused: $path is larger than 1 MB"; bad=1; continue; }
    fi
    case "$path" in
      LICENSE|lakefile.toml|lean-toolchain|lake-manifest.json|templates/*|agents/*|docs/*|scripts/*|tests/*|programmes/*|literature/notes/TEMPLATE.md|papers/*/withdrawn.md|papers/*/human-audits.md)
        log "refused: human-owned path $path"; bad=1; continue ;;
      # Generated, never committed (scripts/certify.py).
      catalogue/certification.md|papers/*/certification.tex)
        log "refused: $path is generated, never committed"; bad=1; continue ;;
      # roadmaps/ is the owner's, except a proposal (propose-roadmap) and dropped candidate
      # directions (garden): role_allows decides.
      roadmaps/*)
        role_allows "$role" "$paper" "$path" "$st" || { log "refused: human-owned path $path"; bad=1; continue; } ;;
    esac
    case "$path" in Statements/*) [ "$st" = A ] || { log "refused: $st on frozen $path"; bad=1; continue; } ;; esac
    case "$path" in papers/*/*) f=${path#papers/}; f=${f%%/*}; in_list "$f" "$papers_touched" || papers_touched="$papers_touched $f" ;; esac
    role_allows "$role" "$paper" "$path" "$st" || { log "refused: $role may not change $path ($st)"; bad=1; }
  done < "$raw"
  rm -f "$raw"
  # write-paper: one new paper directory, P<nnn>-<slug>, absent from main.
  if [ "$role" = write-paper ]; then
    set -- $papers_touched
    if [ $# -ne 1 ]; then log "refused: write-paper must add exactly one paper directory (got:${papers_touched:- none})"; bad=1
    elif ! [[ "$1" =~ ^P[0-9]{3}-[A-Za-z0-9-]+$ ]]; then log "refused: bad paper id $1"; bad=1
    elif repo_git cat-file -e "$base:papers/$1" 2>/dev/null; then log "refused: papers/$1 already exists on main"; bad=1
    elif [ -n "$(papers_on_main | awk -v n="$(paper_num "$1")" '{ sub(/^P0*/, ""); sub(/-.*/, ""); if ($0 == n) print }')" ]; then
      log "refused: the number of $1 is taken on main"; bad=1
    fi
  fi
  # propose-roadmap: one complete proposal, with the status `proposed` (scripts/certify.py).
  if [ "$role" = propose-roadmap ] && [ "$bad" = 0 ]; then
    certify_py proposal --base "$base" --head "$new" >/dev/null || { log "refused: not a valid roadmap proposal"; bad=1; }
  fi
  # Root import files: import lines only; Statements.lean: additions only.
  for f in $ROOT_FILES; do
    local d
    d=$(repo_git diff --no-renames -U0 "$base" "$new" -- "$f" | grep -E '^[+-]' | grep -vE '^(\+\+\+|---) ')
    [ -n "$d" ] || continue
    if printf '%s\n' "$d" | grep -vqE '^[+-]((public )?import [A-Za-z0-9_.«»]+)?[[:space:]]*$'; then
      log "refused: $f may only change import lines"; bad=1
    fi
    if [ "$f" = Statements.lean ] && printf '%s\n' "$d" | grep -qE '^-[^[:space:]]'; then
      log "refused: Statements.lean lost an import"; bad=1
    fi
  done
  # Never a secret in the diff.
  if repo_git diff "$base" "$new" | grep -qE 'sk-ant-[A-Za-z0-9_-]{20,}'; then
    log "refused: the diff contains what looks like a Claude token"; bad=1
  fi
  return "$bad"
}

# Mechanical rebase helpers (D13). resolve_imports <worktree> <file>: during a conflicted rebase, the
# file becomes the header of "ours" followed by the sorted union of the import lines of both sides.
resolve_imports() {
  local wt=$1 f=$2 ours theirs
  ours=$(git -C "$wt" show ":2:$f") || return 1
  theirs=$(git -C "$wt" show ":3:$f") || return 1
  { printf '%s\n' "$ours" | awk '/^(public )?import /{exit} {print}'
    { printf '%s\n' "$ours"; printf '%s\n' "$theirs"; } | grep -E '^(public )?import ' | LC_ALL=C sort -u
  } > "$wt/$f"
}
diff_signature() {  # base head: "mode blob status path" of every changed path, sorted
  repo_git diff --raw --no-renames --no-abbrev "$1" "$2" \
    | awk -F'\t' '{ split($1, m, " "); print m[2], m[4], m[5], $2 }' | LC_ALL=C sort
}

# Merge categories (D15) of a path: papers literature proofs exploration statements directions
# roadmap other. `roadmap` is never in INCOGNITA_AUTOMERGE: a proposal merges only through the
# scripted approval of the loop (AGENTS.md section 4).
path_category() {  # kind path status
  local kind=$1 path=$2 st=$3
  case "$path" in
    Exploration/*|Exploration.lean) echo exploration ;;
    literature/*) echo literature ;;
    roadmaps/*/directions.md) echo directions ;;
    roadmaps/*) echo roadmap ;;
    papers/library.bib) if [ "$kind" = paper ]; then echo papers; else echo literature; fi ;;
    catalogue/definitions/*|Statements/*|Statements.lean) echo statements ;;
    catalogue/results/*) if [ "$st" = A ]; then echo proofs; else echo literature; fi ;;
    catalogue/*) echo literature ;;
    Incognita/*|Incognita.lean) echo proofs ;;
    papers/*)
      if [ "$kind" = paper ]; then echo papers
      elif [ "$kind" = statements ]; then echo statements
      else
        # A proof PR may add rows to blueprint.md and lemmas to formalisation.tex (not re-refereed:
        # Lean checks them); a bibliographer fixes metadata in refs.bib. Errata and statement
        # corrections (a paper becomes disputed) go to the owner.
        case "$path" in
          papers/*/blueprint.md|papers/*/formalisation.tex) echo proofs ;;
          papers/*/refs.bib) echo literature ;;
          *) echo other ;;
        esac
      fi ;;
    *) echo other ;;
  esac
}
# pr_kind <role>: paper | statements | roadmap | generic
pr_kind() {
  case "$1" in
    write-paper|revise) echo paper ;;
    formalize-statements) echo statements ;;
    propose-roadmap) echo roadmap ;;
    *) echo generic ;;
  esac
}
automerge_enabled() { case ",$INCOGNITA_AUTOMERGE," in *",$1,"*) return 0 ;; *) return 1 ;; esac; }

# A proof PR adds only lemmas and theorems (SPEC 1.3): no new def/structure/class/instance/axiom...
adds_only_theorems() {  # base new
  ! repo_git diff --no-renames -U0 "$1" "$2" -- 'Incognita/*.lean' 'Incognita/**/*.lean' \
    | grep -E '^\+' | grep -vE '^\+\+\+ ' \
    | grep -qE '^\+[[:space:]]*(@\[[^]]*\][[:space:]]*)?((private|protected|noncomputable|partial|unsafe|public|nonrec)[[:space:]]+)*(def|structure|class|instance|axiom|inductive|abbrev|opaque|macro|macro_rules|syntax|elab|elab_rules|notation|infix|infixl|infixr|prefix|postfix|initialize|builtin_initialize|declare_syntax_cat|attribute|set_option|unsafe|extern|implemented_by)([[:space:]]|$)'
}

# ---------------------------------------------------------------- the agent sandbox (D11)
AGENT_PATH="$INCOGNITA_AGENT_HOME/.local/bin:$INCOGNITA_AGENT_HOME/.elan/bin:/usr/local/bin:/usr/bin:/bin"
SANDBOX_UNIT=""
# run_sandboxed <unit> <max-seconds> <with-token: yes|no> <extra-rw-path|-> -- command...
# stdin/stdout/stderr are the caller's (systemd-run --pipe).
run_sandboxed() {
  local unit=$1 secs=$2 token=$3 rw=$4; shift 4
  [ "$1" = -- ] && shift
  local args=(--quiet --wait --pipe --collect "--unit=$unit"
    "--uid=$INCOGNITA_AGENT_USER" "--gid=$INCOGNITA_AGENT_USER"
    -p "WorkingDirectory=$INCOGNITA_AGENT_HOME/work"
    -E "HOME=$INCOGNITA_AGENT_HOME" -E "USER=$INCOGNITA_AGENT_USER" -E "LOGNAME=$INCOGNITA_AGENT_USER"
    -E "PATH=$AGENT_PATH" -E DISABLE_AUTOUPDATER=1 -E LANG=C.UTF-8
    -p "RuntimeMaxSec=$secs" -p "MemoryMax=$INCOGNITA_AGENT_MEMORY"
    -p NoNewPrivileges=yes -p PrivateTmp=yes -p ProtectSystem=strict
    -p "ReadWritePaths=$INCOGNITA_AGENT_HOME" -p "InaccessiblePaths=$HOME")
  [ "$token" = yes ] && args+=(-p "EnvironmentFile=$INCOGNITA_AGENT_ENV")
  [ "$rw" != - ] && args+=(-p "ReadWritePaths=$rw")
  if is_dry; then
    log "dry run: sudo systemd-run ${args[*]} $*"
    return 0
  fi
  SANDBOX_UNIT=$unit
  timeout -k 60 $(( secs + 300 )) sudo -n systemd-run "${args[@]}" "$@"
  local rc=$?
  SANDBOX_UNIT=""
  return $rc
}
stop_sandbox() {  # stop the running unit, if any (trap)
  [ -n "${SANDBOX_UNIT:-}" ] && sudo -n systemctl stop "$SANDBOX_UNIT.service" >/dev/null 2>&1
  return 0
}

# Re-sync the agent's .lake from the loop's clone when the toolchain or manifest changed (D11).
lake_stamp() { repo_git show origin/main:lean-toolchain origin/main:lake-manifest.json 2>/dev/null | sha256sum | cut -c1-16; }
sync_agent_lake() {
  local want have
  want=$(lake_stamp) || return 1
  have=$(cat "$INCOGNITA_EXCHANGE/lake.stamp" 2>/dev/null || true)
  [ "$want" = "$have" ] && return 0
  is_dry && { log "dry run: would re-sync the agent's .lake ($have -> $want)"; return 0; }
  log "the toolchain or manifest changed: rebuilding the loop's clone and re-syncing the agent's .lake"
  set_activity "re-sync of the agent's .lake"
  (cd "$INCOGNITA_REPO" && timeout -k 60 3600 bash scripts/build.sh Incognita >/dev/null 2>&1) \
    || { log "build of main failed: .lake not re-synced"; return 1; }
  # rsync runs as root into the agent's home: refuse if the agent replaced a directory by a link.
  # No agent process runs between tasks (each session is a systemd unit, killed when it ends).
  if sudo -n test -L "$INCOGNITA_AGENT_HOME/work" || sudo -n test -L "$INCOGNITA_AGENT_HOME/work/.lake"; then
    log "refused: the agent's work or work/.lake is a symbolic link"; return 1
  fi
  sudo -n rsync -a --delete --chown="$INCOGNITA_AGENT_USER:$INCOGNITA_AGENT_USER" \
    "$INCOGNITA_REPO/.lake/" "$INCOGNITA_AGENT_HOME/work/.lake/" || return 1
  # The toolchain is installed by the agent's own elan, inside the sandbox (no token).
  run_sandboxed "incognita-elan-$(date +%s)" 1800 no - -- \
    "$INCOGNITA_AGENT_HOME/.elan/bin/elan" toolchain install "$(show_main lean-toolchain)" </dev/null >/dev/null 2>&1 \
    || log "elan toolchain install failed (lake will retry inside the session)"
  printf '%s\n' "$want" | sudo -n tee "$INCOGNITA_EXCHANGE/lake.stamp" >/dev/null
}
