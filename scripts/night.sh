#!/usr/bin/env bash
# One night of Incognita: startup checks, then scripts/loop.sh until the deadline (restarted if it
# dies), then the night report. See agents/README.md ("Launching a night").
#
# Usage (in tmux, in the loop's clone of main):
#   INCOGNITA_PACE=0:100 INCOGNITA_DEADLINE=02:45 bash scripts/night.sh
#   INCOGNITA_DRY_RUN=1 INCOGNITA_DEADLINE=02:45 bash scripts/night.sh    checks + one dry pass
#
# Exit: 0 night done (report written), 1 a startup check failed (report written), 2 usage.
set -u -o pipefail
# shellcheck source=scripts/lib.sh
. "$(dirname "${BASH_SOURCE[0]}")/lib.sh"

[ -n "${INCOGNITA_DEADLINE:-}" ] || { echo "set INCOGNITA_DEADLINE=HH:MM (local time of the end)" >&2; exit 2; }
init_state || { echo "cannot create $INCOGNITA_STATE" >&2; exit 1; }
DEADLINE=$(deadline_epoch) || exit 2
export INCOGNITA_DEADLINE_EPOCH=$DEADLINE INCOGNITA_NIGHT
START=$(now)
export INCOGNITA_NIGHT_START=$START
LOG=$INCOGNITA_LOGS/$INCOGNITA_NIGHT.log
exec > >(tee -a "$LOG") 2>&1
export INCOGNITA_LOGGING=1   # loop.sh writes to our output, already logged

exec 9>"$INCOGNITA_HOME/night.lock"
flock -n 9 || { log "another scripts/night.sh is running (lock $INCOGNITA_HOME/night.lock)"; exit 1; }

LOOP_PID=""
STOP_REASON=""
on_signal() {
  STOP_REASON="interrupted (signal)"
  [ -n "$LOOP_PID" ] && kill -TERM "$LOOP_PID" 2>/dev/null && wait "$LOOP_PID" 2>/dev/null
  write_report
  exit 130
}

# ---------------------------------------------------------------- startup checks
FAILED=""
check() {  # description command...: run a check, remember the failures
  local what=$1; shift
  if "$@" >/dev/null 2>&1; then log "ok: $what"; else log "FAILED: $what"; FAILED="$FAILED
- $what"; fi
}
disk_ok() { [ "$(df -Pk "$1" | awk 'NR == 2 { print int($4 / 1048576) }')" -ge "${INCOGNITA_MIN_DISK_GB:-10}" ]; }
on_main() { [ "$(repo_git rev-parse --abbrev-ref HEAD)" = main ]; }
clean_tree() { [ -z "$(repo_git status --porcelain --untracked-files=no)" ]; }
no_worker() { ! pgrep -u "$(id -u)" -f 'tauceti .*work' >/dev/null; }
pacer_ok() { case "${INCOGNITA_PACE:-}" in 0:100|off) return 0 ;; *) command -v tauceti ;; esac; }
agent_ok() {
  id -u "$INCOGNITA_AGENT_USER" && sudo -n test -d "$INCOGNITA_AGENT_HOME/work/.git" \
    && sudo -n test -x "$INCOGNITA_AGENT_HOME/.local/bin/claude" \
    && sudo -n test -x "$INCOGNITA_AGENT_HOME/.elan/bin/lake" \
    && [ -d "$INCOGNITA_EXCHANGE/in" ] && [ -d "$INCOGNITA_EXCHANGE/out" ] && [ -d "$INCOGNITA_EXCHANGE/template" ]
}
token_set() { sudo -n grep -qE '^CLAUDE_CODE_OAUTH_TOKEN=sk-ant-' "$INCOGNITA_AGENT_ENV"; }
claude_login() {  # one tiny session in the sandbox, as a task would run
  local out
  out=$(printf 'Reply with the single word OK.\n' | run_sandboxed "incognita-login-$(date +%s)" 300 yes - -- \
    "$INCOGNITA_AGENT_HOME/.local/bin/claude" -p --output-format json --model "$INCOGNITA_MODEL_REVIEWER" \
    --max-turns 1 2>/dev/null | head -c 100000)
  is_dry && return 0
  [ "$(printf '%s' "$out" | jq -r '.is_error' 2>/dev/null)" = false ]
}

log "== night $INCOGNITA_NIGHT: deadline $(date -d "@$DEADLINE" '+%F %T'), pace ${INCOGNITA_PACE:-default}, repo $INCOGNITA_REPO"
check "the loop's clone is on main" on_main
check "the loop's clone has no local change" clean_tree
repo_git worktree prune >/dev/null 2>&1
check "main can be fetched and fast-forwarded" sync_main
check "at least ${INCOGNITA_MIN_DISK_GB:-10} GB free in $HOME" disk_ok "$HOME"
check "gh is logged in" gh auth status
check "the loop's GitHub account is known" owner_login
have_tools() { local t; for t in jq python3 git flock systemd-run rsync sudo; do command -v "$t" || return 1; done; }
check "jq, python3, git, flock, systemd-run, rsync, sudo are installed" have_tools
check "sudo works without password" sudo -n true
check "the agent user is set up (scripts/server/setup-agent-user.sh)" agent_ok
check "a Claude token is in $INCOGNITA_AGENT_ENV" token_set
check "the quota pacer is available (or INCOGNITA_PACE=0:100)" pacer_ok
check "the Tau Ceti worker is not running (never both at once)" no_worker
owner_login >/dev/null 2>&1
if [ -z "$FAILED" ] && [ "${INCOGNITA_CHECK_LOGIN:-1}" = 1 ]; then
  check "Claude answers in the sandbox (token valid, quota left)" claude_login
fi

# ---------------------------------------------------------------- the night report (basic)
iso() { date -u -d "@$1" +%Y-%m-%dT%H:%M:%SZ; }
ev() { [ -f "$NIGHT_DIR/events.tsv" ] && awk -F'\t' -v k="$1" '$2 == k' "$NIGHT_DIR/events.tsv"; }
or_none() { local x; x=$(cat); if [ -n "$x" ]; then printf '%s\n' "$x"; else echo "(none)"; fi; }
write_report() {
  local f=$INCOGNITA_LOGS/$INCOGNITA_NIGHT-report.md end merged n title body role p
  end=$(now)
  [ -n "$STOP_REASON" ] || STOP_REASON="deadline"
  merged=$(ghr pr list --state merged --limit 200 --search "merged:>=$(iso "$START")" \
    --json number,title,body,headRefOid,url 2>/dev/null || echo '[]')
  audit_status > "$NIGHT_DIR/audit-end.txt" 2>/dev/null || true
  {
    printf '# Night report %s\n\n' "$INCOGNITA_NIGHT"
    printf '%s → %s (server time). Stopped: %s.\n\n' "$(date -d "@$START" '+%F %H:%M')" "$(date -d "@$end" '+%F %H:%M')" "$STOP_REASON"
    if [ -n "$FAILED" ]; then printf '**Startup checks failed; nothing was run:**%s\n\n' "$FAILED"; fi

    echo "## 1. Decisions waiting for the owner"
    echo
    { ghr pr list --state open --label needs-human --limit 200 --json number,title,url \
      --jq '.[] | "- needs-human: [#\(.number)](\(.url)) \(.title)"' 2>/dev/null
    ev owner-merge | awk -F'\t' '{ print $4 "\t" $5 }' | sort -u -k1,1n | while IFS=$'\t' read -r n why; do
      [ "$(gh pr view "$n" --json state --jq .state 2>/dev/null)" = OPEN ] && echo "- to merge by the owner: #$n ($why)"
    done
    ghr pr list --state open --limit 200 --json number,title,headRefName,isCrossRepository \
      --jq '.[] | select(.isCrossRepository == false and (.headRefName | startswith("agent/") | not)) | "- human pull request open: #\(.number) \(.title)"' 2>/dev/null
    ev ask-owner | awk -F'\t' '{ print "- question (from #" $4 ", " $3 "): " $5 }'
    } | or_none
    echo

    echo "## 2. Papers accepted tonight"
    echo
    printf '%s' "$merged" | jq -r '.[] | select((.body // "") | split("\n")[0] | test("^Role: `(write-paper|revise)`")) | "\(.number)\t\(.headRefOid)\t\(.url)\t\(.title)"' 2>/dev/null \
      | while IFS=$'\t' read -r n h url title; do
          echo "- [#$n]($url) $title"
          statuses_of "$h" 2>/dev/null | awk -F'\t' '$1 ~ /^Referee/ && $3 == "yes" { print "  - " $1 ": " $4 }'
          for p in $(gh pr view "$n" --json files --jq '.files[].path' 2>/dev/null | sed -n -E 's#^papers/([^/]+)/paper\.tex$#\1#p' | sort -u); do
            show_main "papers/$p/paper.tex" | sed -n '/\\begin{abstract}/,/\\end{abstract}/p' | sed '1d;$d' | head -n 3 | sed 's/^/  > /'
          done
          echo "  - PDF: artifact of the CI run of $url (tab Checks)"
        done | or_none
    echo

    echo "## 3. Statements frozen tonight"
    echo
    printf '%s' "$merged" | jq -r '.[] | select((.body // "") | split("\n")[0] | test("^Role: `formalize-statements`")) | "\(.number)\t\(.url)\t\(.title)"' 2>/dev/null \
      | while IFS=$'\t' read -r n url title; do
          echo "- [#$n]($url) $title"
          gh pr view "$n" --json files --jq '.files[].path | select(startswith("Statements/") and endswith(".lean"))' 2>/dev/null | sed 's/^/  - `/; s/$/`/'
        done | or_none
    echo

    echo "## 4. Results verified tonight"
    echo
    if [ -s "$NIGHT_DIR/audit-end.txt" ]; then
      awk 'NR == FNR { s[$1 " " $2] = $3; next } $3 == "proved" && s[$1 " " $2] != "proved" { print "- `" $1 " " $2 "` proved" }
           $3 == "refuted" && s[$1 " " $2] != "refuted" { print "- `" $1 " " $2 "` REFUTED" }' \
        "$NIGHT_DIR/audit-start.txt" "$NIGHT_DIR/audit-end.txt" 2>/dev/null | or_none
    else echo "(no frozen statement, or the audit of main is unknown)"; fi
    echo

    echo "## 5. Papers rejected tonight"
    echo
    ev rejected | awk -F'\t' '{ print "- #" $4 ": " $5 }' | or_none
    echo

    echo "## 6. Machine statistics"
    echo
    echo "<details><summary>Tasks, merges, waits</summary>"
    echo
    echo "| Role | ok | fail | skip |"
    echo "|---|---|---|---|"
    ev task | awk -F'\t' '{ split($5, w, " "); c[$3 "\t" w[1]]++; r[$3] = 1 }
      END { for (x in r) printf "| %s | %d | %d | %d |\n", x, c[x "\tok"], c[x "\tfail"], c[x "\tskip"] }' | sort
    echo
    echo "- merges: $(ev merge | wc -l | tr -d ' '); mechanical rebases: $(ev rebase | wc -l | tr -d ' '); CI reruns: $(ev ci-rerun | wc -l | tr -d ' ')"
    echo "- quota waits: $(ev quota-wait | awk -F'\t' '{ s += $5 + 0 } END { print int(s / 60) }') min; idle: $(ev idle | awk -F'\t' '{ s += $5 + 0 } END { print int(s / 60) }') min"
    echo "- parked targets: $(ev parked | awk -F'\t' '{ printf "%s %s; ", $3, $4 }')"
    echo "- loop restarts: $(ev loop-died | wc -l | tr -d ' ')"
    echo
    echo "Tasks:"
    echo
    ev task | awk -F'\t' '{ print "- " substr($1, 12, 5) " " $3 " " $4 ": " $5 }'
    echo
    echo "</details>"
  } > "$f"
  log "night report: $f"
  if ! is_dry && owner_login >/dev/null 2>&1; then
    local issue m
    m=$(repo_git rev-parse origin/main 2>/dev/null)
    if issue=$(pinned_issue "Night reports"); then
      sanitize 60000 < "$f" > "$f.post"
      post_comment "$issue" night-report "${m:-0000000000000000000000000000000000000000}" "$f.post" >/dev/null \
        && log "posted on issue #$issue"
      rm -f "$f.post"
    fi
  fi
}

if [ -n "$FAILED" ] && is_dry; then
  log "dry run: startup checks failed (above); the dry pass runs anyway"
elif [ -n "$FAILED" ]; then
  STOP_REASON="startup checks failed"
  record_event stop - - "startup checks failed"
  write_report
  exit 1
fi
trap on_signal INT TERM
audit_status > "$NIGHT_DIR/audit-start.txt" 2>/dev/null || true
sync_agent_lake || log "warning: the agent's .lake could not be re-synced"

# ---------------------------------------------------------------- run the loop, restart it if it dies
if is_dry; then
  bash "$INCOGNITA_SCRIPTS/loop.sh"
  STOP_REASON="dry run"
  write_report
  exit 0
fi
deaths=""
while [ "$(remaining)" -gt 0 ]; do
  bash "$INCOGNITA_SCRIPTS/loop.sh" &
  LOOP_PID=$!
  rc=0; wait "$LOOP_PID" || rc=$?
  LOOP_PID=""
  case "$rc" in
    0) STOP_REASON="deadline"; break ;;
    3) STOP_REASON="Claude logged out: renew the token in $INCOGNITA_AGENT_ENV (claude setup-token)"; break ;;
  esac
  log "== loop.sh died (exit $rc): restarting"
  record_event loop-died - - "exit $rc"
  deaths="$deaths $(now)"
  # 3 deaths in 10 minutes: pause 20 minutes (D14).
  recent=0
  for d in $deaths; do [ $(( $(now) - d )) -le 600 ] && recent=$(( recent + 1 )); done
  if [ "$recent" -ge 3 ]; then
    log "== 3 deaths in 10 min: pausing 20 min"
    record_event pause - - "3 loop deaths in 10 min"
    deaths=""
    sleep_bounded 1200
  else
    sleep_bounded 30
  fi
done
[ "$(remaining)" -le 0 ] && [ -z "$STOP_REASON" ] && STOP_REASON="deadline"
write_report
exit 0
