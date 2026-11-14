#!/usr/bin/env bash
# One night of Incognita: startup checks, then scripts/loop.sh until the deadline (restarted if it
# dies), then the night report. See agents/README.md ("Launching a night").
#
# Normally started by scripts/start-night.sh (the owner's one command: end time in Paris, weekly cap,
# a new token, tmux). By hand (in tmux, in the loop's clone of main):
#   INCOGNITA_PACE=0:100 INCOGNITA_DEADLINE=02:45 INCOGNITA_WEEKLY_CAP=88 bash scripts/night.sh
#   INCOGNITA_DRY_RUN=1 INCOGNITA_DEADLINE=02:45 bash scripts/night.sh    checks + one dry pass
#   bash scripts/night.sh --reset-token     only remove the Claude token from the agents' env file
#
# Token hygiene (the owner's choice, agents/README.md): a new token before every launch in
# /etc/incognita/agent.env (scripts/start-night.sh creates it with `claude setup-token`); at the end
# of every night (normal end, a failed startup check, the weekly cap, Ctrl-C or TERM) this script puts
# the placeholder REPLACE_ME back, so that no token stays on the server or in its snapshots. A dry run
# leaves it.
#
# Exit: 0 night done (report written), 1 a startup check failed (report written), 2 usage.
set -u -o pipefail
# shellcheck source=scripts/lib.sh
. "$(dirname "${BASH_SOURCE[0]}")/lib.sh"

# reset_token (scripts/lib.sh): the agents' env file gets the placeholder again (root, mode 600).
if [ "${1:-}" = --reset-token ]; then reset_token; exit 0; fi

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
# From here on, whatever the way out, the token is removed at the end (not by a dry run, and not
# above: another night may be running). A signal during the startup checks exits through it too.
is_dry || trap reset_token EXIT
trap 'exit 143' TERM INT HUP

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
no_worker() { ! tauceti_running; }
cap_valid() { [ -z "$INCOGNITA_WEEKLY_CAP" ] || parse_cap "$INCOGNITA_WEEKLY_CAP"; }
pacer_ok() { case "${INCOGNITA_PACE:-}" in 0:100|off) return 0 ;; *) command -v tauceti ;; esac; }
agent_ok() {
  # ~/work: a directory (each task rebuilds its repository from the bundle, and repairs it once).
  id -u "$INCOGNITA_AGENT_USER" && sudo -n test -d "$INCOGNITA_AGENT_HOME/work" && ! sudo -n test -L "$INCOGNITA_AGENT_HOME/work" \
    && [ -x "$AGENT_CLAUDE" ] && [ "$(stat -c %U "$AGENT_CLAUDE")" = root ] \
    && sudo -n test -x "$INCOGNITA_AGENT_HOME/.elan/bin/lake" \
    && [ -d "$INCOGNITA_EXCHANGE/in" ] && [ -d "$INCOGNITA_EXCHANGE/out" ] && [ -d "$INCOGNITA_EXCHANGE/template" ]
}
claude_login() {  # one tiny session in the sandbox, as a task would run
  local out
  out=$(printf 'Reply with the single word OK.\n' | run_sandboxed "incognita-login-$(date +%s)" 300 yes - -- \
    "$AGENT_CLAUDE" -p --output-format json --model "$INCOGNITA_MODEL_REVIEWER" \
    --max-turns 1 2>/dev/null | head -c 100000)
  is_dry && return 0
  [ "$(printf '%s' "$out" | jq -r '.is_error' 2>/dev/null)" = false ]
}

log "== night $INCOGNITA_NIGHT: deadline $(date -d "@$DEADLINE" '+%F %T %Z') ($(TZ=$PARIS_TZ date -d "@$DEADLINE" '+%F %H:%M') in Paris), pace ${INCOGNITA_PACE:-default}, weekly cap ${INCOGNITA_WEEKLY_CAP:-none}${INCOGNITA_WEEKLY_CAP:+ %}, repo $INCOGNITA_REPO"
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
check "a Claude token is in $INCOGNITA_AGENT_ENV (it is removed after every night: run \`claude setup-token\`, then \`sudo nano $INCOGNITA_AGENT_ENV\` and replace REPLACE_ME)" token_set
if ! token_set >/dev/null 2>&1; then
  log "no Claude token: the night cannot start. Create one with \`claude setup-token\` (it prints sk-ant-oat01-...),"
  log "put it in $INCOGNITA_AGENT_ENV (line CLAUDE_CODE_OAUTH_TOKEN=..., sudo nano), then launch again."
fi
check "the quota pacer is available (or INCOGNITA_PACE=0:100)" pacer_ok
check "the Tau Ceti worker is not running (never both at once)" no_worker
check "the weekly cap INCOGNITA_WEEKLY_CAP is empty or a percentage from 1 to 100" cap_valid
# The weekly usage of the subscription at the start (night report), read with the token. With a cap,
# a token the usage endpoint refuses, or a usage already at the cap, stops the night here.
USAGE_START="not read (no token)"
if token_set; then
  if USAGE_START=$(usage_now 0); then
    log "weekly usage at the start: $(usage_text "$USAGE_START") (cap ${INCOGNITA_WEEKLY_CAP:-none}${INCOGNITA_WEEKLY_CAP:+ %})"
    if [ "$(cap_decision "${USAGE_START%% *}" "$INCOGNITA_WEEKLY_CAP")" = stop ]; then
      log "FAILED: the weekly usage is below the cap"; FAILED="$FAILED
- the weekly usage ($(usage_text "$USAGE_START")) is below the cap ($INCOGNITA_WEEKLY_CAP %)"
    fi
  else
    log "the weekly usage cannot be read with the token: $USAGE_START"
    if [ -n "$INCOGNITA_WEEKLY_CAP" ] && usage_persistent "$USAGE_START"; then
      log "FAILED: the weekly usage can be read with the token (INCOGNITA_WEEKLY_CAP is set)"; FAILED="$FAILED
- the weekly usage can be read with the token ($USAGE_START), as INCOGNITA_WEEKLY_CAP needs"
    fi
  fi
fi
owner_login >/dev/null 2>&1
if [ -z "$FAILED" ] && [ "${INCOGNITA_CHECK_LOGIN:-1}" = 1 ]; then
  check "Claude answers in the sandbox (token valid, quota left)" claude_login
fi

# ---------------------------------------------------------------- the night report (basic)
iso() { date -u -d "@$1" +%Y-%m-%dT%H:%M:%SZ; }
# proposals_md: the open roadmap proposals and what they wait for (AGENTS.md section 4).
proposals_md() {
  local prs n h title st rv lp tc w
  prs=$(ghr pr list --state open --limit 200 --json number,title,body,headRefOid,headRefName,isCrossRepository,author 2>/dev/null) || return 0
  printf '%s' "$prs" | jq -r --arg o "${OWNER:-}" '.[] | select(.isCrossRepository == false and .author.login == $o
      and (.headRefName | startswith("agent/")) and ((.body // "") | startswith("Role: `propose-roadmap`")))
    | "\(.number)\t\(.headRefOid)\t\(.title)"' | while IFS=$'\t' read -r n h title; do
    st=$(statuses_of "$h" 2>/dev/null) || st=""
    rv=$(verdict_in "$st" "Incognita review" review-roadmap)
    lp=$(verdict_in "$st" "Incognita loop" loop)
    tc=$(trusted_comments "$n" 2>/dev/null) || tc='[]'
    w=$(jq -r '[.[] | select(.kind == "veto-window" or .kind == "owner-approval")] | last | if . == null then ""
      elif .kind == "owner-approval" then "waits for your approval (new domain): comment `approve` or `veto`"
      else (.body | capture("Window: (?<s>[0-9-]+) to (?<e>[0-9-]+)") | "veto window until the night of \(.e): comment `veto` to stop it, `approve` to approve at once") // "" end' <<< "$tc")
    if [ "$lp" = approved ]; then echo "- roadmap proposal #$n ($title): approved by the loop, merged after CI"
    elif [ "$rv" = approve ]; then echo "- roadmap proposal #$n ($title): ${w:-approved by review-roadmap; the veto window opens at the next pass}"
    else echo "- roadmap proposal #$n ($title): review-roadmap verdict: $rv"; fi
  done
}
ev() { [ -f "$NIGHT_DIR/events.tsv" ] && awk -F'\t' -v k="$1" '$2 == k' "$NIGHT_DIR/events.tsv"; }
or_none() { local x; x=$(cat); if [ -n "$x" ]; then printf '%s\n' "$x"; else echo "(none)"; fi; }
write_report() {
  local f=$INCOGNITA_LOGS/$INCOGNITA_NIGHT-report.md end merged n title body role p
  end=$(now)
  [ -n "$STOP_REASON" ] || STOP_REASON="deadline"
  merged=$(ghr pr list --state merged --limit 200 --search "merged:>=$(iso "$START")" \
    --json number,title,body,headRefOid,url 2>/dev/null || echo '[]')
  audit_status > "$NIGHT_DIR/audit-end.txt" 2>/dev/null || true
  # The weekly usage at the end, read before the token is removed (the EXIT trap removes it after).
  local usage_end="not read (no token)" wreset
  if token_set; then usage_end=$(usage_now 0) || true; fi
  wreset=$(printf '%s\n%s\n' "$usage_end" "$USAGE_START" | awk '$1 ~ /^[0-9.]+$/ && $2 ~ /^[0-9]+$/ { print $2; exit }')
  {
    printf '# Night report %s\n\n' "$INCOGNITA_NIGHT"
    printf '%s → %s (server time). Stopped: %s.\n\n' "$(date -d "@$START" '+%F %H:%M')" "$(date -d "@$end" '+%F %H:%M')" "$STOP_REASON"
    printf 'Weekly usage of the subscription (claude.ai, Settings, Usage): %s at the start, %s at the end; cap %s%s.\n\n' \
      "$(usage_text "$USAGE_START")" "$(usage_text "$usage_end")" "${INCOGNITA_WEEKLY_CAP:-none}${INCOGNITA_WEEKLY_CAP:+ % (INCOGNITA_WEEKLY_CAP)}" \
      "${wreset:+; weekly reset $(date -u -d "@$wreset" '+%F %H:%M UTC')}"
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
    ev ask-owner | awk -F'\t' '{ print "- question (from " ($4 ~ /^[0-9]+$/ ? "#" : "") $4 ", " $3 "): " $5 }'
    proposals_md
    certify_py disputed-deps 2>/dev/null | awk '{ print "- " $1 " depends on " $2 ", which is " $3 ": its certification is capped (dependency check once " $2 " has a new version)" }'
    parked_list | while read -r k; do
      echo "- parked after $INCOGNITA_PARK_AFTER failures: \`$k\` (role_target; delete \`$INCOGNITA_STATE/parked/$k\` to retry)"
    done
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
          echo "  - PDF: artifact \`papers-pdf\` of the run of the workflow Papers on $url (tab Checks)"
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

    echo "## 6. Roadmaps and directions"
    echo
    { ev roadmap-approved | awk -F'\t' '{ print "- roadmap proposal #" $4 " approved: " $5 }'
      ev roadmap-vetoed | awk -F'\t' '{ print "- roadmap proposal #" $4 " vetoed by the owner: " $5 }'
      ev directions | awk -F'\t' '{ print "- candidate directions from #" $4 ": " $5 }'
      ev exhausted | awk -F'\t' '{ print "- " $4 ": a writer found no open item (a roadmap proposal follows)" }'
      certify_py depchecks 2>/dev/null | awk '{ print "- dependency check pending: " $1 " (" $2 ")" }'
    } | or_none
    echo

    echo "## 7. Certification of the library"
    echo
    if [ -s "$NIGHT_DIR/audit-end.txt" ]; then certify_py report --audit "$NIGHT_DIR/audit-end.txt" 2>&1 | sed '1,2d'
    else certify_py report 2>&1 | sed '1,2d'; fi
    echo

    echo "## 8. Machine statistics"
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
    echo "- parked targets (tonight): $(ev parked | awk -F'\t' '{ printf "%s %s; ", $3, $4 }')"
    echo "- parked targets (all; delete the file in $INCOGNITA_STATE/parked/ to retry): $(ls "$INCOGNITA_STATE/parked" 2>/dev/null | tr '\n' ' ')"
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
trap on_signal INT TERM HUP
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
    6) STOP_REASON="weekly cap reached ($(ev weekly-cap | tail -n 1 | cut -f5))"; break ;;
    7) STOP_REASON="the agent's ~/work could not be prepared, even after one automatic repair (see the log: the preparation's last lines); check the server (disk, sudo bash scripts/server/setup-agent-user.sh --check) before the next night"; break ;;
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
