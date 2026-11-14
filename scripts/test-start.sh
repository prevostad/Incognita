#!/usr/bin/env bash
# Offline tests of the launcher (scripts/start-night.sh) and of the weekly cap: the end of a night in
# Paris time (changes of hour included), the cap, the answers of the usage endpoint (fake JSON, a fake
# curl), the decisions before a task (usage_gate), the agents' env file, and the capture of the token
# from a fake `claude setup-token`. Needs bash, GNU date with the zone Europe/Paris, python3, jq.
# No network, no sudo, no Claude. Usage: bash scripts/test-start.sh
# shellcheck disable=SC2034  # variables are read inside the eval'd checks
set -u -o pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
t=$(mktemp -d)
trap 'rm -rf "$t"' EXIT
export INCOGNITA_HOME=$t/home INCOGNITA_NIGHT=test INCOGNITA_GH_REPO=owner/repo INCOGNITA_REPO=$t/repo
export INCOGNITA_AGENT_ENV=$t/etc/agent.env   # a throwaway env file, never the real one
export INCOGNITA_TAUCETI_BIN=$t/bin/tauceti    # a fake Tau Ceti pacer, never the real one
mkdir -p "$INCOGNITA_REPO" "$t/etc" "$t/bin"
# shellcheck source=scripts/lib.sh
. "$here/lib.sh"
init_state
AS_ROOT=() AGENT_ENV_READ=(cat --)   # as ourselves (the loop runs them through sudo)
fails=0
ok() { if eval "$2"; then echo "ok   $1"; else echo "FAIL $1"; fails=$(( fails + 1 )); fi; }
ep() { date -u -d "$1" +%s; }
refused_all() { local s; for s in "$@"; do end_epoch "$s" "$n" >/dev/null 2>&1 && { echo "accepted: $s"; return 1; }; done; return 0; }
all_short() { local r; for r in "$@"; do short_role "$r" || return 1; done; }
exit_code() { "$@" >/dev/null 2>&1; echo $?; }

# ---- the end of a night, in Paris time
n=$(ep "2026-11-15 18:58 UTC")   # Sunday 15/11 19:58 in Paris (CET, UTC+1)
ok "02:45 on Sunday evening: Monday 02:45 in Paris, 01:45 UTC" '[ "$(end_epoch 02:45 "$n")" = "$(ep "2026-11-16 01:45 UTC")" ]'
ok "what the owner reads" '[ "$(describe_end "$(end_epoch 02:45 "$n")" "$n")" = "lundi 16/11 à 02:45 (heure de Paris), dans 6 h 47" ]'
ok "H:MM is HH:MM" '[ "$(end_epoch 2:45 "$n")" = "$(end_epoch 02:45 "$n")" ]'
ok "a time later the same evening" '[ "$(end_epoch 23:30 "$n")" = "$(ep "2026-11-15 22:30 UTC")" ]'
n=$(ep "2026-11-16 00:00 UTC")   # Monday 01:00 in Paris
ok "after midnight: the same day" '[ "$(end_epoch 02:45 "$n")" = "$(ep "2026-11-16 01:45 UTC")" ]'
ok "the time it is now: the next day" '[ "$(end_epoch 01:00 "$n")" = "$(ep "2026-11-17 00:00 UTC")" ]'
n=$(ep "2026-07-05 19:00 UTC")   # Sunday 05/07 21:00 in Paris (CEST, UTC+2)
ok "summer time: 02:45 in Paris is 00:45 UTC" '[ "$(end_epoch 02:45 "$n")" = "$(ep "2026-07-06 00:45 UTC")" ]'
ok "summer: what the owner reads" '[ "$(describe_end "$(end_epoch 02:45 "$n")" "$n")" = "lundi 06/07 à 02:45 (heure de Paris), dans 5 h 45" ]'
n=$(ep "2027-03-27 21:00 UTC")   # Saturday 27/03 22:00 CET; Sunday 28/03 02:00 CET -> 03:00 CEST
ok "spring change of hour: 03:30 CEST is 01:30 UTC" '[ "$(end_epoch 03:30 "$n")" = "$(ep "2027-03-28 01:30 UTC")" ]'
ok "spring: the time left is real time (4 h 30, not 5 h 30)" '[ "$(describe_end "$(end_epoch 03:30 "$n")" "$n")" = "dimanche 28/03 à 03:30 (heure de Paris), dans 4 h 30" ]'
ok "spring: 02:30 does not exist that night: refused" '! end_epoch 02:30 "$n" 2>/dev/null'
n=$(ep "2026-10-24 20:00 UTC")   # Saturday 24/10 22:00 CEST; Sunday 25/10 03:00 CEST -> 02:00 CET
ok "autumn change of hour: 04:00 CET is 03:00 UTC (7 h)" '[ "$(end_epoch 04:00 "$n")" = "$(ep "2026-10-25 03:00 UTC")" ] && [ "$(describe_end "$(end_epoch 04:00 "$n")" "$n")" = "dimanche 25/10 à 04:00 (heure de Paris), dans 7 h" ]'
n=$(ep "2026-11-15 18:58 UTC")
ok "durations: 8h, 6h45, 6h45m, 6H45, 45m, 90m, 24h" '[ "$(end_epoch 8h "$n")" = $(( n + 28800 )) ] && [ "$(end_epoch 6h45 "$n")" = $(( n + 24300 )) ] && [ "$(end_epoch 6h45m "$n")" = $(( n + 24300 )) ] && [ "$(end_epoch 6H45 "$n")" = $(( n + 24300 )) ] && [ "$(end_epoch 45m "$n")" = $(( n + 2700 )) ] && [ "$(end_epoch 90m "$n")" = $(( n + 5400 )) ] && [ "$(end_epoch 24h "$n")" = $(( n + 86400 )) ]'
ok "a duration reads as such" '[ "$(describe_end "$(end_epoch 45m "$n")" "$n")" = "dimanche 15/11 à 20:43 (heure de Paris), dans 45 min" ] && [ "$(describe_end "$(end_epoch 8h "$n")" "$n")" = "lundi 16/11 à 03:58 (heure de Paris), dans 8 h" ]'
n=$(ep "2027-03-27 21:00 UTC")
ok "a duration across the change of hour is real time" '[ "$(end_epoch 6h "$n")" = "$(ep "2027-03-28 03:00 UTC")" ]'
n=$(ep "2026-11-15 18:58 UTC")
ok "refused: 0h, 0m, 25h, 1441m, 6h75, 2:61, 24:00, 6:5, 02-45, abc, empty" 'refused_all 0h 0m 25h 1441m 6h75 2:61 24:00 6:5 02-45 abc ""'
ok "the cap: 88%, 88, 100%" '[ "$(parse_cap 88%)" = 88 ] && [ "$(parse_cap 88)" = 88 ] && [ "$(parse_cap 100%)" = 100 ] && [ "$(parse_cap 07)" = 7 ]'
ok "the cap: refused 0, 101, 8.5, abc, empty" '! parse_cap 0 2>/dev/null && ! parse_cap 101% 2>/dev/null && ! parse_cap 8.5 2>/dev/null && ! parse_cap abc 2>/dev/null && ! parse_cap "" 2>/dev/null'

# ---- the answer of the usage endpoint (its format in November 2026, as cached by the Tau Ceti pacer)
cat > "$t/u-real.json" <<'EOF'
{"five_hour":{"utilization":74.0,"resets_at":"2026-11-14T01:10:00.336884+00:00","limit_dollars":null},
 "seven_day":{"utilization":39.0,"resets_at":"2026-11-16T02:00:00.336904+00:00","limit_dollars":null},
 "seven_day_oauth_apps":null,"seven_day_opus":null,"seven_day_sonnet":null,
 "extra_usage":{"is_enabled":false,"utilization":null},
 "limits":[{"kind":"session","group":"session","percent":74,"severity":"normal","resets_at":"2026-11-14T01:10:00.336884+00:00","scope":null,"is_active":true},
           {"kind":"weekly_all","group":"weekly","percent":39,"severity":"normal","resets_at":"2026-11-16T02:00:00.336904+00:00","scope":null,"is_active":false},
           {"kind":"weekly_scoped","group":"weekly","percent":95,"severity":"normal","resets_at":"2026-11-16T02:00:00+00:00","scope":{"model":{"id":null,"display_name":"Fable"},"surface":null},"is_active":false}]}
EOF
ok "usage: weekly 39 %, its reset, session 74 %, its reset; the model-scoped weekly is ignored" '[ "$(usage_parse < "$t/u-real.json")" = "39 $(ep "2026-11-16 02:00:00 UTC") 74 $(ep "2026-11-14 01:10:00 UTC")" ]'
jq 'del(.limits)' "$t/u-real.json" > "$t/u-flat.json"
ok "usage: the flat records seven_day and five_hour without limits[]" '[ "$(usage_parse < "$t/u-flat.json")" = "39 $(ep "2026-11-16 02:00:00 UTC") 74 $(ep "2026-11-14 01:10:00 UTC")" ]'
jq '.limits[1].percent = 87 | .seven_day.utilization = 12' "$t/u-real.json" > "$t/u-both.json"
ok "usage: limits[] wins over the flat record" '[ "$(usage_parse < "$t/u-both.json" | cut -d" " -f1)" = 87 ]'
echo '{"five_hour":null,"seven_day":{"utilization":87.5,"resets_at":"2026-11-16T02:00:00Z"}}' > "$t/u-null.json"
ok "usage: a null five-hour window is 0 %; a decimal figure, a Z time" '[ "$(usage_parse < "$t/u-null.json")" = "87.5 $(ep "2026-11-16 02:00:00 UTC") 0 -" ]'
echo '{"five_hour":{"utilization":3,"resets_at":null}}' > "$t/u-noweek.json"
ok "usage: no weekly figure, not JSON, not an object, a bad figure: unreadable" '! usage_parse < "$t/u-noweek.json" && ! echo "<html>" | usage_parse && ! echo "[1]" | usage_parse && ! echo "{\"seven_day\":{\"utilization\":\"x\"}}" | usage_parse'

# ---- decisions before a task
ok "cap: 50 go, 84.9 go, 85 short, 87 short, 88 stop, 93 stop (cap 88, margin 3)" '[ "$(cap_decision 50 88)$(cap_decision 84.9 88)$(cap_decision 85 88)$(cap_decision 87 88)$(cap_decision 88 88)$(cap_decision 93 88)" = gogoshortshortstopstop ]'
ok "cap: none set, always go" '[ "$(cap_decision 99 "")" = go ]'
ok "short roles near the cap: reviews, referees, bibliographer, garden" 'all_short referee-scope referee-proofs review-statements review-pr review-roadmap bibliographer garden'
ok "long roles near the cap: write-paper, prove, revise, formalize-statements, fix-pr, propose-roadmap" '! short_role write-paper && ! short_role prove && ! short_role revise && ! short_role formalize-statements && ! short_role fix-pr && ! short_role propose-roadmap'
ok "usage failures that waiting does not cure" 'usage_persistent "HTTP 401" && usage_persistent "HTTP 403" && usage_persistent "no token in x" && ! usage_persistent "HTTP 429" && ! usage_persistent "HTTP 000" && ! usage_persistent "HTTP 503"'

# ---- the agents' env file (a throwaway path) and the usage endpoint through a fake curl
TOK=sk-ant-oat01-AbCdEf_GhIjKl-MnOpQrStUvWxYz0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQ-Rs_tAA
ok "write_agent_token: the line, mode 600" 'printf "%s\n" "$TOK" | write_agent_token && grep -qx "CLAUDE_CODE_OAUTH_TOKEN=$TOK" "$INCOGNITA_AGENT_ENV" && [ "$(stat -c %a "$INCOGNITA_AGENT_ENV")" = 600 ] && token_set'
ok "write_agent_token: refuses what is not a token" '! printf "sk-ant-oat01-a b\n" | write_agent_token 2>/dev/null && grep -qx "CLAUDE_CODE_OAUTH_TOKEN=$TOK" "$INCOGNITA_AGENT_ENV"'
cat > "$t/bin/curl" <<'EOF'
#!/usr/bin/env bash
# fake curl: records its arguments and its standard input; answers $FAKE_DIR/usage.json with the
# status in $FAKE_DIR/usage.code
printf '%s\n' "$@" > "$FAKE_DIR/curl.args"
out=""; while [ $# -gt 0 ]; do case "$1" in -o) out=$2; shift 2 ;; *) shift ;; esac; done
cat > "$FAKE_DIR/curl.stdin"
cp "$FAKE_DIR/usage.json" "$out"
cat "$FAKE_DIR/usage.code"
EOF
chmod +x "$t/bin/curl"
export FAKE_DIR=$t
PATH=$t/bin:$PATH
cp "$t/u-real.json" "$t/usage.json"; echo 200 > "$t/usage.code"
code=$(usage_fetch "$t/answer.json")
ok "usage_fetch: HTTP 200 and the answer" '[ "$code" = 200 ] && cmp -s "$t/answer.json" "$t/u-real.json"'
ok "usage_fetch: the token is never in curl's arguments" '! grep -q "sk-ant" "$t/curl.args"'
ok "usage_fetch: the token goes to curl on stdin, as a header" '[ "$(cat "$t/curl.stdin")" = "header = \"Authorization: Bearer $TOK\"" ]'
ok "usage_fetch: the endpoint and the headers of the Tau Ceti pacer" 'grep -qx "https://api.anthropic.com/api/oauth/usage" "$t/curl.args" && grep -qx "anthropic-beta: oauth-2025-04-20" "$t/curl.args" && grep -qx -- "-K" "$t/curl.args"'
ok "usage_now: parsed, read with the agents' token, cached" '[ "$(usage_now 0)" = "39 $(ep "2026-11-16 02:00:00 UTC") 74 $(ep "2026-11-14 01:10:00 UTC") agent" ] && grep -q " ok 39 " "$INCOGNITA_STATE/usage-last"'
echo 403 > "$t/usage.code"
ok "usage_now: a fresh enough reading comes from the cache" '[ "$(usage_now 300 | cut -d" " -f1)" = 39 ]'
ok "usage_now: HTTP 403 (and no Tau Ceti) is a failure, cached as such" '! u=$(usage_now 0) && [ "$u" = "HTTP 403 (and none through tauceti status)" ] && usage_persistent "$u" && ! usage_now 300 >/dev/null'
echo 200 > "$t/usage.code"; echo 'not json' > "$t/usage.json"
ok "usage_now: an unreadable answer" '[ "$(usage_now 0)" = "unreadable answer of the usage endpoint (and none through tauceti status)" ]'
# The fallback: the Tau Ceti pacer, with lean's own login (its `status --json`, format of November 2026).
cat > "$t/bin/tauceti" <<'EOF'
#!/usr/bin/env bash
printf '%s\n' "$@" > "$FAKE_DIR/tauceti.args"
cat "$FAKE_DIR/status.json"
EOF
chmod +x "$t/bin/tauceti"
printf '%s' '{"quota": {"claude": {"name": "claude", "available": false, "windows": [{"name": "session", "used": 7.0, "elapsed": 7.2, "resets_at": 1794684000.06, "status": "over-pace"}, {"name": "weekly", "used": 53.0, "elapsed": 78.9, "resets_at": 1794794400.06, "status": "under-pace"}], "error": null}, "codex": {}}, "survey": {}}' > "$t/status.json"
echo 403 > "$t/usage.code"
ok "usage_now: the endpoint refuses the token: the figures of the Tau Ceti pacer (lean)" '[ "$(usage_now 0)" = "53 1794794400 7 1794684000 lean" ] && [ "$(tr "\n" " " < "$t/tauceti.args")" = "--conf $INCOGNITA_TAUCETI_CONF status --json " ]'
ok "usage_text says where the figure comes from" '[ "$(usage_text "53 1 7 2 lean")" = "53 % (read with lean'"'"'s Claude login (tauceti status))" ] && [ "$(usage_text "39 1 74 2 agent")" = "39 %" ] && [ "$(usage_text "HTTP 403")" = "unknown (HTTP 403)" ]'
printf '%s' '{"quota": {"claude": {"windows": [{"name": "weekly", "used": null, "resets_at": null, "status": "unknown"}], "error": "claude usage HTTP 401"}}}' > "$t/status.json"
ok "usage_now: lean's login expired too: a failure" '! usage_now 0 >/dev/null'
rm -f "$t/bin/tauceti"
printf 'CLAUDE_CODE_OAUTH_TOKEN=REPLACE_ME\n' > "$INCOGNITA_AGENT_ENV"; rm -f "$t/curl.args"
ok "usage_now: no token, no request" '[ "$(usage_now 0)" = "no token in $INCOGNITA_AGENT_ENV" ] && [ ! -e "$t/curl.args" ] && ! token_set'

# ---- usage_gate: a fake usage (one line per reading) and a fake sleep
FAKE_LINES=$t/readings
usage_now() {  # pops the next reading: "<w> <wr> <s> <sr>" or "ERR <reason>"
  local l; l=$(head -n 1 "$FAKE_LINES"); sed -i 1d "$FAKE_LINES"
  case "$l" in ERR\ *) echo "${l#ERR }"; return 1 ;; *) echo "$l" ;; esac
}
sleep_bounded() { echo "$1" >> "$t/slept"; [ "${FAKE_DEADLINE_AFTER_SLEEP:-}" = 1 ] && DEADLINE=1; return 0; }
gate() {  # cap readings...: runs usage_gate, sets G_RC, G_SHORT, G_SLEPT
  local c=$1; shift
  printf '%s\n' "$@" > "$FAKE_LINES"; : > "$t/slept"
  DEADLINE=$(( $(now) + 36000 )) INCOGNITA_WEEKLY_CAP=$c
  G_RC=0; usage_gate 2>>"$t/gate.log" || G_RC=$?
  G_SHORT=$CAP_SHORT_ONLY G_SLEPT=$(tr '\n' ' ' < "$t/slept")
}
gate 88 "50 - 10 -"
ok "gate: far from the cap, any task" '[ "$G_RC" = 0 ] && [ "$G_SHORT" = 0 ] && [ -z "$G_SLEPT" ]'
gate 88 "86 - 10 -"
ok "gate: within 3 points of the cap, short tasks only" '[ "$G_RC" = 0 ] && [ "$G_SHORT" = 1 ]'
gate 88 "88 - 10 -"
ok "gate: at the cap, the night stops (6), recorded for the report" '[ "$G_RC" = 6 ] && grep -q "weekly-cap.*weekly usage 88 % >= cap 88 %" "$NIGHT_DIR/events.tsv"'
gate 88 "ERR HTTP 503" "ERR HTTP 403" "50 - 10 -"
ok "gate: usage unknown with a cap: 10 min waits, then the task" '[ "$G_RC" = 0 ] && [ "$G_SLEPT" = "600 600 " ]'
gate "" "ERR HTTP 403"
ok "gate: usage unknown without a cap: the task starts" '[ "$G_RC" = 0 ] && [ -z "$G_SLEPT" ]'
gate 88 "50 - 100 $(( $(now) + 7200 ))" "50 - 2 -"
ok "gate: five-hour window exhausted: wait for its reset (+1 min)" '[ "$G_RC" = 0 ] && s=${G_SLEPT% } && [ "$s" -ge 7255 ] && [ "$s" -le 7260 ]'
FAKE_DEADLINE_AFTER_SLEEP=1 gate 88 "ERR HTTP 000" "50 - 10 -"
ok "gate: the deadline comes while waiting (1)" '[ "$G_RC" = 1 ]'
INCOGNITA_DRY_RUN=1 gate 88 "ERR HTTP 403" "50 - 10 -"
ok "gate: a dry run never waits" '[ "$G_RC" = 0 ] && [ -z "$G_SLEPT" ]'
unset -f usage_now sleep_bounded

# ---- the capture of the token (scripts/capture-token.py) from a fake `claude setup-token`
cat > "$t/bin/fake-claude" <<EOF
#!/usr/bin/env bash
# fake claude setup-token: the link, the code, then the token in pieces, inside escape sequences
[ "\${1:-}" = setup-token ] || exit 9
printf 'Browser did not open? Use the url below to sign in:\nhttps://claude.ai/oauth/authorize?code=true&client_id=x\n\nPaste code here if prompted > '
sleep 0.3
printf '\n\033[32m✓ Long-lived authentication token created successfully!\033[39m\n\nYour OAuth token (valid for 1 year):\n\n\033[1msk-a'
sleep 0.7
printf 'nt-oat01-${TOK:13:30}'
sleep 0.7
printf '${TOK:43}\033[22m\n\nStore this token securely. You won'"'"'t be able to see it again.\n'
printf '\nUse this token by setting: export CLAUDE_CODE_OAUTH_TOKEN=<token>\nbye s'
exit \${FAKE_RC:-0}
EOF
chmod +x "$t/bin/fake-claude"
cap() {  # runs the capture: C_RC, C_OUT (what the owner sees), C_TOK (what start-night.sh gets)
  C_RC=0
  C_TOK=$(python3 -I "$here/capture-token.py" --token-fd 3 -- "$@" 3>&1 1>"$t/screen" 2>"$t/screen.err" </dev/null) || C_RC=$?
  C_OUT=$(cat "$t/screen")
}
cap "$t/bin/fake-claude" setup-token
ok "capture: the token is handed over whole" '[ "$C_RC" = 0 ] && [ "$C_TOK" = "$TOK" ]'
ok "capture: no piece of it reaches the screen" '[[ "$C_OUT" != *"${TOK:13:8}"* && "$C_OUT" != *"${TOK:43:8}"* && "$C_OUT" != *"${TOK: -8}"* ]]'
ok "capture: the rest is shown (link, prompt, mask, end)" '[[ "$C_OUT" == *"https://claude.ai/oauth/authorize"* && "$C_OUT" == *"Paste code here"* && "$C_OUT" == *"sk-ant-oat01-[hidden]"* && "$C_OUT" == *"bye s"* ]]'
size=$(python3 -I "$here/capture-token.py" --token-fd 3 -- bash -c "stty size" 3>/dev/null </dev/null | tr -d '\r')
ok "capture: the command sees a wide terminal (the token is never wrapped)" '[[ "$size" =~ ^[0-9]+\ ([0-9]+)$ ]] && [ "${BASH_REMATCH[1]}" -ge 200 ]'
cat > "$t/bin/fake-none" <<'EOF'
#!/usr/bin/env bash
echo "Login cancelled. sk-ant-api"; exit ${FAKE_RC:-0}
EOF
chmod +x "$t/bin/fake-none"
cap "$t/bin/fake-none"
ok "capture: no token: exit 1, nothing handed over" '[ "$C_RC" = 1 ] && [ -z "$C_TOK" ] && [[ "$C_OUT" == *"Login cancelled. sk-ant-api"* ]]'
FAKE_RC=3 cap "$t/bin/fake-none"
ok "capture: the command failed: exit 4" '[ "$C_RC" = 4 ] && [ -z "$C_TOK" ]'
cap bash -c "echo sk-ant-oat01-${TOK:13:40}; echo sk-ant-oat01-ZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZ"
ok "capture: two different tokens: exit 2, none handed over, none shown" '[ "$C_RC" = 2 ] && [ -z "$C_TOK" ] && [[ "$C_OUT" != *ZZZZZZ* ]]'
cap bash -c "printf 'sk-ant-oat01-${TOK:13:40}'"
ok "capture: a token at the very end of the output" '[ "$C_RC" = 0 ] && [ "$C_TOK" = "sk-ant-oat01-${TOK:13:40}" ] && [[ "$C_OUT" != *"${TOK:13:8}"* ]]'
cap /nonexistent/claude setup-token
ok "capture: a command that cannot start: exit 4" '[ "$C_RC" = 4 ]'
ok "capture: without the token descriptor: usage (3)" 'python3 -I "$here/capture-token.py" --token-fd 7 -- true </dev/null >/dev/null 2>&1; [ $? = 3 ]'

# ---- start-night.sh: arguments
ok "start-night: usage without arguments (2)" '[ "$(exit_code bash "$here/start-night.sh")" = 2 ]'
ok "start-night: a bad end or cap (2)" '[ "$(exit_code bash "$here/start-night.sh" 25:00 88%)" = 2 ] && [ "$(exit_code bash "$here/start-night.sh" 02:45 120%)" = 2 ]'
ok "start-night: an unknown option (2)" '[ "$(exit_code bash "$here/start-night.sh" 02:45 88% --force)" = 2 ]'
ok "start-night --stop without a night" '[[ "$(bash "$here/start-night.sh" --stop 2>&1)" == *"Aucune nuit ne tourne."* ]]'

echo "$fails failure(s)"
[ "$fails" = 0 ]
