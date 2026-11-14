#!/usr/bin/env bash
# End-to-end test of the isolation of scripts/agent.sh, WITHOUT Claude: a fake session (a shell
# command run as incognita-agent in the same sandbox) commits in the agent's clone; the result is
# collected as a bundle and checked by the path whitelist in a clone of the loop's user.
# Run on the server as the loop's user, after scripts/server/setup-agent-user.sh:
#   INCOGNITA_REPO=<a clone of main, not the production one> bash scripts/server/test-sandbox.sh
# shellcheck disable=SC2034  # variables are read inside the eval'd checks
set -u -o pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
: "${INCOGNITA_REPO:?set INCOGNITA_REPO to a scratch clone of main}"
export INCOGNITA_HOME=${INCOGNITA_HOME:-$(mktemp -d)} INCOGNITA_NIGHT=sandbox-test
# shellcheck source=scripts/lib.sh
. "$here/lib.sh"
init_state
fails=0
ok() { if eval "$2"; then echo "ok   $1"; else echo "FAIL $1"; fails=$(( fails + 1 )); fi; }
A=$INCOGNITA_AGENT_HOME

M=$(repo_git rev-parse origin/main)
task=$(date +%Y%m%d-%H%M%S)-sandbox-test
in=$INCOGNITA_EXCHANGE/in/$task out=$INCOGNITA_EXCHANGE/out/$task
t=$(mktemp -d)
cleanup() { rm -rf "$in" "$t"; sudo -n rm -rf "$out"; repo_git update-ref -d "refs/incognita/bundle/$task-main"
  repo_git update-ref -d "refs/incognita/bundle/$task-head"; repo_git update-ref -d "refs/incognita/tasks/$task"; }
trap cleanup EXIT

# 1. The wrapper itself.
o=$(run_sandboxed "incognita-$task-id" 60 yes - -- bash -c 'id -un; [ -n "${CLAUDE_CODE_OAUTH_TOKEN:-}" ] && echo token-set; ls /home/lean >/dev/null 2>&1 && echo home-readable; cat /etc/incognita/agent.env >/dev/null 2>&1 && echo env-readable; touch /srv/incognita/out/x 2>/dev/null && echo out-writable; echo done' </dev/null 2>&1)
ok "runs as $INCOGNITA_AGENT_USER" '[ "$(printf "%s\n" "$o" | head -n1)" = "$INCOGNITA_AGENT_USER" ]'
ok "the token comes from the EnvironmentFile" '[[ "$o" == *token-set* ]]'
ok "no access to the loop user home" '[[ "$o" != *home-readable* ]]'
ok "agent.env unreadable" '[[ "$o" != *env-readable* ]]'
ok "out/ not writable from a session" '[[ "$o" != *out-writable* && "$o" == *done* ]]'
o=$(run_sandboxed "incognita-$task-mem" 60 no - -- bash -c 'cat /proc/self/cgroup; systemctl show -p MemoryMax "$(basename "$(cut -d: -f3 /proc/self/cgroup)")" 2>/dev/null' </dev/null 2>&1)
ok "runs in its own unit" '[[ "$o" == *"incognita-$task-mem"* ]]'

# 2. prepare (as agent.sh does it)
mkdir -p "$in/agents" && echo "# Task (test)" > "$in/agents/task.md"
repo_git update-ref "refs/incognita/bundle/$task-main" "$M"
repo_git update-ref "refs/incognita/bundle/$task-head" "$M"
repo_git bundle create -q "$in/in.bundle" "refs/incognita/bundle/$task-main" "refs/incognita/bundle/$task-head"
cp "$here/agent-side.sh" "$in/agent-side.sh"; chmod -R a+rX,go-w "$in"
# A previous session left a hostile configuration: a hook and an alias in .git/config.
run_sandboxed "incognita-$task-dirty" 60 no - -- bash -c 'cd ~/work && printf "[core]\n\thooksPath = /tmp/evil\n" >> .git/config && echo junk > untracked.txt' </dev/null
o=$(run_sandboxed "incognita-$task-prep" 300 no - -- bash "$in/agent-side.sh" prepare "$in" "$M" "$GH_REPO" \
  "refs/incognita/bundle/$task-main" "refs/incognita/bundle/$task-head" </dev/null 2>&1)
ok "prepare checks out main" '[[ "$o" == *"prepared $M"* ]]'
o=$(run_sandboxed "incognita-$task-look" 60 no - -- bash -c 'cd ~/work; git config core.hooksPath; ls untracked.txt 2>&1; cat .agents/task.md; git rev-parse origin/main; ls ~/.claude' </dev/null 2>&1)
ok "git configuration reset" '[[ "$o" == /dev/null* ]]'
ok "untracked files removed" '[[ "$o" == *"No such file"* ]]'
ok "context files copied" '[[ "$o" == *"# Task (test)"* ]]'
ok "Claude configuration from the template" '[[ "$o" == *settings.json* ]]'

# 3. a fake session: one allowed commit, a summary with hostile text
run_sandboxed "incognita-$task-fake" 120 no - -- bash -c 'cd ~/work && mkdir -p papers/P901-sandbox-test/notebook && echo "\\documentclass{article}" > papers/P901-sandbox-test/paper.tex && echo "print(1)" > papers/P901-sandbox-test/notebook/exp.py && git add -A && git commit -qm "Add P901" && printf "## Results\n@someone <!-- marker --> fixes #1\n" > .agents/summary.md' </dev/null
sudo -n install -d -o "$INCOGNITA_AGENT_USER" -g "$(id -gn)" -m 750 "$out"
o=$(run_sandboxed "incognita-$task-collect" 300 no "$out" -- bash "$in/agent-side.sh" collect "$out" "$M" - </dev/null 2>&1)
ok "collect: one new commit" '[ "$(cat "$out/count")" = 1 ]'
repo_git -c transfer.fsckObjects=true fetch -q --no-tags "$out/out.bundle" "+refs/incognita/out:refs/incognita/tasks/$task"
new=$(repo_git rev-parse "refs/incognita/tasks/$task")
ok "the bundle carries the agent's head" '[ "$new" = "$(cat "$out/head")" ]'
ok "the whitelist accepts it (write-paper)" 'check_paths write-paper "" "$M" "$new" 2>/dev/null'
s=$(sanitize 60000 < "$out/summary.md")
ok "the summary is sanitised" '[[ "$s" != *"<!--"* && "$s" != *"fixes #1"* ]]'

# 4. a hostile session: symlink, human path
run_sandboxed "incognita-$task-bad" 120 no - -- bash -c 'cd ~/work && ln -s /etc/passwd papers/P901-sandbox-test/l && echo x >> README.md && git add -A && git commit -qm bad' </dev/null
sudo -n rm -rf "$out"; sudo -n install -d -o "$INCOGNITA_AGENT_USER" -g "$(id -gn)" -m 750 "$out"
run_sandboxed "incognita-$task-collect2" 300 no "$out" -- bash "$in/agent-side.sh" collect "$out" "$M" - </dev/null >/dev/null 2>&1
repo_git fetch -q --no-tags "$out/out.bundle" "+refs/incognita/out:refs/incognita/tasks/$task"
new=$(repo_git rev-parse "refs/incognita/tasks/$task")
ok "the whitelist refuses a symlink and README.md" '! check_paths write-paper "" "$M" "$new" 2>/dev/null'

# 5. a TERM to the runner stops the unit (the pattern of agent.sh: background, wait, trap)
unit="incognita-$task-term"
bash -c '. "$1/lib.sh"; trap "exit 130" TERM; trap stop_sandbox EXIT
  SANDBOX_UNIT=$2; { run_sandboxed "$2" 600 no - -- sleep 600 </dev/null; } & wait $!' _ "$here" "$unit" &
runner=$!
sleep 3
ok "the session unit runs" '[ "$(systemctl is-active "$unit.service" 2>/dev/null)" = active ]'
kill -TERM "$runner"; wait "$runner" 2>/dev/null
sleep 2
ok "TERM to the runner stops the unit" '[ "$(systemctl is-active "$unit.service" 2>/dev/null)" != active ]'

echo "$fails failure(s)"
[ "$fails" = 0 ]
