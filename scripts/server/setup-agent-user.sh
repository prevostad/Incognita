#!/usr/bin/env bash
# Set up (or check) the isolated user that runs the agents' sessions (DECISIONS D11). Idempotent:
# run it again after a change; it never overwrites the token file.
#
# Usage (on the server, as the loop's user, with sudo):
#   sudo bash scripts/server/setup-agent-user.sh [--skip-apt] [--skip-lake] [--check]
#     --skip-apt    do not install system packages
#     --skip-lake   do not copy the loop clone's .lake (8 GB) to the agent's clone
#     --check       change nothing; run the sandbox test only
#
# What it does:
#   1. system packages: git, jq, rsync, curl, LaTeX (latexmk, texlive-*), Python with numpy, scipy,
#      matplotlib (papers are compiled and numerical experiments run inside the sandbox only);
#   2. the user incognita-agent (no password, no sudo, home 700) and no access to the loop user's home;
#   3. /srv/incognita/{in,out,template}: in/ written by the loop user and read by the agent (group),
#      out/<task>/ created per task by the loop (via sudo) and written by the agent;
#   4. /etc/incognita/agent.env (root, 600): CLAUDE_CODE_OAUTH_TOKEN=<token> — a placeholder is
#      written if the file is missing. Before EVERY night, put a new long-lived token there (the
#      owner's choice: scripts/night.sh puts REPLACE_ME back at the end of every night, so that no
#      token stays on the server or in its snapshots; agents/README.md, "The token"). The launcher
#      does it: bash scripts/start-night.sh 02:45 88% (claude setup-token, captured and masked). By hand:
#        claude setup-token                      (as the owner, anywhere; prints sk-ant-oat01-...)
#        sudo nano /etc/incognita/agent.env      (replace REPLACE_ME; never commit or print it)
#   5. for the agent: elan and the Lean toolchain (~/.elan, read-only in the sessions), Claude Code
#      in /opt/incognita/bin (root-owned, outside the agent's home, so that no session can replace
#      it for the next one: the binary of the loop user's native install, same version, or a native
#      install made for the purpose; autoupdater off), an anonymous clone of the public repository
#      in ~/work, a full copy of the loop clone's .lake (rsync --chown), and a template of ~/.claude
#      in /srv/incognita/template (copied over ~/.claude before every task);
#   6. a test of the sandbox (systemd-run as the agent: id, claude --version, lake with ~/.elan
#      read-only, no access to the loop user's home, read-only system).
set -euo pipefail

AGENT=${INCOGNITA_AGENT_USER:-incognita-agent}
AGENT_HOME=/home/$AGENT
AGENT_BIN=${INCOGNITA_AGENT_BIN:-/opt/incognita/bin}
LOOP_USER=${SUDO_USER:-lean}
LOOP_HOME=$(getent passwd "$LOOP_USER" | cut -d: -f6)
LOOP_REPO=${INCOGNITA_REPO:-$LOOP_HOME/Incognita}
REPO_URL=${INCOGNITA_REPO_URL:-https://github.com/prevostad/Incognita.git}
EXCHANGE=${INCOGNITA_EXCHANGE:-/srv/incognita}
ENV_FILE=${INCOGNITA_AGENT_ENV:-/etc/incognita/agent.env}
skip_apt=0 skip_lake=0 check_only=0
for a in "$@"; do
  case "$a" in
    --skip-apt) skip_apt=1 ;;
    --skip-lake) skip_lake=1 ;;
    --check) check_only=1 ;;
    *) echo "unknown option $a" >&2; exit 2 ;;
  esac
done
[ "$(id -u)" = 0 ] || { echo "run with sudo" >&2; exit 2; }
[ "$LOOP_USER" != root ] && [ -n "$LOOP_HOME" ] || { echo "run with sudo from the loop's user (SUDO_USER)" >&2; exit 2; }
say() { printf '== %s\n' "$*"; }
as_agent() { sudo -u "$AGENT" -H env -i HOME="$AGENT_HOME" USER="$AGENT" LANG=C.UTF-8 \
  PATH="$AGENT_HOME/.local/bin:$AGENT_HOME/.elan/bin:/usr/local/bin:/usr/bin:/bin" "$@"; }

sandbox_test() {
  say "sandbox test (systemd-run as $AGENT, as scripts/lib.sh run_sandboxed)"
  systemd-run --quiet --wait --pipe --collect --unit="incognita-setup-test-$$" \
    --uid="$AGENT" --gid="$AGENT" -p WorkingDirectory="$AGENT_HOME/work" \
    -E HOME="$AGENT_HOME" -E PATH="$AGENT_BIN:$AGENT_HOME/.elan/bin:/usr/local/bin:/usr/bin:/bin" \
    -E DISABLE_AUTOUPDATER=1 -E PYTHONNOUSERSITE=1 -p RuntimeMaxSec=120 -p MemoryMax=6G -p NoNewPrivileges=yes \
    -p PrivateTmp=yes -p ProtectSystem=strict -p ProtectProc=invisible -p PrivateIPC=yes -p PrivateDevices=yes \
    -p TemporaryFileSystem=/dev/shm:mode=1777 -p TemporaryFileSystem=/run/lock:mode=1777 \
    -p ReadWritePaths="$AGENT_HOME" \
    -p ReadOnlyPaths="$AGENT_HOME/.elan" -p InaccessiblePaths="$LOOP_HOME" \
    bash -c '
      echo "id: $(id)"
      echo "claude: $(command -v claude) $(claude --version 2>&1 | head -n 1)"
      echo "lake: $(lake --version 2>&1 | head -n 1)"
      if touch "$HOME/.elan/incognita-test" 2>/dev/null; then rm -f "$HOME/.elan/incognita-test"; echo "FAIL: ~/.elan is writable"; else echo "ok: ~/.elan read-only"; fi
      if touch "$(command -v claude)" 2>/dev/null; then echo "FAIL: claude is writable"; else echo "ok: claude read-only"; fi
      echo "latexmk: $(latexmk -v 2>&1 | grep -m1 Version)"; echo "pdflatex: $(pdflatex --version 2>&1 | head -n 1)"
      echo "python3: $(python3 -c "import numpy, scipy, matplotlib; print(\"numpy\", numpy.__version__)" 2>&1)"
      if ls "$0" >/dev/null 2>&1; then echo "FAIL: the loop user home is readable"; else echo "ok: no access to $0"; fi
      if touch /usr/incognita-test 2>/dev/null; then echo "FAIL: /usr is writable"; else echo "ok: system read-only"; fi
      if touch "$HOME/.incognita-test" 2>/dev/null; then rm -f "$HOME/.incognita-test"; echo "ok: home writable"; else echo "FAIL: home not writable"; fi
      if sudo -n true 2>/dev/null; then echo "FAIL: sudo works"; else echo "ok: no sudo"; fi
      if [ "$(ps -e --no-headers | wc -l)" -le 5 ]; then echo "ok: other processes invisible"; else echo "FAIL: $(ps -e --no-headers | wc -l) processes visible"; fi
      if [ -n "${CLAUDE_CODE_OAUTH_TOKEN:-}" ]; then echo "FAIL: token present without EnvironmentFile"; else echo "ok: no token in this test"; fi
    ' "$LOOP_HOME"
}
if [ "$check_only" = 1 ]; then sandbox_test; exit 0; fi

# 1. Packages
if [ "$skip_apt" = 0 ]; then
  pkgs="git jq rsync curl ca-certificates util-linux python3 python3-numpy python3-scipy python3-matplotlib latexmk lmodern texlive-latex-recommended texlive-latex-extra texlive-fonts-recommended texlive-science"
  missing=""
  for p in $pkgs; do dpkg -s "$p" >/dev/null 2>&1 || missing="$missing $p"; done
  if [ -n "$missing" ]; then
    say "installing:$missing"
    apt-get update -q
    # shellcheck disable=SC2086
    DEBIAN_FRONTEND=noninteractive apt-get install -y -q --no-install-recommends $missing
  else say "packages already installed"; fi
fi

# 2. User
if ! id -u "$AGENT" >/dev/null 2>&1; then
  say "creating the user $AGENT"
  useradd --create-home --home-dir "$AGENT_HOME" --shell /bin/bash --user-group "$AGENT"
fi
passwd -l "$AGENT" >/dev/null 2>&1 || true
chmod 700 "$AGENT_HOME"
if [ -n "$(find "$LOOP_HOME" -maxdepth 0 -perm /o=rwx)" ]; then
  say "removing other users' access to $LOOP_HOME"
  chmod o-rwx "$LOOP_HOME"
fi
if id -nG "$AGENT" | tr ' ' '\n' | grep -qxE "sudo|admin|wheel|$LOOP_USER"; then
  echo "the user $AGENT is in a privileged group: fix it by hand" >&2; exit 1
fi

# 3. Exchange directories
install -d -o root -g root -m 755 "$EXCHANGE" "$EXCHANGE/out" "$EXCHANGE/template" "$EXCHANGE/template/claude"
install -d -o "$LOOP_USER" -g "$AGENT" -m 2750 "$EXCHANGE/in"
cat > "$EXCHANGE/template/claude/settings.json" <<'EOF'
{
  "env": {
    "DISABLE_AUTOUPDATER": "1",
    "DISABLE_TELEMETRY": "1",
    "DISABLE_ERROR_REPORTING": "1"
  },
  "permissions": {
    "deny": [
      "Read(//proc/**)",
      "Read(//etc/incognita/**)",
      "Read(//srv/incognita/out/**)"
    ]
  }
}
EOF
printf '{\n  "hasCompletedOnboarding": true\n}\n' > "$EXCHANGE/template/claude.json"
chmod 644 "$EXCHANGE/template/claude/settings.json" "$EXCHANGE/template/claude.json"

# 4. Token file (never overwritten, never printed)
install -d -o root -g root -m 700 "$(dirname "$ENV_FILE")"
if [ ! -f "$ENV_FILE" ]; then
  say "writing a placeholder $ENV_FILE: put the token of 'claude setup-token' in it"
  umask 077
  printf '# Long-lived Claude token of the owner for the agents (claude setup-token). Root only.\n# scripts/night.sh puts REPLACE_ME back at the end of every night: a new token before each launch.\nCLAUDE_CODE_OAUTH_TOKEN=REPLACE_ME\n' > "$ENV_FILE"
  umask 022
fi
chown root:root "$ENV_FILE"; chmod 600 "$ENV_FILE"
grep -qE '^CLAUDE_CODE_OAUTH_TOKEN=sk-ant-' "$ENV_FILE" && say "a token is set in $ENV_FILE" \
  || say "no token yet in $ENV_FILE (REPLACE_ME): nights will not start"

# 5. Toolchains, Claude Code, clone, .lake
if [ ! -x "$AGENT_HOME/.elan/bin/elan" ]; then
  say "installing elan for $AGENT"
  as_agent bash -c 'curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none --no-modify-path'
fi
# Claude Code for the sessions: a root-owned copy in $AGENT_BIN (never in the agent's home, where a
# session could replace it). The binary of the loop user's native install when it is the version
# wanted; otherwise a native install made in a temporary home, then copied.
want=${CLAUDE_VERSION:-$(basename "$(readlink -f "$LOOP_HOME/.local/bin/claude" 2>/dev/null)" 2>/dev/null || true)}
[[ "$want" =~ ^[0-9]+\.[0-9]+\.[0-9]+$ ]] || want=stable
have=$(as_agent "$AGENT_BIN/claude" --version 2>/dev/null | awk '{print $1}' || true)
if [ "$have" != "$want" ]; then
  src=$(readlink -f "$LOOP_HOME/.local/bin/claude" 2>/dev/null || true)
  if [ -z "$src" ] || [ ! -f "$src" ] || [ "$(basename "$src")" != "$want" ]; then
    say "installing Claude Code $want (native installer, in a temporary home)"
    th=$(mktemp -d)
    HOME=$th bash -c "curl -fsSL https://claude.ai/install.sh | bash -s $want" >/dev/null
    src=$(readlink -f "$th/.local/bin/claude")
  fi
  say "copying Claude Code $want to $AGENT_BIN/claude (root-owned)"
  install -d -o root -g root -m 755 "$(dirname "$AGENT_BIN")" "$AGENT_BIN"
  install -o root -g root -m 755 "$src" "$AGENT_BIN/claude"
  [ -n "${th:-}" ] && rm -rf "$th"
fi
# The old install in the agent's home is not used any more (not on the sessions' PATH); the
# preparation of every task removes ~/.local anyway.
rm -rf "$AGENT_HOME/.local"
if [ ! -e "$AGENT_HOME/work" ]; then   # (each task rebuilds the repository of ~/work from a bundle)
  say "cloning $REPO_URL (anonymous) into $AGENT_HOME/work"
  as_agent git clone -q "$REPO_URL" "$AGENT_HOME/work"
fi
toolchain=$(sudo -u "$LOOP_USER" git -C "$LOOP_REPO" show origin/main:lean-toolchain 2>/dev/null || cat "$AGENT_HOME/work/lean-toolchain")
as_agent "$AGENT_HOME/.elan/bin/elan" toolchain install "$toolchain" >/dev/null 2>&1 || as_agent "$AGENT_HOME/.elan/bin/elan" toolchain install "$toolchain"
if [ "$skip_lake" = 0 ]; then
  [ -d "$LOOP_REPO/.lake" ] || { echo "$LOOP_REPO/.lake is missing: build the loop's clone first (bash scripts/build.sh Incognita)" >&2; exit 1; }
  if [ -L "$AGENT_HOME/work" ] || [ -L "$AGENT_HOME/work/.lake" ]; then echo "the agent's work/.lake is a link: refusing" >&2; exit 1; fi
  say "copying $LOOP_REPO/.lake to the agent's clone (full copy, a few minutes the first time)"
  rsync -a --delete --chown="$AGENT:$AGENT" "$LOOP_REPO/.lake/" "$AGENT_HOME/work/.lake/"
  # Same stamp as scripts/lib.sh (lake_stamp), so that the loop does not copy again.
  sudo -u "$LOOP_USER" git -C "$LOOP_REPO" show origin/main:lean-toolchain origin/main:lake-manifest.json \
    | sha256sum | cut -c1-16 > "$EXCHANGE/lake.stamp"
fi

# 6. Test
sandbox_test
say "done. Next, in the loop's clone: a dry run, bash scripts/start-night.sh 02:45 88% --dry-run, then a night, bash scripts/start-night.sh 02:45 88%"
