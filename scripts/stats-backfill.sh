#!/usr/bin/env bash
# Backfill of the raw events of the nights run before scripts/night.sh posted them (owner request of
# 2026-11-19; human-owned, run once by the owner, from his own machine). For each night given, reads
# ~/.incognita/state/nights/<night>/events.tsv on the server over ssh (read only: `cat`, nothing is
# written there), formats it with scripts/stats.py events-block (the format night.sh posts), and posts
# it as a comment on the issue "Night reports", headed "Backfill of the night of <night>", in as many
# comments as GitHub's size limit needs. scripts/stats.py then reads it like the blocks of the loop.
# The model of each session, which these task lines do not carry, is taken from the night's log
# (~/.incognita/logs/<night>.log, read the same way: `== session: <role> <target>, model <m>, …`).
#
#   bash scripts/stats-backfill.sh --dry-run                  show what would be posted, post nothing
#   bash scripts/stats-backfill.sh                            the nights 2026-11-17, 2026-11-18, 2026-11-19
#   bash scripts/stats-backfill.sh 2026-11-19                 one night
#
# Options: --host <ssh alias> (default tauceti), --issue <n> (default: the open issue "Night reports"
# of the repository's owner, #21), --yes (no confirmation), --force (post a night already backfilled),
# --dry-run. Needs ssh to the server, gh logged in as the owner (the account the loop posts with:
# stats.py reads only its comments), and Python 3.11+ ($PYTHON, else python3 or python; never the
# Microsoft Store stub). A night still running on the server is skipped: wait for its end.
# Exit: 0 done, 1 an error, 2 usage.
set -u -o pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
REPO=${INCOGNITA_GH_REPO:-prevostad/Incognita}
host=tauceti issue="" yes=0 force=0 dry=0 nights=()
usage() { sed -n '2,20p' "$0" | sed 's/^# \{0,1\}//'; exit 2; }
while [ $# -gt 0 ]; do
  case "$1" in
    --host) host=${2:-}; shift 2 || usage ;;
    --issue) issue=${2:-}; shift 2 || usage ;;
    --yes) yes=1; shift ;;
    --force) force=1; shift ;;
    --dry-run) dry=1; shift ;;
    -h|--help) usage ;;
    -*) echo "unknown option: $1" >&2; usage ;;
    *) nights+=("$1"); shift ;;
  esac
done
[ "${#nights[@]}" -gt 0 ] || nights=(2026-11-17 2026-11-18 2026-11-19)
for n in "${nights[@]}"; do [[ "$n" =~ ^[0-9]{4}-[0-9]{2}-[0-9]{2}$ ]] || { echo "not a night: $n (YYYY-MM-DD)" >&2; exit 2; }; done
[[ "$host" =~ ^[A-Za-z0-9._@-]+$ ]] || { echo "bad host: $host" >&2; exit 2; }

pick_python() {
  local p c
  if [ -n "${PYTHON:-}" ]; then echo "$PYTHON"; return 0; fi
  for p in python3 python; do
    c=$(command -v "$p" 2>/dev/null) || continue
    case "$c" in *WindowsApps*) continue ;; esac   # the Microsoft Store stub, which hangs
    echo "$p"; return 0
  done
  return 1
}
PY=$(pick_python) || { echo "no Python found: set PYTHON" >&2; exit 1; }
"$PY" -I -c 'import sys; sys.exit(0 if sys.version_info >= (3, 11) else 1)' || { echo "$PY: Python 3.11+ needed" >&2; exit 1; }
command -v gh >/dev/null || { echo "gh is needed" >&2; exit 1; }
owner=$(gh api user --jq .login) || { echo "gh is not logged in" >&2; exit 1; }
[ "$owner" = "${REPO%%/*}" ] || echo "warning: gh is logged in as $owner, not ${REPO%%/*}: stats.py will not trust these comments" >&2
if [ -z "$issue" ]; then
  issue=$(gh issue list -R "$REPO" --state open --author "$owner" --limit 200 --json number,title \
    --jq 'map(select(.title == "Night reports")) | first | .number // empty') || exit 1
  [ -n "$issue" ] || { echo "no open issue \"Night reports\": give --issue" >&2; exit 1; }
fi
[[ "$issue" =~ ^[0-9]+$ ]] || { echo "bad issue: $issue" >&2; exit 2; }

t=$(mktemp -d) || exit 1
trap 'rm -rf "$t"' EXIT
# The nights already on the issue (first part of a block of the owner's account), to post each once.
gh api --paginate "repos/$REPO/issues/$issue/comments?per_page=100" \
  --jq ".[] | select(.user.login == \"$owner\") | .body" > "$t/existing" || { echo "cannot read the issue #$issue" >&2; exit 1; }
# The latest night directory, and whether a night is running (read only: ls and pgrep).
running=$(ssh -o BatchMode=yes "$host" 'pgrep -f "scripts/[n]ight.sh" >/dev/null && ls -1 ~/.incognita/state/nights | tail -n 1' 2>/dev/null) || running=""

today=$(date -u +%F)
posts=()
for n in "${nights[@]}"; do
  if [ "$force" = 0 ] && grep -q "<!-- incognita:events v1 night=$n part=1/" "$t/existing"; then
    echo "$n: already on the issue #$issue (--force to post it again; stats.py counts each line once)"; continue
  fi
  if [ "$n" = "$running" ]; then echo "$n: the night is still running on $host: skipped (run again after its end)"; continue; fi
  if ! ssh -o BatchMode=yes "$host" "cat ~/.incognita/state/nights/$n/events.tsv" > "$t/$n.tsv" 2>"$t/ssh.err"; then
    echo "$n: no events on $host ($(head -c 200 "$t/ssh.err" | tr '\n' ' '))"; continue
  fi
  # The night's log, for the model of each session (task lines of these nights do not carry it yet).
  logs=()
  ssh -o BatchMode=yes "$host" "cat ~/.incognita/logs/$n.log" > "$t/$n.log" 2>/dev/null && logs=(--log "$t/$n.log")
  k=$("$PY" -I "$here/stats.py" events-block --night "$n" --out "$t/$n" "${logs[@]}" "$t/$n.tsv") || { echo "$n: could not be formatted" >&2; exit 1; }
  [ "$k" -gt 0 ] 2>/dev/null || { echo "$n: no event line"; continue; }
  for i in $(seq 1 "$k"); do
    { printf '# Backfill of the night of %s%s\n\n' "$n" "$( [ "$k" -gt 1 ] && echo " (part $i of $k)")"
      printf 'Raw events of this night, read from the server on %s by `scripts/stats-backfill.sh` (owner request of 2026-11-19): its night report was posted before the loop posted them. Read by `scripts/stats.py`.\n\n' "$today"
      cat "$t/$n/part-$i.md"; } > "$t/$n-$i.md"
    posts+=("$t/$n-$i.md")
  done
  echo "$n: $(grep -c . "$t/$n.tsv") lines in events.tsv, $k comment(s) ($(cat "$t/$n"/part-*.md | wc -c | tr -d ' ') bytes)"
done
[ "${#posts[@]}" -gt 0 ] || { echo "nothing to post"; exit 0; }
if [ "$dry" = 1 ]; then
  for f in "${posts[@]}"; do echo "======== $(basename "$f")"; cat "$f"; done
  echo "dry run: nothing posted (${#posts[@]} comment(s) on #$issue)"; exit 0
fi
if [ "$yes" = 0 ]; then
  printf 'Post %d comment(s) on %s#%s as %s? [y/N] ' "${#posts[@]}" "$REPO" "$issue" "$owner"
  read -r a; case "$a" in y|Y|yes|o|oui) ;; *) echo "nothing posted"; exit 0 ;; esac
fi
for f in "${posts[@]}"; do
  url=$(gh api -X POST "repos/$REPO/issues/$issue/comments" -F body=@- --jq .html_url < "$f") \
    || { echo "could not post $(basename "$f"); the comments before it are posted" >&2; exit 1; }
  echo "posted: $url"
done
