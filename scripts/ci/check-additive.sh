#!/usr/bin/env bash
# Pull requests only: frozen statements and proof markers are append-only.
#
# Usage: bash scripts/ci/check-additive.sh <base-ref>      e.g. origin/main
#
# Compares HEAD with its merge base with <base-ref> (`git diff <base-ref>...HEAD`) and fails if:
#   - a path under Statements/ (statements, locks) is anything but added;
#   - Statements.lean changes otherwise than by added `import Statements.…` lines;
#   - a proof marker catalogue/results/*.toml is anything but added (README.md may change).
# The owner merges a deliberate non-additive change with the ruleset's admin bypass.
set -euo pipefail

base=${1:?usage: scripts/ci/check-additive.sh <base-ref>}
root="$(git rev-parse --show-toplevel)"
cd "$root"
git rev-parse --verify --quiet "$base" > /dev/null || { echo "unknown base $base" >&2; exit 2; }

status=0
fail() { echo "$*"; status=1; }

# name-status pairs, NUL-separated: "<status>\0<path>\0".
changes() {
  git -c core.quotePath=false diff -z --name-status --no-renames "$base...HEAD" -- "$@"
}

while IFS= read -r -d '' st && IFS= read -r -d '' path; do
  [ "$st" = A ] || fail "Statements/ is append-only: $st $path"
done < <(changes Statements/)

while IFS= read -r line; do
  case "$line" in
    '+++ '*|'--- '*) ;;
    +*)
      if ! printf '%s\n' "${line#+}" | grep -qE '^(public )?import Statements(\.[^ ]+)+[[:space:]]*$'; then
        fail "Statements.lean: only import lines of new statement modules may be added: $line"
      fi ;;
    -*) fail "Statements.lean: lines may not be removed: $line" ;;
  esac
done < <(git -c core.quotePath=false diff --no-renames -U0 "$base...HEAD" -- Statements.lean)

while IFS= read -r -d '' st && IFS= read -r -d '' path; do
  case "$path" in
    *.toml) [ "$st" = A ] || fail "proof markers are append-only: $st $path" ;;
  esac
done < <(changes catalogue/results/)

if [ "$status" = 0 ]; then
  echo "Statements/ and proof markers: additions only"
else
  echo "non-additive change: only the owner can merge it (admin bypass)" >&2
fi
exit "$status"
