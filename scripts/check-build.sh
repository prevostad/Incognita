#!/usr/bin/env bash
# Build a library and fail on any warning except `declaration uses 'sorry'`; with --no-sorry, fail
# on those too. Prints how many declarations use sorry.
#
# Usage: scripts/check-build.sh <library> [--no-sorry]
#
# Adapted from lml-paper-template's scripts/check-build.sh (Apache 2.0).
set -euo pipefail

root="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
cd "$root"
lib=${1:?usage: scripts/check-build.sh <library> [--no-sorry]}
nosorry=${2:-}
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

log=$(mktemp)
trap 'rm -f "$log"' EXIT
if ! bash "$here/build.sh" "$lib" 2>&1 | tee "$log"; then
  echo "the build of $lib failed" >&2
  exit 1
fi

sorries=$(grep -c "declaration uses .sorry." "$log" || true)
others=$(grep "warning:" "$log" | grep -vc "declaration uses .sorry." || true)
echo "$lib: $sorries declarations use sorry, $others other warnings"
if [ "$others" != 0 ]; then
  echo "fix the warnings above: only 'declaration uses sorry' is allowed" >&2
  exit 1
fi
if [ "$nosorry" = "--no-sorry" ] && [ "$sorries" != 0 ]; then
  echo "$lib must not use sorry" >&2
  exit 1
fi
