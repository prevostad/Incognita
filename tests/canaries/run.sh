#!/usr/bin/env bash
# Canaries of the audit (scripts/Audit.lean). In a temporary copy of the repository, a correct
# example (a definition, three frozen statements: one proved, one refuted, one open, their locks
# and proof markers) must pass `lake exe audit --check` with the expected statuses, and each
# scenario breaking one rule must make the audit fail with the expected message. The repository
# itself is never modified: the copy shares only `.lake/packages` (read) and starts from a copy of
# `.lake/build`.
#
# Usage: bash tests/canaries/run.sh [scenario ...]     (after a build of the project, as in CI)
set -uo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
[ -d "$root/.lake/packages" ] || { echo "no .lake/packages: build the project first" >&2; exit 2; }
work="$(mktemp -d "${TMPDIR:-/tmp}/incognita-canaries.XXXXXX")"
trap 'rm -rf "$work"' EXIT
repo="$work/repo"
out="$work/out"

mkdir -p "$repo/.lake"
tar -C "$root" --exclude=./.lake --exclude=./.git -cf - . | tar -C "$repo" -xf -
ln -s "$root/.lake/packages" "$repo/.lake/packages"
if [ -d "$root/.lake/build" ]; then cp -a "$root/.lake/build" "$repo/.lake/build"; fi
cd "$repo" || exit 2
git init -q && git add -A && git -c user.name=canary -c user.email=canary@invalid commit -qm copy

die() { echo "canaries: $*" >&2; [ -f "$out" ] && tail -n 60 "$out" >&2; exit 1; }
# write <path>: the file's content on stdin.
write() { mkdir -p "$(dirname "$1")"; cat > "$1"; }
# add_import <root> <module>: import a new module from a library root.
add_import() { printf 'public import %s\n' "$2" >> "$1.lean"; }
audit() { lake exe audit "$@" > "$out" 2>&1; }

# --- The correct example ------------------------------------------------------------------------

defs() {
  write Incognita/Canary/Defs.lean <<'EOF'
module

public import Incognita.Basic

@[expose] public section

namespace Incognita.Canary

/-- Twice a natural number. -/
def double (n : Nat) : Nat := n + n

/-- Two colours. -/
inductive Colour where
  | red
  | green

end Incognita.Canary
EOF
}

statements() {
  write Statements/P999/Canary.lean <<'EOF'
module

public import Incognita.Canary.Defs

@[expose] public section

namespace Incognita.Statements.P999

theorem double_even (n : Nat) : ∃ k, Incognita.Canary.double n = 2 * k := sorry

theorem double_zero : Incognita.Canary.double 0 = 1 := sorry

theorem colour_red (c : Incognita.Canary.Colour) : c = .red := sorry
EOF
  if [ "${1:-}" != open-namespace ]; then echo 'end Incognita.Statements.P999' >> Statements/P999/Canary.lean; fi
}

# proofs [even-proof|-] [even-type]: the library's proofs; "-" leaves double_even out.
proofs() {
  local even=${1:-'⟨n, by unfold Incognita.Canary.double; omega⟩'}
  local type=${2:-'∃ k, Incognita.Canary.double n = 2 * k'}
  {
    cat <<'EOF'
module

public import Incognita.Canary.Defs

@[expose] public section

namespace Incognita.P999

theorem double_zero_false : ¬ Incognita.Canary.double 0 = 1 := by decide
EOF
    if [ "$even" != - ]; then
      printf '\ntheorem double_even (n : Nat) : %s :=\n  %s\n' "$type" "$even"
    fi
    printf '\nend Incognita.P999\n'
  } | write Incognita/Canary/Proofs.lean
}

defs
statements
proofs
add_import Incognita Incognita.Canary.Defs
add_import Incognita Incognita.Canary.Proofs
add_import Statements Statements.P999.Canary
write catalogue/results/P999-double_even.toml <<'EOF'
statement = "Incognita.Statements.P999.double_even"
EOF
write catalogue/results/P999-double_zero.toml <<'EOF'
statement = "Incognita.Statements.P999.double_zero"
status = "refuted"
EOF

audit --selftest || die "the SHA-256 self-test fails"
audit --new-locks || die "--new-locks fails on the correct example"
[ "$(grep -c '^wrote Statements/P999/' "$out")" = 3 ] || die "--new-locks did not write three locks"
audit --new-locks || die "--new-locks fails the second time"
grep -q '^wrote' "$out" && die "--new-locks rewrote an existing lock"
audit --check || die "the correct example fails the audit"
grep -q '^replay: ' "$out" || die "the kernel replay did not run"
lake exe audit --status > "$out" 2> "$work/err" || die "--status fails"
printf 'P999 colour_red open\nP999 double_even proved\nP999 double_zero refuted\n' > "$work/expected"
diff "$work/expected" "$out" > /dev/null || { cat "$work/err" >&2; die "unexpected --status output"; }
lake exe audit --dump P999.double_even > "$work/dump" 2> /dev/null || die "--dump fails"
dumped=$(sha256sum < "$work/dump" | cut -d' ' -f1)
locked=$(sed -n 's/^sha256 //p' Statements/P999/double_even.lock)
[ "$dumped" = "$locked" ] || die "sha256sum of --dump ($dumped) differs from the lock ($locked)"
grep -q '^constant def Incognita.Canary.double$' Statements/P999/double_even.lock ||
  die "the lock of double_even does not list Incognita.Canary.double"
grep -q '^constant inductive Incognita.Canary.Colour$' Statements/P999/colour_red.lock ||
  die "the lock of colour_red does not list Incognita.Canary.Colour"
git add -A && git -c user.name=canary -c user.email=canary@invalid commit -qm base
echo "ok   correct example: check passes, statuses open/proved/refuted, dump matches lock"
echo "     Statements/P999/double_even.lock:"
sed 's/^/       /' Statements/P999/double_even.lock
echo "     its dump starts with:"
head -c 600 "$work/dump" | sed 's/^/       /'
echo

# --- Scenarios: each must fail ------------------------------------------------------------------

sorry_proof() {
  proofs 'sorry'
  expect "depends on non-standard axioms" "sorryAx" \
    "P999-double_even.toml says Incognita.Statements.P999.double_even is proved, but it is open"
}

changed_definition() {
  sed -i 's/def double (n : Nat) : Nat := n + n/def double (n : Nat) : Nat := 2 * n/' \
    Incognita/Canary/Defs.lean
  grep -q '2 \* n' Incognita/Canary/Defs.lean || die "changed_definition: sed failed"
  expect "locks: Statements/P999/double_even.lock does not match"
}

def_in_statements() {
  write Statements/P999/Helper.lean <<'EOF'
module

public import Incognita.Canary.Defs

@[expose] public section

namespace Incognita.Statements.P999

/-- A definition, where only theorems belong. -/
def helper : Nat := 3

end Incognita.Statements.P999
EOF
  add_import Statements Statements.P999.Helper
  expect "statements: Incognita.Statements.P999.helper (def, in Statements.P999.Helper) is not allowed"
}

proof_in_statements() {
  proofs -
  write Statements/P999/Sneaky.lean <<'EOF'
module

public import Incognita.Canary.Defs

@[expose] public section

namespace Incognita.P999

theorem double_even (n : Nat) : ∃ k, Incognita.Canary.double n = 2 * k :=
  ⟨n, by unfold Incognita.Canary.double; omega⟩

end Incognita.P999
EOF
  add_import Statements Statements.P999.Sneaky
  expect "statements: Incognita.P999.double_even (theorem, in Statements.P999.Sneaky) is not allowed" \
    "it is declared in Statements.P999.Sneaky, outside Incognita/" \
    "says Incognita.Statements.P999.double_even is proved, but it is open"
}

removed_proof() {
  proofs -
  expect "markers: catalogue/results/P999-double_even.toml says Incognita.Statements.P999.double_even is proved, but it is open"
}

removed_refutation() {
  sed -i '/double_zero_false/d' Incognita/Canary/Proofs.lean
  expect "P999-double_zero.toml says Incognita.Statements.P999.double_zero is refuted, but it is open"
}

missing_lock() {
  statements open-namespace
  printf '\ntheorem extra : True := sorry\n\nend Incognita.Statements.P999\n' >> Statements/P999/Canary.lean
  expect "locks: Incognita.Statements.P999.extra has no lock Statements/P999/extra.lock"
}

orphan_lock() {
  cp Statements/P999/colour_red.lock Statements/P999/ghost.lock
  expect "locks: Statements/P999/ghost.lock matches no frozen statement"
}

edited_lock() {
  sed -i 's/^sha256 .*/sha256 0000000000000000000000000000000000000000000000000000000000000000/' \
    Statements/P999/colour_red.lock
  expect "locks: Statements/P999/colour_red.lock does not match"
}

changed_statement() {
  sed -i 's/c = .red := sorry/c = .green := sorry/' Statements/P999/Canary.lean
  expect "locks: Statements/P999/colour_red.lock does not match"
}

custom_axiom() {
  proofs '(cheat).elim'
  sed -i 's/^namespace Incognita.P999$/namespace Incognita.P999\n\naxiom cheat : False/' \
    Incognita/Canary/Proofs.lean
  expect "library: Incognita.P999.cheat depends on non-standard axioms" \
    "says Incognita.Statements.P999.double_even is proved, but it is open"
}

wrong_type() {
  proofs '⟨n, by unfold Incognita.Canary.double; omega⟩' '∃ k, Incognita.Canary.double n = k + k'
  expect "proofs: Incognita.P999.double_even does not prove Incognita.Statements.P999.double_even: its type differs from the frozen type"
}

statement_uses_statements() {
  statements open-namespace
  printf '\ntheorem match_type (n : Nat) : (match n with | 0 => True | _ + 1 => True) := sorry\n\nend Incognita.Statements.P999\n' \
    >> Statements/P999/Canary.lean
  expect "statements: the type of Incognita.Statements.P999.match_type uses Incognita.Statements.P999.match_type.match_1"
}

unknown_marker() {
  echo 'statement = "nothing"' > catalogue/results/P999-nothing.toml
  expect "markers: catalogue/results/P999-nothing.toml names no frozen statement"
}

unsafe_library() {
  printf '\nnamespace Incognita.Canary\n\nunsafe def fast : Nat := 0\n\nend Incognita.Canary\n' \
    >> Incognita/Canary/Defs.lean
  expect "library: Incognita.Canary.fast is unsafe"
}

library_imports_statements() {
  write Incognita/Canary/Uses.lean <<'EOF'
module

public import Statements.P999.Canary
EOF
  add_import Incognita Incognita.Canary.Uses
  expect "library: module Incognita.Canary.Uses imports Statements.P999.Canary"
}

library_in_statements_namespace() {
  printf '\ntheorem Incognita.Statements.P999.lemma_here : True := trivial\n' >> Incognita/Canary/Proofs.lean
  expect "library: Incognita.Statements.P999.lemma_here (in Incognita.Canary.Proofs) lies in the namespace Incognita.Statements"
}

# A theorem the kernel never checked (here `False`, "proved" by `True.intro`): it uses no axiom,
# so only the kernel replay can catch it. Meta code like this is also refused by
# scripts/ci/check-meta.py before any build.
unchecked_declaration() {
  write Incognita/Canary/Forged.lean <<'EOF'
module

public import Incognita.Basic
public meta import Lean.Elab.Command

open Lean in
set_option debug.skipKernelTC true in
run_cmd Elab.Command.liftCoreM do
  let forged : TheoremVal :=
    { name := `Incognita.Canary.forged, levelParams := [], type := mkConst ``False,
      value := mkConst ``True.intro }
  addDecl (.thmDecl forged)
EOF
  add_import Incognita Incognita.Canary.Forged
  audit --check --no-replay
  grep -q '^audit: OK' "$out" || {
    echo "FAIL unchecked_declaration: the forged declaration was not built as expected"
    tail -n 30 "$out"
    failures=$((failures + 1))
    reset
    return
  }
  expect "replay: the kernel rejects the project"
}

# `--refresh-new-locks` (not a failure scenario): a statement added by the pull request and changed
# in it gets its lock rewritten, an orphan lock of the pull request is removed, and a lock that is
# on origin/main is never touched (the audit still fails on a changed frozen statement).
refresh_new_locks() {
  local bad=""
  git update-ref refs/remotes/origin/main HEAD
  write Statements/P999/Fresh.lean <<'EOF'
module

public import Incognita.Canary.Defs

@[expose] public section

namespace Incognita.Statements.P999

theorem fresh : Incognita.Canary.double 1 = 2 := sorry

end Incognita.Statements.P999
EOF
  add_import Statements Statements.P999.Fresh
  audit --new-locks && grep -q '^wrote Statements/P999/fresh.lock$' "$out" || bad="--new-locks did not lock the new statement"
  if [ -z "$bad" ]; then
    sed -i 's/double 1 = 2/double 2 = 4/' Statements/P999/Fresh.lean
    cp Statements/P999/fresh.lock "$work/fresh.before"
    audit --new-locks
    cmp -s Statements/P999/fresh.lock "$work/fresh.before" || bad="--new-locks rewrote a lock"
  fi
  if [ -z "$bad" ]; then
    audit --check && bad="the audit passed with a stale lock"
    grep -qF "locks: Statements/P999/fresh.lock does not match" "$out" || bad="${bad:-the stale lock was not reported}"
  fi
  if [ -z "$bad" ]; then
    cp Statements/P999/fresh.lock Statements/P999/gone.lock
    sed -i 's/c = .red := sorry/c = .green := sorry/' Statements/P999/Canary.lean
    cp Statements/P999/colour_red.lock "$work/red.before"
    audit --refresh-new-locks || bad="--refresh-new-locks failed"
  fi
  if [ -z "$bad" ]; then
    grep -q '^rewrote Statements/P999/fresh.lock$' "$out" || bad="--refresh-new-locks did not rewrite the lock of the pull request"
    grep -q '^removed Statements/P999/gone.lock' "$out" || bad="${bad:-the orphan lock of the pull request was not removed}"
    [ ! -e Statements/P999/gone.lock ] || bad="${bad:-gone.lock still exists}"
    cmp -s Statements/P999/colour_red.lock "$work/red.before" || bad="${bad:---refresh-new-locks touched a lock of origin/main}"
  fi
  if [ -z "$bad" ]; then
    audit --check && bad="the audit passed with a changed frozen statement of origin/main"
    grep -qF "locks: Statements/P999/colour_red.lock does not match" "$out" || bad="${bad:-the changed frozen statement was not reported}"
    grep -qF "fresh.lock does not match" "$out" && bad="${bad:-the refreshed lock still does not match}"
  fi
  if [ -z "$bad" ]; then
    sed -i 's/c = .green := sorry/c = .red := sorry/' Statements/P999/Canary.lean
    audit --check || bad="the audit fails after --refresh-new-locks"
  fi
  if [ -z "$bad" ]; then
    git update-ref -d refs/remotes/origin/main
    audit --refresh-new-locks && bad="--refresh-new-locks ran without origin/main"
  fi
  if [ -z "$bad" ]; then
    echo "ok   $current"
  else
    echo "FAIL $current: $bad"
    tail -n 30 "$out"
    failures=$((failures + 1))
  fi
  git update-ref -d refs/remotes/origin/main 2>/dev/null
  reset
}

all=(sorry_proof changed_definition def_in_statements proof_in_statements removed_proof
  removed_refutation missing_lock orphan_lock edited_lock changed_statement custom_axiom
  wrong_type statement_uses_statements unknown_marker unsafe_library library_imports_statements
  library_in_statements_namespace unchecked_declaration refresh_new_locks)

failures=0
current=""
reset() { git reset -q --hard && git clean -qfd; }
# expect <message> ...: the audit fails, and its output contains every message.
expect() {
  if audit --check; then
    echo "FAIL $current: the audit passed"
    tail -n 30 "$out"
    failures=$((failures + 1))
  else
    local missing=""
    for m in "$@"; do grep -qF -- "$m" "$out" || missing="$m"; done
    if [ -n "$missing" ]; then
      echo "FAIL $current: the audit failed, but its output lacks: $missing"
      tail -n 30 "$out"
      failures=$((failures + 1))
    else
      echo "ok   $current"
    fi
  fi
  reset
}

scenarios=("$@")
[ ${#scenarios[@]} = 0 ] && scenarios=("${all[@]}")
for s in "${scenarios[@]}"; do
  current=$s
  "$s"
done

if [ "$failures" = 0 ]; then
  echo "canaries: the audit passes the correct example and fails all ${#scenarios[@]} scenarios"
else
  echo "canaries: $failures of ${#scenarios[@]} scenarios misbehave" >&2
  exit 1
fi
