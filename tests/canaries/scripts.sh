#!/usr/bin/env bash
# Canaries of the CI scripts that run before any build: scripts/ci/check-meta.py (metaprogramming
# blacklist) and scripts/ci/check-additive.sh (append-only Statements/ and proof markers). Each
# must accept the harmless cases and refuse every forbidden one. Needs no Lean; works in a
# temporary directory.
#
# Usage: bash tests/canaries/scripts.sh
set -uo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
work="$(mktemp -d "${TMPDIR:-/tmp}/incognita-ci-canaries.XXXXXX")"
trap 'rm -rf "$work"' EXIT
failures=0
pass() { echo "ok   $1"; }
fail() { echo "FAIL $1"; failures=$((failures + 1)); }

# --- check-meta.py ------------------------------------------------------------------------------

meta() { python3 "$root/scripts/ci/check-meta.py" "$work/meta.lean" > "$work/meta.out" 2>&1; }

cat > "$work/meta.lean" <<'EOF'
/-!
# Harmless

This docstring says the algorithm is initialized, that `syntax` and `macro` are words, and
mentions #eval, set_option and unsafe. /- A nested comment with run_cmd. -/
-/

/-- The elaboration of `x` uses `native_decide` nowhere. -/
theorem elaborate_macroscopic (h' : True) : True := h' -- elab, meta, extern in a comment
def «weird -- name» : Nat := 1
def my_macro_lemma : Nat := 'a'.toNat
def externalities : Nat := 2
@[simp, reducible] def unsafeish : Nat := 3
attribute [local simp] my_macro_lemma
EOF
if meta; then pass "check-meta: harmless file"; else fail "check-meta: harmless file refused"; cat "$work/meta.out"; fi

bad=(
  '#eval 1 + 1'
  '#eval! 1 + 1'
  'run_cmd pure ()'
  'run_elab pure ()'
  'run_meta pure ()'
  'example : True := by run_tac pure ()'
  'def x : Nat := by_elab pure (Lean.mkNatLit 0)'
  'elab "foo" : term => pure (Lean.mkNatLit 0)'
  'macro "foo" : term => `(0)'
  'macro_rules | `(foo) => `(0)'
  'syntax "foo" : term'
  'declare_syntax_cat foo'
  'initialize pure ()'
  'unsafe def x : Nat := 0'
  'public meta import Lean'
  'meta def x : Nat := 0'
  '@[implemented_by y] def x : Nat := 0'
  '@[extern "c_x"] opaque x : Nat'
  'set_option maxHeartbeats 0 in'
  'simproc foo (_) := fun _ => pure .continue'
  'example : 2 + 2 = 4 := by native_decide'
  'register_simp_attr my_simp'
  '@[command_elab foo] def x := 0'
  '@[term_elab foo] def x := 0'
  '@[tactic foo] def x := 0'
  '@[delab app.foo] def x := 0'
  '@[app_unexpander foo] def x := 0'
  '@[env_linter] def x := 0'
  '@[init y] def x := 0'
  '@[export x] def x := 0'
  '@[csimp] theorem x : @a = @b := rfl'
  '@[builtin_term_elab foo] def x := 0'
  'attribute [local tactic foo] bar'
  'def s : String := "-- hidden"'
  'notation:50 a " --| " b => a + b'
  'def x := 1 /- unterminated'
)
for snippet in "${bad[@]}"; do
  printf '%s\n' "$snippet" > "$work/meta.lean"
  if meta; then fail "check-meta accepts: $snippet"; else pass "check-meta refuses: $snippet"; fi
done

# --- check-additive.sh --------------------------------------------------------------------------

repo="$work/additive"
mkdir -p "$repo" && cd "$repo" || exit 2
git init -q -b main
g() { git -c user.name=canary -c user.email=canary@invalid "$@"; }
mkdir -p scripts/ci Statements/P001 catalogue/results
cp "$root/scripts/ci/check-additive.sh" scripts/ci/
printf 'module\n\npublic import Statements.P001.A\n' > Statements.lean
echo 'theorem a : True := sorry' > Statements/P001/A.lean
echo 'sha256 0' > Statements/P001/a.lock
echo '# markers' > catalogue/results/README.md
echo 'statement = "a"' > catalogue/results/P001-a.toml
g add -A && g commit -qm base
base=$(git rev-parse HEAD)

# case <name> <expected: pass|fail> <commands...>: run the commands on a branch from base.
case_() {
  local name=$1 want=$2
  shift 2
  g checkout -q -B "t-$RANDOM" "$base"
  eval "$*"
  g add -A && g commit -qm "$name" --allow-empty
  if bash scripts/ci/check-additive.sh "$base" > "$work/add.out" 2>&1; then got=pass; else got=fail; fi
  if [ "$got" = "$want" ]; then
    pass "check-additive: $name ($want)"
  else
    fail "check-additive: $name (expected $want, got $got)"
    cat "$work/add.out"
  fi
}

case_ "new statement, lock, import and marker" pass \
  "echo 'theorem b : True := sorry' > Statements/P001/B.lean; echo 'sha256 1' > Statements/P001/b.lock;" \
  "echo 'public import Statements.P001.B' >> Statements.lean; echo 'statement = \"b\"' > catalogue/results/P001-b.toml"
case_ "README of the markers edited" pass "echo more >> catalogue/results/README.md"
case_ "nothing changed" pass "true"
case_ "statement edited" fail "echo 'theorem a : False := sorry' > Statements/P001/A.lean"
case_ "lock edited" fail "echo 'sha256 2' > Statements/P001/a.lock"
case_ "lock removed" fail "rm Statements/P001/a.lock"
case_ "statement renamed" fail "git mv Statements/P001/A.lean Statements/P001/A2.lean"
case_ "import removed" fail "printf 'module\n\n' > Statements.lean"
case_ "other line added to Statements.lean" fail "echo 'set_option x true' >> Statements.lean"
case_ "marker edited" fail "echo 'status = \"refuted\"' >> catalogue/results/P001-a.toml"
case_ "marker removed" fail "rm catalogue/results/P001-a.toml"

if [ "$failures" = 0 ]; then
  echo "CI script canaries: all passed"
else
  echo "CI script canaries: $failures failures" >&2
  exit 1
fi
