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

# --- certify.py check (library metadata) ------------------------------------------------------

lib="$work/library"
mkdir -p "$lib/papers/P001-one" "$lib/roadmaps/RB" && cd "$lib" || exit 2
git init -q -b main
printf 'roadmap = "RB"\nkind = "internal"\ndirections = ["D1"]\nauthors = ["m"]\nversion = 1\ndepends_on = []\n' > papers/P001-one/META.toml
cat > papers/P001-one/paper.tex <<'EOF'
\title{One}
\begin{theorem}\label{thm:main} T. \end{theorem}
\section{Open questions}
\begin{openquestion}\label{oq:a} Q? \end{openquestion}
EOF
printf '# Candidate directions of R\n\n## C1 (d, from P001v1 oq:a)\n- Title: -\n- Statement: Q?\n- Source: s\n- Rating: r\n' > roadmaps/RB/directions.md
printf '# R\n\n| | |\n|---|---|\n| Status | **approved** (d) |\n' > roadmaps/RB/ROADMAP.md
mkdir -p catalogue
printf '| Date | Model | Item | Check | Outcome | Main |\n|---|---|---|---|---|---|\n| d | m | P001 | known-cases | confirmed: ok | x |\n' > catalogue/garden.md
printf '# Errata of P001\n\n## E1 (d, prove, m)\n- Node: thm:main\n- Problem: p.\n' > papers/P001-one/errata.md
g add -A && g commit -qm base
lbase=$(git rev-parse HEAD)
# lcase <name> <expected: pass|fail> <commands...>: run the commands on a branch from lbase.
lcase() {
  local name=$1 want=$2
  shift 2
  g checkout -q -f -B "l-$RANDOM" "$lbase" && git clean -qfd
  eval "$*"
  if python3 "$root/scripts/certify.py" check --base "$lbase" > "$work/lib.out" 2>&1; then got=pass; else got=fail; fi
  if [ "$got" = "$want" ]; then pass "certify check: $name ($want)"
  else fail "certify check: $name (expected $want, got $got)"; cat "$work/lib.out"; fi
}
lcase "a consistent library" pass "true"
lcase "a roadmap that does not exist" fail "sed -i 's/^roadmap = .*/roadmap = \"Nope\"/' papers/P001-one/META.toml"
lcase "a roadmap name that is a path" fail "sed -i 's#^roadmap = .*#roadmap = \"../RB\"#' papers/P001-one/META.toml"
lcase "a row of garden.md appended" pass "echo '| d | m2 | P001 | known-cases | confirmed: again | y |' >> catalogue/garden.md"
lcase "a row of garden.md changed" fail "sed -i 's/confirmed: ok/failed: no/' catalogue/garden.md"
lcase "an erratum revised" pass "echo 'Revised in the version of d: fixed.' >> papers/P001-one/errata.md"
lcase "an erratum edited" fail "sed -i 's/Problem: p./Problem: q./' papers/P001-one/errata.md"
lcase "an erratum deleted" fail "echo '# Errata of P001' > papers/P001-one/errata.md"
lcase "\\leanok written in a paper" fail "printf '%s\n' '\\leanok' >> papers/P001-one/paper.tex"
lcase "a new paper.tex without a new version" fail "echo x >> papers/P001-one/paper.tex"
lcase "a new paper.tex with a new version" pass "echo x >> papers/P001-one/paper.tex; sed -i 's/^version = 1/version = 2/' papers/P001-one/META.toml; python3 '$root/scripts/certify.py' bib >/dev/null"
lcase "a citation of a library paper not in depends_on" fail "printf '%s\n' 'See \\cite{INC-P001}.' >> papers/P001-one/paper.tex; sed -i 's/^version = 1/version = 2/' papers/P001-one/META.toml; python3 '$root/scripts/certify.py' bib >/dev/null"
lcase "a candidate direction edited" fail "sed -i 's/Statement: Q?/Statement: R?/' roadmaps/RB/directions.md"
lcase "a candidate direction dropped" pass "echo 'Dropped (d, garden, m): known.' >> roadmaps/RB/directions.md"
cd "$root" || exit 2

if [ "$failures" = 0 ]; then
  echo "CI script canaries: all passed"
else
  echo "CI script canaries: $failures failures" >&2
  exit 1
fi
