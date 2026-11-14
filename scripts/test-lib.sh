#!/usr/bin/env bash
# Offline tests of scripts/lib.sh: sanitising, trusted statuses, PR rows and busy targets, the path
# whitelist (D12), merge categories, the mechanical resolution of root import files, the state.
# Needs git, jq, python3. No GitHub, no sudo, no Claude. Usage: bash scripts/test-lib.sh
# shellcheck disable=SC2034  # variables are read inside the eval'd checks
set -u -o pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
t=$(mktemp -d)
trap 'rm -rf "$t"' EXIT
export INCOGNITA_HOME=$t/home INCOGNITA_NIGHT=test INCOGNITA_GH_REPO=owner/repo
export INCOGNITA_REPO=$t/repo
mkdir -p "$INCOGNITA_REPO"
# shellcheck source=scripts/lib.sh
. "$here/lib.sh"
init_state
OWNER=owner
fails=0
ok() { if eval "$2"; then echo "ok   $1"; else echo "FAIL $1"; fails=$(( fails + 1 )); fi; }

# ---- sanitize
s=$(printf 'a <!-- x --> @bob fixes #3 sk-ant-oat01-ABCDEFGHIJKLMNOP \xe2\x80\xaeevil\n' | sanitize 1000)
ok "sanitize escapes <!--" '[[ "$s" == *"&lt;!-- x"* ]]'
ok "sanitize breaks @mentions" '[[ "$s" == *$'"'"'@​bob'"'"'* ]]'
ok "sanitize neutralises closing keywords" '[[ "$s" != *"fixes #3"* ]]'
ok "sanitize redacts tokens" '[[ "$s" != *"sk-ant-oat01-ABC"* && "$s" == *"[redacted]"* ]]'
ok "sanitize drops bidi overrides" '[[ "$s" != *$'"'"'‮'"'"'* ]]'
long=$(python3 -c 'print("x" * 70000)' | sanitize 60000)
ok "sanitize truncates" '[ ${#long} -lt 60200 ] && [[ "$long" == *"truncated by the script"* ]]'
ok "one_line" '[ "$(printf "a\nb  c\n" | one_line 10)" = "a b c" ]'

# ---- statuses and verdicts
sts=$(printf '%s\t%s\t%s\t%s\n' \
  "Referee scope" success yes "role=referee-scope verdict=accept pr=4" \
  "Referee proofs" failure no "role=referee-proofs verdict=accept pr=4" \
  "Incognita review" success yes "role=review-pr verdict=approve pr=5 copied-from=abc")
ok "trusted verdict" '[ "$(verdict_in "$sts" "Referee scope" referee-scope)" = accept ]'
ok "untrusted status ignored" '[ "$(verdict_in "$sts" "Referee proofs" referee-proofs)" = none ]'
ok "role must match" '[ "$(verdict_in "$sts" "Incognita review" review-statements)" = none ]'
ok "copied status parsed" '[ "$(verdict_in "$sts" "Incognita review" "review-pr|review-statements")" = approve ]'

# ---- PR rows, busy targets
cat > "$t/prs.json" <<'EOF'
[
 {"number": 7, "title": "Paper", "body": "Role: `write-paper`. Target: `BatchedBandits`. Model: `opus`.\n\nx",
  "headRefName": "agent/write-paper-1", "headRefOid": "aaa", "isCrossRepository": false, "isDraft": false,
  "labels": [], "mergeable": "MERGEABLE", "author": {"login": "owner"}, "baseRefName": "main",
  "statusCheckRollup": [{"name": "Build and check", "status": "COMPLETED", "conclusion": "SUCCESS"},
                        {"name": "Compile papers", "status": "COMPLETED", "conclusion": "SUCCESS"}]},
 {"number": 8, "title": "Fork", "body": "Role: `prove`. Target: `P001-x`. Model: `opus`.",
  "headRefName": "agent/prove-1", "headRefOid": "bbb", "isCrossRepository": true, "isDraft": false,
  "labels": [], "mergeable": "MERGEABLE", "author": {"login": "mallory"}, "baseRefName": "main", "statusCheckRollup": []},
 {"number": 9, "title": "Human", "body": "no role line", "headRefName": "fix-docs", "headRefOid": "ccc",
  "isCrossRepository": false, "isDraft": false, "labels": [{"name": "x"}], "mergeable": "CONFLICTING",
  "author": {"login": "owner"}, "baseRefName": "main", "statusCheckRollup": []},
 {"number": 10, "title": "Draft", "body": "Role: `prove`. Target: `P001-x`. Model: `opus`.",
  "headRefName": "agent/prove-2", "headRefOid": "ddd", "isCrossRepository": false, "isDraft": true,
  "labels": [{"name": "incomplete"}], "mergeable": "UNKNOWN", "author": {"login": "owner"}, "baseRefName": "main",
  "statusCheckRollup": [{"name": "Build and check", "status": "IN_PROGRESS", "conclusion": ""}]}
]
EOF
rows=$(agent_rows "$t/prs.json")
ok "agent rows: same-repository agent PRs only" '[ "$(printf "%s\n" "$rows" | cut -f1 | tr "\n" " ")" = "7 10 " ]'
ok "row fields" '[ "$(printf "%s\n" "$rows" | head -n1)" = "$(printf "7\taaa\tagent/write-paper-1\tready\tMERGEABLE\twrite-paper\tBatchedBandits\t-\tSUCCESS")" ]'
ok "draft row" '[ "$(printf "%s\n" "$rows" | tail -n1 | cut -f4,8,9)" = "$(printf "draft\tincomplete\tIN_PROGRESS")" ]'
busy=$(busy_pairs "$t/prs.json")
ok "busy pairs ignore forks" '[ "$busy" = "$(printf "write-paper BatchedBandits\nprove P001-x")" ]'
ok "open-prs.md" '[ "$(open_prs_md "$t/prs.json" | wc -l)" = 3 ]'

# ---- the build of a head: "Build and check" (CI) and "Compile papers" (Papers), CI_JQ
cat > "$t/prs2.json" <<'EOF'
[
 {"number": 11, "body": "Role: `write-paper`. Target: `BB`. Model: `m`.", "headRefName": "agent/a", "headRefOid": "e",
  "isCrossRepository": false, "isDraft": false, "labels": [], "mergeable": "MERGEABLE", "author": {"login": "owner"}, "baseRefName": "main",
  "statusCheckRollup": [{"name": "Build and check", "status": "COMPLETED", "conclusion": "SUCCESS"},
                        {"name": "Compile papers", "status": "COMPLETED", "conclusion": "FAILURE"}]},
 {"number": 12, "body": "Role: `revise`. Target: `P001-x`. Model: `m`.", "headRefName": "agent/b", "headRefOid": "f",
  "isCrossRepository": false, "isDraft": false, "labels": [], "mergeable": "MERGEABLE", "author": {"login": "owner"}, "baseRefName": "main",
  "statusCheckRollup": [{"name": "Build and check", "status": "COMPLETED", "conclusion": "SUCCESS"}]},
 {"number": 13, "body": "Role: `prove`. Target: `P001-x`. Model: `m`.", "headRefName": "agent/c", "headRefOid": "g",
  "isCrossRepository": false, "isDraft": false, "labels": [], "mergeable": "MERGEABLE", "author": {"login": "owner"}, "baseRefName": "main",
  "statusCheckRollup": [{"name": "Compile papers", "status": "COMPLETED", "conclusion": "SUCCESS"},
                        {"name": "Build and check", "status": "COMPLETED", "conclusion": "SUCCESS"},
                        {"name": "Summary PDF", "status": "COMPLETED", "conclusion": "FAILURE"}]},
 {"number": 14, "body": "Role: `prove`. Target: `P001-x`. Model: `m`.", "headRefName": "agent/d", "headRefOid": "h",
  "isCrossRepository": false, "isDraft": false, "labels": [], "mergeable": "MERGEABLE", "author": {"login": "owner"}, "baseRefName": "main",
  "statusCheckRollup": [{"name": "Build and check", "status": "COMPLETED", "conclusion": "SUCCESS"},
                        {"name": "Compile papers", "status": "IN_PROGRESS", "conclusion": ""}]},
 {"number": 15, "body": "Role: `garden`. Target: `-`. Model: `m`.", "headRefName": "agent/e", "headRefOid": "i",
  "isCrossRepository": false, "isDraft": false, "labels": [], "mergeable": "MERGEABLE", "author": {"login": "owner"}, "baseRefName": "main",
  "statusCheckRollup": [{"name": "Build and check", "status": "COMPLETED", "conclusion": "SUCCESS"}]}
]
EOF
ci_col() { agent_rows "$t/prs2.json" | awk -F'\t' -v n="$1" '$1 == n { print $9 }'; }
ok "CI: a paper PR needs Compile papers (failed)" '[ "$(ci_col 11)" = FAILURE ]'
ok "CI: a paper PR without Compile papers is not green" '[ "$(ci_col 12)" = NONE ]'
ok "CI: other checks are ignored" '[ "$(ci_col 13)" = SUCCESS ]'
ok "CI: Compile papers counts for any PR when it runs" '[ "$(ci_col 14)" = IN_PROGRESS ]'
ok "CI: a non-paper PR needs only Build and check" '[ "$(ci_col 15)" = SUCCESS ]'
ok "CI: the same rule in agent.sh (ci_of)" '[ "$(jq -r --arg role write-paper "$CI_JQ"'"'"' .[0] | ci_of($role)'"'"' "$t/prs2.json")" = FAILURE ]'

# ---- path whitelist on a scratch repository
cd "$INCOGNITA_REPO" || exit 1
git init -q -b main . && git config user.name t && git config user.email t@t
mkdir -p Statements Incognita papers literature
printf 'module\n\npublic import Statements.Basic\n' > Statements.lean
printf 'module\n\npublic import Incognita.Basic\n' > Incognita.lean
echo x > Statements/Basic.lean; echo x > Incognita/Basic.lean; echo r > README.md
git add -A && git commit -qm base && git update-ref refs/remotes/origin/main HEAD
base=$(git rev-parse HEAD)
try() {  # name role paper expect(0 pass, 1 refuse) setup-commands
  local name=$1 role=$2 paper=$3 expect=$4 rc=0; shift 4
  git checkout -q -f "$base" && git clean -qfdx
  eval "$*"
  git add -A && git commit -qm change
  check_paths "$role" "$paper" "$base" HEAD 2>"$t/why" || rc=1
  ok "whitelist: $name" '[ "$rc" = "$expect" ]'
  [ "$rc" = "$expect" ] || cat "$t/why"
}
try "write-paper adds a paper, notebook, exploration, literature" write-paper "" 0 \
  'mkdir -p papers/P001-test/notebook Exploration literature/notes; echo a > papers/P001-test/paper.tex; echo b > papers/P001-test/notebook/x.py; echo c > Exploration/A.lean; echo d > literature/notes/K.md'
try "write-paper may not touch README.md" write-paper "" 1 'mkdir -p papers/P001-t; echo a > papers/P001-t/paper.tex; echo s >> README.md'
try "write-paper adds exactly one paper" write-paper "" 1 'mkdir -p papers/P001-a papers/P002-b; echo a > papers/P001-a/x; echo b > papers/P002-b/x'
try "symlinks refused" write-paper "" 1 'mkdir -p papers/P001-t; ln -s /etc/passwd papers/P001-t/link'
try "dot paths refused" write-paper "" 1 'mkdir -p papers/P001-t/.hidden; echo a > papers/P001-t/.hidden/x'
try "AGENTS.md anywhere refused" write-paper "" 1 'mkdir -p papers/P001-t; echo a > papers/P001-t/AGENTS.md'
try "files over 1 MB refused" write-paper "" 1 'mkdir -p papers/P001-t; head -c 1100000 /dev/zero | tr "\0" a > papers/P001-t/big.txt'
try "tokens refused" write-paper "" 1 'mkdir -p papers/P001-t; echo "sk-ant-oat01-AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA" > papers/P001-t/x'
try "revise changes its paper" revise P001-test 0 'mkdir -p papers/P001-test; echo v2 > papers/P001-test/paper.tex'
try "revise may not change another paper" revise P001-test 1 'mkdir -p papers/P002-other; echo a > papers/P002-other/x'
try "formalize-statements adds statements and imports" formalize-statements P001-test 0 \
  'mkdir -p Statements/P001 papers/P001-test; echo t > Statements/P001/thm.lean; echo h > Statements/P001/thm.lock; echo "public import Statements.P001.thm" >> Statements.lean; echo b > papers/P001-test/blueprint.md'
try "formalize-statements may not modify a frozen statement" formalize-statements P001-test 1 'echo y >> Statements/Basic.lean'
try "Statements.lean may not lose an import" formalize-statements P001-test 1 'printf "module\n\n" > Statements.lean'
try "root files: imports only" prove P001-test 1 'echo "theorem x : True := trivial" >> Incognita.lean'
try "prove: library, results marker, blueprint.md, formalisation.tex, errata, corrections" prove P001-test 0 \
  'mkdir -p catalogue/results papers/P001-test; echo l > Incognita/L.lean; echo m > catalogue/results/P001-thm.toml; echo b > papers/P001-test/blueprint.md; echo f > papers/P001-test/formalisation.tex; echo e > papers/P001-test/errata.md; echo s > papers/P001-test/statement-corrections.md'
try "prove may not edit the paper" prove P001-test 1 'mkdir -p papers/P001-test; echo p > papers/P001-test/paper.tex'
try "prove may not touch Statements/" prove P001-test 1 'mkdir -p Statements/P001; echo t > Statements/P001/x.lean'
try "bibliographer: literature and catalogue only" bibliographer "" 1 'echo l > Incognita/L.lean'
try "review roles change nothing" review-pr "" 1 'mkdir -p literature; echo l > literature/x.md'
try "fix-main may fix the library" fix-main "" 0 'echo z >> Incognita/Basic.lean'

# ---- the table of AGENTS.md §2, line by line (role_allows)
# write-paper: one new directory with paper.tex, refs.bib, META.toml, notebook/; literature; drafts
try "write-paper: refs.bib, META.toml" write-paper "" 0 'mkdir -p papers/P001-t; echo a > papers/P001-t/paper.tex; echo b > papers/P001-t/refs.bib; echo c > papers/P001-t/META.toml'
try "write-paper may not write blueprint.md" write-paper "" 1 'mkdir -p papers/P001-t; echo a > papers/P001-t/paper.tex; echo b > papers/P001-t/blueprint.md'
try "write-paper may not write errata.md" write-paper "" 1 'mkdir -p papers/P001-t; echo a > papers/P001-t/paper.tex; echo b > papers/P001-t/errata.md'
try "write-paper: no file in a subdirectory but notebook/" write-paper "" 1 'mkdir -p papers/P001-t/fig; echo a > papers/P001-t/paper.tex; echo b > papers/P001-t/fig/x.tex'
try "write-paper may not touch the library" write-paper "" 1 'mkdir -p papers/P001-t; echo a > papers/P001-t/paper.tex; echo l > Incognita/L.lean'
try "write-paper may not touch catalogue/" write-paper "" 1 'mkdir -p papers/P001-t catalogue/definitions; echo a > papers/P001-t/paper.tex; echo d > catalogue/definitions/X.toml'
try "write-paper: a paper is required" write-paper "" 1 'mkdir -p literature; echo l > literature/x.md'
try "write-paper: bad paper id" write-paper "" 1 'mkdir -p papers/P01-t; echo a > papers/P01-t/paper.tex'
# revise: its paper's sources, notebook and errata.md (Revised in lines); literature; drafts
try "revise: notebook, errata.md, refs.bib, META.toml, literature, exploration" revise P001-test 0 \
  'mkdir -p papers/P001-test/notebook literature Exploration; echo n > papers/P001-test/notebook/N.md; echo e > papers/P001-test/errata.md; echo r > papers/P001-test/refs.bib; echo m > papers/P001-test/META.toml; echo l > literature/x.md; echo x > Exploration/X.lean'
try "revise may not write blueprint.md" revise P001-test 1 'mkdir -p papers/P001-test; echo b > papers/P001-test/blueprint.md'
try "revise may not write statement-corrections.md" revise P001-test 1 'mkdir -p papers/P001-test; echo b > papers/P001-test/statement-corrections.md'
try "revise may not touch the library" revise P001-test 1 'echo l > Incognita/L.lean'
# formalize-statements
try "formalize-statements: definitions, catalogue/definitions, errata, corrections" formalize-statements P001-test 0 \
  'mkdir -p Incognita/BB catalogue/definitions papers/P001-test; echo d > Incognita/BB/Grid.lean; echo "public import Incognita.BB.Grid" >> Incognita.lean; echo c > catalogue/definitions/Grid.toml; echo e > papers/P001-test/errata.md; echo s > papers/P001-test/statement-corrections.md'
try "formalize-statements may not edit paper.tex" formalize-statements P001-test 1 'mkdir -p papers/P001-test; echo p > papers/P001-test/paper.tex'
try "formalize-statements may not write the notebook" formalize-statements P001-test 1 'mkdir -p papers/P001-test/notebook; echo p > papers/P001-test/notebook/N.md'
try "formalize-statements may not write formalisation.tex" formalize-statements P001-test 1 'mkdir -p papers/P001-test; echo p > papers/P001-test/formalisation.tex'
try "formalize-statements: only .lean and .lock under Statements/P<nnn>/" formalize-statements P001-test 1 'mkdir -p Statements/P001; echo x > Statements/P001/notes.md'
try "formalize-statements: Statements/<dir> is a paper prefix" formalize-statements P001-test 1 'mkdir -p Statements/Foo; echo x > Statements/Foo/a.lean'
try "formalize-statements may not touch another paper" formalize-statements P001-test 1 'mkdir -p papers/P002-x; echo b > papers/P002-x/blueprint.md'
try "formalize-statements may not write proof markers" formalize-statements P001-test 1 'mkdir -p catalogue/results; echo m > catalogue/results/P001-a.toml'
# prove
try "prove may not write the notebook" prove P001-test 1 'mkdir -p papers/P001-test/notebook; echo n > papers/P001-test/notebook/n.py'
try "prove: a proof marker is P<nnn>-<name>.toml" prove P001-test 1 'mkdir -p catalogue/results; echo m > catalogue/results/thm.toml'
try "prove may not write catalogue/definitions" prove P001-test 1 'mkdir -p catalogue/definitions; echo d > catalogue/definitions/X.toml'
try "prove may not delete a library file" prove P001-test 1 'git rm -q Incognita/Basic.lean'
# bibliographer
try "bibliographer: literature, attribution, refs.bib of any paper" bibliographer "" 0 \
  'mkdir -p literature/notes catalogue/attribution papers/P007-z; echo n > literature/notes/K.md; echo a > catalogue/attribution/P001.md; echo r > papers/P007-z/refs.bib'
try "bibliographer may not write proof markers" bibliographer "" 1 'mkdir -p catalogue/results; echo m > catalogue/results/P001-a.toml'
try "bibliographer may not write catalogue/relations.toml" bibliographer "" 1 'mkdir -p catalogue; echo r > catalogue/relations.toml'
try "bibliographer may not edit a paper" bibliographer "" 1 'mkdir -p papers/P001-test; echo p > papers/P001-test/paper.tex'
try "bibliographer writes no Lean draft" bibliographer "" 1 'mkdir -p Exploration; echo x > Exploration/X.lean'
# garden
try "garden: library theorems, relations.toml, garden.md, exploration" garden "" 0 \
  'mkdir -p Incognita/BB catalogue Exploration; echo r > Incognita/BB/Relations.lean; echo r > catalogue/relations.toml; echo g > catalogue/garden.md; echo x > Exploration/X.lean'
try "garden may not write literature/" garden "" 1 'mkdir -p literature; echo l > literature/x.md'
try "garden may not write attribution audits" garden "" 1 'mkdir -p catalogue/attribution; echo a > catalogue/attribution/P001.md'
# fix-main
try "fix-main: Statements.lean imports" fix-main "" 0 'echo "public import Statements.P001.x" >> Statements.lean'
try "fix-main may not touch papers/" fix-main "" 1 'mkdir -p papers/P001-test; echo p > papers/P001-test/blueprint.md'
try "fix-main may not touch Statements/" fix-main "" 1 'mkdir -p Statements/P001; echo t > Statements/P001/x.lean'
# the owner's paths, for every role
try "README.md anywhere is the owner's" bibliographer "" 1 'mkdir -p literature; echo r > literature/README.md'
try "withdrawn.md is the owner's" revise P001-test 1 'mkdir -p papers/P001-test; echo w > papers/P001-test/withdrawn.md'
try "tests/ is the owner's" prove P001-test 1 'mkdir -p tests; echo t > tests/x.sh'
try "the template of notes is the owner's" bibliographer "" 1 'mkdir -p literature/notes; echo t > literature/notes/TEMPLATE.md'
git checkout -q -f "$base"; mkdir -p papers/P001-test/notebook; echo n > papers/P001-test/notebook/N.md
git add -A; git commit -qm paper; base2=$(git rev-parse HEAD)
git rm -q papers/P001-test/notebook/N.md; git commit -qm del
ok "whitelist: nothing under papers/ is deleted" '! check_paths revise P001-test "$base2" HEAD 2>/dev/null'

# ---- merge categories, definitions in proof PRs
ok "category papers" '[ "$(path_category paper papers/P001-a/paper.tex M)" = papers ]'
ok "papers/ in a proof PR: blueprint.md, formalisation.tex ok; errata, paper.tex for the owner" '[ "$(path_category generic papers/P001-a/blueprint.md M)" = proofs ] && [ "$(path_category generic papers/P001-a/formalisation.tex A)" = proofs ] && [ "$(path_category generic papers/P001-a/errata.md A)" = other ] && [ "$(path_category generic papers/P001-a/paper.tex M)" = other ]'
ok "refs.bib fixed by the bibliographer: literature" '[ "$(path_category generic papers/P001-a/refs.bib M)" = literature ]'
ok "category statements" '[ "$(path_category generic Statements/P/x.lean A)" = statements ]'
ok "results markers: additions are proofs" '[ "$(path_category generic catalogue/results/x.toml A)" = proofs ] && [ "$(path_category generic catalogue/results/x.toml M)" = literature ]'
git checkout -q -f "$base"; mkdir -p Incognita/P; printf 'theorem a : True := trivial\n' > Incognita/P/A.lean; git add -A; git commit -qm thm
ok "a theorem is a proof" 'adds_only_theorems "$base" HEAD'
printf 'noncomputable def f : Nat := 0\n' >> Incognita/P/A.lean; git add -A; git commit -qm def
ok "a def is not" '! adds_only_theorems "$base" HEAD'

# ---- mechanical resolution of root import files
git checkout -q -f -B side "$base"; printf 'public import Incognita.Side\n' >> Incognita.lean; git commit -qam side
git checkout -q -f -B main2 "$base"; printf 'public import Incognita.Alpha\n' >> Incognita.lean; git commit -qam alpha
git checkout -q -f side
GIT_EDITOR=true git rebase -q main2 >/dev/null 2>&1
ok "rebase conflicts on the root file" '[ "$(git diff --name-only --diff-filter=U)" = Incognita.lean ]'
resolve_imports "$INCOGNITA_REPO" Incognita.lean && git add Incognita.lean && GIT_EDITOR=true git rebase --continue >/dev/null 2>&1
ok "sorted union of imports" '[ "$(cat Incognita.lean)" = "$(printf "module\n\npublic import Incognita.Alpha\npublic import Incognita.Basic\npublic import Incognita.Side")" ]'

# ---- errata and statement corrections (entry_flags; AGENTS.md §6.6)
flags=$(cat <<'EOF' | entry_flags
# Errata of P001

## E1 (2026-11-20, prove, m)
- Node: thm:main
- Frozen statement: `Incognita.Statements.P001.lower_bound`
- Problem: false for one batch.
Revised in the version of 2026-11-22: hypothesis added.

## E2 (2026-11-21, formalize-statements, m)
- Node: lem:tail
- Problem: a gap.

## E3 (2026-11-21, prove, m)
- Frozen statement: Incognita.Statements.P001.upper_bound
- Revised in the version of 2026-11-23: constant fixed.
- Resolved by Incognita.Statements.P001.upper_bound_v2 (statements pull request #9).

## Notes
Resolved by nothing: not an entry.
EOF
)
ok "entry_flags" '[ "$flags" = "$(printf "E1 1 0 Incognita.Statements.P001.lower_bound\nE2 0 0 -\nE3 1 1 Incognita.Statements.P001.upper_bound")" ]'
git checkout -q -f "$base"; mkdir -p papers/P001-test
printf '## E1 (d)\n- Node: thm:main\n\n## E2 (d)\nRevised in the version of d: x\n\n## E3 (d)\n- Frozen statement: Incognita.Statements.P001.a\nRevised in v\nResolved by Incognita.Statements.P001.a_v2\n' > papers/P001-test/errata.md
printf '## SC1 (d)\n- Frozen statement: Incognita.Statements.P001.b\n\n## SC2 (d)\n- Frozen statement: Incognita.Statements.P001.c\nResolved by Incognita.Statements.P001.c_v2\n' > papers/P001-test/statement-corrections.md
git add -A; git commit -qm errata; git update-ref refs/remotes/origin/main HEAD
ok "disputed: an erratum neither revised nor resolved" '[ "$(disputed_entries P001-test)" = E1 ]'
ok "to freeze: errata revised, corrections not resolved" '[ "$(freeze_entries P001-test | tr "\n" " ")" = "E2 SC1 " ]'
ok "superseded: frozen statements of resolved entries" '[ "$(superseded P001-test | tr "\n" " ")" = "a c " ]'
ok "no errata file: nothing" '[ -z "$(disputed_entries P009-none)$(freeze_entries P009-none)" ]'
git update-ref refs/remotes/origin/main "$base"

# ---- state
record_attempt prove P001-x fail no-commit
record_attempt prove P001-x fail no-commit
ok "night failures counted" '[ "$(night_fails prove P001-x)" = 2 ]'
INCOGNITA_PARK_AFTER=3 record_attempt prove P001-x fail no-commit
ok "parked after INCOGNITA_PARK_AFTER failures" 'is_parked prove P001-x'
d=$(INCOGNITA_DEADLINE=02:45 deadline_epoch)
ok "deadline in the next 24 h" '[ "$d" -gt "$(now)" ] && [ "$d" -le $(( $(now) + 86400 )) ]'

echo "$fails failure(s)"
[ "$fails" = 0 ]
