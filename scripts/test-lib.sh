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
mkdir -p Statements Incognita papers literature roadmaps/BB
printf 'module\n\npublic import Statements.Basic\n' > Statements.lean
printf 'module\n\npublic import Incognita.Basic\n' > Incognita.lean
echo x > Statements/Basic.lean; echo x > Incognita/Basic.lean; echo r > README.md
printf '# Roadmap\n\n| | |\n|---|---|\n| Status | **approved** (2026-11-14) |\n| Domain | `bandits` |\n\n## Open directions\n\n- **D1. One.** Text.\n- **D2. Two.** On hold.\n' > roadmaps/BB/ROADMAP.md
printf 'Reviewed by owner: 2026-11-14\n' > roadmaps/BB/KNOWN.md
printf '# Candidate directions of BB\n' > roadmaps/BB/directions.md
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
# library.bib, dependency checks (AGENTS.md 5.6)
try "write-paper may regenerate papers/library.bib" write-paper "" 0 'mkdir -p papers/P001-t; echo a > papers/P001-t/paper.tex; echo b > papers/library.bib'
try "revise: dependency-checks.md, library.bib" revise P001-test 0 'mkdir -p papers/P001-test; echo d > papers/P001-test/dependency-checks.md; echo b > papers/library.bib'
try "prove may not write library.bib" prove P001-test 1 'mkdir -p papers; echo b > papers/library.bib'
try "fix-main may regenerate library.bib" fix-main "" 0 'mkdir -p papers; echo b > papers/library.bib'
# candidate directions (roadmaps/<R>/directions.md): entries by the loop, Dropped lines by garden
try "garden may add a Dropped line to directions.md" garden "" 0 'echo "Dropped (d, garden, m): known." >> roadmaps/BB/directions.md'
try "garden may not create directions.md" garden "" 1 'mkdir -p roadmaps/XX; echo x > roadmaps/XX/directions.md'
try "garden may not touch ROADMAP.md" garden "" 1 'echo x >> roadmaps/BB/ROADMAP.md'
try "garden: an erratum after a failed re-check" garden "" 0 'mkdir -p papers/P001-test; echo e > papers/P001-test/errata.md'
try "write-paper may not touch directions.md" write-paper "" 1 'mkdir -p papers/P001-t; echo a > papers/P001-t/paper.tex; echo x >> roadmaps/BB/directions.md'
# roadmap proposals (propose-roadmap): one new roadmap or one extension, status proposed
newrm='mkdir -p roadmaps/NewArea; printf "# R\n\n| | |\n|---|---|\n| Status | **proposed** (by propose-roadmap, m, d) |\n| Domain | \`bandits\` |\n\n- **D1. A.** x\n" > roadmaps/NewArea/ROADMAP.md'
try "propose-roadmap: a new roadmap" propose-roadmap "" 0 "$newrm; printf 'Reviewed by owner: no\n' > roadmaps/NewArea/KNOWN.md"
try "propose-roadmap: KNOWN.md not reviewed" propose-roadmap "" 1 "$newrm; printf 'Reviewed by owner: 2026-01-01\n' > roadmaps/NewArea/KNOWN.md"
try "propose-roadmap: never approved by the agent" propose-roadmap "" 1 "$newrm; sed -i 's/proposed/approved/' roadmaps/NewArea/ROADMAP.md; printf 'Reviewed by owner: no\n' > roadmaps/NewArea/KNOWN.md"
try "propose-roadmap: without KNOWN.md" propose-roadmap "" 1 "$newrm"
ext='mkdir -p roadmaps/BB/extensions; printf "# X1\n\n| | |\n|---|---|\n| Status | **proposed** (by propose-roadmap, m, d) |\n\n- **D3. New.** x\n" > roadmaps/BB/extensions/X1.md'
try "propose-roadmap: an extension" propose-roadmap "" 0 "$ext"
try "propose-roadmap: an extension reuses no direction number" propose-roadmap "" 1 "$ext; sed -i 's/D3/D2/' roadmaps/BB/extensions/X1.md"
try "propose-roadmap: extensions are numbered" propose-roadmap "" 1 "$ext; git mv -f roadmaps/BB/extensions/X1.md roadmaps/BB/extensions/X2.md 2>/dev/null || mv roadmaps/BB/extensions/X1.md roadmaps/BB/extensions/X2.md"
try "propose-roadmap: one proposal per pull request" propose-roadmap "" 1 "$ext; $newrm; printf 'Reviewed by owner: no\n' > roadmaps/NewArea/KNOWN.md"
try "propose-roadmap may not edit a roadmap" propose-roadmap "" 1 'echo x >> roadmaps/BB/ROADMAP.md'
try "propose-roadmap may not write papers" propose-roadmap "" 1 "$ext; mkdir -p papers/P001-t; echo a > papers/P001-t/paper.tex"
try "review-roadmap changes nothing" review-roadmap "" 1 "$ext"
# the owner's paths, for every role
try "human audits are the owner's" garden "" 1 'mkdir -p papers/P001-test; echo h > papers/P001-test/human-audits.md'
try "the certification is generated, never committed" fix-main "" 1 'mkdir -p papers/P001-test; echo c > papers/P001-test/certification.tex'
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
ok "categories directions and roadmap" '[ "$(path_category generic roadmaps/BB/directions.md M)" = directions ] && [ "$(path_category roadmap roadmaps/X/ROADMAP.md A)" = roadmap ]'
ok "library.bib: papers in a paper PR, literature otherwise" '[ "$(path_category paper papers/library.bib M)" = papers ] && [ "$(path_category generic papers/library.bib M)" = literature ]'
ok "pr_kind of a proposal" '[ "$(pr_kind propose-roadmap)" = roadmap ]'
ok "roadmap is never an automerge category by default" '! automerge_enabled roadmap && automerge_enabled directions'
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

# ---- library metadata (scripts/certify.py): versions, dependencies, library.bib, certification,
#      roadmap items, candidate directions, roadmap proposals
L=$t/lib; mkdir -p "$L"; cd "$L" || exit 1
git init -q -b main . && git config user.name t && git config user.email t@t
C() { python3 "$here/certify.py" --repo "$L" "$@"; }
mkpaper() {  # dir version depends_on cite-line [directions]
  mkdir -p "papers/$1"
  printf 'roadmap = "BB"\nkind = "internal"\ndirections = [%s]\nauthors = ["m"]\nversion = %s\ndepends_on = %s\n' \
    "${5:-\"D1\"}" "$2" "$3" > "papers/$1/META.toml"
  cat > "papers/$1/paper.tex" <<EOF
\title{Paper $1\thanks{Written by agents.}}
\date{2026-11-20}
\begin{theorem}\label{thm:main} T. \end{theorem}
$4
\section{Open questions}
\begin{openquestion}[Rate]\label{oq:rate}
Is the rate optimal on every grid?
\end{openquestion}
\begin{openquestion}\label{oq:other}
Another question.
\end{openquestion}
EOF
}
mkdir -p roadmaps/BB
printf '# R\n\n| | |\n|---|---|\n| Status | **approved** (d) |\n| Domain | `bandits` |\n\n- **F0. Setting.** x\n- **D1. One.** x\n- **D2. Two.** **On hold**.\n' > roadmaps/BB/ROADMAP.md
printf 'Reviewed by owner: 2026-11-14\n' > roadmaps/BB/KNOWN.md
mkpaper P001-first 1 '[]' ''
mkpaper P002-second 1 '["P001v1:thm:main"]' 'By \cite[Theorem~1]{INC-P001}.' '"D2"'
C bib >/dev/null
ok "certify: a consistent library passes" 'C check >/dev/null'
ok "certify: library.bib has the key and the version" 'grep -q "@misc{INC-P002," papers/library.bib && grep -q "version      = {1}" papers/library.bib && grep -q "title        = {{Paper P001-first}}" papers/library.bib'
git add -A; git commit -qm "P001, P002

Incognita-Role: write-paper
Incognita-Reviews: referee-scope=accept referee-proofs=accept"
base=$(git rev-parse HEAD)
sed -i 's/By .cite.Theorem~1..INC-P001../By the first paper./' papers/P002-second/paper.tex
ok "certify: depends_on without a citation fails" '! C check >/dev/null'
git checkout -q -- .
sed -i 's/thm:main/thm:nope/' papers/P002-second/META.toml
ok "certify: a dependency on a missing label fails" '! C check >/dev/null'
git checkout -q -- .
echo '% stale' >> papers/library.bib
ok "certify: a stale library.bib fails" '! C check >/dev/null'
git checkout -q -- .
echo 'More.' >> papers/P001-first/paper.tex
ok "certify: a new paper.tex needs a new version" '! C check --base "$base" >/dev/null'
sed -i 's/^version = 1/version = 2/' papers/P001-first/META.toml; C bib >/dev/null
ok "certify: version 2 with the new paper.tex passes" 'C check --base "$base" >/dev/null'
ok "certify: the dependants of a revised paper need a check" '[ "$(C depchecks)" = "P002-second P001v1->v2" ]'
ok "certify: formalisation priority (dependants)" '[ "$(C dependants | tr "\n" " ")" = "P001-first 1 P002-second 0 " ]'
git add -A; git commit -qm "P001 v2"
lv() { C report | awk -F'|' -v p="$1" 'index($2, "[" p "]") { print $5 }' | sed 's/^ *//; s/ *$//'; }
ok "certify: a paper.tex last merged outside the loop is accepted by the owner" '[ "$(lv P001)" = "1 accepted (by the owner)" ]'
# Certification: frozen statements (locks), proof markers, garden log, human audits.
mkdir -p Statements/P001 Statements/P002 catalogue/results
: > Statements/P001/main.lock
printf 'paper = "P001-first"\nlabel = "thm:main"\nstatement = "Incognita.Statements.P001.main"\nproof = "Incognita.P001.main"\nstatus = "proved"\n' > catalogue/results/P001-main.toml
git add -A; git commit -qm "P001 proved"
ok "certify: level 2 when every frozen statement is proved" '[[ "$(lv P001)" == "2 Lean-verified" ]]'
ok "certify: level 1 without frozen statements (accepted by both referees)" '[ "$(lv P002)" = "1 accepted" ]'
: > Statements/P002/main.lock
printf 'paper = "P002-second"\nlabel = "thm:main"\nstatus = "proved"\n' > catalogue/results/P002-main.toml
m1=$(git rev-parse HEAD)
printf '| Date | Model | Item | Check | Outcome | Main |\n|---|---|---|---|---|---|\n| 2026-11-21 | m1 | P001 | back-translation | confirmed | %s |\n| 2026-11-22 | m1 | P001 thm:main | back-translation | confirmed | %s |\n' "$m1" "$m1" > catalogue/garden.md
ok "certify: level 3 after a re-check; a repeated pass brings nothing new" '[[ "$(lv P001)" == "3 re-verified" ]] && C report | grep -q "| 1 (back-translation by m1) |"'
printf '| 2026-11-23 | m2 | P001 | back-translation | confirmed | %s |\n' "$m1" >> catalogue/garden.md
ok "certify: another model counts" 'C report | grep -q "| 2 (back-translation by m1, back-translation by m2) |"'
ok "certify: used by a verified paper" 'C report | grep -F "[P001]" | grep -q "used by 1 (P002)"'
printf -- '- A. Owner, 2026-11-25, v1: read thm:main.\n' > papers/P001-first/human-audits.md
ok "certify: audited by a human (of an older version)" 'C report | grep -F "[P001]" | grep -q "audited by a human: A. Owner, 2026-11-25, v1 (current: v2)"'
C leanok >/dev/null
ok "certify: the PDF gets the verified node" 'grep -qF "\\incognitaverified{thm:main}{Incognita.P001.main}" papers/P001-first/certification.tex'
mkpaper P003-third 1 '["P002v1:thm:main"]' 'From \cite{INC-P002}.'
mkdir -p Statements/P003; : > Statements/P003/main.lock
printf 'paper = "P003-third"\nlabel = "thm:main"\nstatus = "proved"\n' > catalogue/results/P003-main.toml
printf '| 2026-11-24 | m1 | P002 | known-cases | failed | %s |\n' "$m1" >> catalogue/garden.md
ok "certify: a failed re-check disputes the paper" '[[ "$(lv P002)" == "0 disputed"* ]]'
ok "certify: and caps its dependants" '[ "$(lv P003)" = "0 capped (own level 2 Lean-verified)" ] && C report | grep -F "[P003]" | grep -q "conditional on P002v1:thm:main"'
ok "certify: papers depending on a disputed paper" '[ "$(C disputed-deps)" = "P003-third P002 disputed" ]'
rm -rf papers/P003-third Statements/P003 catalogue/results/P003-main.toml; git checkout -q -- catalogue/garden.md 2>/dev/null; rm -f catalogue/garden.md
# Roadmap items and candidate directions.
ok "certify: items (closed, covered, open)" '[ "$(C items BB | tr "\n" ";")" = "F0 open;D1 covered P001;D2 closed;" ]'
cat > "$t/scope.md" <<'EOF'
Verdict: accept

## Open questions
| Question | Interest | Novelty | Fit | Candidate | Reason |
|---|---|---|---|---|---|
| oq:rate | high | open | D1 | yes | |
| `oq:other` | low | open | D1 | no | |
EOF
ok "certify: accepted open questions become candidate directions" '[ "$(C add-candidates --paper P002-second --report "$t/scope.md" --pr 7 --head abcdef0123456789 --date 2026-11-26)" = 1 ]'
ok "certify: the entry" 'grep -q "^## C1 (2026-11-26, from P002v1 oq:rate)" roadmaps/BB/directions.md && grep -q "^- Rating: interest high; novelty open; fit D1 (referee-scope, pull request #7, head abcdef012345)" roadmaps/BB/directions.md'
ok "certify: candidates are added once" '[ "$(C add-candidates --paper P002-second --report "$t/scope.md" --pr 7 --head abcdef0123456789)" = 0 ] && C check >/dev/null'
ok "certify: a candidate is an item" 'C items BB --free | grep -qx "C1 open"'
git add -A; git commit -qm "directions"; base=$(git rev-parse HEAD)
printf 'Dropped (2026-11-27, garden, m): answered by P001.\n' >> roadmaps/BB/directions.md
ok "certify: a Dropped line may be added" 'C check --base "$base" >/dev/null && C items BB | grep -qx "C1 dropped"'
sed -i 's/^- Title: Rate/- Title: Speed/' roadmaps/BB/directions.md
ok "certify: an entry is never edited" '! C check --base "$base" >/dev/null'
git checkout -q -- .
# Roadmap proposals: validity, scripted approval, verification of scripted commits.
git checkout -q -b proposal
mkdir -p roadmaps/NewArea
printf '# R\n\n| | |\n|---|---|\n| Status | **proposed** (by propose-roadmap, m, d) |\n| Domain | `bandits` |\n\n- **D1. A.** x\n' > roadmaps/NewArea/ROADMAP.md
printf 'Reviewed by owner: no\n' > roadmaps/NewArea/KNOWN.md
git add -A; git commit -qm proposal; ph=$(git rev-parse HEAD)
ok "certify: a proposal in an existing domain" '[ "$(C proposal --base main --head HEAD)" = "new NewArea bandits existing" ]'
sed -i 's/`bandits`/`games`/' roadmaps/NewArea/ROADMAP.md; git commit -qam "other domain"
ok "certify: a proposal in a new domain" '[ "$(C proposal --base main --head HEAD)" = "new NewArea games new" ]'
C approve-roadmap --base main --text "by the loop on 2026-11-30: test" >/dev/null; git commit -qam "Incognita loop: approved"
ok "certify: the scripted approval sets the status" 'grep -q "^| Status | \*\*approved\*\* (by the loop on 2026-11-30: test) |$" roadmaps/NewArea/ROADMAP.md'
ok "certify: the scripted approval checks" 'C verify-scripted --kind approved --parent HEAD^ --head HEAD >/dev/null'
echo "- **D2. Smuggled.** x" >> roadmaps/NewArea/ROADMAP.md; git commit -qam "tampered"
ok "certify: anything else in a scripted commit is refused" '! C verify-scripted --kind approved --parent HEAD^ --head HEAD >/dev/null 2>&1'
git checkout -q main
cd "$INCOGNITA_REPO" || exit 1

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
