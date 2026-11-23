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
# Tau Ceti's rubrics are off by default (2026-11-20): their tests turn them all on.
export INCOGNITA_RUBRICS=correctness,reuse,scope,attribution,api-design,generality,placement,naming,documentation,proof-quality,quality-pass
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
s=$(printf 'gh: oauth_token: gho_ABCDEFGHIJKLMNOPQRSTUVWXYZ0123 and ghp_abcdefghijklmnopqrstuvwxyz012345 and github_pat_11ABCDEFG0123456789_abcdefghijklmnop\n-----BEGIN OPENSSH PRIVATE KEY-----\nb3BlbnNzaC1rZXktdjEAAAAA\n-----END OPENSSH PRIVATE KEY-----\nafter\n-----BEGIN RSA PRIVATE KEY-----\nMIIE truncated\n' | sanitize 1000)
ok "sanitize redacts GitHub tokens" '[[ "$s" != *gho_ABC* && "$s" != *ghp_abc* && "$s" != *github_pat_11* ]]'
ok "sanitize redacts private keys (with or without their end)" '[[ "$s" != *b3BlbnNz* && "$s" != *MIIE* && "$s" == *after* ]]'
long=$(python3 -c 'print("x" * 70000)' | sanitize 60000)
ok "sanitize truncates" '[ ${#long} -lt 60200 ] && [[ "$long" == *"truncated by the script"* ]]'
ok "one_line" '[ "$(printf "a\nb  c\n" | one_line 10)" = "a b c" ]'

# ---- ghr: a failed gh is a failure (2026-11-14: a refused merge was taken for a merge)
ok "ghr passes the output of gh" '[ "$( gh() { echo hi; }; ghr api x )" = hi ]'
ok "ghr fails when gh fails three times" '! ( gh() { echo partial; return 4; }; sleep() { :; }; ghr api x >/dev/null 2>&1 )'
ok "ghr keeps the status of gh" '( gh() { return 4; }; sleep() { :; }; ghr api x >/dev/null 2>&1; [ $? = 4 ] )'
ok "ghr succeeds at the second try" '[ "$( : > "$t/ghcount"; gh() { echo x >> "$t/ghcount"; [ "$(wc -l < "$t/ghcount")" -ge 2 ] && echo ok2; }; sleep() { :; }; ghr api x 2>/dev/null )" = ok2 ]'

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
# Papers of the owner: branch owner/*, role write-paper (a new paper) or revise (a presentation
# revision of an accepted paper, AGENTS.md 5.6) only, opened by the owner's account.
cat > "$t/prs3.json" <<'EOF'
[
 {"number": 20, "title": "HY", "body": "Role: `write-paper`. Target: `BatchedBandits`. Model: `owner`.",
  "headRefName": "owner/hy", "headRefOid": "o1", "isCrossRepository": false, "isDraft": false,
  "labels": [], "mergeable": "MERGEABLE", "author": {"login": "owner"}, "baseRefName": "main", "statusCheckRollup": []},
 {"number": 23, "title": "P002 v2", "body": "Role: `revise`. Target: `P002-drift`. Model: `claude-opus-5-5`.",
  "headRefName": "owner/p002-v2", "headRefOid": "o4", "isCrossRepository": false, "isDraft": false,
  "labels": [], "mergeable": "MERGEABLE", "author": {"login": "owner"}, "baseRefName": "main", "statusCheckRollup": []},
 {"number": 21, "title": "Not a paper", "body": "Role: `prove`. Target: `P001-x`. Model: `owner`.",
  "headRefName": "owner/prove", "headRefOid": "o2", "isCrossRepository": false, "isDraft": false,
  "labels": [], "mergeable": "MERGEABLE", "author": {"login": "owner"}, "baseRefName": "main", "statusCheckRollup": []},
 {"number": 22, "title": "Someone else", "body": "Role: `write-paper`. Target: `BatchedBandits`. Model: `x`.",
  "headRefName": "owner/x", "headRefOid": "o3", "isCrossRepository": false, "isDraft": false,
  "labels": [], "mergeable": "MERGEABLE", "author": {"login": "mallory"}, "baseRefName": "main", "statusCheckRollup": []}
]
EOF
ok "owner rows: a paper of the owner and a presentation revision only" '[ "$(agent_rows "$t/prs3.json" | cut -f1,3,6,7 | tr "\t\n" ", ")" = "20,owner/hy,write-paper,BatchedBandits 23,owner/p002-v2,revise,P002-drift " ]'
ok "owner rows: a presentation revision makes its paper busy for revise" 'busy_pairs "$t/prs3.json" | grep -qx "revise P002-drift"'
ok "owner rows: a presentation revision needs Compile papers" '[ "$(agent_rows "$t/prs3.json" | awk -F"\t" "\$1 == 23 { print \$9 }")" = NONE ]'
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
try "GitHub tokens refused" write-paper "" 1 'mkdir -p papers/P001-t; echo "token: gho_AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA" > papers/P001-t/paper.tex'
try "private keys refused" write-paper "" 1 'mkdir -p papers/P001-t; printf -- "-----BEGIN OPENSSH PRIVATE KEY-----\nx\n" > papers/P001-t/paper.tex'
try "revise changes its paper" revise P001-test 0 'mkdir -p papers/P001-test; echo v2 > papers/P001-test/paper.tex'
# A paper of the owner keeps its human_authors and its \author line through a revision.
git checkout -q -f "$base" && git clean -qfdx
mkdir -p papers/P005-hy && printf 'roadmap = "BB"\nhuman_authors = ["Adrien Prevost"]\n' > papers/P005-hy/META.toml
printf '\\title{HY}\n\\author{Adrien Prevost}\n' > papers/P005-hy/paper.tex
git add -A && git commit -qm owner && hb=$(git rev-parse HEAD)
printf 'roadmap = "BB"\nhuman_authors = ["Adrien Prevost"]\nauthors = ["m"]\n' > papers/P005-hy/META.toml
printf '\\title{HY v2}\n\\author{Adrien Prevost}\n' > papers/P005-hy/paper.tex
git add -A && git commit -qm rev1 && h1=$(git rev-parse HEAD)
git checkout -q -f "$hb" && printf 'roadmap = "BB"\nhuman_authors = ["Someone"]\n' > papers/P005-hy/META.toml
git add -A && git commit -qm rev2 && h2=$(git rev-parse HEAD)
git checkout -q -f "$hb" && printf '\\title{HY}\n\\author{Incognita agents}\n' > papers/P005-hy/paper.tex
git add -A && git commit -qm rev3 && h3=$(git rev-parse HEAD)
ok "owner paper: a revision keeps its authors" 'human_authors_kept "$hb" "$h1" 2>/dev/null'
ok "owner paper: a change of human_authors is refused" '! human_authors_kept "$hb" "$h2" 2>/dev/null'
ok "owner paper: a change of the author line is refused" '! human_authors_kept "$hb" "$h3" 2>/dev/null'
ok "agent paper: no author constraint" 'human_authors_kept "$base" "$h2" 2>/dev/null'
git checkout -q -f "$base" && git clean -qfdx
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
try "write-paper: refs.bib, META.toml, DOSSIER.md" write-paper "" 0 'mkdir -p papers/P001-t; echo a > papers/P001-t/paper.tex; echo b > papers/P001-t/refs.bib; echo c > papers/P001-t/META.toml; echo d > papers/P001-t/DOSSIER.md'
try "write-paper: a figure of the paper in notebook/" write-paper "" 0 'mkdir -p papers/P001-t/notebook; echo a > papers/P001-t/paper.tex; echo f > papers/P001-t/notebook/fig.pdf'
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
try "revise: DOSSIER.md (a presentation revision: paper.tex, DOSSIER.md, refs.bib, META.toml, notebook/)" revise P001-test 0 \
  'mkdir -p papers/P001-test/notebook; echo p > papers/P001-test/paper.tex; echo d > papers/P001-test/DOSSIER.md; echo r > papers/P001-test/refs.bib; echo m > papers/P001-test/META.toml; echo n > papers/P001-test/notebook/N.md'
try "revise may not write the DOSSIER.md of another paper" revise P001-test 1 'mkdir -p papers/P002-other; echo d > papers/P002-other/DOSSIER.md'
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
# library.bib is generated, never committed; dependency checks (AGENTS.md 5.6)
try "write-paper may not commit papers/library.bib" write-paper "" 1 'mkdir -p papers/P001-t; echo a > papers/P001-t/paper.tex; echo b > papers/library.bib'
try "revise: dependency-checks.md" revise P001-test 0 'mkdir -p papers/P001-test; echo d > papers/P001-test/dependency-checks.md'
try "revise may not commit library.bib" revise P001-test 1 'mkdir -p papers/P001-test; echo b > papers/library.bib'
try "fix-main may not commit library.bib" fix-main "" 1 'mkdir -p papers; echo b > papers/library.bib'
# P000 is a number like the others (L4)
git checkout -q -f "$base"; mkdir -p papers/P000-setting; echo s > papers/P000-setting/paper.tex
git add -A; git commit -qm P000; git update-ref refs/remotes/origin/main HEAD; base0=$(git rev-parse HEAD)
mkdir -p papers/P000-again; echo a > papers/P000-again/paper.tex; git add -A; git commit -qm again
ok "whitelist: the number of P000 is taken" '! check_paths write-paper "" "$base0" HEAD 2>/dev/null'
ok "paper_num: P000 is 0, P010 is 10" '[ "$(paper_num P000-setting)" = 0 ] && [ "$(paper_num P010-x)" = 10 ] && [ -z "$(paper_num README.md)" ]'
ok "AWK_NUM: P000 is 0" '[ "$(printf "P000 a open\nP001 b open\n" | awk "$AWK_NUM"'"'"' num($1) == 0 { print $2 }'"'"')" = a ]'
git update-ref refs/remotes/origin/main "$base"
# candidate directions (roadmaps/<R>/directions.md): entries by the loop, Dropped lines by garden
git checkout -q -f "$base"; printf '\n## C1 (d, from P001v1 oq:a)\n- Title: -\n- Statement: Q?\n- Source: s\n- Rating: r\n' >> roadmaps/BB/directions.md
git add -A; git commit -qm C1; git update-ref refs/remotes/origin/main HEAD; base_c=$base; base=$(git rev-parse HEAD)
try "garden may add a Dropped line to directions.md" garden "" 0 'echo "Dropped (d, garden, m): known." >> roadmaps/BB/directions.md'
try "garden may not add a candidate direction (S6)" garden "" 1 'printf "\n## C2 (d, from P001v1 oq:b)\n- Title: -\n- Statement: R?\n- Source: s\n- Rating: r\n" >> roadmaps/BB/directions.md'
try "garden may not edit a candidate direction" garden "" 1 'sed -i "s/Statement: Q?/Statement: Z?/" roadmaps/BB/directions.md'
base=$base_c; git update-ref refs/remotes/origin/main "$base"
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
ok "pr_kind of a proposal" '[ "$(pr_kind propose-roadmap)" = roadmap ]'
ok "pr_kind of the loop's own pull requests" '[ "$(pr_kind loop)" = scripted ]'
ok "roadmap is never an automerge category by default" '! automerge_enabled roadmap && automerge_enabled directions'
git checkout -q -f "$base"; mkdir -p Incognita/P; printf 'theorem a : True := trivial\n' > Incognita/P/A.lean; git add -A; git commit -qm thm
ok "a theorem is a proof" 'adds_only_theorems "$base" HEAD'
printf 'noncomputable def f : Nat := 0\n' >> Incognita/P/A.lean; git add -A; git commit -qm def
ok "a def is not" '! adds_only_theorems "$base" HEAD'
# Lean pull requests (Tau Ceti's rubrics review them too; owner, 2026-11-17)
ok "a garden PR changing Incognita/*.lean is a Lean PR" 'is_lean_pr garden "$base" HEAD'
ok "prove and formalize-statements always are" 'is_lean_pr prove x y && is_lean_pr formalize-statements x y'
ok "papers, proposals and the loop's pull requests never are" '! is_lean_pr write-paper "$base" HEAD && ! is_lean_pr revise "$base" HEAD && ! is_lean_pr propose-roadmap "$base" HEAD && ! is_lean_pr loop "$base" HEAD'
git checkout -q -f "$base"; mkdir -p literature Exploration; echo n > literature/n.md; echo e > Exploration/E.lean; git add -A; git commit -qm lit
ok "a PR without .lean under Incognita/ or Statements/ is not (Exploration/ does not count)" '! is_lean_pr bibliographer "$base" HEAD && ! is_lean_pr garden "$base" HEAD'
git checkout -q -f "$base"; mkdir -p Statements/P001; echo s > Statements/P001/a.lean; git add -A; git commit -qm st
ok "a fix of main adding under Statements/ is" 'is_lean_pr fix-pr "$base" HEAD'
git checkout -q -f "$base"

# ---- Tau Ceti's rubrics: the list, the state of a head, blocks, the quality pass of a description
ok "rubric roles are review roles (budget, model, short near the cap)" 'is_rubric_role rubric-api-design && is_review_role rubric-quality-pass && short_role rubric-naming && is_role rubric-correctness && ! is_rubric_role rubric-bogus && ! is_rubric_role review-pr'
ok "the default list: the 11 rubrics in Tau Ceti's order" '[ "$(rubrics_enabled | tr "\n" " ")" = "$RUBRICS_ALL " ] && [ "$(rubrics_enabled | wc -l | tr -d " ")" = 11 ]'
ok "INCOGNITA_RUBRICS trims the list (Tau Ceti's order kept, unknown names ignored)" '[ "$(INCOGNITA_RUBRICS="quality-pass, correctness,bogus" rubrics_enabled | tr "\n" " ")" = "correctness quality-pass " ]'
rsts() {  # verdict of each rubric, in order (- or missing: none): trusted status lines of one head
  local r v i=0 out=""
  for r in $RUBRICS_ALL; do
    i=$(( i + 1 )); v=${!i:--}
    [ "$v" = - ] || out="$out$(printf '%s\t%s\t%s\t%s' "Incognita rubric/$r" x yes "role=rubric-$r verdict=$v pr=5")"$'\n'
  done
  printf '%s' "$out"
}
A="approve approve approve approve approve approve approve approve approve approve approve"
ok "no verdict yet: the first rubric is next" '[ "$(rubrics_state "")" = "next correctness" ]'
ok "in order: the first rubric without a verdict" '[ "$(rubrics_state "$(rsts approve approve)")" = "next scope" ]'
ok "a block stops the round" '[ "$(rubrics_state "$(rsts approve block)")" = "block reuse" ]'
ok "every rubric approves" '[ "$(rubrics_state "$(rsts $A)")" = approve ]'
ok "one asks for changes" '[ "$(rubrics_state "$(rsts approve request_changes approve approve approve approve approve approve approve approve approve)")" = changes ]'
ok "a request_changes does not stop the round" '[ "$(rubrics_state "$(rsts approve request_changes)")" = "next scope" ]'
ok "an untrusted rubric status does not count" '[ "$(rubrics_state "$(rsts $A | sed "s/\tyes\t/\tno\t/")")" = "next correctness" ]'
ok "a status of another role does not count" '[ "$(rubrics_state "$(rsts $A | sed "s/role=rubric-correctness/role=review-pr/")")" = "next correctness" ]'
ok "an empty INCOGNITA_RUBRICS: nothing to wait for" '[ "$(INCOGNITA_RUBRICS= rubrics_state "")" = approve ]'
ok "a trimmed list waits only for its rubrics" '[ "$(INCOGNITA_RUBRICS=reuse rubrics_state "$(rsts - approve)")" = approve ]'
cat > "$t/rc.json" <<'EOF'
[{"kind": "rubric-reuse", "sha": "aaaa", "body": "Verdict: block\n\n## Summary\nx"},
 {"kind": "rubric-scope", "sha": "aaaa", "body": "Verdict: block\nx"},
 {"kind": "rubric-scope", "sha": "bbbb", "body": "intro\nVerdict: `block`\nx"},
 {"kind": "rubric-scope-partial", "sha": "cccc", "body": "Verdict: block"},
 {"kind": "rubric-correctness", "sha": "dddd", "body": "Verdict: request_changes\nblock"},
 {"kind": "review-pr", "sha": "eeee", "body": "Verdict: block"}]
EOF
ok "blocked heads: distinct heads of rubric reports with the verdict block" '[ "$(rubric_blocked_heads < "$t/rc.json")" = 2 ]'
printf 'Role: `prove`. Target: `P001-x`. Model: `m`.\n\n## Results\nr\n## Quality pass\nQuality pass:\n- Q1 Mathlib duplicates: old\n## Not done\nn\n\nOpened by `scripts/agent.sh` (see agents/README.md).\n' > "$t/body1.md"
printf 'Role: `prove`. Target: `P001-x`. Model: `m`.\n\n## Results\nr\n\nOpened by `scripts/agent.sh` (see agents/README.md).\n' > "$t/body2.md"
printf '## Results\nnew\n## Quality pass\nQuality pass:\n- Q1 Mathlib duplicates: checked \\le new\n## Not done\nx\n' > "$t/sum.md"
replace_section "$t/body1.md" "$t/sum.md" "Quality pass" > "$t/nb1.md"
ok "the quality pass of a fix round replaces the one of the description" 'head -n 1 "$t/nb1.md" | grep -q "^Role: " && grep -qF "checked \\le new" "$t/nb1.md" && ! grep -q old "$t/nb1.md" && grep -qx r "$t/nb1.md" && grep -qx n "$t/nb1.md" && ! grep -qx new "$t/nb1.md" && [ "$(grep -c "^## Quality pass" "$t/nb1.md")" = 1 ]'
replace_section "$t/body2.md" "$t/sum.md" "Quality pass" > "$t/nb2.md"
ok "a description without one gets it before its last line" 'head -n 1 "$t/nb2.md" | grep -q "^Role: " && [ "$(grep -n "^## Quality pass" "$t/nb2.md" | cut -d: -f1)" -lt "$(grep -n "^Opened by" "$t/nb2.md" | cut -d: -f1)" ]'
ok "a summary without a quality pass changes nothing" '! replace_section "$t/body2.md" "$t/body2.md" "Quality pass" >/dev/null'

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
wbase=$base   # the base of the whitelist repository (base is reused below)
L=$t/lib; mkdir -p "$L"; cd "$L" || exit 1
git init -q -b main . && git config user.name t && git config user.email t@t
C() { python3 "$here/certify.py" --repo "$L" "$@"; }
mkpaper() {  # dir version depends_on cite-line [directions]
  mkdir -p "papers/$1"
  printf 'roadmap = "BB"\nkind = "internal"\ndirections = [%s]\nauthors = ["m"]\nversion = %s\ndepends_on = %s\n' \
    "${5:-\"D1\"}" "$2" "$3" > "papers/$1/META.toml"
  printf '# Dossier of %s\n\n## Closest known\n- K1: not the same class.\n' "$1" > "papers/$1/DOSSIER.md"
  cat > "papers/$1/paper.tex" <<EOF
\title{Paper $1\thanks{Written by agents.}}
\date{2026-11-20}
\begin{theorem}\label{thm:main} T. \end{theorem}
$4
\section{Open questions}
\begin{openquestion}[Rate]\label{oq:rate}
\extends{D1}
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
# (P002 keeps a KNOWN id in its text, as the papers written before the rules of 2026-11-15: it is
# checked only when a pull request changes its paper.tex.)
mkpaper P002-second 1 '["P001v1:thm:main"]' 'By \cite[Theorem~1]{INC-P001}. Compare with K7.' '"D2"'
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
sed -i 's/section{Open questions}/section{Conclusion and open questions}/' papers/P002-second/paper.tex
ok "certify: the section of the template, Conclusion and open questions, passes" 'C check >/dev/null'
sed -i 's/section{Conclusion and open questions}/section{Questions}/' papers/P002-second/paper.tex
ok "certify: a paper without its open questions section fails" '! C check >/dev/null'
git checkout -q -- .
sed -i 's/thm:main/thm:nope/' papers/P002-second/META.toml
ok "certify: a dependency on a missing label fails" '! C check >/dev/null'
git checkout -q -- .
sed -i 's/^roadmap = "BB"/roadmap = "..\/..\/x"/' papers/P002-second/META.toml
ok "certify: a roadmap that is not a name fails (S4)" '[[ "$(C check 2>&1)" == *"roadmap must be the name of a roadmap"* ]]'
git checkout -q -- .
sed -i 's/^roadmap = "BB"/roadmap = "Nope"/' papers/P002-second/META.toml
ok "certify: a roadmap that does not exist fails" '[[ "$(C check 2>&1)" == *"there is no roadmap roadmaps/Nope/"* ]]'
ok "certify: add-candidates refuses a bad paper directory" '! C add-candidates --paper ../x --report /dev/null --pr 1 --head 0 >/dev/null 2>&1'
git checkout -q -- .
echo 'More.' >> papers/P001-first/paper.tex
ok "certify: a new paper.tex needs a new version" '! C check --base "$base" >/dev/null'
sed -i 's/^version = 1/version = 2/' papers/P001-first/META.toml; C bib >/dev/null
ok "certify: version 2 with the new paper.tex passes" 'C check --base "$base" >/dev/null'
# What never appears in a new or changed paper.tex (AGENTS.md 5.2): KNOWN ids in the prose, "(to be
# checked)"; and its DOSSIER.md.
ok "certify: a paper unchanged since the base is not checked again (P002 keeps its KNOWN id)" 'C check --base "$base" >/dev/null && grep -q K7 papers/P002-second/paper.tex'
cp papers/P001-first/paper.tex "$t/p1.tex"
printf '%s\n' 'As in K12, the rate is $\log T$.' >> papers/P001-first/paper.tex
n=$(wc -l < papers/P001-first/paper.tex | tr -d ' ')
ok "certify: a KNOWN id in the text of a changed paper fails, naming the line" '[[ "$(C check --base "$base" 2>&1)" == *"paper.tex:$n: a KNOWN id (K12)"* ]]'
cp "$t/p1.tex" papers/P001-first/paper.tex
printf '%s\n' '% K12 is the closest entry.' 'With $K_2 = 1$, \(K3\) and \extends{K4} in a remark.' '\begin{align} K5 \end{align}' >> papers/P001-first/paper.tex
ok "certify: KNOWN ids in comments, mathematics and \\extends are not seen" 'C check --base "$base" >/dev/null'
cp "$t/p1.tex" papers/P001-first/paper.tex
printf '%s\n' 'See \cite{GMS19} (to be checked).' >> papers/P001-first/paper.tex
n=$(wc -l < papers/P001-first/paper.tex | tr -d ' ')
ok "certify: \"(to be checked)\" in a changed paper fails" '[[ "$(C check --base "$base" 2>&1)" == *"paper.tex:$n: \"(to be checked)\""* ]]'
cp "$t/p1.tex" papers/P001-first/paper.tex
rm papers/P001-first/DOSSIER.md
ok "certify: a changed paper.tex needs a DOSSIER.md" '[[ "$(C check --base "$base" 2>&1)" == *"papers/P001-first: no DOSSIER.md"* ]]'
git checkout -q -- papers/P001-first/DOSSIER.md
sed -i 's/^\\extends{D1}$/\\extends{K1}/' papers/P001-first/paper.tex
ok "certify: \\extends names roadmap items" '[[ "$(C check 2>&1)" == *"\\extends{K1} in oq:rate"* ]]'
cp "$t/p1.tex" papers/P001-first/paper.tex
ok "certify: back to a passing version 2" 'C check --base "$base" >/dev/null'
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
printf '| Date | Model | Item | Check | Outcome | Main |\n|---|---|---|---|---|---|\n| 2026-11-21 | m1 | P001 | back-translation | confirmed: the Lean says the statement | %s |\n| 2026-11-22 | m1 | P001 thm:main | back-translation | confirmed | %s |\n' "$m1" "$m1" > catalogue/garden.md
ok "certify: level 3 after a re-check (documented format \"confirmed: ...\"); a repeated pass brings nothing new" '[[ "$(lv P001)" == "3 re-verified" ]] && C report | grep -q "| 1 (back-translation by m1) |"'
printf '| 2026-11-23 | m2 | P001 | back-translation | Confirmed: again | %s |\n' "$m1" >> catalogue/garden.md
ok "certify: another model counts" 'C report | grep -q "| 2 (back-translation by m1, back-translation by m2) |"'
ok "certify: used by a verified paper" 'C report | grep -F "[P001]" | grep -q "used by 1 (P002)"'
printf -- '- A. Owner, 2026-11-25, v1: read thm:main.\n' > papers/P001-first/human-audits.md
ok "certify: audited by a human (of an older version)" 'C report | grep -F "[P001]" | grep -q "audited by a human: A. Owner, 2026-11-25, v1 (current: v2)"'
C leanok >/dev/null
ok "certify: the PDF gets the verified node" 'grep -qF "\\incognitaverified{thm:main}{Incognita.P001.main}" papers/P001-first/certification.tex'
ok "certify: the certification line in plain words, badges only when there are some" 'grep -qF "{Incognita library, P001 version 2. Accepted by the owner; Lean-verified (its frozen statement proved); re-verified 2 times by gardening. Used by 1 Lean-verified paper (P002). Audited by a human: A. Owner, 2026-11-25, version 1 (now version 2).}" papers/P001-first/certification.tex && grep -qF "{Incognita library, P002 version 1. Refereed and accepted by two AI referees; Lean-verified (its frozen statement proved).}" papers/P002-second/certification.tex'
C leanok --base "$base" >/dev/null
ok "certify: in a pull request, a changed paper is submitted" 'grep -qF "{Incognita library, P001 version 2. Submitted: under refereeing by AI agents, not accepted yet.}" papers/P001-first/certification.tex && grep -qF "P002 version 1. Refereed and accepted" papers/P002-second/certification.tex'
mkpaper P003-third 1 '["P002v1:thm:main"]' 'From \cite{INC-P002}.'
mkdir -p Statements/P003; : > Statements/P003/main.lock
printf 'paper = "P003-third"\nlabel = "thm:main"\nstatus = "proved"\n' > catalogue/results/P003-main.toml
printf '| 2026-11-24 | m1 | P002 | known-cases | failed: the instance is false | %s |\n' "$m1" >> catalogue/garden.md
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
| `oq:other` | 3/10 | open | D1 | yes | |
EOF
ok "certify: accepted open questions become candidate directions" '[ "$(C add-candidates --paper P002-second --report "$t/scope.md" --pr 7 --head abcdef0123456789 --date 2026-11-26)" = 1 ]'
ok "certify: the entry" 'grep -q "^## C1 (2026-11-26, from P002v1 oq:rate)" roadmaps/BB/directions.md && grep -q "^- Rating: interest high; novelty open; fit D1 (referee-scope, pull request #7, head abcdef012345)" roadmaps/BB/directions.md'
ok "certify: the items of \\extends go to their own line, not into the statement" 'grep -qx -- "- Statement: Is the rate optimal on every grid?" roadmaps/BB/directions.md && grep -qx -- "- Extends: D1" roadmaps/BB/directions.md'
ok "certify: candidates are added once" '[ "$(C add-candidates --paper P002-second --report "$t/scope.md" --pr 7 --head abcdef0123456789)" = 0 ] && C check >/dev/null'
ok "certify: a candidate is an item, with its interest" 'C items BB --free | grep -qx "C1 open interest high"'
ok "certify: a question rated below 4/10 is never a candidate" '! grep -q "oq:other" roadmaps/BB/directions.md'
git add -A; git commit -qm "directions"; base=$(git rev-parse HEAD)
printf 'Dropped (2026-11-27, garden, m): answered by P001.\n' >> roadmaps/BB/directions.md
ok "certify: a Dropped line may be added" 'C check --base "$base" >/dev/null && C items BB | grep -qx "C1 dropped"'
sed -i 's/^- Title: Rate/- Title: Speed/' roadmaps/BB/directions.md
ok "certify: an entry is never edited" '! C check --base "$base" >/dev/null'
git checkout -q -- .
# Append-only files (S6): the gardening log, errata and statement corrections.
printf '| Date | Model | Item | Check | Outcome | Main |\n|---|---|---|---|---|---|\n| 2026-11-21 | m1 | P001 | back-translation | confirmed | x |\n' > catalogue/garden.md
printf '# Errata of P001\n\n## E1 (2026-11-20, prove, m)\n- Node: thm:main\n- Problem: false.\n' > papers/P001-first/errata.md
git add -A; git commit -qm "log and errata"; base=$(git rev-parse HEAD)
printf '| 2026-11-22 | m2 | P001 | known-cases | confirmed | y |\n' >> catalogue/garden.md
printf 'Revised in the version of 2026-11-22: fixed.\n\n## E2 (2026-11-23, garden, m)\n- Node: lem:a\n' >> papers/P001-first/errata.md
ok "certify: rows appended to garden.md, a line under an erratum, a new erratum" 'C check --base "$base" >/dev/null'
git checkout -q -- .
sed -i 's/| confirmed | x |/| failed | x |/' catalogue/garden.md
ok "certify: a row of garden.md is never changed" '[[ "$(C check --base "$base" 2>&1)" == *"catalogue/garden.md: existing lines"* ]]'
git checkout -q -- .
sed -i 's/- Problem: false./- Problem: true after all./' papers/P001-first/errata.md
ok "certify: an erratum is never edited" '[[ "$(C check --base "$base" 2>&1)" == *"E1 was edited"* ]]'
git checkout -q -- .
printf -- '- Note: something else.\n' >> papers/P001-first/errata.md
ok "certify: under an erratum, only Revised in / Resolved by lines" '[[ "$(C check --base "$base" 2>&1)" == *"only a line \"Revised in"* ]]'
git checkout -q -- .
printf '# Errata of P001\n' > papers/P001-first/errata.md
ok "certify: an erratum is never deleted" '[[ "$(C check --base "$base" 2>&1)" == *"entries were removed"* ]]'
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

# ---- outputs of a session are never opened by the loop as itself (S1): out_read, out_copy
AGENT_READ=()   # as ourselves here; the loop runs them through sudo -u incognita-agent
o=$t/out; mkdir -p "$o"; printf 'secret-of-the-loop\n' > "$t/loop-secret"
printf '## Results\nfine\n' > "$o/summary.md"
ln -s "$t/loop-secret" "$o/link.md"
mkfifo "$o/fifo.md" 2>/dev/null || true
head -c 5000 /dev/zero > "$o/big"
ok "out_read: a regular file" '[ "$(out_read "$o/summary.md" 1000)" = "$(printf "## Results\nfine")" ]'
ok "out_read: a symbolic link is refused (never followed)" '! out_read "$o/link.md" 1000 >/dev/null 2>&1 && [ -z "$(out_read "$o/link.md" 1000 2>/dev/null)" ]'
ok "out_read: a FIFO is refused (never opened)" '( timeout 5 bash -c ". \"$here/lib.sh\"; AGENT_READ=(); out_read \"$o/fifo.md\" 100" >/dev/null 2>&1; [ $? = 1 ] )'
ok "out_read: capped" '[ "$(out_read "$o/big" 100 | wc -c)" = 100 ]'
ok "out_irregular: the links and FIFOs of an output directory" '[[ "$(out_irregular "$o")" == *"l link.md"* && "$(out_irregular "$o")" != *summary.md* ]]'
ok "out_copy: refused above the cap" '! out_copy "$o/big" 1000 "$t/copy" 2>/dev/null && out_copy "$o/big" 5000 "$t/copy" && [ "$(wc -c < "$t/copy")" = 5000 ]'
AGENT_READ=(sudo -n -u "$INCOGNITA_AGENT_USER")

# ---- one commit per round (S3): squash_parent, squash_onto
git checkout -q -f "$wbase"; git update-ref refs/remotes/origin/main "$wbase"
mkdir -p papers/P001-sq; echo "sk-ant-oat01-SECRETSECRETSECRETSECRET" > papers/P001-sq/paper.tex
git add -A; git commit -qm "add (with a secret)"; echo clean > papers/P001-sq/paper.tex; git commit -qam "remove the secret"
new=$(git rev-parse HEAD)
printf 'P001: a paper\n\nbody\n' > "$t/msg"
sp=$(squash_parent "$wbase" "$new"); sq=$(squash_onto "$sp" "$new" "$t/msg")
ok "squash: a new pull request is one commit on the merge base" '[ "$sp" = "$wbase" ] && [ "$(git rev-parse "$sq^")" = "$wbase" ] && [ "$(git rev-list --count "$wbase..$sq")" = 1 ]'
ok "squash: same tree, the secret only in the dropped commits" '[ "$(git rev-parse "$sq^{tree}")" = "$(git rev-parse "$new^{tree}")" ] && ! git log -p "$wbase..$sq" | grep -q SECRET'
ok "squash: author and committer are the bot identity, not the session's" '[ "$(git log -1 --format="%an <%ae>|%cn <%ce>" "$sq")" = "Incognita agents (prevostad) <prevostad@users.noreply.github.com>|Incognita agents (prevostad) <prevostad@users.noreply.github.com>" ]'
printf 'P001: a paper

body
- one

Incognita-Model: opus
Incognita-Agent-Role: write-paper
' > "$t/msg2"
sq2=$(squash_onto "$sp" "$new" "$t/msg2")
ok "squash: the model is a trailer of the message" '[ "$(git log -1 --format="%(trailers:key=Incognita-Model,valueonly)" "$sq2" | head -n 1)" = opus ]'
h=$new; echo more >> papers/P001-sq/paper.tex; git commit -qam r1; echo again >> papers/P001-sq/paper.tex; git commit -qam r2; new=$(git rev-parse HEAD)
ok "squash: a round on a pull request is one commit on its head" '[ "$(squash_parent "$wbase" "$new" "$h")" = "$h" ]'
git checkout -q -f -B rebased "$wbase"; echo m > main-moved.txt; git add -A; git commit -qm "main moves"; m2=$(git rev-parse HEAD)
git cherry-pick "$wbase..$new" >/dev/null 2>&1 || git cherry-pick --abort; new=$(git rev-parse HEAD)
ok "squash: a rebased round is one commit on the new base" '[ "$(squash_parent "$m2" "$new" "$h")" = "$m2" ]'

# ---- statuses survive a mechanical rebase when only shared files moved (L2): diff_signature
git checkout -q -f -B sigpr "$wbase"; mkdir -p papers/P001-sig literature
echo "public import Incognita.Mine" >> Incognita.lean; echo p > papers/P001-sig/paper.tex; echo "- mine" >> literature/index.md
git add -A; git commit -qm pr; pr1=$(git rev-parse HEAD)
git checkout -q -f -B sigmain "$wbase"; mkdir -p literature; echo "public import Incognita.Theirs" >> Incognita.lean; echo "- theirs" > literature/other.md
git add -A; git commit -qm main; m3=$(git rev-parse HEAD)
git checkout -q -f -B sigre "$pr1"; GIT_EDITOR=true git rebase -q "$m3" >/dev/null 2>&1
if [ -n "$(git diff --name-only --diff-filter=U)" ]; then resolve_imports "$INCOGNITA_REPO" Incognita.lean; git add Incognita.lean; GIT_EDITOR=true git rebase --continue >/dev/null 2>&1; fi
pr2=$(git rev-parse HEAD)
ok "diff_signature: the same after a rebase that moved root imports" '[ "$(diff_signature "$wbase" "$pr1")" = "$(diff_signature "$m3" "$pr2")" ]'
git checkout -q -f -B sigre2 "$pr2"; echo q > papers/P001-sig/paper.tex; git commit -qam changed
ok "diff_signature: differs when the paper changed" '[ "$(diff_signature "$wbase" "$pr1")" != "$(diff_signature "$m3" HEAD)" ]'
git checkout -q -f "$wbase"

# ---- proportionate rubric reviews (owner, 2026-11-19): lean_strip_comments, change_class
printf '%s\n' '/-- doc' '  more -/' 'theorem foo : 1 = 1 := by -- note' '  /- a /- nested -/ b -/ rfl' '  exact "a--b\"c" -- x' '/-! mod -/' '' 'end' > "$t/c.lean"
ok "lean_strip_comments: docstrings, nested blocks and line comments go, strings and indentation stay" \
  '[ "$(lean_strip_comments < "$t/c.lean")" = "$(printf "%s\n" "theorem foo : 1 = 1 := by" "   rfl" "  exact \"a--b\\\"c\"" end)" ]'
git checkout -q -f -B ccbase "$wbase"; mkdir -p Incognita/CC; printf 'theorem a : True := trivial\n' > Incognita/CC/A.lean
printf 'theorem b : True := trivial\n' > Incognita/CC/Main.lean; git add -A; git commit -qm ccbase; ccb=$(git rev-parse HEAD)
printf '/-- A. -/\ntheorem a : True := trivial\n' > Incognita/CC/A.lean; git commit -qam pr; cc0=$(git rev-parse HEAD)
echo "p" > papers/note.md 2>/dev/null || { mkdir -p papers; echo p > papers/note.md; }; git add -A; git commit -qm notes; cc1=$(git rev-parse HEAD)
printf '/-- A, better. -/\ntheorem a : True := trivial -- why\n' > Incognita/CC/A.lean; git commit -qam doc; cc2=$(git rev-parse HEAD)
printf '/-- A, better. -/\ntheorem a : True := by trivial\n' > Incognita/CC/A.lean; git commit -qam code; cc3=$(git rev-parse HEAD)
git checkout -q -f -B ccmain "$ccb"; printf 'theorem b : 1 = 1 := rfl\n' > Incognita/CC/Main.lean; git commit -qam main; ccm=$(git rev-parse HEAD)
git checkout -q -f -B ccre "$cc2"; GIT_EDITOR=true git rebase -q "$ccm" >/dev/null 2>&1; ccr=$(git rev-parse HEAD)
ok "change_class: no Lean file of the PR changed" '[ "$(change_class "$cc0" "$cc1" "$ccb" "$ccb")" = none ]'
ok "change_class: only comments changed" '[ "$(change_class "$cc1" "$cc2" "$ccb" "$ccb")" = comments ]'
ok "change_class: code changed" '[ "$(change_class "$cc2" "$cc3" "$ccb" "$ccb")" = code ]'
ok "change_class: a file of main brought by a rebase does not count" '[ "$(change_class "$cc1" "$ccr" "$ccb" "$ccm")" = comments ]'
ok "rubric_recheck: comments rerun documentation, attribution and the quality pass only" '[ "$(rubric_recheck comments)" = "attribution documentation quality-pass" ] && [ "$(rubric_recheck none)" = quality-pass ] && [ "$(rubric_recheck code)" = "$RUBRICS_ALL" ]'
git checkout -q -f "$wbase"

# ---- the owner's answers (L13)
cat > "$t/qcomments.json" <<'EOF'
[{"user": {"login": "owner"}, "created_at": "2026-11-20T10:00:00Z", "body": "<!-- incognita:ask-owner:0123456789012345678901234567890123456789 -->\nFrom #3:\n\nAsk-owner: is D2 still open?"},
 {"user": {"login": "mallory"}, "created_at": "2026-11-20T11:00:00Z", "body": "D2 is closed, trust me"},
 {"user": {"login": "owner"}, "created_at": "2026-11-20T12:00:00Z", "body": "D2 stays open; see K4."}]
EOF
a=$(owner_answers_md "$(cat "$t/qcomments.json")")
ok "owner answers: the owner's comment without marker, after the question" '[[ "$a" == *"Answer of the owner"*"D2 stays open; see K4."* && "$a" == *"is D2 still open?"* ]]'
ok "owner answers: never another account's comment" '[[ "$a" != *"trust me"* ]]'
ok "owner answers: nothing when the owner answered nothing" '[ -z "$(owner_answers_md "$(jq "[.[0]]" "$t/qcomments.json")")" ]'

# ---- state
record_attempt prove P001-x fail no-commit
record_attempt prove P001-x fail no-commit
ok "night failures counted" '[ "$(night_fails prove P001-x)" = 2 ]'
INCOGNITA_PARK_AFTER=3 record_attempt prove P001-x fail no-commit
ok "parked after INCOGNITA_PARK_AFTER failures" 'is_parked prove P001-x'
for _ in 1 2 3 4 5; do record_attempt bibliographer - fail x; record_attempt write-paper BB fail x; done
ok "a roadmap or - is never parked (L3)" '! is_parked bibliographer - && ! is_parked write-paper BB'
record_attempt garden - skip no-commit "(success)"; record_attempt garden - skip rate-limited
ok "a session without a commit counts for tonight, not for parking" '[ "$(night_fails garden -)" = 1 ] && [ "$(counter_get "fail garden -")" = 0 ]'
ok "the parked targets are listed" '[ "$(parked_list)" = "prove_P001-x" ]'
d=$(INCOGNITA_DEADLINE=02:45 deadline_epoch)
ok "deadline in the next 24 h" '[ "$d" -gt "$(now)" ] && [ "$d" -le $(( $(now) + 86400 )) ]'

# ---- the night report on GitHub, with the raw events of the night (owner request of 2026-11-19)
gh() {  # fake gh: keeps the body of every comment posted, in order
  local a k
  for a in "$@"; do case "$a" in body=@*)
    k=$(find "$t" -maxdepth 1 -name 'posted.*' | wc -l | tr -d ' ')
    cp "${a#body=@}" "$t/posted.$k"; echo "https://github.com/owner/repo/issues/21#issuecomment-$k"; return 0 ;; esac
  done
  return 0
}
posted_n() { find "$t" -maxdepth 1 -name 'posted.*' | wc -l | tr -d ' '; }
printf '%s\t%s\t%s\t%s\t%s\n' "2026-11-19 22:00:00" task prove P001-x 'ok pr #7 (turns 3, 60s, $1.5)' \
  "2026-11-19 22:01:00" ask-owner prove P001-x "see <!-- here --> and @bob" \
  "2026-11-19 22:02:00" ask-owner prove P001-x "a token sk-ant-oat01-ABCDEFGHIJKLMNOPQRSTUV leaked" > "$NIGHT_DIR/events.tsv"
rm -f "$NIGHT_DIR/usage.tsv"
usage_record ok "39 1795399200 74 1795111800 agent"
ok "usage readings are recorded for the night (kind usage)" '[ "$(cut -f2- "$NIGHT_DIR/usage.tsv")" = "$(printf "usage\t-\t-\tok 39 1795399200 74 1795111800 agent")" ]'
printf '# Night report test\n\nBody of the report.\n' > "$t/report.md"
post_night_report 21 0123456789012345678901234567890123456789 "$t/report.md" 2>/dev/null; rc=$?
p0=$(cat "$t/posted.0" 2>/dev/null)
ok "report: one comment, the events appended to it" '[ "$rc" = 0 ] && [ "$(posted_n)" = 1 ] && [[ "$p0" == "<!-- incognita:night-report:0123456789012345678901234567890123456789 -->"*"Body of the report."*"<!-- incognita:events v1 night=test part=1/1 lines=3 -->"* ]]'
ok "report: the events in a collapsed fenced block" '[[ "$p0" == *"<details><summary>Raw events of the night of test"*$'"'"'\n~~~tsv\n'"'"'*$'"'"'2026-11-19 22:00:00\ttask\tprove\tP001-x\tok pr #7'"'"'*$'"'"'\n~~~\n\n</details>'"'"'* ]]'
ok "report: a line that looks like a secret is left out" '[[ "$p0" != *sk-ant* && "$p0" == *"1 line left out"* ]]'
ok "report: event texts cleaned like agent text (<!--, @)" '[[ "$p0" == *"&lt;!-- here"* && "$p0" == *$'"'"'@\xe2\x80\x8bbob'"'"'* ]]'
ok "report: stats.py reads the events back (usage reading included)" '[ "$(python3 -I "$here/stats.py" events-read "$t/posted.0" | cut -f3 | sort | tr "\n" " ")" = "ask-owner task usage " ]'
rm -f "$t"/posted.*
awk 'BEGIN { for (i = 0; i < 400; i++) { printf "2026-11-19 %02d:%02d:%02d\ttask\treview-pr\t%d\tok verdict approve ", int(i / 60) % 24, i % 60, i % 60, i; for (j = 0; j < 30; j++) printf "padding%02d ", j; printf "(turns 1, 10s, $0.1)\n" } }' > "$NIGHT_DIR/events.tsv"
post_night_report 21 0123456789012345678901234567890123456789 "$t/report.md" 2>/dev/null; rc=$?
ok "a long night: the report alone, then the events in comments of their own" '[ "$rc" = 0 ] && [ "$(posted_n)" -ge 3 ] && ! grep -q "incognita:events" "$t/posted.0" && head -n 1 "$t/posted.1" | grep -q "^<!-- incognita:night-events:"'
ok "a long night: every comment within the limit of GitHub" '[ -z "$(find "$t" -maxdepth 1 -name "posted.*" -size +65000c)" ]'
ok "a long night: every event read back, once" '[ "$(python3 -I "$here/stats.py" events-read "$t"/posted.* | sort -u | wc -l | tr -d " ")" = 401 ]'
rm -f "$t"/posted.*
unset -f gh

ok "Tau Ceti's rubrics are off by default (owner, 2026-11-20)" 'grep -qxF -- "$(printf ": \"\${INCOGNITA_RUBRICS=}\"")" "$here/lib.sh"'

# ---- scripts/stats.py on fixtures (no network)
ok "stats.py: the fixture test (scripts/test-stats.py)" 'python3 -I "$here/test-stats.py" > "$t/stats.log" 2>&1 || { cat "$t/stats.log"; false; }'

echo "$fails failure(s)"
[ "$fails" = 0 ]
