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
  "statusCheckRollup": [{"name": "Build and check", "status": "COMPLETED", "conclusion": "SUCCESS"}]},
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
try "prove: library, results marker, formalisation.tex, notebook" prove P001-test 0 \
  'mkdir -p catalogue/results papers/P001-test/notebook; echo l > Incognita/L.lean; echo m > catalogue/results/P001-test-thm.toml; echo f > papers/P001-test/formalisation.tex; echo n > papers/P001-test/notebook/n.py'
try "prove may not edit the paper" prove P001-test 1 'mkdir -p papers/P001-test; echo p > papers/P001-test/paper.tex'
try "prove may not touch Statements/" prove P001-test 1 'mkdir -p Statements/P001; echo t > Statements/P001/x.lean'
try "bibliographer: literature and catalogue only" bibliographer "" 1 'echo l > Incognita/L.lean'
try "review roles change nothing" review-pr "" 1 'mkdir -p literature; echo l > literature/x.md'
try "fix-main may fix the library" fix-main "" 0 'echo z >> Incognita/Basic.lean'

# ---- merge categories, definitions in proof PRs
ok "category papers" '[ "$(path_category paper papers/P001-a/paper.tex M)" = papers ]'
ok "papers/ in a proof PR: notebook ok, paper.tex for the owner" '[ "$(path_category generic papers/P001-a/notebook/x.py A)" = proofs ] && [ "$(path_category generic papers/P001-a/paper.tex M)" = other ]'
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
