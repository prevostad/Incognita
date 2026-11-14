#!/usr/bin/env bash
# Offline test of the task selection of scripts/loop.sh (dry run, one pass) on fake worlds: a local
# bare repository as origin and a fake `gh` answering from JSON files. Needs git, jq, python3.
# No GitHub, no sudo, no Claude. Usage: bash scripts/test-loop.sh
set -u -o pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
t=$(mktemp -d)
trap 'rm -rf "$t"' EXIT
fails=0
FAKE=$t/fake; export FAKE
mkdir -p "$FAKE/bin"

cat > "$FAKE/bin/gh" <<'GH'
#!/usr/bin/env bash
# fake gh: answers from $FAKE/*.json; applies --jq like gh does
jqf=""; args=()
while [ $# -gt 0 ]; do case "$1" in --jq) jqf=$2; shift 2 ;; *) args+=("$1"); shift ;; esac; done
set -- "${args[@]}"
out() { if [ -n "$jqf" ]; then jq -r "$jqf"; else cat; fi; }
path=""; for a in "$@"; do case "$a" in repos/*) path=$a ;; esac; done
case "$1" in
  api)
    case "$path" in
      "") [[ " $* " == *" user "* ]] && echo '{"login": "owner"}' | out ;;
      */statuses*) sha=${path#*/commits/}; sha=${sha%%/*}; cat "$FAKE/statuses-$sha.json" 2>/dev/null || echo '[]' ;;
      */comments*) n=${path#*/issues/}; n=${n%%/*}; cat "$FAKE/comments-$n.json" 2>/dev/null || echo '[]' ;;
      */actions/runs*) echo '{"workflow_runs": []}' | out ;;
      *) echo '{}' | out ;;
    esac ;;
  pr)
    case "$2" in
      list) if [[ " $* " == *" --state open "* ]]; then cat "$FAKE/prs.json"; else echo '[]'; fi | out ;;
      view) jq --argjson n "$3" '.[] | select(.number == $n) + {state: "OPEN"}' "$FAKE/prs.json" | out ;;
      *) exit 0 ;;
    esac ;;
  *) echo '[]' | out ;;
esac
GH
chmod +x "$FAKE/bin/gh"
export PATH=$FAKE/bin:$PATH

# world <known-first-line> [paper-on-main]: a fresh origin with an approved roadmap.
world() {
  rm -rf "${t:?}/origin.git" "${t:?}/repo" "${t:?}/w" "${t:?}/home"; rm -f "${FAKE:?}"/*.json
  git init -q --bare -b main "$t/origin.git"
  git init -q -b main "$t/w"; cd "$t/w" || exit 1
  git config user.name t; git config user.email t@t
  mkdir -p roadmaps/BB
  printf '# Roadmap\n\n| | |\n|---|---|\n| Status | **approved** (2026-11-14) |\n' > roadmaps/BB/ROADMAP.md
  printf '%s\n' "$1" > roadmaps/BB/KNOWN.md
  mkdir -p catalogue/results; echo '# Proof markers' > catalogue/results/README.md   # not material to garden
  if [ -n "${2:-}" ]; then
    mkdir -p "papers/$2"; printf 'roadmap = "BB"\nkind = "internal"\ndirections = ["D1"]\n' > "papers/$2/META.toml"
    echo x > "papers/$2/paper.tex"
  fi
  git add -A; git commit -qm main; git push -q "$t/origin.git" main
  git clone -q "$t/origin.git" "$t/repo"
  echo '[]' > "$FAKE/prs.json"
}
# pr <number> <role> <target> [draft]: a PR adding a paper (write-paper) or a file, head in refs/pull/N/head
pr() {
  local n=$1 role=$2 target=$3 draft=${4:-false} sha
  cd "$t/w" || exit 1
  git checkout -q -B "pr$n" main
  if [ "$role" = write-paper ]; then mkdir -p "papers/P10$n-new"; printf 'roadmap = "BB"\n' > "papers/P10$n-new/META.toml"
  else mkdir -p literature; echo "$n" > "literature/n$n.md"; fi
  git add -A; git commit -qm "pr $n"; sha=$(git rev-parse HEAD)
  git push -q "$t/origin.git" "+HEAD:refs/pull/$n/head"
  git checkout -q main
  jq --argjson n "$n" --arg r "$role" --arg tg "$target" --arg h "$sha" --argjson d "$draft" \
    '. + [{number: $n, title: "PR \($n)", body: "Role: `\($r)`. Target: `\($tg)`. Model: `m`.\n\ntext",
      headRefName: "agent/\($r)-\($n)", headRefOid: $h, isCrossRepository: false, isDraft: $d,
      labels: (if $d then [{name: "incomplete"}] else [] end), mergeable: "MERGEABLE", author: {login: "owner"},
      baseRefName: "main", createdAt: "", updatedAt: "",
      statusCheckRollup: ([{name: "Build and check", status: "COMPLETED", conclusion: "SUCCESS"}]
        + (if $r == "write-paper" or $r == "revise"
           then [{name: "Compile papers", status: "COMPLETED", conclusion: "SUCCESS"}] else [] end))}]' \
    "$FAKE/prs.json" > "$FAKE/p.tmp" && mv "$FAKE/p.tmp" "$FAKE/prs.json"
  echo "$sha"
}
check() {  # <pr> <check name> <conclusion>: set the conclusion of a check of a PR
  jq --argjson n "$1" --arg c "$2" --arg v "$3" \
    'map(if .number == $n then .statusCheckRollup |= ([.[] | select(.name != $c)] + [{name: $c, status: "COMPLETED", conclusion: $v}]) else . end)' \
    "$FAKE/prs.json" > "$FAKE/p.tmp" && mv "$FAKE/p.tmp" "$FAKE/prs.json"
}
on_main() {  # <path> <content>: commit a file on main (origin) and refresh the loop's clone
  cd "$t/w" || exit 1
  mkdir -p "$(dirname "$1")"; printf '%s\n' "$2" > "$1"
  git add -A; git commit -qm "main: $1"; git push -q "$t/origin.git" main
}
nopass() {  # the dry pass must NOT print this fragment
  local out
  out=$(cd "$t/repo" && INCOGNITA_REPO=$t/repo INCOGNITA_HOME=$t/home INCOGNITA_GH_REPO=o/r INCOGNITA_DRY_RUN=1 \
    INCOGNITA_DEADLINE_EPOCH=$(( $(date +%s) + 36000 )) bash "$here/loop.sh" 2>&1)
  if [[ "$out" != *"$2"* && "$out" == *"dry run: one pass done"* ]]; then echo "ok   $1"
  else echo "FAIL $1 (did not want \"$2\", or the pass did not end)"; printf '%s\n' "$out" | grep -E '== task|would|error|fatal' | head -n 5; fails=$(( fails + 1 )); fi
}
status() {  # sha context role verdict state
  local f=$FAKE/statuses-$1.json
  [ -f "$f" ] || echo '[]' > "$f"
  jq --arg c "$2" --arg d "role=$3 verdict=$4 pr=1" --arg s "$5" \
    '. + [{context: $c, state: $s, description: $d, creator: {login: "owner"}, created_at: "2026-11-14T10:00:00Z"}]' \
    "$f" > "$f.tmp" && mv "$f.tmp" "$f"
}
pass() {  # expected "== task: ..." or "would merge" fragment
  local out
  out=$(cd "$t/repo" && INCOGNITA_REPO=$t/repo INCOGNITA_HOME=$t/home INCOGNITA_GH_REPO=o/r INCOGNITA_DRY_RUN=1 \
    INCOGNITA_DEADLINE_EPOCH=$(( $(date +%s) + 36000 )) bash "$here/loop.sh" 2>&1)
  if [[ "$out" == *"$2"* ]]; then echo "ok   $1"; else echo "FAIL $1 (wanted \"$2\")"; printf '%s\n' "$out" | grep -E '== task|would|FAIL|error|fatal' | head -n 5; fails=$(( fails + 1 )); fi
}

world "Reviewed by owner: 2026-11-14"
pass "an approved, reviewed roadmap gets a paper" "== task: write-paper BB"
pass "task.md gives the number of the new paper" 'a new directory `papers/P000-<slug>/`'
pass "task.md gives the roadmap and its KNOWN.md" 'KNOWN.md: `roadmaps/BB/KNOWN.md`'
world "Reviewed by owner: no (draft)"
pass "KNOWN not reviewed: no paper, fallback bibliographer" "== task: bibliographer -"
world "Reviewed by owner: 2026-11-14" P001-old
pass "formalisation before writing" "== task: formalize-statements P001-old"
world "Reviewed by owner: 2026-11-14"
h=$(pr 5 write-paper BB)
pass "a new paper PR goes to referee-scope" "== task: referee-scope 5"
status "$h" "Referee scope" referee-scope accept success
pass "scope accepted: referee-proofs" "== task: referee-proofs 5"
status "$h" "Referee proofs" referee-proofs major failure
pass "a gap: revise" "== task: revise 5"
world "Reviewed by owner: 2026-11-14"
h=$(pr 6 write-paper BB)
status "$h" "Referee scope" referee-scope accept success
status "$h" "Referee proofs" referee-proofs accept success
status "$h" "Incognita review" referees accept success
pass "both referees accept: merged" "would merge #6"
world "Reviewed by owner: 2026-11-14"
h=$(pr 7 write-paper BB)
jq '.[0].statusCheckRollup = [{name: "Build and check", status: "COMPLETED", conclusion: "SUCCESS"}] | .[0].isCrossRepository = true' \
  "$FAKE/prs.json" > "$FAKE/p.tmp" && mv "$FAKE/p.tmp" "$FAKE/prs.json"
pass "fork PRs are ignored" "== task: write-paper BB"
world "Reviewed by owner: 2026-11-14"
h=$(pr 8 bibliographer -)
status "$h" "Incognita review" review-pr request_changes failure
pass "changes requested: fix-pr" "== task: fix-pr 8"
world "Reviewed by owner: 2026-11-14"
h=$(pr 9 bibliographer -)
f=$FAKE/statuses-$h.json; echo '[{"context": "Incognita review", "state": "success", "description": "role=review-pr verdict=approve pr=9", "creator": {"login": "github-actions[bot]"}, "created_at": "2026-11-14T10:00:00Z"}]' > "$f"
pass "a workflow's status is not trusted: review-pr" "== task: review-pr 9"
world "Reviewed by owner: 2026-11-14"
h=$(pr 10 prove P001-x true)
pass "an incomplete draft is continued" "== task: fix-pr 10"

# Papers: the check "Compile papers" (workflow Papers) counts; repairs of paper PRs go to revise.
world "Reviewed by owner: 2026-11-14"
h=$(pr 11 write-paper BB true)
pass "an incomplete paper draft is continued by revise" "== task: revise 11"
world "Reviewed by owner: 2026-11-14"
h=$(pr 12 write-paper BB)
check 12 "Build and check" FAILURE
pass "a paper whose build failed: revise (not fix-pr)" "== task: revise 12"
world "Reviewed by owner: 2026-11-14"
h=$(pr 13 write-paper BB)
check 13 "Compile papers" FAILURE
status "$h" "Referee scope" referee-scope accept success
status "$h" "Referee proofs" referee-proofs accept success
status "$h" "Incognita review" referees accept success
nopass "accepted but LaTeX fails: not merged" "would merge #13"
pass "accepted but LaTeX fails: revise" "== task: revise 13"
world "Reviewed by owner: 2026-11-14"
h=$(pr 14 write-paper BB)
jq 'map(.statusCheckRollup |= map(select(.name != "Compile papers")))' "$FAKE/prs.json" > "$FAKE/p.tmp" && mv "$FAKE/p.tmp" "$FAKE/prs.json"
nopass "Compile papers missing: no referee yet" "== task: referee-scope 14"

# Errata and statement corrections (AGENTS.md §6.6).
world "Reviewed by owner: 2026-11-14" P001-old
on_main papers/P001-old/errata.md "$(printf '## E1 (d)\n- Node: thm:main')"
pass "a disputed paper is revised" "== task: revise P001-old"
pass "task.md names the errata entries" "for the errata entries E1"
world "Reviewed by owner: 2026-11-14" P001-old
on_main Statements/P001/main_thm.lock "x"
on_main papers/P001-old/errata.md "$(printf '## E1 (d)\n- Node: thm:main\nRevised in the version of d: x')"
pass "an erratum revised in a new version: corrected statements to freeze" "== task: formalize-statements P001-old"
world "Reviewed by owner: 2026-11-14" P001-old
on_main Statements/P001/main_thm.lock "x"
on_main papers/P001-old/statement-corrections.md "$(printf '## SC1 (d)\n- Frozen statement: Incognita.Statements.P001.main_thm')"
pass "a statement correction: corrected statement to freeze" "== task: formalize-statements P001-old"
pass "task.md names the entries to resolve" "Entries to resolve: SC1"
world "Reviewed by owner: 2026-11-14" P001-old
on_main Statements/P001/main_thm.lock "x"
on_main papers/P001-old/statement-corrections.md "$(printf '## SC1 (d)\n- Frozen statement: Incognita.Statements.P001.main_thm\nResolved by Incognita.Statements.P001.main_thm_v2')"
nopass "a resolved correction needs nothing" "== task: formalize-statements P001-old"

echo "$fails failure(s)"
[ "$fails" = 0 ]
