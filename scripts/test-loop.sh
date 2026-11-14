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
      statusCheckRollup: [{name: "Build and check", status: "COMPLETED", conclusion: "SUCCESS"}]}]' \
    "$FAKE/prs.json" > "$FAKE/p.tmp" && mv "$FAKE/p.tmp" "$FAKE/prs.json"
  echo "$sha"
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

echo "$fails failure(s)"
[ "$fails" = 0 ]
