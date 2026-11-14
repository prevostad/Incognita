#!/usr/bin/env bash
# The Incognita loop: until the deadline, pass after pass, merge what is ready (one PR per pass),
# rebase mechanically what conflicts, then run the most useful agent task (scripts/agent.sh).
# Normally started (and restarted) by scripts/night.sh. See agents/README.md ("The loop").
#
# Usage: scripts/loop.sh            in the loop's clone of main (on branch main, never edited by hand)
#        INCOGNITA_DRY_RUN=1 scripts/loop.sh    one pass: print what would be done, change nothing
#
# Exit: 0 deadline reached (or dry run done), 3 Claude logged out, 1 fatal error. Never exits on its
# own otherwise: no `set -e`; every call is checked.
set -u -o pipefail
# shellcheck source=scripts/lib.sh
. "$(dirname "${BASH_SOURCE[0]}")/lib.sh"

init_state || { echo "cannot create $INCOGNITA_STATE" >&2; exit 1; }
DEADLINE=$(deadline_epoch) || exit 1
export INCOGNITA_DEADLINE_EPOCH=$DEADLINE
LOG=$INCOGNITA_LOGS/$INCOGNITA_NIGHT.log
if ! is_dry && [ -z "${INCOGNITA_LOGGING:-}" ]; then exec > >(tee -a "$LOG") 2>&1; fi
trap 'log "error: exit $? at line $LINENO: $BASH_COMMAND"' ERR

# Heartbeat: one line a minute with the current activity (read by night.sh and by the owner).
# Detached from our output, so that nothing waits for its sleep.
HB=""
if ! is_dry; then
  ( while kill -0 "$$" 2>/dev/null; do
      printf '%s %s pid=%s %s\n' "$(now)" "$(date '+%F %T')" "$$" "$(cat "$INCOGNITA_HOME/activity" 2>/dev/null)" \
        > "$INCOGNITA_HOME/heartbeat" 2>/dev/null
      sleep 60
    done ) </dev/null >/dev/null 2>&1 &
  HB=$!
fi
work=$(mktemp -d)
trap '[ -n "$HB" ] && kill "$HB" 2>/dev/null; rm -rf "$work"; set_activity stopped' EXIT
AGENT_PID=""
on_term() {
  log "== loop terminated by a signal"
  if [ -n "$AGENT_PID" ]; then kill -TERM "$AGENT_PID" 2>/dev/null; wait "$AGENT_PID" 2>/dev/null; fi
  exit 143
}
trap on_term TERM INT

PRS=$work/prs.json ROWS=$work/rows.tsv BUSY=$work/busy.txt
declare -A STS=()

until owner_login >/dev/null; do
  log "gh api user failed: retrying in 2 min"
  [ "$(remaining)" -le 120 ] && exit 0
  sleep 120
done
log "== loop start (pid $$), owner $OWNER, deadline $([ "$DEADLINE" = 0 ] && echo none || date -d "@$DEADLINE" '+%F %T'), pace ${INCOGNITA_PACE:-default}, automerge ${INCOGNITA_AUTOMERGE:-none}"

# ---------------------------------------------------------------- quota
# INCOGNITA_PACE=0:100 (the owner's rule) or off: no pacing; rate-limit errors of a session make the
# loop wait until the reset. Otherwise, v1's Tau Ceti pacer (`tauceti status --json`).
tauceti_conf=${INCOGNITA_TAUCETI_CONF:-https://raw.githubusercontent.com/LeanMachineLearning/LMLExplore/main/tauceti.toml}
wait_for_quota() {
  local until
  until=$(cat "$INCOGNITA_STATE/rate-limit-until" 2>/dev/null || echo 0)
  if [[ "$until" =~ ^[0-9]+$ ]] && [ "$until" -gt "$(now)" ]; then
    log "== quota: rate limited until $(date -d "@$until" '+%F %T'); waiting"
    set_activity "rate limited until $(date -d "@$until" '+%H:%M')"
    record_event quota-wait - - "$(( until - $(now) ))s (rate limit)"
    sleep_bounded $(( until - $(now) + 30 ))
  fi
  rm -f "$INCOGNITA_STATE/rate-limit-until"
  case "${INCOGNITA_PACE:-}" in 0:100|off) return 0 ;; esac
  local q ok next s
  while [ "$(remaining)" -gt 0 ]; do
    if [ -n "${INCOGNITA_PACE:-}" ]; then
      q=$(TAUCETI_PACE="$INCOGNITA_PACE" tauceti --conf "$tauceti_conf" status --json 2>/dev/null \
        | jq -c '.quota.claude' 2>/dev/null) || q=""
    else
      q=$(tauceti --conf "$tauceti_conf" status --json 2>/dev/null | jq -c '.quota.claude' 2>/dev/null) || q=""
    fi
    ok=$(printf '%s' "${q:-null}" | jq -r '
      if . == null or (.windows | length) == 0 then "unknown (\(.error // "no reading"))"
      elif .rate_limited then "rate limited"
      elif ([.windows[].status] | all(. == "under-pace" or . == "idle")) then "yes"
      else "over pace" end' 2>/dev/null || echo "unknown")
    [ "$ok" = yes ] && return 0
    next=$(printf '%s' "${q:-null}" | jq -r '.next_eligible // empty' 2>/dev/null || true)
    if [ -n "$next" ]; then s=$(( ${next%.*} - $(now) + 60 )); else s=900; fi
    [ "$s" -lt 300 ] && s=300
    [ "$s" -gt 3600 ] && s=3600
    log "== quota: $ok; waiting ${s}s"
    set_activity "quota: $ok"
    record_event quota-wait - - "${s}s ($ok)"
    sleep_bounded "$s"
  done
  return 1
}

# ---------------------------------------------------------------- helpers on rows
load_sts() {  # sha: STS_CUR = its statuses (cached for the pass)
  if [ -z "${STS[$1]+x}" ]; then
    STS[$1]=$(statuses_of "$1") || { STS_CUR=""; return 1; }
  fi
  STS_CUR=${STS[$1]}
}
has_label() { case ",$1," in *",$2,"*) return 0 ;; *) return 1 ;; esac; }
is_busy() {  # role target (target "*" = any)
  if [ "$2" = "*" ]; then grep -q "^$1 " "$BUSY"; else grep -qxF "$1 $2" "$BUSY"; fi
}
can_try() {  # role target: not parked, fewer than INCOGNITA_MAX_FAILS failures tonight
  is_parked "$1" "$2" && return 1
  [ "$(night_fails "$1" "$2")" -lt "$INCOGNITA_MAX_FAILS" ]
}
task_budget() {  # role: seconds a task of this role may take now (0 if it does not fit)
  local b max min v
  b=$(( $(remaining) - 300 ))
  if is_review_role "$1"; then max=$INCOGNITA_TIMEOUT_REVIEW min=$INCOGNITA_MIN_REVIEW
  else max=$INCOGNITA_TIMEOUT_WRITE min=$INCOGNITA_MIN_WRITE; fi
  v=INCOGNITA_TIMEOUT_$(printf '%s' "$1" | tr 'a-z-' 'A-Z_')   # per-role override, as in agent.sh
  [ -n "${!v:-}" ] && max=${!v}
  [ "$b" -lt "$min" ] && { echo 0; return; }
  [ "$b" -gt "$max" ] && b=$max
  echo "$b"
}
T_ROLE="" T_TARGET="" T_HEAD="" T_NOTE="" T_BUDGET=0
pick() {  # role target head note: select this task if allowed and it fits before the deadline
  local b
  can_try "$1" "$2" || return 1
  b=$(task_budget "$1")
  [ "$b" -gt 0 ] || return 1
  T_ROLE=$1 T_TARGET=$2 T_HEAD=$3 T_NOTE=$4 T_BUDGET=$b
  return 0
}
revise_rounds() {  # pr: "<rounds pushed> <rounds without change>" (trusted comments)
  trusted_comments "$1" | jq -r '"\([.[] | select(.kind == "revise")] | length) \([.[] | select(.kind == "revise-nochange")] | length)"'
}

# ---------------------------------------------------------------- merge (D13, D15): one per pass
NEEDS_REBASE=""
try_merge() {
  local n H br draft mg role target labels ci kind mb cats c bad eff paper title
  while IFS=$'\t' read -r n H br draft mg role target labels ci; do
    [ "$draft" = ready ] || continue
    has_label "$labels" needs-human || has_label "$labels" incomplete || has_label "$labels" rejected && continue
    [ "$mg" = MERGEABLE ] || continue
    [ "$ci" = SUCCESS ] || continue
    if [ "$MAIN_RED" = 1 ] && ! { [ "$role" = fix-pr ] && [ "$target" = main ]; }; then continue; fi
    kind=$(pr_kind "$role")
    load_sts "$H" || continue
    case "$kind" in
      paper)
        [ "$(verdict_in "$STS_CUR" "Referee scope" referee-scope)" = accept ] \
          && [ "$(verdict_in "$STS_CUR" "Referee proofs" referee-proofs)" = accept ] \
          && [ "$(verdict_in "$STS_CUR" "Incognita review" referees)" = accept ] || continue ;;
      statements) [ "$(verdict_in "$STS_CUR" "Incognita review" review-statements)" = approve ] || continue ;;
      *) [ "$(verdict_in "$STS_CUR" "Incognita review" review-pr)" = approve ] || continue ;;
    esac
    fetch_pr_head "$n" "$H" || continue
    mb=$(repo_git merge-base origin/main "$H") || continue
    # Categories: every changed path in an enabled category.
    bad=""
    cats=$(repo_git diff --raw --no-renames --no-abbrev "$mb" "$H" \
      | awk -F'\t' '{ split($1, m, " "); print m[5] "\t" $2 }' \
      | while IFS=$'\t' read -r st path; do path_category "$kind" "$path" "$st"; done | sort -u | tr '\n' ' ')
    for c in $cats; do
      { [ "$c" != other ] && automerge_enabled "$c"; } || bad="$bad $c"
    done
    if [ -n "$bad" ]; then
      mark_has "owner-merge $H" || { log "#$n is ready but waits for the owner (categories:$bad)"; mark_set "owner-merge $H"
        record_event owner-merge - "$n" "categories:$bad"; }
      continue
    fi
    if in_list proofs "$cats" && ! adds_only_theorems "$mb" "$H"; then
      mark_has "owner-merge $H" || { log "#$n adds definitions: waits for the owner"; mark_set "owner-merge $H"
        record_event owner-merge - "$n" "adds definitions"; }
      continue
    fi
    # Defence in depth: the whitelist of the role that opened the PR, again, on the whole PR.
    case "$role" in fix-pr) eff=fix-main ;; *) eff=$role ;; esac
    paper=$(repo_git diff --name-only --no-renames "$mb" "$H" -- papers | sed -n -E 's#^papers/([^/]+)/.*#\1#p' | head -n 1)
    [ "$role" = formalize-statements ] || [ "$role" = prove ] && paper=$(paper_of_num "$(paper_num "$target")" || echo "$target")
    if ! check_paths "$eff" "$paper" "$mb" "$H" 2>"$work/paths.log"; then
      log "#$n: paths refused at merge time:"; cat "$work/paths.log" >&2
      escalate "$n" "paths refused at merge time"
      continue
    fi
    # Lean changes merge only on top of main (D13).
    if repo_git diff --name-only --no-renames "$mb" "$H" | grep -qE '\.(lean|lock)$' \
        && ! repo_git merge-base --is-ancestor origin/main "$H"; then
      NEEDS_REBASE="$NEEDS_REBASE $n"
      continue
    fi
    title=$(jq -r --argjson n "$n" '.[] | select(.number == $n) | .title' "$PRS" | one_line 200)
    if is_dry; then log "dry run: would merge #$n ($kind, categories: $(echo $cats)) at ${H:0:12}"; return 0; fi
    set_activity "merging #$n"
    if ghr api -X PUT "repos/$GH_REPO/pulls/$n/merge" -f sha="$H" -f merge_method=squash \
        -f commit_title="$title (#$n)" \
        -f commit_message="Merged by the Incognita loop: role $role, target $target, categories $(echo $cats), reviews on $H." >/dev/null; then
      log "== merged #$n ($kind: $(echo $cats)) $title"
      record_event merge "$role" "$n" "$kind $(echo $cats) — $title"
      gh api -X DELETE "repos/$GH_REPO/git/refs/heads/$br" >/dev/null 2>&1 || true
      return 0
    fi
    log "merge of #$n failed"
  done < "$ROWS"
  return 1
}

# ---------------------------------------------------------------- mechanical rebase (D13)
mech_rebase() {  # pr H branch: 0 rebased and pushed, 1 needs an agent, 2 error, 3 nothing to do
  local n=$1 h=$2 br=$3 wt=$INCOGNITA_HOME/work/rebase-$1 gd newh i conflicted f
  fetch_pr_head "$n" "$h" || return 2
  repo_git merge-base --is-ancestor origin/main "$h" && return 3
  if is_dry; then log "dry run: would rebase #$n on main"; return 3; fi
  set_activity "rebasing #$n"
  repo_git worktree remove --force "$wt" >/dev/null 2>&1; rm -rf "$wt"; repo_git worktree prune
  repo_git worktree add -q --detach "$wt" "$h" || return 2
  local g=(git -C "$wt" -c core.hooksPath=/dev/null -c core.fsmonitor=false
           -c "user.name=$INCOGNITA_BOT_NAME" -c "user.email=$INCOGNITA_BOT_EMAIL")
  gd=$("${g[@]}" rev-parse --absolute-git-dir)
  GIT_EDITOR=true "${g[@]}" rebase -q origin/main >/dev/null 2>&1
  for i in $(seq 1 300); do
    [ -d "$gd/rebase-merge" ] || [ -d "$gd/rebase-apply" ] || break
    conflicted=$("${g[@]}" diff --name-only --diff-filter=U)
    for f in $conflicted; do
      if in_list "$f" "$ROOT_FILES" && resolve_imports "$wt" "$f"; then
        "${g[@]}" add -- "$f"
      else
        log "#$n: conflict on $f: left to fix-pr"
        "${g[@]}" rebase --abort >/dev/null 2>&1
        repo_git worktree remove --force "$wt" >/dev/null 2>&1
        mark_set "rebase-failed $h"
        return 1
      fi
    done
    GIT_EDITOR=true "${g[@]}" rebase --continue >/dev/null 2>&1 \
      || { [ -z "$("${g[@]}" diff --name-only --diff-filter=U)" ] && GIT_EDITOR=true "${g[@]}" rebase --skip >/dev/null 2>&1; }
  done
  if [ -d "$gd/rebase-merge" ] || [ -d "$gd/rebase-apply" ]; then
    "${g[@]}" rebase --abort >/dev/null 2>&1; repo_git worktree remove --force "$wt" >/dev/null 2>&1
    mark_set "rebase-failed $h"; return 1
  fi
  newh=$("${g[@]}" rev-parse HEAD)
  repo_git worktree remove --force "$wt" >/dev/null 2>&1
  [ "$newh" = "$h" ] && return 3
  if ! repo_git push -q --force-with-lease="refs/heads/$br:$h" origin "$newh:refs/heads/$br"; then
    log "#$n: push of the rebase refused (the branch moved)"; return 2
  fi
  local copied=no
  # Statuses follow the rebase only if every changed path has the same blob (D13).
  if [ "$(diff_signature "$(repo_git merge-base origin/main "$h")" "$h")" = "$(diff_signature origin/main "$newh")" ] \
      && load_sts "$h"; then
    local ctx state trusted desc
    while IFS=$'\t' read -r ctx state trusted desc; do
      [ "$trusted" = yes ] || continue
      case "$ctx" in "Referee scope"|"Referee proofs"|"Incognita review") ;; *) continue ;; esac
      set_status "$newh" "$ctx" "$state" "${desc%% copied-from=*} copied-from=${h:0:12}" && copied=yes
    done <<< "$STS_CUR"
  fi
  printf 'Rebased on `main` by the script (no agent): `%s` → `%s`. Reviews copied: %s.\n' \
    "${h:0:12}" "${newh:0:12}" "$copied" > "$work/rebase.md"
  post_comment "$n" rebase "$newh" "$work/rebase.md" >/dev/null
  log "== rebased #$n: ${h:0:12} -> ${newh:0:12} (statuses copied: $copied)"
  record_event rebase - "$n" "statuses copied: $copied"
  return 0
}

# ---------------------------------------------------------------- what to do (SPEC 3.4, D5, D6)
paper_open_errata() {  # paper: disputed, not yet revised (an errata entry with neither "Revised in" nor "Resolved by")
  [ -n "$(disputed_entries "$1")" ]
}
needs_statements() {  # paper: no frozen statement yet, or entries waiting for corrected statements
  [ -z "$(locks_of "$1")" ] || [ -n "$(freeze_entries "$1")" ]
}
# statements_state <paper>: none | open | verified | settled, from the audit status of main. Frozen
# statements superseded by a resolved erratum or correction (papers/README.md) do not count.
# open: some statement is still open (prove has work); verified: all proved; settled: none open,
# some refuted (the paper is disputed or its corrected statements are frozen).
statements_state() {
  local n locks sup
  locks=$(locks_of "$1")
  [ -n "$locks" ] || { echo none; return; }
  n=$(paper_num "$1")
  if [ "$AUDIT_OK" != 1 ]; then echo open; return; fi
  sup=$(superseded "$1" | tr '\n' ' ')
  printf '%s\n' "$AUDIT" | awk -v n="$n" -v sup=" $sup " '
    { k = $1; sub(/^P0*/, "", k); sub(/[^0-9].*/, "", k) }
    k == n && index(sup, " " $2 " ") == 0 { seen = 1; if ($3 == "open") o = 1; else if ($3 == "refuted") r = 1 }
    END { if (o || !seen) print "open"; else if (r) print "settled"; else print "verified" }'
}
accepted_unverified() {  # roadmap: papers on main not verified yet (D5 cap)
  local r=$1 p c=0
  for p in $(papers_on_main); do
    [ "$(meta_get "$p" roadmap)" = "$r" ] || continue
    [ "$(meta_get "$p" kind)" = definitions ] && continue
    paper_open_errata "$p" && continue
    [ "$(statements_state "$p")" = verified ] || c=$(( c + 1 ))
  done
  echo "$c"
}
in_review() { grep -cxF "write-paper $1" "$BUSY"; }
has_material() {  # something validated to garden
  local p
  for p in $(papers_on_main); do [ "$(meta_get "$p" kind)" != definitions ] && return 0; done
  [ -n "$(ls_main catalogue/results)" ]
}
bib_needed() {  # external papers without source notes, or verified papers without an attribution audit
  local p src
  for p in $(papers_on_main); do
    if [ "$(meta_get "$p" kind)" = external ]; then
      src=$(meta_get "$p" source | tr -d '[]')
      [ -n "$src" ] && ! repo_git cat-file -e "origin/main:literature/notes/$src.md" 2>/dev/null && return 0
    fi
    # Novelty lives in catalogue/attribution/<prefix>.md (proof markers are additions only).
    [ "$AUDIT_OK" = 1 ] && [ "$(meta_get "$p" kind)" = internal ] \
      && [ "$(statements_state "$p")" = verified ] \
      && ! repo_git cat-file -e "origin/main:catalogue/attribution/$(printf '%s' "$p" | sed -E 's/^(P[0-9]+).*/\1/').md" 2>/dev/null \
      && return 0
  done
  return 1
}
pick_rotation() {  # garden / bibliographer, alternately
  local first second r
  if [ "$(cat "$INCOGNITA_STATE/last-rotation" 2>/dev/null)" = garden ]; then first=bibliographer second=garden
  else first=garden second=bibliographer; fi
  for r in $first $second; do
    is_busy "$r" "*" && continue
    [ "$r" = garden ] && ! has_material && continue
    pick "$r" - "" "Regular $r pass (rotation)." && return 0
  done
  return 1
}
pick_write_paper() {  # cap: fewer than this many papers in review in the roadmap
  local cap=$1 r best="" bestc=999 c
  for r in $(roadmaps_writable); do
    c=$(in_review "$r")
    [ "$c" -lt "$cap" ] || continue
    [ "$(accepted_unverified "$r")" -lt "$INCOGNITA_ACCEPTED_UNVERIFIED_MAX" ] || continue
    can_try write-paper "$r" || continue
    [ "$c" -lt "$bestc" ] && { best=$r; bestc=$c; }
  done
  [ -n "$best" ] && pick write-paper "$best" "" ""
}

choose_task() {
  T_ROLE="" T_TARGET="" T_HEAD="" T_NOTE="" T_BUDGET=0
  local n H br draft mg role target labels ci kind cie sc pv rv rounds fixes fixer
  local fixes_list="" reviews_list=""
  # 1. main is red: one fix-main task.
  if [ "$MAIN_RED" = 1 ] && ! is_busy fix-pr main; then
    pick fix-pr main "" "The build of main is red." && return 0
  fi
  # 2-3. Agents' PRs: fixes and revisions first, then reviews (oldest PR first).
  while IFS=$'\t' read -r n H br draft mg role target labels ci; do
    has_label "$labels" needs-human || has_label "$labels" rejected && continue
    kind=$(pr_kind "$role")
    fixes=$(counter_get "fix-rounds $n")
    # Repairs (failed build, conflict, incomplete draft): `revise` for a paper PR (a repair round,
    # not a revision round), `fix-pr` for any other.
    fixer=fix-pr
    [ "$kind" = paper ] && fixer=revise
    if [ "$draft" = draft ]; then
      has_label "$labels" incomplete || continue
      if [ "$fixes" -ge "$INCOGNITA_FIX_LIMIT" ]; then
        if [ "$kind" = paper ]; then close_rejected "$n" "$H" "could not be completed after $fixes rounds"
        else escalate "$n" "still incomplete after $fixes rounds"; fi
        continue
      fi
      fixes_list="$fixes_list $fixer:$n:$H:incomplete"
      continue
    fi
    cie=$(ci_effective "$H" "$ci")
    if [ "$cie" = failed ] || { [ "$mg" = CONFLICTING ] && mark_has "rebase-failed $H"; }; then
      if [ "$fixes" -ge "$INCOGNITA_FIX_LIMIT" ]; then
        if [ "$kind" = paper ]; then close_rejected "$n" "$H" "build or conflict not repaired after $fixes rounds"
        else escalate "$n" "$fixes fix rounds without success"; fi
        continue
      fi
      fixes_list="$fixes_list $fixer:$n:$H:$([ "$cie" = failed ] && echo build || echo conflict)"
      continue
    fi
    load_sts "$H" || continue
    if [ "$kind" = paper ]; then
      sc=$(verdict_in "$STS_CUR" "Referee scope" referee-scope)
      pv=$(verdict_in "$STS_CUR" "Referee proofs" referee-proofs)
      if [ "$sc" = reject ] || [ "$pv" = reject ]; then
        close_rejected "$n" "$H" "a referee rejected the paper"; continue
      fi
      if [ "$sc" = major ] || [ "$sc" = minor ] || [ "$pv" = major ] || [ "$pv" = minor ]; then
        rounds=$(revise_rounds "$n") || continue
        set -- $rounds
        # D2: at most INCOGNITA_REVISION_ROUNDS rounds; rounds that changed nothing count half.
        if [ "${1:-0}" -ge "$INCOGNITA_REVISION_ROUNDS" ] \
            || [ $(( ${1:-0} + ${2:-0} )) -ge $(( 2 * INCOGNITA_REVISION_ROUNDS )) ]; then
          close_rejected "$n" "$H" "gaps remain after ${1:-0} revision rounds (${2:-0} without change)"; continue
        fi
        fixes_list="$fixes_list revise:$n:$H:referees"
        continue
      fi
    else
      case "$kind" in statements) rv=$(verdict_in "$STS_CUR" "Incognita review" review-statements) ;;
                      *) rv=$(verdict_in "$STS_CUR" "Incognita review" review-pr) ;; esac
      if [ "$rv" = reject ]; then escalate "$n" "review verdict reject"; continue; fi
      if [ "$rv" = request_changes ]; then
        if [ "$fixes" -ge "$INCOGNITA_FIX_LIMIT" ]; then escalate "$n" "$fixes fix rounds without approval"; continue; fi
        fixes_list="$fixes_list fix-pr:$n:$H:review"
        continue
      fi
    fi
    # Reviews: build green, no conflict, no trusted verdict on H for the needed role.
    [ "$cie" = success ] && [ "$mg" != CONFLICTING ] || continue
    if [ "$MAIN_RED" = 1 ] && ! { [ "$role" = fix-pr ] && [ "$target" = main ]; }; then continue; fi
    case "$kind" in
      paper)
        if [ "$sc" = none ]; then reviews_list="$reviews_list referee-scope:$n:$H:-"
        elif [ "$sc" = accept ] && [ "$pv" = none ]; then reviews_list="$reviews_list referee-proofs:$n:$H:-"; fi ;;
      statements) [ "$rv" = none ] && reviews_list="$reviews_list review-statements:$n:$H:-" ;;
      *) [ "$rv" = none ] && reviews_list="$reviews_list review-pr:$n:$H:-" ;;
    esac
  done < "$ROWS"
  local it r t h why note
  for it in $fixes_list $reviews_list; do
    IFS=: read -r r t h why <<< "$it"
    case "$why" in
      build) note="The build failed on the head (after one automatic rerun)." ;;
      conflict) note="The branch conflicts with main and the mechanical rebase failed: rebase it (\`git rebase origin/main\`)." ;;
      incomplete) note="Continue the incomplete work of this draft." ;;
      review) note="The reviewer requested changes on the head: address the latest report." ;;
      referees) note="The referees found gaps on the head: address their latest reports." ;;
      *) note="" ;;
    esac
    pick "$r" "$t" "$h" "$note" && return 0
  done
  # 4. Rotation: garden and bibliographer, regularly (D6, D7).
  if [ "$(counter_get since-rotation)" -ge "$INCOGNITA_ROTATION_EVERY" ]; then
    pick_rotation && return 0
  fi
  # 5. prove: frozen, unproved statements, oldest paper first (D5: formalisation first).
  local p
  if [ "$AUDIT_OK" = 1 ]; then
    for p in $(papers_on_main); do
      [ "$(statements_state "$p")" = open ] || continue
      is_busy prove "$p" && continue
      pick prove "$p" "" "" && return 0
    done
  fi
  # 6. formalize-statements: accepted papers without frozen statements, or with corrected statements
  #    to freeze (an erratum revised in a new version, a statement correction), not disputed.
  for p in $(papers_on_main); do
    paper_open_errata "$p" && continue
    needs_statements "$p" || continue
    is_busy formalize-statements "$p" && continue
    pick formalize-statements "$p" "" "" && return 0
  done
  # 7. revise: disputed papers (an errata entry neither revised nor resolved).
  for p in $(papers_on_main); do
    paper_open_errata "$p" || continue
    is_busy revise "$p" && continue
    pick revise "$p" "" "The paper is disputed: write its next version." && return 0
  done
  # 8. bibliographer when something waits for it.
  if ! is_busy bibliographer "*" && bib_needed; then
    pick bibliographer - "" "Source notes or novelty checks are missing." && return 0
  fi
  # 9. write-paper, below INCOGNITA_PAPERS_IN_REVIEW papers in review per roadmap.
  pick_write_paper "$INCOGNITA_PAPERS_IN_REVIEW" && return 0
  # 10. Fallback: write-paper up to INCOGNITA_PAPERS_MAX, then garden, then bibliographer.
  pick_write_paper "$INCOGNITA_PAPERS_MAX" && return 0
  if ! is_busy garden "*" && has_material; then pick garden - "" "Fallback gardening pass." && return 0; fi
  if ! is_busy bibliographer "*"; then pick bibliographer - "" "Fallback bibliography pass." && return 0; fi
  return 1
}

# ---------------------------------------------------------------- one pass
MAIN_RED=0 AUDIT="" AUDIT_OK=0
one_pass() {  # 0 did something, 10 idle, 11 GitHub unknown, 3 logged out
  STS=()
  NEEDS_REBASE=""
  set_activity "pass: reading GitHub"
  local M rc did=0 n H br draft mg role target labels ci k
  M=$(sync_main) || return 11
  fetch_open_prs > "$PRS" || return 11
  agent_rows "$PRS" | sort -n > "$ROWS" || return 11
  busy_pairs "$PRS" > "$BUSY" || return 11
  if main_red "$M"; then
    [ "$MAIN_RED" = 1 ] || { log "== main is red (${M:0:12}): no reviews, no merges but fix-main"; record_event main-red - - "${M:0:12}"; }
    MAIN_RED=1
  else MAIN_RED=0; fi
  if AUDIT=$(audit_status); then AUDIT_OK=1; else AUDIT_OK=0; log "audit status of main unknown"; fi
  # Merge one PR.
  try_merge && did=1
  # Mechanical rebases: conflicting agent PRs, and ready Lean PRs behind main (at most 2 per pass).
  k=0
  while IFS=$'\t' read -r n H br draft mg role target labels ci; do
    [ "$k" -lt 2 ] || break
    has_label "$labels" needs-human || has_label "$labels" rejected && continue
    if [ "$mg" = CONFLICTING ] && ! mark_has "rebase-failed $H"; then :
    elif in_list "$n" "$NEEDS_REBASE"; then :
    else continue; fi
    rc=0; mech_rebase "$n" "$H" "$br" || rc=$?
    k=$(( k + 1 ))
    [ "$rc" = 0 ] && did=1
  done < "$ROWS"
  # One agent task.
  if ! choose_task; then
    [ "$did" = 1 ] && return 0
    return 10
  fi
  log "== task: $T_ROLE $T_TARGET${T_HEAD:+ (head ${T_HEAD:0:12})}, budget ${T_BUDGET}s${T_NOTE:+ — $T_NOTE}"
  if is_dry; then
    INCOGNITA_HEAD=$T_HEAD INCOGNITA_TASK_TIMEOUT=$T_BUDGET INCOGNITA_NOTE=$T_NOTE \
      bash "$INCOGNITA_SCRIPTS/agent.sh" "$T_ROLE" "$T_TARGET"
    return 0
  fi
  wait_for_quota || return 0
  [ "$(task_budget "$T_ROLE")" -gt 0 ] || return 0
  T_BUDGET=$(task_budget "$T_ROLE")
  rc=0
  counter_inc since-rotation >/dev/null
  case "$T_ROLE" in garden|bibliographer)
    counter_set since-rotation 0; printf '%s\n' "$T_ROLE" > "$INCOGNITA_STATE/last-rotation" ;;
  esac
  # In the background, then `wait`: a TERM reaches our trap at once, which stops agent.sh (and its unit).
  INCOGNITA_HEAD=$T_HEAD INCOGNITA_TASK_TIMEOUT=$T_BUDGET INCOGNITA_NOTE=$T_NOTE \
    bash "$INCOGNITA_SCRIPTS/agent.sh" "$T_ROLE" "$T_TARGET" &
  AGENT_PID=$!
  wait "$AGENT_PID" || rc=$?
  AGENT_PID=""
  case "$rc" in
    0) ;;
    3) return 3 ;;
    4) log "rate limited: the next pass waits for the reset" ;;
    *) log "agent.sh $T_ROLE $T_TARGET exited with $rc"; record_attempt "$T_ROLE" "$T_TARGET" fail "agent.sh exit $rc"
       record_event task "$T_ROLE" "$T_TARGET" "fail agent.sh exit $rc" ;;
  esac
  return 0
}

# ---------------------------------------------------------------- main loop
backoff=60 pass=0
while :; do
  if [ "$DEADLINE" != 0 ] && [ "$(remaining)" -le 0 ]; then
    log "== deadline reached: loop ends"; record_event stop - - "deadline"; exit 0
  fi
  pass=$(( pass + 1 ))
  rc=0; one_pass || rc=$?
  is_dry && { log "dry run: one pass done (rc $rc)"; exit 0; }
  case "$rc" in
    0) backoff=60 ;;
    3) log "== Claude is logged out: the loop stops"; record_event stop - - "claude logged out"; exit 3 ;;
    10) log "== nothing to do: sleeping $(( INCOGNITA_IDLE_SLEEP / 60 )) min"; set_activity "idle"
        record_event idle - - "${INCOGNITA_IDLE_SLEEP}s"; sleep_bounded "$INCOGNITA_IDLE_SLEEP" ;;
    11) log "GitHub or git unknown: retrying in ${backoff}s"; set_activity "backoff"
        sleep_bounded "$backoff"; backoff=$(( backoff * 2 )); [ "$backoff" -gt 1200 ] && backoff=1200 ;;
    *) sleep_bounded 60 ;;
  esac
done
