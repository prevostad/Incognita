# Tau Ceti's review rubrics, for the Lean pull requests

The owner's decision (2026-11-17): the Lean pull requests of Incognita are reviewed like those of
LMLExplore, by the **11 rubrics of Tau Ceti**, each judged by an independent review session, and
merged only when every rubric approves the current head (in addition to everything already
required: CI, the Incognita review, the merge categories, the path whitelist).

## Source and license

`tauceti/` is vendored **verbatim** (not one byte changed; checked by the blob hashes of git) from:

- `TauCetiProject/TauCetiReview`, directory `rubrics/`, commit
  `9f6561e2c2b86813b779de548cc49b6434fd8e58` (2026-11-18): `README.md`, `_common.md`, the eleven
  rubrics `correctness.md`, `reuse.md`, `scope.md`, `attribution.md`, `api-design.md`,
  `generality.md`, `placement.md`, `naming.md`, `documentation.md`, `proof-quality.md`,
  `quality-pass.md`, and `references/naming-conventions.md` (Mathlib's naming conventions with
  Tau Ceti's addendum, given to the rubric `naming` after it, as Tau Ceti does);
- `TauCetiProject/TauCeti`, `.github/pull_request_template.md`, commit
  `1d80832a1f213349a4574f1e86313f3305a0a71e` (2026-11-15), as `tauceti/pull_request_template.md`:
  the `Quality pass:` block that the authors fill in and the rubric `quality-pass` checks.

Both repositories are released under the Apache License 2.0; its text is `tauceti/LICENSE` (copied
from TauCetiReview; neither repository has a NOTICE file). Copyright of these files remains with
their authors, the Tau Ceti project. To refresh them: fetch the same paths at a new commit, replace
`tauceti/`, and update the commits above; never edit a file of `tauceti/` by hand.

## Incognita's adaptations

Only in [`_incognita.md`](_incognita.md), read by every rubric session right after Tau Ceti's
`_common.md`: what the code, the dependencies and the "roadmap" are here (the paper, its
`blueprint.md`, its frozen statements and its roadmap item), the rules of AGENTS.md section 6 that
win over Tau Ceti's (frozen statements, no theorem lost, proof pull requests add only lemmas and
theorems, forbidden keywords, names), the quality pass in the description's section
`## Quality pass`, and the verdict format the loop parses (`Verdict: approve|request_changes|block`
on the first line, no JSON, no marker).

## How the loop runs them (scripts/lib.sh, scripts/loop.sh, scripts/agent.sh)

- **Lean pull requests**: role `prove` or `formalize-statements`, or any other pull request
  (`garden`, `fix-pr`, …) whose diff changes a `.lean` file under `Incognita/` or `Statements/`
  (`is_lean_pr`). Papers, literature, roadmap proposals, candidate directions: unchanged.
- **One role per rubric**, `rubric-<name>` (for example `rubric-api-design`), a review role: the
  reviewers' model (`INCOGNITA_MODEL_REVIEWER`) and budget (`INCOGNITA_TIMEOUT_REVIEW`, `_MIN_REVIEW`),
  allowed near the weekly cap, resumable from a partial report; per-rubric overrides
  `INCOGNITA_MODEL_RUBRIC_<NAME>`, `INCOGNITA_TIMEOUT_RUBRIC_<NAME>`. Its prompt, from `main`:
  `tauceti/_common.md`, `_incognita.md`, a pointer to the pull request (`.agents/`), then the
  rubric (and for `naming` the naming conventions). Its tools: read-only (no Lean, no shell but
  `ls`, `grep`, `wc` and `git diff|log|show`; Tau Ceti's reviewers have no shell), `Write` for its
  report so far.
- **Order, on one head**: first the Incognita review (`review-pr`, or `review-statements` for a
  statements pull request: frozen types, locks, markers, paths, back-translation), then the
  rubrics of `INCOGNITA_RUBRICS` (default: all 11) in Tau Ceti's order: `correctness`, `reuse`,
  `scope`, `attribution` (the angles that may block), `api-design`, `generality`, `placement`,
  `naming`, `documentation`, `proof-quality`, `quality-pass`. A `request_changes` does not stop the
  round: every rubric judges the head, then one `fix-pr` round answers every report.
- **Statuses**: each rubric posts its report as a comment with the loop's trusted marker (kind
  `rubric-<name>`) and sets the status `Incognita rubric/<name>` on the head (`role=rubric-<name>
  verdict=<v> pr=<n>`; success only for `approve`). A verdict counts only on the head it was given
  on: after a fix commit the rubrics run again, in proportion to the change (owner, 2026-11-19;
  `INCOGNITA_RUBRIC_CARRY`, default `proportionate`, `off` to rerun all). The loop compares the new
  head with the last head the rubrics judged, on the pull request's own `.lean` files, comments
  removed (`change_class` in `scripts/lib.sh`):
  - **code changed**: every rubric judges the new head;
  - **only comments** (docstrings, `--` and `/- -/` blocks): `documentation`, `attribution` and
    `quality-pass` judge it again; the others keep an approval they gave (status
    `... carried-from=<h0> change=comments`);
  - **no `.lean` file changed** (paper, blueprint, notes): only `quality-pass` judges it again.
  A verdict other than `approve` is never carried: that rubric always judges the new head. The
  Incognita review (review-pr, review-statements) always judges it. A mechanical rebase that leaves
  the pull request's change identical, blob for blob, copies every status, as it copies the
  Incognita review.
- **block**: the round stops on that head (the rubrics after it do not run). As in Tau Ceti, the
  author answers it: one `fix-pr` round, told which rubric blocked (it fixes the problem within the
  pull request's purpose, or contests the finding with its reasons, or asks the owner). A block on
  `INCOGNITA_BLOCK_LIMIT` (2) heads of the same pull request sends it to the owner (`needs-human`):
  an agent could not settle it. `INCOGNITA_FIX_LIMIT` still bounds the fix rounds.
- **Merge**: `try_merge` requires, for a Lean pull request, `approve` from every rubric of
  `INCOGNITA_RUBRICS` on the current head, besides the Incognita review and the other conditions;
  the merge commit records them in its trailer `Incognita-Reviews` (`rubrics=<name>:<verdict>,…`).
- **Quality pass**: `prove`, `formalize-statements`, and `garden` or `fix-pr` when they change
  Lean, write Tau Ceti's `Quality pass:` block in the section `## Quality pass` of their summary,
  which is the pull request's description; a fix round's section replaces the description's.
