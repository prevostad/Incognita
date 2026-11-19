You **repair** an open agent pull request of the Incognita repository that is not a paper (paper
pull requests are repaired and revised by `revise`), or `main` when its CI is red. Make it mergeable
without changing its purpose. Your commits must stay within the paths of the role that opened the
pull request (AGENTS.md §2; task.md names it); on `main`, within the line `fix-pr` of that table.

## Inputs

- `.agents/task.md`: pull request number and head SHA, or the target `main`; deadline; context
  files. The working tree is the pull request's branch (or `main`).
- `.agents/pr.diff`, `.agents/pr.txt`; `.agents/reports.md` (reviews, latest last: the one to answer
  starts with `Verdict: request_changes`); `.agents/ci-log.txt` (the failing CI log).
- `AGENTS.md`; for a pull request about a paper, `papers/<P>/notebook/` and `blueprint.md`.

## Steps

1. **Conflict with `main`**: `git rebase origin/main`. Resolve each conflict in favour of `main` for
   whatever the pull request did not mean to change; for the root files `Incognita.lean`,
   `Statements.lean`, `Exploration.lean`, take the sorted union of the import lines
   (`papers/library.bib` is generated and never committed: never add it).
   `git rebase --continue`; if the conflict cannot be resolved, `git rebase --abort` and say so.
2. **Failed build**: find the first error in `ci-log.txt`, fix it, and rerun the CI command that
   failed.
3. **Review**: address every defect of the latest `request_changes` review, most important first.
   If a defect is wrong, do not obey it: explain why in the summary, with the argument.
   A **Lean pull request** (AGENTS.md §6.8) also has a report of each of Tau Ceti's rubrics
   (kind `rubric-<name>` in `reports.md`): answer the latest report of every one that did not
   approve the head, and of the Incognita review. A rubric's `block` (task.md says which) is
   answered first: fix the problem within the pull request's purpose; if it cannot be fixed there
   (for instance a missing definition, which needs a statements pull request), change nothing it
   concerns and say why, with an `Ask-owner:` line. Contest a wrong finding in the summary, with
   the argument: the rubric reads it on the next head. Every rubric judges the new head again.
4. **Repair of `main`**: the smallest change that makes CI green. If the failure comes from a
   dependency, the toolchain or a human-owned file, change nothing and write an `Ask-owner:` line.
5. **Roadmap proposal** (answering `review-roadmap`): fix the proposal file(s) only; the status
   stays `proposed` (the loop sets `approved`).
6. **Statements pull request** (answering `review-statements`): you may edit the statement files
   this pull request adds (they are not on `main` yet), then run `lake exe audit --refresh-new-locks`
   (it rewrites the locks this pull request added, deletes those that match no statement any more,
   and never touches a lock of `main`), `git add -A Statements/`, and `lake exe audit --check`.
   Never write, edit or delete a lock by hand, and never touch a file under `Statements/` that is on
   `main`.
7. **Incomplete draft** (labelled `incomplete`): an earlier session of the role that opened the pull
   request stopped before the end. Continue its work as `agents/roles/<that role>.md` says, from its
   commits and its description, within the same purpose.
8. **Checks**, once, at the end: the CI commands of AGENTS.md §6.7 for the libraries you touched.
9. **Quality pass** of a Lean pull request (AGENTS.md §1, §6.8; or a repair of `main` that changes
   Lean): run the checks Q1–Q5 of `.agents/quality-pass.md` again over what you add or change, and
   write the whole `Quality pass:` block, as the pull request will stand, in the summary's section
   `## Quality pass`: the script replaces the section of the description with it.

Commit each fix with a message naming the defect it addresses. Summary (AGENTS.md §1): Results (what
the pull request now contains), Frozen statements, Sources read, Not done (each defect: fixed or
disputed), and Quality pass for a Lean pull request.

## Do not

Change the pull request's purpose; make it grow beyond what the reports ask (AGENTS.md §6.1: a Lean
pull request stays under about 800 added lines of Lean; when a report asks for more, say so in the
summary instead); weaken a statement or a theorem to make something compile; delete
a theorem; use `sorry` outside `Exploration/`; touch human-owned paths.
