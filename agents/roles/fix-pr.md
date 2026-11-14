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
   `Statements.lean`, `Exploration.lean`, take the sorted union of the import lines.
   `git rebase --continue`; if the conflict cannot be resolved, `git rebase --abort` and say so.
2. **Failed build**: find the first error in `ci-log.txt`, fix it, and rerun the CI command that
   failed.
3. **Review**: address every defect of the latest `request_changes` review, most important first.
   If a defect is wrong, do not obey it: explain why in the summary, with the argument.
4. **Repair of `main`**: the smallest change that makes CI green. If the failure comes from a
   dependency, the toolchain or a human-owned file, change nothing and write an `Ask-owner:` line.
5. **Statements pull request** (answering `review-statements`): you may edit the statement files
   this pull request adds (they are not on `main` yet), then run `lake exe audit --refresh-new-locks`
   (it rewrites the locks this pull request added, deletes those that match no statement any more,
   and never touches a lock of `main`), `git add -A Statements/`, and `lake exe audit --check`.
   Never write, edit or delete a lock by hand, and never touch a file under `Statements/` that is on
   `main`.
6. **Incomplete draft** (labelled `incomplete`): an earlier session of the role that opened the pull
   request stopped before the end. Continue its work as `agents/roles/<that role>.md` says, from its
   commits and its description, within the same purpose.
7. **Checks**, once, at the end: the CI commands of AGENTS.md §6.7 for the libraries you touched.

Commit each fix with a message naming the defect it addresses. Summary (AGENTS.md §1): Results (what
the pull request now contains), Frozen statements, Sources read, Not done (each defect: fixed or
disputed).

## Do not

Change the pull request's purpose; weaken a statement or a theorem to make something compile; delete
a theorem; use `sorry` outside `Exploration/`; touch human-owned paths.
