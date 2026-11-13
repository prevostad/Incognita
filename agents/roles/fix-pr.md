You fix an open pull request of the Incognita repository: pull request #{TARGET}, written by an agent.
Read AGENTS.md. The working tree is the pull request's branch. The script has put in `.agents/`:
`pr.txt` (title and description), `reviews.md` (the review comments, latest last), `ci.txt` (the
status of the checks) and, if the build failed, `ci-log.txt` (the end of the failing log), and
`rebase.txt` if the branch must be rebased on `origin/main`.

Task: make the pull request mergeable, without changing its purpose.

1. If `rebase.txt` exists, rebase the branch on `origin/main` (`git rebase origin/main`), resolving
   conflicts in favour of `main` for everything the pull request did not mean to change.
2. If the build failed, find the cause in `ci-log.txt` and fix it; check with the same commands
   as CI (`scripts/check-build.sh Incognita --no-sorry`, `scripts/check-build.sh Statements`,
   `lake exe audit`).
3. Address every defect of the latest review whose first line is `Verdict: request_changes`, most
   important first. If you think a defect is wrong, do not obey it: explain why in the summary.
   You may read the web to check a claim.
4. Keep the rules of AGENTS.md: never weaken a frozen statement that is on `main`, never touch
   human-owned paths, cite only what was read.

Commit each fix with a message saying which defect it addresses. If the pull request cannot be
fixed without changing its purpose, change nothing and say so in the summary.
