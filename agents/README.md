# Running agents (operations)

**Status: v3, written and tested without Claude** (offline tests, sandbox tests on the server, dry
runs against GitHub); no real night has run on it yet.

Each agent task is one non-interactive Claude Code session (`claude -p`) with one role. The role
prompts are in [roles/](roles/) (`agents/roles/<role>.md`, read from `main`); [AGENTS.md](../AGENTS.md)
is the contract they all follow. This file is the operations part: how a task runs, the loop, the
settings, the setup and the launch.

| Role | Call (`scripts/agent.sh …`) | Writes | Model | Timeout |
|---|---|---|---|---|
| `write-paper` | `write-paper <Roadmap>` | a new `papers/P<nnn>-<slug>/` (number given in task.md): `paper.tex`, `refs.bib`, `META.toml`, `notebook/`; `literature/` | author | 90 min |
| `referee-scope` | `referee-scope <PR>` | report (comment) + status `Referee scope` | reviewer | 30 min |
| `referee-proofs` | `referee-proofs <PR>` | report (comment) + status `Referee proofs` | reviewer | 30 min |
| `revise` | `revise <PR>` (revision or repair of a paper PR) or `revise <Paper>` (disputed) | its paper's `paper.tex`, `refs.bib`, `META.toml`, `notebook/`, `errata.md` (`Revised in` lines); `literature/` | author | 90 min |
| `formalize-statements` | `formalize-statements <Paper>` | `Statements/P<nnn>/` (`.lean`, `.lock`; additions), `Statements.lean` (imports), `Incognita/`, `catalogue/definitions/`, the paper's `blueprint.md`, `errata.md`, `statement-corrections.md` | author | 90 min |
| `review-statements` | `review-statements <PR>` | report + status `Incognita review` | reviewer | 30 min |
| `prove` | `prove <Paper>` | `Incognita/`, `catalogue/results/P<nnn>-<name>.toml` (additions), the paper's `blueprint.md`, `formalisation.tex`, `errata.md`, `statement-corrections.md` | author | 90 min |
| `review-pr` | `review-pr <PR>` | report + status `Incognita review` | reviewer | 30 min |
| `fix-pr` | `fix-pr <PR>` or `fix-pr main` | the PR's branch, within the paths of the role that opened it; on main: `Incognita/`, `Incognita.lean`, `Statements.lean` (imports) | author | 90 min |
| `bibliographer` | `bibliographer` | `literature/`, `catalogue/attribution/`, papers' `refs.bib` | author | 90 min |
| `garden` | `garden` | `Incognita/` (theorems), `catalogue/relations.toml`, `catalogue/garden.md` | author | 90 min |

This column is a summary of the table of [AGENTS.md](../AGENTS.md) §2, which `role_allows` in
`scripts/lib.sh` follows line for line (`scripts/test-lib.sh` tests each line). Every writing role
but the bibliographer may also change `Exploration/` and `Exploration.lean`; nothing under
`papers/` is ever deleted. Nobody may change: dot-files or directories, `CLAUDE.md`, `AGENTS.md`,
`README.md`, `CONTRIBUTING.md` anywhere, `LICENSE`, `lakefile.*`, `lean-toolchain`,
`lake-manifest.json`, `templates/`, `agents/`, `docs/`, `scripts/`, `tests/`, `roadmaps/`,
`literature/notes/TEMPLATE.md`, `papers/*/withdrawn.md`, symbolic links, submodules, files over
1 MB, or a frozen statement (anything but an addition under `Statements/`).

## How a task runs (isolation, DECISIONS D11–D13)

The loop runs as the user `lean` in its own clone of `main` (`~/Incognita`, never edited by hand).
Sessions run as the user **`incognita-agent`**, which has no GitHub token, no SSH key, no sudo and no
access to `/home/lean`; this isolation is a **hard requirement**: the sessions' tools run LaTeX
(`latexmk`, `pdflatex`), Python (`python3`, numerical experiments) and Lean code written by the agents,
and `scripts/agent.sh` refuses to start without it.

1. **Inputs.** `scripts/agent.sh` fixes the head `H` of the PR (if any) when the task starts, writes the
   context files and a git bundle (main + `H`) in `/srv/incognita/in/<task>/`, and copies
   `scripts/agent-side.sh` there (so the agent cannot change it).
2. **Preparation**, as `incognita-agent` in the sandbox (`agent-side.sh prepare`): the agent's clone
   `~incognita-agent/work` gets a fresh `.git/config` and no hooks, fetches the bundle (`origin/main`,
   `origin/pr-head`), checks out the branch `incognita-task` (at `main`, or at `H` for PR tasks),
   removes untracked files except `.lake`, copies the context files to `.agents/`, and resets
   `~/.claude*` from `/srv/incognita/template`.
3. **Session**: `sudo systemd-run --quiet --wait --pipe --collect --uid=incognita-agent …
   -p EnvironmentFile=/etc/incognita/agent.env -p RuntimeMaxSec=<timeout> -p MemoryMax=6G
   -p NoNewPrivileges=yes -p PrivateTmp=yes -p ProtectSystem=strict
   -p ReadWritePaths=/home/incognita-agent -p InaccessiblePaths=/home/lean claude -p --output-format json
   --model … --effort … --max-turns … --permission-mode acceptEdits --allowedTools …`, the prompt
   (role file + a pointer to `.agents/task.md`) on stdin. The JSON result is read from the pipe
   (first 8 MB).
4. **Outputs**, as `incognita-agent` in the same sandbox with `/srv/incognita/out/<task>` writable
   (`agent-side.sh collect`): a git bundle of the new commits (not in `main` nor in `H`), and the first
   200 000 bytes of `.agents/summary.md`. The loop never runs git or lake in the agent's clone; it
   fetches the bundle into its own clone (`transfer.fsckObjects`), checks the whitelist on
   `git diff --raw -z --no-renames`, and pushes with its own token. Uncommitted work is dropped.
5. **Publication.** Writing roles: a new PR (branch `agent/<role>-<stamp>`, first line of the body
   ``Role: `<role>`. Target: `<target>`. Model: `<model>`.``, then the summary), or a push to the PR
   branch with `--force-with-lease` against `H` (`fix-pr`, `revise`) and a comment. A writing session
   that fails (timeout, `error_max_turns`…) with commits gives a **draft PR labelled `incomplete`**,
   continued later by `revise` (a paper PR) or `fix-pr` (any other). Reviewers: the report is posted as a comment whose first line is the
   hidden marker `<!-- incognita:<role>:<H> -->`, then the commit statuses are set on `H` with the
   description `role=<r> verdict=<v> pr=<n>`: `Incognita review` (review-pr, review-statements), or
   `Referee scope`, `Referee proofs` and the aggregate `Incognita review` (success only when both
   referees accept the same head). Lines `Ask-owner: …` of a report or of a writer's summary (even
   without a commit) go to the pinned issue "Questions for the owner".
6. **Sanitising.** Every agent text posted to GitHub: control and bidi characters removed, anything
   like a Claude token (`sk-ant-…`) redacted, `<!--` escaped, `@` followed by a zero-width space,
   closing keywords (`fixes #3`) neutralised, truncated at 60 000 characters. A diff containing a
   token is refused.

Context files in `.agents/` (listed in `task.md`; AGENTS.md §1 describes them to the agents):
`task.md` (role, target, PR and head, paper and its Lean prefix, or for `write-paper` the number of the
new paper, roadmap and KNOWN.md paths, deadline, situation — e.g. the errata entries to resolve —,
output rules), `open-prs.md` (one line per open PR with its Role/Target line: busy targets), and
depending on the task `pr.diff` (`git diff $(merge-base main H) H`), `pr.txt` (title and body),
`reports.md` (earlier trusted reports on the PR; for `write-paper` and `referee-scope`, also the
referee reports of the roadmap's rejected papers), `revision.diff` (for a reviewer: diff since its
last report), `ci-log.txt` (end of the failed logs of the workflows CI and Papers), `papers.md`
(write-paper: papers and directions of the roadmap on main, in open PRs, rejected),
`known-private.md` (the owner's private KNOWN entries of the roadmap, from
`$INCOGNITA_PRIVATE_KNOWN/<Roadmap>.md`, only if that variable is set). The prompt is the role file
verbatim (no substitution), followed by a pointer to `task.md`. Writing roles write
`.agents/summary.md`.

Paper verdicts: `Verdict: accept|major|reject`, computed by the referee from its defect table
(`reject` if any F, `major` if any G or L, `accept` if only P: an accepted paper keeps no error;
`minor` is read as `major`); other reviews: `Verdict: approve|request_changes|reject`. The runner
reads the first line starting with `Verdict: `. A paper is rejected (PR closed with the label
`rejected`) on a `reject`, or on a `major` after `INCOGNITA_REVISION_ROUNDS` (2) revision rounds (only
`revise` rounds answering a referee's `major` count; repairs of a paper PR are fix rounds, comment
kind `revise-fix`), or after `INCOGNITA_FIX_LIMIT` (3) fix rounds; a non-paper PR gets `needs-human`
on a `reject`, after `INCOGNITA_FIX_LIMIT` fix rounds, or after 3 reviews without a verdict.

## The loop (`scripts/loop.sh`, SPEC §3, D5, D13–D15)

Pass after pass until the deadline (`INCOGNITA_DEADLINE`), never exiting on its own otherwise:

1. fetch `main`; list the open PRs (`--limit 200`; a failed `gh` call is "unknown": back off, never
   "empty"); agents' PRs = same repository, branch `agent/*`, opened by the loop's account (`OWNER =
   gh api user`), with a Role line. Fork PRs are ignored everywhere.
2. `main` is red only if the push CI of its head failed after one automatic rerun: then no reviews and
   no merges, except a `fix-pr main` task and its PR.
3. **Merge** at most one PR per pass, via `PUT /pulls/N/merge` with `sha=H`: build green on `H` (the
   check "Build and check" of the workflow CI, and "Compile papers" of the workflow Papers for paper
   PRs or when it ran; `CI_JQ` in `scripts/lib.sh`); trusted
   statuses on `H` (created by OWNER, not by a workflow) accepting it; every changed path in an enabled
   category of `INCOGNITA_AUTOMERGE` (`papers` — both referees; `literature`; `proofs` — lemmas and
   theorems only, no `def`/`structure`/`instance`/…; `exploration`; `statements` is off for the first
   nights); the whitelist of the role checked again; for `.lean`/`.lock` changes, `main` an ancestor of
   `H`. Anything else waits for the owner (listed in the night report).
4. **Mechanical rebase** (no Claude) of conflicting agents' PRs and of ready Lean PRs behind main;
   conflicts on root import files are resolved by the sorted union of their import lines; any other
   conflict goes to `fix-pr`. Statuses are copied to the new head only if every changed path has the
   same blob.
5. **One agent task**, the first available after the filters (target not busy in an open PR, fewer
   than `INCOGNITA_MAX_FAILS` failures tonight for this role and target, not parked, enough time
   before the deadline), in the order of AGENTS.md §3: `fix-pr main` if main is red; repairs and
   revisions — `revise` for paper PRs (referees' `major`, failed build, failed rebase, incomplete
   draft), `fix-pr` for the others (changes requested, failed build, failed rebase, incomplete draft);
   reviews (`referee-scope`, then `referee-proofs`; `review-statements`; `review-pr`); every
   `INCOGNITA_ROTATION_EVERY` tasks a `garden` or `bibliographer` task; `prove` (frozen statements
   still open and not superseded, oldest paper first); `formalize-statements` (accepted papers without
   locks, or with errata entries revised but not resolved, or unresolved statement corrections);
   `revise` of disputed papers (errata entries neither revised nor resolved); `bibliographer` when an
   external paper lacks its source note or a verified internal paper has no
   `catalogue/attribution/<P>.md`; `write-paper` in approved roadmaps whose `KNOWN.md` starts with
   `Reviewed by owner: <date>`, with fewer than `INCOGNITA_PAPERS_IN_REVIEW` papers in review and fewer
   than `INCOGNITA_ACCEPTED_UNVERIFIED_MAX` accepted papers not verified; fallback: `write-paper` up to
   `INCOGNITA_PAPERS_MAX`, `garden`, `bibliographer`; else sleep `INCOGNITA_IDLE_SLEEP` and look again.
6. Quota: with `INCOGNITA_PACE=0:100` (the owner's rule) or `off`, no pacing; otherwise the Tau Ceti
   pacer of v1. A rate-limited session makes the loop wait until the reset; a logged-out session stops
   the night. All waits end at the deadline.

**Interface with the audit (assumption to keep in sync with `scripts/Audit.lean`):** `lake exe audit
--check` exits 0/1 (CI), and `lake exe audit --status` prints one line per frozen statement,
`<P> <name> open|proved|refuted`, where `<P>` starts with the paper's `P<nnn>`. The loop runs it only in
its own clone of `main` (trusted after merge), cached per commit, never on agents' content. A paper is
"verified" when it has lock files and every statement of its number is `proved`, except statements
superseded by a resolved entry; "disputed" when `papers/<P>/errata.md` has an entry `## E<k>` with
neither a `Revised in` nor a `Resolved by` line (formats: papers/README.md; parser: `entry_flags` in
`scripts/lib.sh`). Locks: `--new-locks` writes missing locks only; `--refresh-new-locks` (writing roles,
in their PR) rewrites only the locks absent from `origin/main`.

`scripts/night.sh` supervises one night: a lock (`flock`), startup checks (clone on main and clean,
disk, `gh`, sudo, agent user and token, a one-line Claude session in the sandbox, the pacer, the Tau
Ceti worker **not** running), the loop restarted if it dies (3 deaths in 10 min: 20 min pause), and at
the end the night report in `~/.incognita/logs/<night>-report.md`, also posted on the pinned issue
"Night reports" (decisions for the owner, papers accepted, statements frozen, results verified, papers
rejected, statistics).

State, outside the repository, in `~/.incognita/`: `state/nights/<night>/` (attempts per role and
target, `events.tsv` for the report), `state/lifetime/` (fix rounds per PR, failures per target),
`state/parked/` (targets parked after `INCOGNITA_PARK_AFTER` failures in all; delete the file to retry),
`state/audit/<sha>.txt`, `logs/<night>.log`, `heartbeat` (one line a minute: time and activity).

## Settings (environment variables)

| Variable | Default | Meaning |
|---|---|---|
| `INCOGNITA_DEADLINE` | (required by night.sh) | `HH:MM`, server time: no task starts if it cannot end before |
| `INCOGNITA_PACE` | unset | `0:100` (always, the owner's rule): no pacing; `off`; else a Tau Ceti pace curve |
| `INCOGNITA_MODEL_AUTHOR` / `_REVIEWER` | `opus` / `sonnet` | models; per role: `INCOGNITA_MODEL_<ROLE>` (e.g. `INCOGNITA_MODEL_REFEREE_PROOFS`) |
| `INCOGNITA_EFFORT`, `INCOGNITA_MAX_TURNS` | `high`, `200` | for every session |
| `INCOGNITA_TIMEOUT_REVIEW` / `_WRITE` | `1800` / `5400` s | per role: `INCOGNITA_TIMEOUT_<ROLE>` |
| `INCOGNITA_MIN_REVIEW` / `_MIN_WRITE` | `900` / `2400` s | a task starts only with this much time left |
| `INCOGNITA_AUTOMERGE` | `papers,literature,proofs,exploration` | merge categories; add `statements` later (D15); empty: none |
| `INCOGNITA_PAPERS_IN_REVIEW` / `_PAPERS_MAX` | `3` / `6` | papers in open PRs per roadmap (normal / fallback) |
| `INCOGNITA_ACCEPTED_UNVERIFIED_MAX` | `2` | accepted papers not verified per roadmap before `write-paper` stops (D5) |
| `INCOGNITA_MAX_FAILS` | `2` | failed attempts per role and target per night |
| `INCOGNITA_FIX_LIMIT`, `INCOGNITA_REVISION_ROUNDS` | `3`, `2` | then `needs-human` (or `rejected` for a paper) |
| `INCOGNITA_PARK_AFTER` | `4` | failures of a role on a target, all nights, before it is parked |
| `INCOGNITA_ROTATION_EVERY` | `6` | one `garden`/`bibliographer` task every n tasks |
| `INCOGNITA_IDLE_SLEEP` | `1200` s | sleep when nothing can be done |
| `INCOGNITA_DRY_RUN` | `0` | `1`: one pass, prints the task, changes nothing |
| `INCOGNITA_PRIVATE_KNOWN` | unset | a directory outside the repository with `<Roadmap>.md` files of private KNOWN entries, given to the sessions of that roadmap as `.agents/known-private.md` |
| `INCOGNITA_CHECK_LOGIN` | `1` | night.sh tries one tiny session at startup |
| `INCOGNITA_AGENT_MEMORY` | `6G` | `MemoryMax` of a session |
| `INCOGNITA_REPO`, `INCOGNITA_HOME`, `INCOGNITA_AGENT_USER`, `INCOGNITA_EXCHANGE`, `INCOGNITA_AGENT_ENV` | `~/Incognita`, `~/.incognita`, `incognita-agent`, `/srv/incognita`, `/etc/incognita/agent.env` | paths |

## Setup (once, on the server)

1. The loop's clone: `git clone https://github.com/prevostad/Incognita ~/Incognita`, built once
   (`bash scripts/build.sh Incognita`); `gh` logged in; `lean` has sudo without password.
2. `sudo bash scripts/server/setup-agent-user.sh` (idempotent): system packages (LaTeX, Python with
   numpy/scipy/matplotlib), the user `incognita-agent`, `/srv/incognita/{in,out,template}`, the token
   file, elan and the toolchain, Claude Code (native installer, same version as `lean`'s), an
   anonymous clone, a full copy of `.lake`, and a sandbox test. `--skip-lake` skips the 8 GB copy;
   `--check` only runs the sandbox test.
3. The token: run `claude setup-token` (a long-lived token of the owner's subscription), then
   `sudo nano /etc/incognita/agent.env` and replace `REPLACE_ME` (line
   `CLAUDE_CODE_OAUTH_TOKEN=sk-ant-…`). Root only (mode 600); never print, commit or copy it. Renew it
   when the night report says "Claude logged out".
4. Tests: `bash scripts/test-lib.sh` and `bash scripts/test-loop.sh` (offline),
   `INCOGNITA_REPO=<scratch clone of main> bash scripts/server/test-sandbox.sh` (sandbox, no Claude).

## Launching a night

In `tmux`, in `~/Incognita` on `main`, never at the same time as the Tau Ceti worker:

```
INCOGNITA_PACE=0:100 INCOGNITA_DEADLINE=02:45 bash scripts/night.sh
```

Dry run first (checks, then one pass that only prints): `INCOGNITA_DRY_RUN=1 INCOGNITA_DEADLINE=02:45
bash scripts/night.sh`. To follow: `tail -f ~/.incognita/logs/<date>.log`, `cat ~/.incognita/heartbeat`.
To stop early: Ctrl-C (the running session is stopped, the report written).
