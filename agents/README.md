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
| `referee-scope` | `referee-scope <PR>` | report (comment) + status `Referee scope` | reviewer | 60 min |
| `referee-proofs` | `referee-proofs <PR>` | report (comment) + status `Referee proofs` | reviewer | 60 min |
| `revise` | `revise <PR>` (revision or repair of a paper PR) or `revise <Paper>` (disputed, or a dependency check) | its paper's `paper.tex`, `refs.bib`, `META.toml`, `notebook/`, `errata.md`, `dependency-checks.md`; `literature/` | author | 90 min |
| `formalize-statements` | `formalize-statements <Paper>` | `Statements/P<nnn>/` (`.lean`, `.lock`; additions), `Statements.lean` (imports), `Incognita/`, `catalogue/definitions/`, the paper's `blueprint.md`, `errata.md`, `statement-corrections.md` | author | 90 min |
| `review-statements` | `review-statements <PR>` | report + status `Incognita review` | reviewer | 30 min |
| `prove` | `prove <Paper>` | `Incognita/`, `catalogue/results/P<nnn>-<name>.toml` (additions), the paper's `blueprint.md`, `formalisation.tex`, `errata.md`, `statement-corrections.md` | author | 90 min |
| `review-pr` | `review-pr <PR>` | report + status `Incognita review` | reviewer | 30 min |
| `fix-pr` | `fix-pr <PR>` or `fix-pr main` | the PR's branch, within the paths of the role that opened it; on main: `Incognita/`, `Incognita.lean`, `Statements.lean` (imports) | author | 90 min |
| `bibliographer` | `bibliographer <Paper>` (a paper that waits for its source notes or its attribution audit) or `bibliographer -` | `literature/`, `catalogue/attribution/`, papers' `refs.bib` | author | 90 min |
| `garden` | `garden` | `Incognita/` (theorems), `catalogue/relations.toml`, `catalogue/garden.md` (rows appended); `Dropped` lines under existing entries of `roadmaps/*/directions.md`; entries of `papers/*/errata.md`, `statement-corrections.md` after a failed re-check | author | 90 min |
| `propose-roadmap` | `propose-roadmap <Roadmap>` (no free item left) or `propose-roadmap -` (periodic) | one new `roadmaps/<Name>/ROADMAP.md` + `KNOWN.md`, or one new `roadmaps/<Roadmap>/extensions/X<k>.md` (status `proposed`); `literature/` | author | 90 min |
| `review-roadmap` | `review-roadmap <PR>` | report + status `Incognita review` | reviewer | 30 min |

This column is a summary of the table of [AGENTS.md](../AGENTS.md) §2, which `role_allows` in
`scripts/lib.sh` follows line for line (`scripts/test-lib.sh` tests each line). Every writing role
but the bibliographer may also change `Exploration/` and `Exploration.lean`; nothing under
`papers/` is ever deleted. Nobody may change: dot-files or directories, `CLAUDE.md`, `AGENTS.md`,
`README.md`, `CONTRIBUTING.md` anywhere, `LICENSE`, `lakefile.*`, `lean-toolchain`,
`lake-manifest.json`, `templates/`, `agents/`, `docs/`, `scripts/`, `tests/`, `roadmaps/` (except a
proposal of `propose-roadmap`, checked whole by `scripts/certify.py proposal`, and `Dropped` lines of
`garden`), `literature/notes/TEMPLATE.md`, `papers/*/withdrawn.md`, `papers/*/human-audits.md`, the
generated `papers/library.bib`, `papers/*/certification.tex` and `catalogue/certification.md`,
symbolic links, submodules, files over 1 MB, a secret (Claude or GitHub token, private key), or a
frozen statement (anything but an addition under `Statements/`).

## How a task runs (isolation, DECISIONS D11–D13)

The loop runs as the user `lean` in its own clone of `main` (`~/Incognita`, never edited by hand).
Sessions run as the user **`incognita-agent`**, which has no GitHub token, no SSH key, no sudo and no
access to `/home/lean`; this isolation is a **hard requirement**: the sessions' tools run LaTeX
(`latexmk`, `pdflatex`), Python (`python3`, numerical experiments) and Lean code written by the agents,
and `scripts/agent.sh` refuses to start without it.

1. **Inputs.** `scripts/agent.sh` fixes the head `H` of the PR (if any) when the task starts, writes the
   context files and a git bundle (main + `H`) in `/srv/incognita/in/<task>/`, and copies
   `scripts/agent-side.sh` there (so the agent cannot change it).
2. **Preparation.** The loop restores the agent's `~/work/.lake` from its own (`rsync --delete`, as
   root, after checking that no directory was replaced by a link): nothing a session changed or
   planted there survives. Then, as `incognita-agent` in the sandbox (`agent-side.sh prepare`): the
   home keeps nothing of an earlier session but `~/work`, `~/.elan` and the old Claude Code install
   (`CLAUDE.md`, `~/.claude*`, `~/.config` with `~/.config/git`, the Python user site, shell files...
   are removed; `.bashrc`, `.profile`, `.bash_logout` come from `/etc/skel`, `~/.claude*` from
   `/srv/incognita/template`); the clone gets a fresh `.git/config` (fixed template), no hooks, no
   attributes or alternates; it fetches the bundle (`origin/main`, `origin/pr-head`), checks out
   the branch `incognita-task` (at `main`, or at `H` for PR tasks), removes untracked files except
   `.lake`, where every `CLAUDE*.md`, `AGENTS*.md` and `.claude/` is removed (those tracked by a
   dependency are hidden from git with `skip-worktree`, so that lake does not report local
   changes), and copies the context files to `.agents/`. The session's timeout is what is left of
   the time announced in task.md.
3. **Session**: `sudo systemd-run --quiet --wait --pipe --collect --uid=incognita-agent …
   -p EnvironmentFile=/etc/incognita/agent.env -p RuntimeMaxSec=<timeout> -p MemoryMax=6G
   -p NoNewPrivileges=yes -p PrivateTmp=yes -p ProtectSystem=strict
   -p ReadWritePaths=/home/incognita-agent -p ReadOnlyPaths=/home/incognita-agent/.elan
   -p InaccessiblePaths=/home/lean -E PATH=/opt/incognita/bin:~/.elan/bin:… -E PYTHONNOUSERSITE=1
   /opt/incognita/bin/claude -p --output-format json --model … --effort … --max-turns …
   --permission-mode acceptEdits --allowedTools …`, the prompt (role file + a pointer to
   `.agents/task.md`) on stdin. Claude Code is a root-owned copy outside the agent's home, and the
   toolchain is read-only: no session can change them for the next one (lake works with `~/.elan`
   read-only; toolchains are installed only by the loop, `sync_agent_lake`). The JSON result is
   read from the pipe (first 8 MB; stderr: first 2 MB).
4. **Outputs**, as `incognita-agent` in the same sandbox with `/srv/incognita/out/<task>` writable
   (`agent-side.sh collect`): the clone's `.git/config` rewritten again, no global or system git
   configuration (`GIT_CONFIG_GLOBAL=/dev/null`…), no hooks, attributes or file system monitor,
   and only plumbing that runs no filter (`rev-parse`, `rev-list`, `bundle`; never `git status`):
   a git bundle of the new commits (not in `main` nor in `H`), and the first 200 000 bytes of
   `.agents/summary.md` (a regular file). The loop never runs git or lake in the agent's clone and
   **never opens a file of the output directory as itself**: it reads each one as the agent user
   (`sudo -u incognita-agent head -c`, after `test -f` and `! test -L`: a regular file, not a link
   nor a FIFO; `out_read` in `scripts/lib.sh`; any entry there that is not a regular file makes it
   keep nothing: `out_irregular`), copies the bundle the same way (at most
   `INCOGNITA_BUNDLE_MAX` bytes), fetches it into its own clone (`transfer.fsckObjects`), checks
   the whitelist on `git diff --raw -z --no-renames`, and pushes with its own token. Uncommitted
   work is dropped.
5. **Publication.** The session's commits are **squashed into one commit** (`git commit-tree` with
   the tree of the agent's head and its author): on the PR head `H` for a round on a pull request
   (on its base when the round rebased the branch), on the merge base with `main` for a new pull
   request; what an intermediate commit added and a later one removed is never pushed. Writing
   roles: a new PR (branch `agent/<role>-<stamp>`, first line of the body
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
   like a secret redacted (a Claude token `sk-ant-…`, a GitHub token `gh[pousr]_…` or
   `github_pat_…`, a private key block), `<!--` escaped, `@` followed by a zero-width space,
   closing keywords (`fixes #3`) neutralised, truncated at 60 000 characters. A diff containing
   such a secret is refused. A comment whose POST failed is posted again only if no identical one
   exists (a timeout may have posted it).

Context files in `.agents/` (listed in `task.md`; AGENTS.md §1 describes them to the agents):
`task.md` (role, target, PR and head, paper and its Lean prefix, or for `write-paper` the number of the
new paper, roadmap and KNOWN.md paths, deadline, situation — e.g. the errata entries to resolve —,
output rules), `open-prs.md` (one line per open PR with its Role/Target line: busy targets), and
depending on the task `pr.diff` (`git diff $(merge-base main H) H`), `pr.txt` (title and body),
`reports.md` (earlier trusted reports on the PR; for `write-paper` and `referee-scope`, also the
referee reports of the roadmap's rejected papers; for `bibliographer <Paper>`, the scope reports on
the pull request that added the paper), `revision.diff` (for a reviewer: diff since its last
report; for a paper, its directory only), `owner-answers.md` (the owner's comments on the issue
"Questions for the owner", without the loop's marker, after the questions they follow), `ci-log.txt`
(end of the failed logs of the workflows CI and Papers), `papers.md`
(write-paper: papers and directions of the roadmap on main, in open PRs, rejected),
`known-private.md` (the owner's private KNOWN entries of the roadmap, from
`$INCOGNITA_PRIVATE_KNOWN/<Roadmap>.md`, only if that variable is set), `items.md` (write-paper,
propose-roadmap: the roadmap's items D, F, C and their state, `scripts/certify.py items`),
`roadmaps.md` (propose-roadmap: every roadmap, its status, domain, KNOWN.md, extensions, free
items, and the existing domains). The prompt is the role file
verbatim (no substitution), followed by a pointer to `task.md`. Writing roles write
`.agents/summary.md`.

Paper verdicts: `Verdict: accept|major|reject`, computed by the referee from its defect table
(`reject` if any F, `major` if any G or L, `accept` if only P: an accepted paper keeps no error;
`minor` is read as `major`); other reviews (`review-roadmap` included):
`Verdict: approve|request_changes|reject`. The runner
reads the first line starting with `Verdict: `. A paper is rejected (PR closed with the label
`rejected`) on a `reject` (a roadmap proposal too), or on a `major` after `INCOGNITA_REVISION_ROUNDS` (2) revision rounds (only
`revise` rounds answering a referee's `major` count; repairs of a paper PR are fix rounds, comment
kind `revise-fix`), or after `INCOGNITA_FIX_LIMIT` (3) fix rounds; a non-paper PR gets `needs-human`
on a `reject` or after `INCOGNITA_FIX_LIMIT` fix rounds, and any PR (papers included) after
`INCOGNITA_REVIEW_FAIL_LIMIT` (3) reviews without a verdict. When the owner reopens a rejected PR
(and removes the label), its rounds are counted again from the reopening, and a referee's `reject`
on its head is answered by one more revision.

## The loop (`scripts/loop.sh`, SPEC §3, D5, D13–D15)

Pass after pass until the deadline (`INCOGNITA_DEADLINE`), never exiting on its own otherwise:

1. fetch `main`; list the open PRs (`--limit 200`; a failed `gh` call is "unknown": back off, never
   "empty"); agents' PRs = same repository, branch `agent/*`, opened by the loop's account (`OWNER =
   gh api user`), with a Role line. Fork PRs are ignored everywhere.
2. `main` is red only if the push CI of its head failed after one automatic rerun: then no reviews and
   no merges, except a `fix-pr main` task and its PR.
3. **Merge** at most one PR per pass, via `PUT /pulls/N/merge` with `sha=H` and a commit message
   whose trailers (`Incognita-Role`, `Incognita-Reviews`, …) record the verdicts for
   `scripts/certify.py`: build green on `H` (the
   check "Build and check" of the workflow CI, and "Compile papers" of the workflow Papers for paper
   PRs or when it ran; `CI_JQ` in `scripts/lib.sh`); trusted
   statuses on `H` (created by OWNER, not by a workflow) accepting it; every changed path in an enabled
   category of `INCOGNITA_AUTOMERGE` (`papers` — both referees; `literature`; `proofs` — lemmas and
   theorems only, no `def`/`structure`/`instance`/…; `exploration`; `directions`; `statements` is off
   for the first nights); the whitelist of the role checked again; for `.lean`/`.lock` changes,
   `main` an ancestor of `H`. Anything else waits for the owner (listed in the night report).
   A pull request that waits for the owner is still kept rebased (the check "Lean changes on top of
   `main`" comes first).
   **Candidate directions** (AGENTS.md §4.1): an accepted paper is merged as reviewed; then a job
   (`state/candidates/<P>`) makes the loop open a pull request of its own (role `loop`, branch
   `agent/loop-directions-<stamp>`, body ``Role: `loop`. Target: `<P>`.``): one scripted commit on
   top of `main` appending the open questions the scope referee rated as candidates (all its
   reports on the paper's pull request, the latest rating of each question winning;
   `scripts/certify.py add-candidates`) to `roadmaps/<R>/directions.md`, with the status
   `Incognita loop` (`role=loop verdict=directions`). It is never reviewed, repaired nor rebased by
   an agent: it merges (category `directions`) once CI is green and `certify.py verify-scripted`
   accepts it whole; a conflicting one is closed and made again on the new `main`; one whose CI
   fails waits for the owner (`needs-human`).
4. **Roadmap proposals** (AGENTS.md §4.2): for a proposal that `review-roadmap` approved, the loop
   posts a veto window (`veto-window` comment: `Window: <night> to <night + INCOGNITA_VETO_NIGHTS>`)
   inside an existing domain, or asks the owner (`owner-approval`) for a new domain. A comment of the
   owner (without the loop's marker) starting with `veto`, or the label `veto`, stops it; one
   starting with `approve` approves it at once (the latest wins; an `approve` counts only after the
   latest `review-roadmap` report and the last fix round). Once approved, a scripted commit
   (`certify.py approve-roadmap`, status `Incognita loop` with `verdict=approved`) sets the status
   line to `approved` with the dates, and the merge follows (category `roadmap`, only this way),
   unless the owner's latest word is then a `veto` (read again at merge time).
5. **Mechanical rebase** (no Claude) of conflicting agents' PRs and of ready Lean PRs behind main;
   conflicts on root import files are resolved by the sorted union of their import lines; any other
   conflict goes to `fix-pr`. Statuses are copied to the new head only if the pull request changes
   the same thing (`diff_signature`): every changed path has the same blob, except the root import
   files (the same import lines added and removed) and `literature/` (the same lines added and
   removed), which other pull requests change too.
6. **One agent task**, the first available after the filters (target not busy in an open PR, fewer
   than `INCOGNITA_MAX_FAILS` failures tonight for this role and target, not parked, enough time
   before the deadline), in the order of AGENTS.md §3: `fix-pr main` if main is red; repairs and
   revisions — `revise` for paper PRs (referees' `major`, failed build, failed rebase, incomplete
   draft), `fix-pr` for the others (changes requested, failed build, failed rebase, incomplete draft);
   reviews (`referee-scope`, then `referee-proofs`; `review-statements`; `review-pr`); every
   `INCOGNITA_ROTATION_EVERY` tasks a `garden` (only once a proof marker `catalogue/results/*.toml`
   exists) or `bibliographer` task; `prove` (frozen statements still open and not superseded; the
   papers with the most dependants first, then the oldest: `certify.py dependants`);
   `formalize-statements` (accepted papers without locks, or with errata entries revised but not
   resolved, or unresolved statement corrections; at most one statements PR open per roadmap; the
   roadmap's `definitions` paper first, then a paper only once that paper and all its dependencies
   have locks on `main`); `revise` of disputed papers (errata entries neither revised nor
   resolved), then `revise` for dependency checks (`certify.py depchecks`: a dependency has a newer
   version than the one cited); `bibliographer <P>` for a paper that waits for it (an external paper
   without its source note, a verified internal paper without `catalogue/attribution/<P>.md`);
   `propose-roadmap <R>` for an approved roadmap whose KNOWN.md is
   reviewed and that has no free item (`certify.py items --free`, or a writer's summary line
   `No open item in <R>.` since its items last changed); `write-paper` in approved roadmaps whose
   `KNOWN.md` starts with `Reviewed by owner: <date>` and that have a free item, with fewer than
   `INCOGNITA_PAPERS_IN_REVIEW` papers in review (1 while the roadmap's `definitions` paper is not
   on `main`) and fewer than `INCOGNITA_ACCEPTED_UNVERIFIED_MAX` accepted papers not verified;
   `propose-roadmap -` every `INCOGNITA_PROPOSE_EVERY` nights if the owner sets it (0, the default:
   never; counted from the first night); fallback: `write-paper` up to `INCOGNITA_PAPERS_MAX`, `garden`,
   `bibliographer`; else sleep `INCOGNITA_IDLE_SLEEP` and look again. At most one proposal at a time;
   when `INCOGNITA_ROADMAPS_WAITING_MAX` approved roadmaps wait for the owner's review of their
   KNOWN.md, the task asks for an extension only.
7. Quota. **Weekly cap** (`INCOGNITA_WEEKLY_CAP`, set by `scripts/start-night.sh`): before every
   task, the loop reads the usage of the owner's subscription, the figures of claude.ai (Settings,
   Usage) (`usage_gate` in `scripts/lib.sh`; at most `INCOGNITA_USAGE_TTL` = 5 min old, always new
   after a task). Weekly usage at the cap or above: no task starts any more and the night stops
   (`loop.sh` exits 6; report, token removed). Within `INCOGNITA_CAP_MARGIN` (3) points of the cap:
   only short tasks start (the reviews, both referees, `bibliographer`, `garden`; never
   `write-paper`, `prove`, `revise`, `formalize-statements`, `fix-pr`, `propose-roadmap`), else the
   loop idles. Five-hour window exhausted: wait until its reset. Usage unreadable: with a cap, wait
   10 min and read again; without one, the task starts (logged). The usage is read from the endpoint
   of the Tau Ceti pacer (`https://api.anthropic.com/api/oauth/usage`, fields `limits[]` of kind
   `weekly_all` and `session`, else `seven_day` and `five_hour`, `utilization` in percent) with the
   agents' token, read through `sudo` and given to `curl` on its standard input (never in an argument,
   a file or the log). A token of `claude setup-token` has the scope `user:inference` only: if the
   endpoint refuses it, the same figures are read through `tauceti status --json` (lean's own Claude
   login, the one of the Tau Ceti worker; it must then be valid for the whole night: `claude auth
   login`). A dry run reads the usage but never waits. Pacing: with `INCOGNITA_PACE=0:100` (the
   owner's rule) or `off`, none; otherwise the Tau Ceti pacer of v1. A rate-limited session makes the
   loop wait until the reset; a logged-out session stops the night. All waits end at the deadline.

Exits of `scripts/loop.sh`: 0 deadline, 3 Claude logged out, 6 weekly cap reached, 1 fatal (night.sh
restarts it). Exits of `scripts/agent.sh`: 0 done (whatever the outcome), 3 Claude logged out (the night stops),
4 rate limited, 5 the infrastructure failed before the session (GitHub, git, the preparation: not
counted against the target; the loop backs off). A session that ended normally without a commit
is recorded as `skip no-commit`: it counts towards tonight's limit (`INCOGNITA_MAX_FAILS`), never
towards parking; only a paper or a pull request is ever parked. The audit build of `main` is not
started when less than an hour is left before the deadline.

**Interface with the audit (assumption to keep in sync with `scripts/Audit.lean`):** `lake exe audit
--check` exits 0/1 (CI), and `lake exe audit --status` prints one line per frozen statement,
`<P> <name> open|proved|refuted`, where `<P>` starts with the paper's `P<nnn>`. The loop runs it only in
its own clone of `main` (trusted after merge), cached per commit, never on agents' content. A paper is
"verified" when it has lock files and every statement of its number is `proved`, except statements
superseded by a resolved entry; "disputed" when `papers/<P>/errata.md` has an entry `## E<k>` with
neither a `Revised in` nor a `Resolved by` line (formats: papers/README.md; parser: `entry_flags` in
`scripts/lib.sh`). Locks: `--new-locks` writes missing locks only; `--refresh-new-locks` (writing roles,
in their PR) rewrites only the locks absent from `origin/main`.

`scripts/night.sh` supervises one night (started by `scripts/start-night.sh`, see "Launching a
night"): a lock (`flock`), startup checks (clone on main and clean, disk, `gh`, sudo, agent user and
token, a one-line Claude session in the sandbox, the pacer, the Tau Ceti worker **not** running, the
weekly cap a percentage, the weekly usage below it and readable when a cap is set), the loop
restarted if it dies (3 deaths in 10 min: 20 min pause; not after exit 0, 3 or 6), and at
the end the night report in `~/.incognita/logs/<night>-report.md`, also posted on the pinned issue
"Night reports". Its first lines: start and end, why the night stopped (deadline, weekly cap, Claude
logged out, signal, failed startup check), and the weekly usage at the start and at the end (and
how it was read), with the cap and the weekly reset. Then: (1) decisions for the owner (pull requests to merge, questions, roadmap proposals
with their veto windows, papers depending on a disputed paper, parked targets), (2) papers accepted, (3) statements
frozen, (4) results verified, (5) papers rejected, (6) roadmaps and directions (proposals approved
or vetoed, candidate directions added, exhausted roadmaps, dependency checks pending), (7) the
certification of the library (`scripts/certify.py report`, from the audit of main), (8) statistics.
Then, whatever the way out (but not after a dry run), it puts `REPLACE_ME` back in the token file
(see "The token").

State, outside the repository, in `~/.incognita/`: `state/nights/<night>/` (attempts per role and
target, `events.tsv` for the report), `state/lifetime/` (fix rounds per PR, failures per target),
`state/parked/` (targets parked after `INCOGNITA_PARK_AFTER` failures in all; delete the file to retry),
`state/audit/<sha>.txt`, `state/first-night` and `state/last-propose-night` (periodic proposals),
`state/candidates/<P>` (candidate directions to add for a merged paper: `<pr> <head> <P>`),
`state/marks/` (veto windows posted, roadmaps found exhausted…), `state/usage-last` (the latest
reading of the usage: time, `ok` or `err`, figures or reason; never the token), `logs/<night>.log`,
`heartbeat` (one line a minute: time and activity).

## Settings (environment variables)

| Variable | Default | Meaning |
|---|---|---|
| `INCOGNITA_DEADLINE` | (required by night.sh) | `HH:MM`, server time (UTC): no task starts if it cannot end before; start-night.sh sets it from the end in Paris time |
| `INCOGNITA_DEADLINE_EPOCH` | unset | the exact end (seconds since 1970), wins over `INCOGNITA_DEADLINE`; set by start-night.sh |
| `INCOGNITA_WEEKLY_CAP` | unset | weekly usage of the subscription (percent, as on claude.ai, Settings, Usage) at which no task starts and the night stops; empty: no cap; set by start-night.sh |
| `INCOGNITA_CAP_MARGIN` | `3` | within this many points of the cap, only short tasks (reviews, referees, bibliographer, garden) |
| `INCOGNITA_USAGE_TTL` | `300` s | how long a reading of the usage serves between two tasks (a new one after every task) |
| `INCOGNITA_USAGE_URL`, `INCOGNITA_TAUCETI_BIN`, `INCOGNITA_TAUCETI_CONF` | the endpoint of the Tau Ceti pacer, `tauceti` in PATH, LMLExplore's `tauceti.toml` | where the usage is read (tests point them at fakes) |
| `INCOGNITA_PACE` | unset | `0:100` (always, the owner's rule; start-night.sh sets it): no pacing; `off`; else a Tau Ceti pace curve |
| `INCOGNITA_MODEL_AUTHOR` / `_REVIEWER` | `opus` / `sonnet` | models; per role: `INCOGNITA_MODEL_<ROLE>` (e.g. `INCOGNITA_MODEL_REFEREE_PROOFS`) |
| `INCOGNITA_EFFORT`, `INCOGNITA_MAX_TURNS` | `high`, `200` | for every session |
| `INCOGNITA_TIMEOUT_REVIEW` / `_WRITE` | `1800` / `5400` s | per role: `INCOGNITA_TIMEOUT_<ROLE>`; `INCOGNITA_TIMEOUT_REFEREE_SCOPE` and `_REFEREE_PROOFS` are `3600` |
| `INCOGNITA_MIN_REVIEW` / `_MIN_WRITE` | `900` / `2400` s | a task starts only with this much time left |
| `INCOGNITA_AUTOMERGE` | `papers,literature,proofs,exploration,directions` | merge categories; add `statements` later (D15); empty: none. `roadmap` is never a category: proposals merge only after their scripted approval |
| `INCOGNITA_VETO_NIGHTS` | `2` | nights of veto window before a proposal inside an existing domain is approved |
| `INCOGNITA_PROPOSE_EVERY` | `0` | nights between two periodic roadmap proposals; `0` (the default for the first nights): never (proposals of exhausted roadmaps still happen) |
| `INCOGNITA_ROADMAPS_WAITING_MAX` | `2` | approved roadmaps whose KNOWN.md the owner has not reviewed, beyond which only extensions are proposed |
| `INCOGNITA_PAPERS_IN_REVIEW` / `_PAPERS_MAX` | `3` / `6` | papers in open PRs per roadmap (normal / fallback) |
| `INCOGNITA_ACCEPTED_UNVERIFIED_MAX` | `2` | accepted papers not verified per roadmap before `write-paper` stops (D5) |
| `INCOGNITA_MAX_FAILS` | `2` | failed attempts (and sessions without a commit) per role and target per night |
| `INCOGNITA_FIX_LIMIT`, `INCOGNITA_REVISION_ROUNDS` | `3`, `2` | then `needs-human` (or `rejected` for a paper) |
| `INCOGNITA_PARK_AFTER` | `4` | failures of a role on a paper or a pull request, all nights, before it is parked (listed in the night report); a roadmap or `-` is never parked |
| `INCOGNITA_ROTATION_EVERY` | `6` | one `garden`/`bibliographer` task every n tasks |
| `INCOGNITA_IDLE_SLEEP` | `1200` s | sleep when nothing can be done |
| `INCOGNITA_DRY_RUN` | `0` | `1`: one pass, prints the task, changes nothing |
| `INCOGNITA_PRIVATE_KNOWN` | unset | a directory outside the repository with `<Roadmap>.md` files of private KNOWN entries, given to the sessions of that roadmap as `.agents/known-private.md` |
| `INCOGNITA_CHECK_LOGIN` | `1` | night.sh tries one tiny session at startup |
| `INCOGNITA_AGENT_MEMORY` | `6G` | `MemoryMax` of a session |
| `INCOGNITA_AGENT_BIN` | `/opt/incognita/bin` | root-owned directory of the sessions' Claude Code |
| `INCOGNITA_BUNDLE_MAX` | `50000000` | bytes: the largest output bundle of a session |
| `INCOGNITA_REPO`, `INCOGNITA_HOME`, `INCOGNITA_AGENT_USER`, `INCOGNITA_EXCHANGE`, `INCOGNITA_AGENT_ENV` | `~/Incognita`, `~/.incognita`, `incognita-agent`, `/srv/incognita`, `/etc/incognita/agent.env` | paths |

## Setup (once, on the server)

1. The loop's clone: `git clone https://github.com/prevostad/Incognita ~/Incognita`, built once
   (`bash scripts/build.sh Incognita`); `gh` logged in; `lean` has sudo without password.
2. `sudo bash scripts/server/setup-agent-user.sh` (idempotent): system packages (LaTeX, Python with
   numpy/scipy/matplotlib), the user `incognita-agent`, `/srv/incognita/{in,out,template}`, the token
   file, elan and the toolchain, Claude Code in `/opt/incognita/bin` (root-owned; the binary of
   `lean`'s native install, same version), an anonymous clone, a full copy of `.lake`, and a
   sandbox test. `--skip-lake` skips the 8 GB copy;
   `--check` only runs the sandbox test.
3. The token: see "The token" below (a new one before every night).
4. Tests: `bash scripts/test-lib.sh`, `bash scripts/test-loop.sh` and `bash scripts/test-start.sh`
   (offline; the last one: the end of a night in Paris time across the changes of hour, the cap,
   the answers of the usage endpoint and of `tauceti status`, the decisions before a task, the env
   file, the capture of the token from a fake `claude setup-token`; its env file is a throwaway path),
   `INCOGNITA_REPO=<scratch clone of main> bash scripts/server/test-sandbox.sh` (sandbox, no Claude:
   isolation, the toolchain read-only, the cleaning of the home, and the attack of a clean filter
   plus a symbolic link in the output directory; its token file is a throwaway copy).

## The token (the owner's choice: never kept)

The sessions authenticate with a long-lived token of the owner's subscription in
`/etc/incognita/agent.env` (root only, mode 600; line `CLAUDE_CODE_OAUTH_TOKEN=sk-ant-…`), read by
`systemd-run` (`EnvironmentFile`), never visible to the sessions' files; the loop reads it only
through `sudo`, to read the weekly usage (`usage_fetch`: given to `curl` on its standard input). The
owner does not want it kept on the server or in its snapshots, so:

- **before every night**, a new one: `scripts/start-night.sh` runs `claude setup-token` (the owner
  follows the link and pastes the code, as with `claude auth login`), captures the token from its
  output on a pseudo-terminal (`scripts/capture-token.py`: what may be a token is held back, every
  token is shown as `sk-ant-oat01-[hidden]`, the command sees a terminal at least 200 columns wide
  so that the token is never broken across lines; the token reaches start-night.sh on a file
  descriptor), and writes it with `sudo install`/`sudo tee` (mode 600, root): it is never printed,
  logged or written elsewhere. If the capture fails, nothing is launched. By hand (or with
  `--keep-token`): `claude setup-token`, then `sudo nano /etc/incognita/agent.env` and replace
  `REPLACE_ME`. Such a token has the scope `user:inference` only (seen in its login link);
- `scripts/night.sh` refuses to start without it (startup check "a Claude token is in …", with
  these instructions in the log and the report); `start-night.sh` removes a token it created when
  the night does not start (refused, failed, Ctrl-C before the launch);
- at the end of every night (normal end, failed startup check, Ctrl-C, TERM), `night.sh` rewrites
  the file with the placeholder `REPLACE_ME` (`sudo install -m 600 -o root`), and logs it. A dry run
  leaves the file alone. After a night that could not clean up (`kill -9`, reboot), and before any
  snapshot: `bash scripts/night.sh --reset-token`.

The old tokens should also be revoked from the account's settings when the owner wants them gone.

## Launching a night

One command, as `lean` in `~/Incognita` on `main` (an SSH session; tmux is not needed, the night
gets its own), never at the same time as the Tau Ceti worker:

```
bash scripts/start-night.sh 02:45 88%     # until the next 02:45 in Paris; weekly cap 88 %
bash scripts/start-night.sh 6h45 88%      # for 6 h 45 min (also 8h, 6h45m, 45m; at most 24 h)
```

The end is a time `HH:MM` in Paris (its next occurrence: Monday 02:45 when launched on Sunday
evening; the changes of hour are handled, and a time that does not exist that night is refused) or a
duration; the server runs in UTC, `night.sh` gets both `INCOGNITA_DEADLINE` (UTC) and the exact
`INCOGNITA_DEADLINE_EPOCH`. The cap is the weekly figure of claude.ai (Settings, Usage): the night
stops at the end time or at the cap, whichever comes first. Steps:

1. it prints what it understood, e.g. `Fin prévue : lundi 16/11 à 02:45 (heure de Paris), dans 6 h
   47 ; plafond hebdomadaire : 88 %`, and asks for confirmation (`--yes`: no question). It refuses at
   once if a night runs (lock, or the tmux session `incognita` exists) or if the Tau Ceti worker runs;
2. it creates the token (see "The token"; `--keep-token` reuses the one in the env file);
3. it reads the weekly usage with it and prints it; at the cap or above, nothing starts. If the
   endpoint refuses the token and `tauceti status` cannot read it either, it asks whether to launch
   without a cap (`--yes`: no launch);
4. it starts `scripts/night.sh` in the tmux session `incognita` (with `INCOGNITA_PACE=0:100`, the
   deadline, `INCOGNITA_WEEKLY_CAP`, and the other `INCOGNITA_*` variables of its environment, e.g.
   `INCOGNITA_PRIVATE_KNOWN`), follows the startup checks for up to 3 minutes, and says whether the
   loop started (or which checks failed: the night then ended, report written, token removed).

To follow: `tmux attach -t incognita` (detach: Ctrl-b then d), `tail -f ~/.incognita/logs/<date>.log`,
`cat ~/.incognita/heartbeat`. To stop early: `bash scripts/start-night.sh --stop` (Ctrl-C in the
session: the running session is stopped, the report written, the token removed). Dry run (startup
checks, then one pass that only prints, in the foreground, no new token): `bash
scripts/start-night.sh 02:45 88% --dry-run`. By hand, without the launcher: in `tmux`, after putting
a new token in the env file, `INCOGNITA_PACE=0:100 INCOGNITA_DEADLINE=02:45 INCOGNITA_WEEKLY_CAP=88
bash scripts/night.sh` (`INCOGNITA_DEADLINE` is then server time).
