# Running agents

**Status: written, not yet run.** The scripts below are a first version, to test on the server.

Each agent is one non-interactive Claude Code session (`claude -p`) with one role. The role prompts
are in [roles/](roles/); [AGENTS.md](../AGENTS.md) is the contract they all follow.

| Role | Script call | Writes | Model (default) |
|---|---|---|---|
| propose | `scripts/agent.sh propose <Programme>` | a new question file | author |
| review-question | `scripts/agent.sh review-question <question file>` | the verdict in the file, the frozen statement | reviewer |
| research | `scripts/agent.sh research <question file>` | Exploration/, library, question file | author |
| formalise | `scripts/agent.sh formalise <Programme>` | a known result, with its frozen statement | author |
| review-pr | `scripts/agent.sh review-pr <number>` | a review comment on the pull request | reviewer |
| garden | `scripts/agent.sh garden` | consolidation, catalogue | author |
| bibliographer | `scripts/agent.sh bibliographer` | `literature/`, novelty in the catalogue, Attribution sections | author |
| fix-pr | `scripts/agent.sh fix-pr <number>` | the branch of an agent's pull request (rebase, build, review findings), then a "Fix round" comment | author |
| check | `scripts/agent.sh check` | one independent check of a merged result, catalogue, equivalence proofs | reviewer |

`scripts/loop.sh [n]` runs `n` tasks (default 1), choosing each time the most useful one, in the order
of AGENTS.md: fix the agents' pull requests (changes requested, failed build, conflict with main),
review them, review proposed questions, audit the attribution of new results, propose a question if
a programme has fewer than `INCOGNITA_OPEN_TARGET` open questions and fewer than
`INCOGNITA_MAX_AWAITING` waiting for a decision; otherwise a rotation over six tasks (research
three times, on the least worked open question; check once; bibliographer once; formalise once;
formalise replaces research or check when there is nothing to research or check); gardening every
tenth task. A question with too many rounds without progress is parked. A pull request with a `block` verdict, or
after three fix rounds, is labelled `needs-human` and left alone.

## How a task runs

1. A fresh git worktree from `origin/main`, on a branch `agent/<role>-<timestamp>`, under
   `.agents/` (ignored by git).
2. `claude -p` runs in it with the role prompt, a restricted tool list (web search and page reading,
   but no shell network commands, no `git push`, no `gh`), and the model of the role. Writing roles
   end by writing `.agents/summary.md`: the results in mathematical form with their Lean names.
3. The script, not the agent, pushes the branch and opens the pull request, with the role and the
   model in its description. For `review-pr`, the script posts the agent's review as a comment.
4. CI builds and audits the pull request, and builds a PDF of its summary with its Lean statements
   (artifact `pr-summary` of the "PR summary" run). A human merges, unless automatic merging is
   enabled for the pull request's category: then `scripts/loop.sh` merges it once the build is green
   and the last review, on the last commit, is `Verdict: approve`. Frozen statements and human-owned
   paths are always merged by a human.

## Configuration (environment variables)

| Variable | Default | Meaning |
|---|---|---|
| `INCOGNITA_MODEL_AUTHOR` | `opus` | model of the writing roles |
| `INCOGNITA_MODEL_REVIEWER` | `sonnet` | model of the reviewing roles: a different model keeps reviews less correlated with the authors |
| `INCOGNITA_MAX_TURNS` | `200` | turn limit of one session |
| `INCOGNITA_EFFORT` | `high` | effort level of every session (`low`, `medium`, `high`, `xhigh`, `max`), as in the Tau Ceti worker |
| `INCOGNITA_PACE` | unset (the worker's default curve) | quota pacing curve, syntax of the Tau Ceti worker's `--pace`; `0:100` uses everything that remains, `off` disables pacing. Before each task, `scripts/loop.sh` reads the Claude usage with `tauceti status --json` and waits while a window is over pace |
| `INCOGNITA_OPEN_TARGET` | `5` | open questions wanted per approved programme: below it (counting the proposed ones), a new question is proposed before research and formalisation |
| `INCOGNITA_MAX_AWAITING` | `3` | at most this many questions waiting for a decision per programme (proposed, including proposals in open pull requests): it bounds the owner's work during calibration |
| `INCOGNITA_PARK_AFTER` | `5` | research rounds without progress after which a question is parked |
| `INCOGNITA_AUTOMERGE` | empty | categories merged automatically, comma-separated: `exploration`, `literature`, `questions`, `library`; empty: none |

## Before the first run

- `claude` and `gh` logged in on the server, `elan` installed, `scripts/build.sh Incognita` working.
- Check the flags of `claude -p` used in `scripts/agent.sh` against the installed version.
- Decide whether agents use the owner's GitHub account or a separate one (see CONTRIBUTING.md).
