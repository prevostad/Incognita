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

`scripts/loop.sh [n]` runs `n` tasks (default 1), choosing each time the most useful one, in the order
of AGENTS.md: review pull requests, review proposed questions, audit the attribution of new results,
research open questions, formalise known results, propose questions; a bibliographer task every fourth
task, gardening every tenth.

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
| `INCOGNITA_PACE` | unset (the worker's default curve) | quota pacing curve, syntax of the Tau Ceti worker's `--pace`; `0:100` uses everything that remains, `off` disables pacing. Before each task, `scripts/loop.sh` reads the Claude usage with `tauceti status --json` and waits while a window is over pace |
| `INCOGNITA_AUTOMERGE` | empty | categories merged automatically, comma-separated: `exploration`, `literature`, `questions`, `library`; empty: none |

## Before the first run

- `claude` and `gh` logged in on the server, `elan` installed, `scripts/build.sh Incognita` working.
- Check the flags of `claude -p` used in `scripts/agent.sh` against the installed version.
- Decide whether agents use the owner's GitHub account or a separate one (see CONTRIBUTING.md).
