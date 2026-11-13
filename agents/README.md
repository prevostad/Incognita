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

`scripts/loop.sh [n]` runs `n` tasks (default 1), choosing each time the most useful one, in the order
of AGENTS.md: review pull requests, review proposed questions, research open questions, formalise
known results, propose questions; gardening every tenth task.

## How a task runs

1. A fresh git worktree from `origin/main`, on a branch `agent/<role>-<timestamp>`, under
   `.agents/` (ignored by git).
2. `claude -p` runs in it with the role prompt, a restricted tool list (no network commands, no
   `git push`, no `gh` for writing roles), and the model of the role.
3. The script, not the agent, pushes the branch and opens the pull request, with the role and the
   model in its description. For `review-pr`, the script posts the agent's review as a comment.
4. A human merges, for now. Merging after approved reviews and green CI can be automated once the
   reviews are calibrated.

## Configuration (environment variables)

| Variable | Default | Meaning |
|---|---|---|
| `INCOGNITA_MODEL_AUTHOR` | `opus` | model of the writing roles |
| `INCOGNITA_MODEL_REVIEWER` | `sonnet` | model of the reviewing roles: a different model keeps reviews less correlated with the authors |
| `INCOGNITA_MAX_TURNS` | `200` | turn limit of one session |

## Before the first run

- `claude` and `gh` logged in on the server, `elan` installed, `scripts/build.sh Incognita` working.
- Check the flags of `claude -p` used in `scripts/agent.sh` against the installed version.
- Decide whether agents use the owner's GitHub account or a separate one (see CONTRIBUTING.md).
