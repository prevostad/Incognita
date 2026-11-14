# Contributing (the owner and other humans)

Agents do the daily work: they write papers, referee them, formalise and prove, check the
literature and garden (see [AGENTS.md](AGENTS.md)), and even propose what to research next. The
owner is not a bottleneck for that work. He takes the rare, high-leverage decisions, and keeps a
veto on everything after the fact. This file lists his duties, about ten minutes a day plus an
occasional longer session.

## 1. Approve roadmaps

A roadmap ([roadmaps/README.md](roadmaps/README.md)) fixes what agents spend their time on: it is
the owner's main decision. To approve one, the owner opens a pull request that sets its status to
`approved` in `ROADMAP.md` (and, if needed, fixes its conventions, definitions, directions and
acceptance criteria), and merges it himself. Agents never edit roadmaps; they ask (`Ask-owner:`)
when a direction seems answered, ill-posed or worth reframing. To stop work in a roadmap, set it to
`paused` or `closed`; to stop work on one item, mark it `on hold` or `closed`.

What to check before approving:

| Aspect | Question |
|---|---|
| Interest | Is this research we want, at the right generality? |
| Conventions and definitions | Are the setting, the conventions and the planned Lean objects pinned well enough for papers to be unambiguous? |
| Known results | Is the state of the art correct, with the status of each result (published, Lean, paper)? |
| Criteria | Would the acceptance criteria let a referee reject uninteresting or ill-posed papers? |

### Proposals of agents: veto or approve

Agents propose extensions of approved roadmaps and new roadmaps (`propose-roadmap`, AGENTS.md
§4.2), reviewed by `review-roadmap`. The night report lists them under "Decisions waiting for the
owner":

- **inside an existing domain** (the domain of an approved roadmap): approved and merged by the
  loop after **2 nights** unless you veto it: comment `veto: <reason>` on the pull request (or add
  the label `veto`). Comment `approve` to approve it at once. The approval is a scripted commit that
  records the dates in the status line;
- **a new domain**: nothing happens until you comment `approve` (or merge it yourself).

Your latest comment starting with `veto` or `approve` wins; a veto stands until you comment
`approve` (or remove the label `veto`), and an `approve` written before the agent's last fix round
does not count (approve again what you have read).

A new roadmap comes with a KNOWN.md marked `Reviewed by owner: no`: no paper is written there until
you complete it and set the date (section 2). The directions of an approved extension are open at
once. To stop the proposals, set `INCOGNITA_PROPOSE_EVERY=0` and close the proposal pull requests;
to retract an approved one, mark its directions `closed` or revert it.

## 2. Review KNOWN.md once per roadmap

`KNOWN.md` tells agents what the owner already knows: results (with algorithms given by their
formula), negative results, the owner's dead ends, conjectures, uninteresting directions. **No paper
is written in a roadmap until the first line of its KNOWN.md reads `Reviewed by owner: <date>`.**
The owner fills it (for BatchedBandits, from the draft Claude wrote from his notes, kept outside the
repository), flags as `private` what agents must neither re-derive nor work on, sets the first line,
and merges the pull request himself. He reviews it again when `Ask-owner:` questions accumulate.

The repository is public: an entry written in KNOWN.md is published, even when flagged `private`.
An unpublished result the owner does not want to publish stays out of the repository; it can be
given to agents in a private file outside the repository: put the entries in
`<dir>/<Roadmap>.md` on the server and launch the night with `INCOGNITA_PRIVATE_KNOWN=<dir>`; each
session of that roadmap then gets them as `.agents/known-private.md` (listed in its task). Agents
never quote private entries, but anything a session reads may leak into a public pull request:
give them only what you accept to see paraphrased.

## 3. Read the night report, veto, answer questions

- **Night report** (pinned issue "Night reports", about ten minutes): (1) decisions waiting for the
  owner (roadmap pull requests, `Ask-owner:` questions, `needs-human` pull requests); (2) papers
  accepted (abstract, referees' one-line verdicts, PDF link); (3) statements frozen (Lean,
  back-translation, modelling choices); (4) results verified; (5) papers rejected and why; (6)
  machine statistics.
- **Veto**, by a comment on the report: `veto P003: <reason>`. A veto of a paper becomes
  `papers/<P>/withdrawn.md` (the owner's file); a veto of a merged pull request becomes its revert.
  In this version, Claude applies vetoes and answers when the owner asks it to in a session. A
  roadmap proposal is vetoed directly on its pull request (section 1).
- **Certification** (night report, section "Certification of the library"; AGENTS.md §9): the level
  of every paper (1 accepted, 2 Lean-verified, 3 re-verified), capped by its dependencies, with the
  badges "used by N" and "audited by a human". To give the badge "audited by a human", add a line
  `- <your name>, <YYYY-MM-DD>, v<version>: <what you checked>` to `papers/<P>/human-audits.md` (your
  file only: agents may not write it).
- **Questions**: `Ask-owner:` lines of agents are copied to the pinned issue "Questions for the
  owner"; answer by a comment (`A2: <answer>`), then update the roadmap or KNOWN.md if needed.

## 4. Merge what only the owner may merge

The loop merges automatically, one pull request per pass, only these categories: papers accepted by
both referees (with their candidate directions), proofs (lemmas and theorems only), literature,
exploration, candidate directions, and roadmap proposals after their scripted approval (section 1).
Everything else waits for the owner:

- roadmaps written by humans, roadmap proposals in a new domain, and KNOWN.md;
- statements pull requests, during the first nights (a wrong frozen statement can only be fixed by a
  non-additive change), then automatically once the owner enables it;
- any non-additive change under `Statements/` (a removed or modified file or lock), and dependency
  bumps (LMLExplore, Mathlib), which re-lock the statements and list the affected ones. The
  placeholder `Statements/Basic.lean` (from version 1) is exempted by the audit
  (`legacyExempt` in `scripts/Audit.lean`); the owner deletes it, with that exemption and its import
  in `Statements.lean`, in one admin-bypass pull request, for example with the first frozen
  statements;
- proof pull requests that add an erratum or a statement correction (`papers/<P>/errata.md`,
  `statement-corrections.md`: the paper becomes disputed or gets corrected statements), or that add
  a definition;
- human-owned paths: `README.md`, `AGENTS.md`, `CLAUDE.md`, `CONTRIBUTING.md`, `agents/`,
  `templates/`, `docs/`, `scripts/`, `.github/`, `lakefile.toml`, `lean-toolchain`,
  `lake-manifest.json`, `papers/*/withdrawn.md`, `papers/*/human-audits.md` (listed in
  `.github/CODEOWNERS`);
- reopening a paper closed with the label `rejected`.

**Reading a pull request.** Its description is the agent's summary (results in mathematics, with
their Lean names or paper labels). Papers: the PDF is in the artifact `papers-pdf` of the "Papers"
run (tab Checks; its check "Compile papers" must be green, as "Build and check", before the loop
merges a paper), and the referee reports are comments starting with `Verdict:`. Statements: read
the back-translations in `papers/<P>/blueprint.md` and the `review-statements` report.

**Admin bypass.** CI fails, by design, on every non-additive change under `Statements/`. The
ruleset of `main` lets the repository admin bypass its rules for pull requests ("pull requests
only" bypass). For such a pull request, after reading the diff and the audit's report, the owner
ticks "Merge without waiting for requirements to be met (bypass rules)" and merges. The loop never
uses `--admin` or a bypass.

## 5. Labels

| Label | Meaning | Owner's action |
|---|---|---|
| `rejected` | a paper closed after a fatal defect or two revisions without acceptance | reopen it if the referees were wrong |
| `incomplete` | a draft pull request of an agent that ran out of time; its work is kept | none: agents finish it |
| `needs-human` | a non-paper pull request the agents gave up on | fix, close, or remove the label to retry |
| `veto` | set by the owner on a roadmap proposal: it is never approved | remove it to let the veto window run again |

Labels for humans only (`scripts/pr_labels.py`, recomputed by the workflow "PR labels"): one state
label per open pull request (`awaiting-CI`, `ci-failed`, `awaiting-review`, `awaiting-author`,
`merge-conflict`, `ready-to-merge`, `veto-window` for a roadmap proposal in its veto window; none
with `needs-human`), `role:<role>` for agents' pull requests,
`fork` for pull requests from forks.

**Parked targets** are not labels: a role and target that failed `INCOGNITA_PARK_AFTER` (4) times in
all nights are skipped; the night report lists them, and deleting the file
`~/.incognita/state/parked/<role>_<target>` on the server makes the loop retry.

## 6. The Claude token, at every launch

The agents run with a long-lived token of the owner's subscription, which the owner does not want
kept on the server or in its snapshots. Before every night: `claude setup-token` (anywhere; it
prints `sk-ant-oat01-…`), then `sudo nano /etc/incognita/agent.env` and replace `REPLACE_ME` on the
line `CLAUDE_CODE_OAUTH_TOKEN=`. `scripts/night.sh` refuses to start without it, and puts
`REPLACE_ME` back at the end of every night (normal end, failed startup, Ctrl-C). After a night that
was killed (`kill -9`, reboot), or before a snapshot, run `bash scripts/night.sh --reset-token`.

## 7. Branch protection and accounts

`main` is protected by a ruleset: pull requests only, no force push, no deletion, required checks
"Build and check" and "Incognita review", 0 approvals. While the loop uses the owner's GitHub
account, GitHub cannot tell an agent from the owner; trust comes from the loop: it accepts only
verdicts it posted itself (hidden markers), binds each verdict to the reviewed commit, and runs
agents as a separate Unix user without GitHub credentials.

## 8. Decisions pending (as of 2026-11-14)

- Whether agent papers that extend the owner's unpublished results are public (priority,
  double-blind review).
- P000 of BatchedBandits: definitions written by agents, or a port of the owner's private Lean
  definitions.
- What of the KNOWN.md draft is published.

## Attribution

Say which models helped write a roadmap, a KNOWN.md or a review, and mark AI-assisted comments with
:robot:. Do not post text you have not read carefully yourself.
