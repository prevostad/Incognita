# Contributing (humans)

Humans do three things here: approve programmes, calibrate and audit the validation of questions,
and approve changes to human-owned paths (see [AGENTS.md](AGENTS.md)). Everything else is done by
agents.

## Programmes

A programme is a directory `programmes/<Name>/` with a `PROGRAMME.md` following
[programmes/README.md](programmes/README.md). It is written by a human, possibly with AI help (say
so), and becomes `approved` when its owner sets the status. Approving a programme is the main
human decision: it fixes what agents may spend their time on.

## Validating questions

Agents propose questions; the long-term goal is that a question reviewer agent validates them
alone. The project gets there in phases:

1. **Bootstrap** (now): the owner writes the first programme. Agents may survey the literature,
   build the catalogue, explore and propose questions.
2. **Calibration**: for each proposed question, the question reviewer agent records its verdict
   and reasons in the question file *before* the owner decides; the owner then decides, and the
   agreement is tracked in `programmes/<Name>/questions/README.md`. The owner's decision counts.
3. **Delegation**: once the reviewer agrees with the owner on almost every question, it validates
   alone. The owner reads a random sample of accepted questions from time to time, and tightens
   the programme's criteria when a bad one slipped through.

## Merging a pull request

1. Open the pull request on GitHub. Its description starts with the agent's summary: the results in
   mathematical form, with their Lean names.
2. For a PDF of the same summary with the Lean statements of the pull request: tab **Checks** →
   run **PR summary** → **Summary** → artifact `pr-summary` (a zip with the PDF).
3. Read the automated review (a comment starting with `Verdict:`). Its verdict is also the check
   **Incognita review**, required by the ruleset of `main` together with "Build and check": GitHub's
   merge button stays grey until the reviewer has approved the last commit. On your own pull
   requests (branches not starting with `agent/`), a workflow marks this check green: you are the
   reviewer.
4. **Merge pull request** → **Confirm merge** (or **Squash and merge**). If something is wrong,
   write a comment and close the pull request, or leave it open for the agent to fix.
5. Pull requests labelled **needs-human** are those the agents gave up on: a `block` verdict, or three
   fix rounds without success. Decide: fix, close, or remove the label to give the agents another try.

Automatic merging can be enabled by category (`INCOGNITA_AUTOMERGE`, see agents/README.md) once the
reviews have proved reliable; frozen statements and human-owned paths always go through a human.

## Branch protection and accounts

`main` is protected by a ruleset: no force push, no deletion, changes through pull requests only,
and the CI job "Build and check" must pass. Human-owned paths are listed in `.github/CODEOWNERS`.

While agents push with the owner's GitHub account, GitHub cannot tell an agent from the owner: a
pull request cannot be approved by its own author, so required approvals stay at 0 and the owner
merges by hand. With a separate account for the agents, the ruleset can require one approval and
code-owner review, so that nothing reaches `main` without the owner.

## Reviewing a programme

| Aspect | Question |
|---|---|
| Interest | Is this research we want, at the right generality? |
| Conventions | Are the setting and the conventions pinned well enough for questions to be unambiguous? |
| Known results | Is the state of the art correct, with the status of each result (published, Lean, paper)? |
| Criteria | Would the validation criteria let a reviewer reject uninteresting or ill-posed questions? |

## Attribution

Say which models helped write a programme or a review, and mark AI-assisted review comments with
:robot:. Do not post text you have not read carefully yourself.
