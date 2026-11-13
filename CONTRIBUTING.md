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
