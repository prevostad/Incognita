# Roadmaps

A roadmap says what agents may research in one area. It is owned by a human: written or adopted by
the owner (possibly with AI help, said in its header), approved by the owner, never edited by agents.
Approving a roadmap is the owner's main decision: it fixes what agents spend their time on.

| Roadmap | Status | Owner | KNOWN.md |
|---|---|---|---|
| [BatchedBandits](BatchedBandits/ROADMAP.md) | approved | Adrien Prevost | not yet reviewed |
| [TransferBandits](TransferBandits/ROADMAP.md) | draft | Adrien Prevost | not yet reviewed |
| [RegretShape](RegretShape/ROADMAP.md) | draft | Adrien Prevost | not yet reviewed |
| [StructuredBandits](StructuredBandits/ROADMAP.md) | draft (proposed by Claude) | to be decided | not yet reviewed |

Papers are written in a roadmap only when its status is `approved` **and** its `KNOWN.md` starts
with `Reviewed by owner: <date>`.

## `ROADMAP.md`

1. **Header**: status (`draft`, `approved`, `paused`, `closed`), owner, dates, arXiv class, AI
   assistance used.
2. **Motivation**: the question of the roadmap, in a few lines.
3. **Pinned conventions**: objects, notation, information model, criterion. Decide conventions up
   front, or writers and formalisers will decide them badly.
4. **Definitions**: the core objects, each with its conventions and its **planned Lean name**, and
   the objects of the dependencies to reuse. The first paper of a roadmap is usually a
   `definitions` paper that formalises them.
5. **What is known**: published results, and unpublished ones with their status (`[Lean]`,
   `[paper]`). Unpublished results appear here only with the owner's consent.
6. **Known results to formalise** F0, F1, …, in order, each with its source; each becomes a paper
   (`external` for a published source, `internal` for an owner's result stated here).
7. **Open directions** D1, D2, …: where papers are welcome. Not exhaustive.
8. **What would be an important result**, and what would not.
9. **Out of scope.**
10. **Acceptance criteria for papers**: what the referees check, specific to the area, besides
    AGENTS.md.

Items (F or D) can be marked `pending owner decision`, `on hold` or `closed`: they are then not
open for papers. A roadmap is short; longer material (an algorithm, proof routes) goes in
appendices.

## `KNOWN.md`

What the owner already knows in the area, so that agents neither propose nor re-derive it:
results, negative results and counterexamples, algorithms already studied (by their formula),
the owner's dead ends, conjectures with a confidence, directions judged uninteresting. Entries are
numbered K1, K2, … and never renumbered; each has a status (`[Lean]`, `[paper]`, `[sketch]`,
`[belief]`), a one-line reason, and possibly the flag `private` (agents never re-derive, propose,
formalise or quote it). The owner writes it and reviews it once per roadmap (and again when
questions accumulate); its first line is `Reviewed by owner: <date>`, or `Reviewed by owner: no`
until then. Entries may also be kept outside the repository and given to agents in a private file
(see [CONTRIBUTING.md](../CONTRIBUTING.md)).

## Changing a roadmap

Only through a pull request merged by the owner. Agents who think a direction is answered,
ill-posed or should be reframed write an `Ask-owner:` line in their report; the owner answers on
the pinned issue "Questions for the owner" and updates the roadmap himself.
