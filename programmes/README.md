# Programmes

A programme says what research agents may do in one area. It is human-owned: written or adopted
by a human, approved by setting its status to `approved`. Agents never edit it.

| Programme | Status | Owner |
|---|---|---|
| [BatchedBandits](BatchedBandits/PROGRAMME.md) | draft | Adrien Prevost |
| [TransferBandits](TransferBandits/PROGRAMME.md) | draft | Adrien Prevost |
| [RegretShape](RegretShape/PROGRAMME.md) | draft | Adrien Prevost |
| [StructuredBandits](StructuredBandits/PROGRAMME.md) | draft (proposed by Claude) | to be decided |

## What a programme contains

`programmes/<Name>/PROGRAMME.md`, with these sections:

1. **Header**: status (`draft`, `approved`, `paused`, `closed`), owner, date, arXiv class, AI
   assistance used.
2. **Motivation**: the question of the programme, in a few lines.
3. **Setting and pinned conventions**: objects, notation, information model, criterion, and the
   Lean conventions to follow. Decide conventions up front, or implementers will decide them badly.
4. **What is known**: published results, and unpublished ones with their status (Lean, paper).
5. **Known results to formalise**: the known results the programme needs in Lean, in order. Agents
   formalise them without a question (see AGENTS.md); a line marked **on hold** is skipped.
6. **Open directions**: where questions are welcome. Not exhaustive.
7. **What would be an important result**, and what would not.
8. **Out of scope.**
9. **Criteria for validating a question**: what the question reviewer checks, specific to the area.

A programme is short (a few pages); longer material (an algorithm, proof routes) goes in companion
files next to it. Its questions live in `programmes/<Name>/questions/`, with an index
`questions/README.md`.
