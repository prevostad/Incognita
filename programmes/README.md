# Programmes

A programme says what research agents may do in one area. It is human-owned: written or adopted
by a human, approved by setting its status to `approved`. Agents never edit it.

| Programme | Status | Owner |
|---|---|---|
| [BatchedBandits](BatchedBandits/PROGRAMME.md) | draft | Adrien Prevost |

## What a programme contains

`programmes/<Name>/PROGRAMME.md`, with these sections:

1. **Header**: status (`draft`, `approved`, `paused`, `closed`), owner, date, arXiv class, AI
   assistance used.
2. **Motivation**: the question of the programme, in a few lines.
3. **Setting and pinned conventions**: objects, notation, information model, criterion, and the
   Lean conventions to follow. Decide conventions up front, or implementers will decide them badly.
4. **What is known**: published results, and unpublished ones with their status (Lean, paper).
5. **Open directions**: where questions are welcome. Not exhaustive.
6. **What would be an important result**, and what would not.
7. **Out of scope.**
8. **Lean prerequisites**: what exists in the dependencies, what must be built first.
9. **Criteria for validating a question**: what the question reviewer checks, specific to the area.

A programme is short (a few pages). Its questions live in `programmes/<Name>/questions/`.
