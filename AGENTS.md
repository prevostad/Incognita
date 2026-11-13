# Working in Incognita

This is the contract for AI agents. Read [README.md](README.md) first, then the programme you work
in (`programmes/<Name>/PROGRAMME.md`) and, for a question, its file and its dead ends.

Incognita produces **new** mathematics. Lean checks proofs; it does not check that a statement
means what it should, that it is new, or that it matters. Most rules below exist to protect those
three things. When a rule slows you down, it is doing its job.

## What you may work on

Only inside an **approved** programme (status `approved` in its `PROGRAMME.md`). If no programme is
approved, you may only: survey the literature for a draft programme, build the catalogue of
existing results in the dependencies, and explore in `Exploration/`. Never write or modify a
`PROGRAMME.md`, and never validate a question you proposed.

Tasks, in order of usefulness:

1. fix or finish your own open pull requests;
2. review other pull requests (as an independent reviewer: see below);
3. validate proposed questions (as question reviewer: see below);
4. work on an `open` question: explore, prove, refute, or prove a justified variant;
5. formalise a known result (see below);
6. audit the attribution of merged results, check references (bibliographer only);
7. propose a question in an approved programme;
8. gardening (see below).

## Formalising known results

New results need old ones. A known result (published, or an unpublished result listed in a
programme with its status) is formalised when it is listed under "Known results to formalise" in an
approved programme, or when an `open` question needs it.

- Its frozen statement is written from the source, with the exact reference (paper, theorem or
  equation number) in its docstring, and reviewed for **fidelity to the source**, not for novelty.
  Differences of form (a `liminf` written with `∀ c < L, eventually`, existential constants...) are
  listed in the docstring.
- Before starting, check that it is not already in Mathlib, Tau Ceti, LML or LMLExplore at the pinned
  versions, and whether an LMLRoadmaps roadmap plans it: then follow the names and statement shapes it
  fixes, so that adopting the upstream version later is a deletion plus an import.
- Formalising an unpublished result is a verification. If the proof fails because the statement is
  false or the source's argument has a gap, report it in a question file (status `proposed`, with
  the counterexample or the gap), and never resolve it by weakening the statement silently.
- Its catalogue entry has `source = "<reference>"`.

## Spaces

- `Exploration/`: drafts. `sorry` is allowed. Nothing outside `Exploration/` may import it. Record
  what you learn in the question's file, not only in code.
- `Statements/`: one module per validated question or known result, holding its frozen statement
  with `sorry`, as `Incognita.Statements.<Programme>.<name>`. Created when a question is validated;
  **changed only by a pull request a human approves**. A frozen statement uses only definitions of
  the library and of the dependencies, never definitions made in `Statements/`.
- The proof of `Incognita.Statements.<Programme>.<name>` is the theorem
  `Incognita.<Programme>.<name>` of the library, with exactly the same type. `lake exe audit`
  checks this, and that the library uses no axiom beyond the three standard ones.
- `Incognita/`: the library. LMLExplore's standard applies in full: no `sorry`, no axioms beyond
  `propext`, `Classical.choice` and `Quot.sound` (so no `native_decide`), Mathlib's linters with
  warnings as errors, no `set_option`, the copyright header below, `module` files.

Every Lean file starts with:

```
/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module
```

## Life of a question

A question is a file `programmes/<Name>/questions/Q<nnn>-<slug>.md`, made from
[templates/QUESTION.md](templates/QUESTION.md). Its status is one of:

`proposed` → `open` (validated, statement frozen) → `proved` | `refuted` | `variant-proved` |
`abandoned`.

A refutation or a justified variant is a result, not a failure. `abandoned` needs a reason in the
file.

## Rules for results

1. **Frozen statement.** Prove exactly the statement in `Statements/`. The proof in `Incognita/`
   restates it under the matching name, and `lake exe audit` checks that the two types are equal.
   Never weaken a statement to make a proof go through.
2. **Variants.** A variant (extra hypothesis, weaker constant, special case) is accepted only with
   a formal reason: a counterexample to the original, or a proof that the extra hypothesis is
   needed, or the explicit label "original still open". A silent weakening is blocked.
3. **Refutations.** A formal proof of the negation of a frozen statement is merged like a proof,
   under the same standard.
4. **New definitions.** Besides a non-trivial witness, each new definition comes with:
   agreement with the classical notion on a known special case; a concrete instance satisfying all
   hypotheses of the main theorem *at once*; when possible, an example showing that dropping a
   hypothesis makes the result false. Definitions are where a new library goes wrong silently.
5. **Main statements are formalised twice.** For a question's main theorem or an important new
   definition, a second agent formalises the statement from the mathematical text alone, without
   seeing the first version; the two are proved equivalent in Lean.
6. **No evaluative definitions.** No `def IsOptimal` meaning "attains bound X". State upper bounds
   with explicit constants and lower bounds with explicit classes of algorithms; "optimal" is a
   named corollary pairing the two in one class.
7. **Dead ends.** Before working on a question, read its dead ends. After a failed approach, add
   one line: the approach, and why it fails.
8. **Novelty.** A result is never called new by its author: its catalogue entry starts with
   `novelty = "unchecked"`, and only the bibliographer's attribution audit can set it to `new`
   (see "Literature and attribution").
9. **Write-up.** A result is finished only with a human-readable proof (LaTeX or Markdown with
   mathematics) that maps each statement to its Lean declaration, and has an **Attribution**
   section: for each technique used, its presumed source as `[KEY, ...]`, or "source not known".

## Literature and attribution

Lean does not check citations, and models invent plausible references. So:

- **Cite only what was read.** A citation `[KEY, Theorem X]` in a docstring, a write-up, a question or
  the catalogue points to an entry of `literature/bibliography.json` whose metadata is `checked` and
  whose part X is marked as read in `literature/index.md`. If you need a reference that is not there,
  add it with metadata `unchecked` and nothing marked as read, and write "(to be checked)" after the
  citation; the bibliographer will check it. Never mark something as read that you did not read in
  the source.
- **Credit techniques, not only results.** The Attribution section of a write-up names where each
  idea of the proof comes from. A new statement proved with an old technique is a new result whose
  technique is credited; the question "is this exact statement in print?" is not enough.
- **Every role may read the web** (search and pages, no other network access). What you read and
  use is recorded in `literature/` (entry, part read, by whom, when), in the same pull request.
- **The bibliographer** audits independently every merged result: is it known,
  is it a special case of something known, where do its techniques come from. It sets `novelty` in
  the catalogue to `new`, `rediscovery of [KEY, ...]` or `known: [KEY, ...]`. It also checks the
  metadata of references and reads the cited parts. Its audit counts as a check of type
  `attribution-audit` for the confidence level.
- Quote sources only briefly; summarise in your own words.

## Validating questions

As question reviewer, you read the question file, the programme and the catalogue, and nothing the
proposer wrote elsewhere. Check the programme's validation criteria one by one; try a short proof
of the question from the catalogue (if it succeeds, the question is a corollary: reject); search the
literature for the answer. Record in the question file your verdict (`accept` or `reject`), the
model you are, the date and your reasons, criterion by criterion. If you accept, write the frozen
statement in `Statements/<Programme>/` and set the status to `open`, unless the question file says
the owner's decision is still required (calibration phase), in which case leave the status
`proposed`.

## Reviewing pull requests

Review as an independent reviewer: you see the mathematical statement and the Lean code, not the
author's reasoning. Restate the statement in your own words from the Lean alone and compare it with
the text ("back-translation"); try to break every new definition and statement (vacuity, wrong
quantifiers, content hidden in hypotheses, degenerate cases); check the rules above. Say which
checks you ran. List defects, most important first, with what would fix them; skip praise.

## Gardening

- Look for results that imply others: try the implication in Lean.
- A result A is marked *subsumed* by B only if B implies A with quantitative content at least as
  good (same constants, same order, same hypotheses). Then A's proof becomes "corollary of B", but
  A's statement stays.
- **No theorem lost.** A pull request that removes or changes a theorem shows that the old
  statement is still provable from the library. Only a human can remove a statement, for a
  definition found to be wrong.
- If a lower bound exceeds an upper bound in the same class, Lean proves `False`: report it at
  once, a definition is wrong somewhere.
- Keep `catalogue/results.toml` current.

## Pull requests

One topic per pull request; no stacked pull requests. A writing role ends by writing
`.agents/summary.md` (results in mathematical form with their Lean names, frozen statements added,
sources read, what is not done): it becomes the pull request's description and, through CI, a PDF
for the human who merges. Reuse what exists in Mathlib, Tau Ceti, LML,
LMLExplore and here, up to renaming and generalisation. Never open pull requests or issues in those
dependencies: their maintainers decide what to adopt. Say in the description which model wrote the
pull request.

Human-owned paths, which you never change: `README.md`, `AGENTS.md`, `CLAUDE.md`,
`CONTRIBUTING.md`, `programmes/*/PROGRAMME.md` and the other files next to it, existing files of
`Statements/`, `templates/`, `agents/`, `docs/`, `scripts/`, `.github/`, `lakefile.toml`,
`lean-toolchain`, `lake-manifest.json`. They are listed in `.github/CODEOWNERS`.

## Building

`scripts/build.sh <Lib>`; CI runs `scripts/check-build.sh Incognita --no-sorry`,
`scripts/check-build.sh Statements`, `scripts/build.sh Exploration` and `lake exe audit`. Never require Mathlib, Tau Ceti or LML directly: they come from LMLExplore, at its pins.
