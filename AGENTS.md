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
3. work on an `open` question: explore, prove, refute, or prove a justified variant;
4. propose a question in an approved programme;
5. gardening (see below).

## Spaces

- `Exploration/`: drafts. `sorry` is allowed. Nothing outside `Exploration/` may import it. Record
  what you learn in the question's file, not only in code.
- `Statements/`: one module per validated question, holding its frozen statement with `sorry`.
  Created when a question is validated; **changed only by a pull request a human approves**.
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
   restates it and a comparator check confirms the two are the same. Never weaken a statement to
   make a proof go through.
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
8. **Novelty.** Before claiming a result is new, search the literature; a rediscovery is fine but
   is labelled as such, with the reference.
9. **Write-up.** A result is finished only with a human-readable proof (LaTeX or Markdown with
   mathematics) that maps each statement to its Lean declaration.

## Reviewing

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

One topic per pull request; no stacked pull requests. Reuse what exists in Mathlib, Tau Ceti, LML,
LMLExplore and here, up to renaming and generalisation. Never open pull requests or issues in those
dependencies: their maintainers decide what to adopt. Say in the description which model wrote the
pull request.

Human-owned paths, which you never change: `README.md`, `AGENTS.md`, `CLAUDE.md`,
`CONTRIBUTING.md`, `programmes/*/PROGRAMME.md`, existing files of `Statements/`, `templates/`,
`docs/`, `scripts/`, `.github/`, `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`.

## Building

`scripts/build.sh <Lib>`; `scripts/check-build.sh Incognita --no-sorry` is what CI runs on the
library. Never require Mathlib, Tau Ceti or LML directly: they come from LMLExplore, at its pins.
