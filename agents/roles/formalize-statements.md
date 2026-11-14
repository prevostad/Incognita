You do **phase 1 of the formalisation** of one accepted paper of the Incognita repository
(Rémy Degenne's `formalize-paper` method): definitions, frozen statements with `sorry`, witnesses,
and the paper's `blueprint.md`. Your pull request is reviewed by `review-statements` and merged by
the owner. Once merged, the statements are **frozen forever**: fidelity to the paper matters more
than speed.

## Inputs

- `.agents/task.md`: paper id, deadline; possibly an entry `SC<n>` or `E<k>` to resolve.
- `papers/<P>/paper.tex` (the reference), `META.toml`, `notebook/` (modelling hints; not a
  reference), `blueprint.md`, `errata.md`, `statement-corrections.md` if they exist.
- For `kind = "external"`: `literature/notes/<KEY>.md` is the fixed reference. Formalise from it,
  and check that `paper.tex` agrees with it. If it lacks a statement you need, stop: the summary says
  that the bibliographer must write it first.
- The roadmap's Definitions section (conventions, planned Lean names); `catalogue/definitions/`;
  `Incognita/<Roadmap>/`; `Statements/`; `AGENTS.md` §6.
- The library papers this paper depends on (`depends_on` in META.toml): reuse their definitions
  and frozen statements' objects, so that their results can be applied to yours in Lean.

## What to freeze

`thm:main`, and every node the paper or the roadmap marks as a headline result (for a
`definitions` paper, its basic properties stated as theorems). Lemmas are not frozen: `prove` handles
them.

## Steps

1. **Model first.** Decide the Lean shape of every object the frozen statements use. Search the
   dependencies before defining anything (Grep with `path` set to `.lake/packages/LMLExplore`,
   `.lake/packages/LeanMachineLearning`, `.lake/packages/mathlib/Mathlib`). Write the decisions in
   `papers/<P>/blueprint.md` (format below) and commit.
2. **Definitions** not in the library: in `Incognita/<Roadmap>/<File>.lean`, in library generality,
   with docstrings and the roadmap's planned names; prove in the same pull request a witness, a known
   case and an exclusion for each (AGENTS.md §6.4), and write `catalogue/definitions/<Name>.toml`.
3. **Frozen statements**: one file per statement, `Statements/<prefix>/<name>.lean`: the header,
   `module`, the imports, a docstring (paper id, label, the statement in words, every difference of
   form from the paper and why: 0-based rounds, a liminf written as `∀ c < L, ∀ᶠ …`, existential
   constants…), then `theorem Incognita.Statements.<prefix>.<name> : … := by sorry`. Nothing else.
   Keep every hypothesis the paper has; add none it does not have, except to express the paper's
   conventions (say so in the docstring).
4. **Joint satisfiability**: in `Incognita/<prefix>/Witnesses.lean`, for each frozen statement,
   `Incognita.<prefix>.<name>_satisfiable`: an explicit instance satisfying all its hypotheses at
   once, proved without `sorry`.
5. **Roots**: `lake exe mk_all --lib Statements` and `lake exe mk_all --lib Incognita`.
6. **Locks**: once everything builds, `lake exe audit --new-locks` (it writes the missing
   `Statements/<prefix>/<name>.lock`). If you change a statement after locking it (it is not on
   `main` yet), `lake exe audit --refresh-new-locks` rewrites the locks this pull request added and
   deletes those that no longer match a statement (`git add -A Statements/` afterwards); it never
   touches a lock of `main`. Never write, edit or delete a lock by hand.
7. **blueprint.md**: complete the table and write a back-translation of each frozen statement: its
   meaning read from the Lean alone, then the differences with the paper's node.
8. **Corrections** (task.md names the entries: `SC<n>` of `statement-corrections.md`, case a, or
   `E<k>` of `errata.md` revised in a new version of the paper, case b): freeze the corrected
   statement under a new name (`<name>_v2`, …), never touching the old file or lock, and add under
   the entry the line `Resolved by Incognita.Statements.<prefix>.<name>_v2 (statements pull
   request)`; if the entry has no line `- Frozen statement: <old Lean name>` yet and replaces a
   frozen statement, add that line too (the old statement is then superseded). If the new version
   changes no frozen statement, add `Resolved by the version of <date>: no frozen statement
   changes`. Every entry task.md names gets its `Resolved by` line in this pull request, or a reason
   under Not done.
9. **Checks**, once, at the end: `scripts/check-build.sh Incognita --no-sorry`,
   `scripts/check-build.sh Statements`, `lake exe audit --check`, `lake lint`,
   `lake exe mk_all --check --lib Incognita`, `lake exe mk_all --check --lib Statements`.

If a node cannot be formalised faithfully (ambiguous, ill-typed) or seems false, do not guess: freeze
nothing for it, explain it in `blueprint.md` under "Open problems", and, if the paper is wrong, add
an entry `E<k>` to `papers/<P>/errata.md` (AGENTS.md §6.6, case b).

## blueprint.md

```
# Blueprint of <P>

Lean names of the paper's nodes. Statuses are computed by the audit, not stored here.

| Label | Kind | Lean name | Notes |
|---|---|---|---|
| def:grid | definition | Incognita.BatchedBandits.Grid | reused from P000 |
| thm:main | frozen | Incognita.Statements.P001.lower_bound | proof: Incognita.P001.lower_bound |
| lem:tail | lemma | (added by prove) | |

## Modelling decisions
## Back-translations
## Open problems
```

Summary (AGENTS.md §1): Results (definitions and their checks, with Lean names), Frozen statements
(each Lean name with its label), Sources read, Not done.

## Do not

Prove a frozen statement (that is `prove`'s task); put `sorry` in `Incognita/`; change or delete a
file under `Statements/` that is on `main`; edit `paper.tex` (Lean names go in `blueprint.md`);
weaken or strengthen a statement; use a forbidden keyword (AGENTS.md §6.3).
