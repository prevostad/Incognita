# Proof markers

One file per verified frozen statement: `catalogue/results/<P>-<name>.toml`, where
`Incognita.Statements.<P>.<name>` is the frozen statement (`P001-lower_bound.toml` for
`Incognita.Statements.P001.lower_bound`). A marker records that the result is in the library and
guarantees that it stays there ("no theorem lost").

## What the machines check

- **CI, on pull requests** (`scripts/ci/check-additive.sh`): marker files are only ever added,
  never modified, renamed or removed. This README may change.
- **`lake exe audit --check`** (`scripts/Audit.lean`), on every build: each marker names a frozen
  statement, and that statement is
  - **proved**: the library has a theorem `Incognita.<P>.<name>` of exactly the frozen type, in a
    module under `Incognita/`, using only the axioms `propext`, `Classical.choice`, `Quot.sound`;
  - or, if the marker has the line `status = "refuted"`, **refuted**: the library has, under the
    same conditions, `Incognita.<P>.<name>_false : ¬ T`.

  A marker whose statement is open again (proof removed, renamed, or its type changed) fails CI.

The audit reads only the file name and the `status` line; the rest of the file is for people and
for the agents.

## Format

TOML, one table at top level:

| Field | Meaning |
|---|---|
| `statement` | the frozen statement, `Incognita.Statements.<P>.<name>` |
| `status` | `"proved"` (default when absent) or `"refuted"` |
| `paper` | the paper directory, `papers/P<nnn>-<slug>`, and the label of the statement in it |
| `novelty` | `unchecked` (set by the prover), then, set only by the bibliographer: `new`, `rediscovery of [KEY, ...]` or `known: [KEY, ...]` |
| `confidence` | `merged`, `checked`, `used`, `established` (see `catalogue/README.md`) |
| `checks` | independent checks passed, for example `back-translation`, `attribution-audit` |

Example, `catalogue/results/P001-lower_bound.toml`:

```toml
statement = "Incognita.Statements.P001.lower_bound"
status = "proved"
paper = "papers/P001-batch-lower-bound, thm:lower"
novelty = "unchecked"
confidence = "merged"
checks = []
```

Since markers are append-only, a later change of `novelty`, `confidence` or `checks` is an owner
pull request (admin bypass), or is recorded elsewhere; the marker itself stays.

## Statuses for scripts

`lake exe audit --status` prints one line `<P> <name> open|proved|refuted` per frozen statement
(stdout only; build logs go to stderr). A statement that is proved or refuted without a marker yet
is waiting for one.
