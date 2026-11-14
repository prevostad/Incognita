# Proof markers

One file per frozen statement that is proved (or refuted): `catalogue/results/<P>-<name>.toml`,
named by the frozen statement's Lean name `Incognita.Statements.<P>.<name>` (`P001-lower_bound.toml`
for `Incognita.Statements.P001.lower_bound`; a refutation keeps that name, never `_false`). A marker
records that the result is in the library and guarantees that it stays there ("no theorem lost").
Written by `prove`, in the pull request that proves the statement.

## What the machines check

- **CI, on pull requests** (`scripts/ci/check-additive.sh`): marker files are only ever added,
  never modified, renamed or removed. This README may change (the owner's).
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

TOML, one table at top level; the fields and an example are in
[catalogue/README.md](../README.md) ("Proof markers"). The fields the scripts rely on:

| Field | Meaning |
|---|---|
| `statement` | the frozen statement, `Incognita.Statements.<P>.<name>` |
| `status` | `"proved"` (the default when absent) or `"refuted"` |

**Novelty is not in the marker**: a marker is never modified, and novelty is decided after the
proof, by the bibliographer's attribution audit `catalogue/attribution/<P>.md` (AGENTS.md §7). Any
later information about a result goes there, in `catalogue/relations.toml` or in
`catalogue/garden.md`; the marker itself stays as written.

## Statuses for scripts

`lake exe audit --status` prints one line `<P> <name> open|proved|refuted` per frozen statement
(stdout only; build logs go to stderr). A statement that is proved or refuted without a marker yet
is waiting for one.
