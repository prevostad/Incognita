# Catalogue

Metadata about the library, used by gardening, by the bibliographer and by the night report. What
can be computed (which statements use a definition, which are locked, proved or refuted) is not
stored here: the audit (`lake exe audit`) computes it.

| Path | Content | Written by |
|---|---|---|
| `definitions/<Name>.toml` | one file per definition of the library: meaning, conventions, checks | `formalize-statements` ([definitions/README.md](definitions/README.md)) |
| `results/<prefix>-<name>.toml` | one proof marker per proved frozen statement (or refutation) | `prove`; **additions only** |
| `attribution/<prefix>.md` | the bibliographer's attribution audit of a verified paper | `bibliographer` |
| `relations.toml` | implications, contradictions, duplicates between results | `garden` |
| `garden.md` | the log of gardening passes | `garden` |

## Proof markers: `results/<prefix>-<name>.toml`

Written once, when `Incognita.<prefix>.<name>` (or the refutation `<name>_false`) is proved; never
modified or deleted (CI checks that `results/` only receives additions, and the audit fails if a
marked statement is no longer proved: "no theorem lost").

```toml
paper = "P001-one-batch-lower-bound"
label = "thm:main"
statement = "Incognita.Statements.P001.lower_bound"   # the frozen statement
proof = "Incognita.P001.lower_bound"                  # or Incognita.P001.lower_bound_false
refutation = false                                    # true for a proof of ¬ T
roadmap = "BatchedBandits"
kind = "lower-bound"        # upper-bound, lower-bound, optimality, refutation, identity, other
quantity = "K_a E N_a(t_l) / L_l at batch ends"
class = "rewards in [0,1], m* < 1; every grid; learners consistent at batch ends, every information model"
regime = "asymptotic"       # or non-asymptotic
constant = "1"              # first-order constant; second-order terms if known
date = "2026-11-20"
proved_by = "claude-opus-5-5"
```

Novelty is not stored in the marker (it would need a modification): it is in `attribution/`.

## Attribution audits: `attribution/<prefix>.md`

```
# Attribution audit of <P>

By <model>, <date>. Independent of the scope referee's report, read only after the search.

## Verdicts
| Frozen statement | Novelty | Evidence |
| Incognita.Statements.P001.lower_bound | new / rediscovery of [KEY, part] / known: [KEY, part] | … |

## Techniques
| Technique | Node | Earliest source found (part read) | Paper's attribution |

## Queries
- "<query>" (<date>): <what it found>

## Disagreements with the scope referee
```

## Relations: `relations.toml`

```toml
[[relation]]
kind = "subsumes"     # subsumes, contradiction, duplicate, same-object
from = "Incognita.P003.upper_bound"
to = "Incognita.P001.upper_bound"
lean = "Incognita.BatchedBandits.Relations.p001_upper_bound_of_p003_upper_bound"
justification = "same constants and order; P003 assumes less"
date = "2026-11-25"
by = "claude-opus-5-5"
```

`subsumes` requires a Lean proof and quantitative content at least as good (same constants, same
order, hypotheses no stronger). A `contradiction` means a definition is wrong: it is also reported to
the owner.

## Gardening log: `garden.md`

A table, one row per item examined, newest last:

```
| Date | Model | Item | Outcome |
|---|---|---|---|
| 2026-11-25 | claude-opus-5-5 | P001 thm:main | implied by P003 thm:main (relation recorded) |
```
