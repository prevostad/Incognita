# Catalogue of results

`results.toml` has one `[[result]]` entry per main theorem of the library. Gardening uses it to
find results that imply others, families of special cases that call for a unification, and
lower and upper bounds of the same class that can be compared.

Fields:

| Field | Meaning |
|---|---|
| `id` | stable identifier, for example `BatchedBandits.HY.upper` |
| `decl` | the Lean declaration |
| `programme` | the programme it belongs to |
| `kind` | `upper-bound`, `lower-bound`, `optimality`, `refutation`, `other` |
| `quantity` | what is bounded, for example `K_a E N_a(t_l) / L_l at batch ends` |
| `class` | instances, grids, learners (information model, consistency notion) |
| `regime` | `asymptotic` or `non-asymptotic` |
| `constant` | the first-order constant, and the size of the second-order terms if known |
| `confidence` | `merged`, `checked`, `used`, `established` |
| `checks` | independent checks passed, for example `double-formalisation`, `back-translation` |
| `subsumes`, `superseded_by` | ids of related results, with the justification in the pull request |

## Confidence levels

| Level | Condition |
|---|---|
| merged | CI green and reviews approved |
| checked | at least three independent checks of different kinds passed |
| used | consumed by later theorems, consistency checks passed |
| established | written up, read by a human, no alert since the last generation of reviewer models |

The level rises with new information, not with elapsed time.
