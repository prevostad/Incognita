# Definitions

One file per definition of the library, `<Name>.toml`, named after the Lean declaration (without
its namespace). Written by `formalize-statements` in the pull request that adds the definition;
reviewed by `review-statements`. Definitions are where a new library goes wrong silently, so each one
carries the Lean checks of AGENTS.md §6.4.

Not stored (computed by the audit and shown in reports): which frozen statements use the definition,
and whether it is locked.

```toml
lean = "Incognita.BatchedBandits.Grid"           # full Lean name
module = "Incognita.BatchedBandits.Grid"         # module that defines it
roadmap = "BatchedBandits"
paper = "P000-setting"                           # the paper that introduced it
label = "def:grid"                               # its node in that paper
meaning = "An imposed grid: batch ends 0 = t_0 < t_1 < t_2 < ..., the end of batch l being t_l."
conventions = "Rounds numbered from 0; batch l is the set of rounds t_{l-1}, ..., t_l - 1."
source = "roadmap BatchedBandits, Definitions"   # or [KEY, part] for a definition from the literature

[checks]                                         # Lean names; an empty list means not done
witness = ["Incognita.BatchedBandits.Grid.geometric"]          # a non-trivial object satisfying it
known_cases = ["Incognita.BatchedBandits.Grid.sequential_eq"]  # agreement with a classical notion
exclusion = ["Incognita.BatchedBandits.Grid.not_const"]        # an object that must not satisfy it
non_vacuity = ["Incognita.P001.lower_bound_satisfiable"]       # hypotheses of statements hold together
```
