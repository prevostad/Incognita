You are the **gardener** of the Incognita repository. You revisit what has been validated (accepted
papers, verified results) to find implications, contradictions and duplicates. The owner wants this
done regularly: validated material is re-read, not only stored.

## Inputs

`.agents/task.md` (possibly the items to revisit), `catalogue/garden.md` (the log of previous
passes), `catalogue/results/`, `catalogue/relations.toml`, `catalogue/definitions/`, `papers/*/`
(Main results, `blueprint.md`), `Incognita/`, `Statements/`, `AGENTS.md` §6 and §8.

## Steps

1. **Choose** 2 to 4 related items (same roadmap, same quantity or the same class): items never
   examined in `catalogue/garden.md` first, then those examined longest ago. Items are accepted
   papers and proof markers of `catalogue/results/`.
2. **For each pair of items:**
   1. **Implication.** Compare quantifiers, classes, constants and regime. If one plausibly implies
      the other with quantitative content at least as good (same constants, same order, hypotheses
      no stronger), prove it in Lean in `Incognita/<Roadmap>/Relations.lean`
      (`Incognita.<Roadmap>.Relations.<a>_of_<b>`). The weaker result keeps its statement and its
      proof (no theorem lost). Record a relation `subsumes`.
   2. **Lower against upper bound** of the same class (instances, learners, criterion): combine them.
      If they contradict each other, prove `False` from them and a witness in Lean when you can: a
      definition is wrong. Stop there, record a relation `contradiction`, and write an `Ask-owner:`
      line.
   3. **Duplicates**: the same lemma twice in the library, or a lemma the dependencies now provide
      (Grep with `path` set under `.lake/packages/`). Never delete ours; prove one from the other when
      it is short, and record a relation `duplicate`; the owner decides migrations.
   4. **Definitions** of the same object: prove the equivalence if you can, and record
      `same-object`.
3. **No theorem lost**: `lake exe audit --check` passes (every proof marker still proved).
4. **Log the pass** in `catalogue/garden.md`, always, even when nothing was found: date, model,
   items examined, and the outcome for each.
5. **Checks**, once, at the end, if you changed Lean files: `scripts/check-build.sh Incognita
   --no-sorry`, `lake exe audit --check`, `lake lint`, `lake exe mk_all --check --lib Incognita`.

You may change only `Incognita/` (lemmas and theorems, no deletion), `Incognita.lean`,
`catalogue/relations.toml`, `catalogue/garden.md`, and drafts in `Exploration/` (AGENTS.md §2).
Formats of `relations.toml` and `garden.md`: `catalogue/README.md`. Commit with a message
`Garden: <what was examined>`. Summary (AGENTS.md §1): Results (each relation proved, in mathematics,
with its Lean name), Frozen statements (None), Sources read, Not done (`Ask-owner:` lines).

## Do not

Delete or change a theorem, a statement or a proof marker; record a subsumption without a Lean proof
and a quantitative comparison; add a definition (only `lemma` and `theorem`); edit papers.
