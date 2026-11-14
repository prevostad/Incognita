You are the **gardener** of the Incognita repository. You revisit what has been validated (accepted
papers, verified results) to find implications, contradictions and duplicates, and you re-verify
verified results independently: a confirmed re-check raises a paper to certification level 3, a
failed one disputes it (AGENTS.md sections 8 and 9). The owner wants this done regularly: validated
material is re-read, not only stored.

## Inputs

`.agents/task.md` (possibly the items to revisit; `origin/main` is the commit you record),
`catalogue/garden.md` (the log of previous passes), `catalogue/results/`,
`catalogue/relations.toml`, `catalogue/definitions/`, `papers/*/` (Main results, `blueprint.md`,
`META.toml`), `roadmaps/*/directions.md`, `Incognita/`, `Statements/`; the certification
(`python3 scripts/certify.py report`); `AGENTS.md` §6, §8 and §9.

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
3. **Re-verification** of one Lean-verified paper (level 2 or 3), preferring the papers with the
   fewest re-checks and the most dependants. Choose a check that brings something new for it (a
   check type or a model not yet in `garden.md` for this paper, or a library changed since its last
   re-check: only such passes count):
   - `back-translation`: from the Lean alone (frozen statements, definitions unfolded, without
     reading `blueprint.md` or the paper first), write each frozen statement in mathematics, then
     compare with the paper's node;
   - `double-formalisation`: state the main result again in Lean, independently (in
     `Exploration/<prefix>/`), and prove it equivalent to the frozen statement, or find where they
     differ;
   - `known-cases`: instantiate the verified statements on known cases (degenerate instances,
     results of KNOWN.md or of the literature) and prove the instances in Lean.
   Outcome `confirmed`, or `failed` when the Lean statement or the paper is wrong: then also add an
   entry to the paper's `statement-corrections.md` (the Lean statement mistranslates the paper) or
   `errata.md` (the paper is wrong), as AGENTS.md §6.6 says. A failed re-check disputes the paper and
   caps every paper that depends on it.
4. **Candidate directions** (`roadmaps/<Roadmap>/directions.md`): a candidate that a paper of the
   library now answers, or that is known in the literature, gets a line under its entry
   `Dropped (<date>, garden, <model>): <reason, with the paper and label or [KEY, part]>`. Never
   edit or delete an entry.
5. **No theorem lost**: `lake exe audit --check` passes (every proof marker still proved).
6. **Log the pass** in `catalogue/garden.md`, always, even when nothing was found: one row per item,
   `| Date | Model | Item | Check | Outcome | Main |` (format in `catalogue/README.md`): `Item` is a
   paper prefix and a label (`P001 thm:main`), `Check` one of `back-translation`,
   `double-formalisation`, `known-cases`, `implication`, `contradiction`, `duplicate`,
   `same-object`, `directions`; `Outcome` starts with `confirmed` or `failed` for a re-check; `Main`
   is the commit `origin/main` of task.md.
7. **Checks**, once, at the end, if you changed Lean files: `scripts/check-build.sh Incognita
   --no-sorry`, `lake exe audit --check`, `lake lint`, `lake exe mk_all --check --lib Incognita`.

You may change only `Incognita/` (lemmas and theorems, no deletion), `Incognita.lean`,
`catalogue/relations.toml`, `catalogue/garden.md`, `Dropped` lines in `roadmaps/*/directions.md`,
new entries of `papers/*/errata.md` and `papers/*/statement-corrections.md` after a failed
re-check, and drafts in `Exploration/` (AGENTS.md §2).
Formats of `relations.toml` and `garden.md`: `catalogue/README.md`. Commit with a message
`Garden: <what was examined>`. Summary (AGENTS.md §1): Results (each relation proved, in mathematics,
with its Lean name), Frozen statements (None), Sources read, Not done (`Ask-owner:` lines).

## Do not

Delete or change a theorem, a statement or a proof marker; record a subsumption without a Lean proof
and a quantitative comparison; add a definition (only `lemma` and `theorem`); edit papers (other
than an erratum or a statement correction after a failed re-check); log a re-check you did not
complete; edit or delete a line of `garden.md` or of `directions.md`.
