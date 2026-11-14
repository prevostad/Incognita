Not refereed: working notes of the authors of P001.

# P001: the optimal constant of the minimax regret (a paper of the owner)

## 2026-11-14, submission (Claude Opus 5.5, for the owner)

**Provenance.** `paper.tex` is the owner's draft of 5 November 2026 ("The optimal constant in the
minimax regret of stochastic multi-armed bandits"), converted to the format of the library. The
statements and the proofs are unchanged. What changed is the form only:

- sections in the order of AGENTS.md 5.2: Main result (Theorem `thm:main`), Setting (its
  paragraphs became definition nodes: `def:regret`, `def:class`, `def:regular`, `def:alloc`,
  `def:limit`, `def:risk`, `def:batched`, `def:kappa`), Closest known, Proofs (the further results,
  the policies, the two-armed computations, the experiments, then the former appendices), Sanity
  checks, Weak points, Open questions, Attribution (these five written for the submission), then
  the notation;
- blueprint: `\uses` generated from the references and from the hyperlinked symbols of each
  statement and proof, `\proves` for every proof placed away from its statement; the four
  algorithms became definition nodes (`def:sc`, `def:opt2`, `def:K2-inf`, `def:K2-tc`); the proofs
  of Theorem `thm:bounds` and Proposition `prop:K2`, written as plain sections, were wrapped in
  proof environments;
- packages of the template only: pseudo-code as indented paragraphs, notation tables as
  paragraphs or plain `tabular`, no figure (below), the bibliography as `refs.bib`, with the keys
  of `literature/bibliography.json` where they exist (`LS` for the book of Lattimore and
  Szepesvári, `Vog60` as in direction D19);
- the author's status lines, notes and working comments (in French) are removed.

**Checks before this version.** The five routes of the proof (limit game, lower bound, upper
bound, many arms, two arms) were each written by an agent and checked by an independent agent;
the whole draft was read by another agent (minor revision; its major points were corrected).
Nothing is formalised in Lean. The certification of the two-armed bounds (Proposition `prop:K2`)
is a computation in double precision, without interval arithmetic.

**Experiments (not refereed).** `experiences.png` is the figure of the author's version, redrawn
on 2026-11-14 from `resultats.json` by `figures.py` (no new run). `simulations.py` produced
`resultats.json` and `simulations_sortie.txt` (about 3 minutes on a laptop; the worst cases of
Section "Experiments"). It reads the threshold table of the two-armed Bayes policy, `seuils_K2.npz`
(1.3 MB, binary: not in the repository), which `table_seuils.py` computed from the author's
scripts of the two-armed recursion (not in the repository either; its output is
`table_seuils_sortie.txt`). The outputs are in French (`pire cas` = worst case).

**Left for later.**

- `literature/`: most of the 42 references are not yet in `bibliography.json`; the bibliographer
  adds them and the notes the cited parts need.
- An interval-arithmetic certification of the two-armed bounds (Open question on `V_2`, and Weak
  point 1).
- Formalisation: the lower bound of Theorem `thm:bounds` (fundamental inequality, convexity of kl,
  a one-needle prior) is within reach of Lean on LML; the identification of the value (Skorokhod
  embedding, compactness of limit policies, Ky Fan) is far from what Mathlib provides.
