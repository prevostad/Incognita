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

## 2026-11-14, revision round 1 (role revise, Claude Opus 5.5)

Answers to the reports of `referee-scope` (SC1.*) and `referee-proofs` (PF1.*) on head `cd471c2`.
Targeted edits only (a paper of the owner): no statement of the owner is changed except
`prop:K2`, which now carries an explicit hypothesis (PF1.1). Branch rebased on `main` (P000 merged;
no conflict).

### Proof defects

- **PF1.1 (G), fixed by an explicit hypothesis.** `prop:K2` is now stated under (H_fp): the two
  double-precision runs (Table `tab:K2-runs`) have the accuracy assumed in `prop:K2-Lnum`(ii)
  (10^-8 per nodal value) and `prop:K2-Unum` (10^-9 per series value). Abstract, Main result,
  Contributions, sanity checks, weak points and `sec:K2-open` say "under (H_fp)". This is a changed
  statement (a new claim). Not done: a rigorous recomputation in interval arithmetic (ball
  arithmetic is not installed, python-flint absent; mpmath interval arithmetic would be far too
  slow for 800 FFT steps of length 8192; the author's scripts of the two-arm computations are not
  in the repository). It removes (H_fp) and stays the first item of `oq:V2`-type work.
- **PF1.2 (G), fixed.** New proof block "Proof of the upper bounds of Corollary examples"
  (`\proves{cor:examples}`, uses `thm:u-upper`): laws on [a,b] are in C(a,b,(b-a)/2,(b-a)/2)
  (variance through the midpoint, Hoeffding's lemma), Bernoulli laws are laws on [0,1], Gaussian
  laws N(mu,sigma^2), sigma <= sbar, are in C(a,b,sbar,sbar). Step 6 of `thm:bounds` now names the
  class C_1 (Gaussian, means in [0,1], sigma <= 1) and uses its upper half.
- **PF1.3 (L), fixed.** `def:batched` defines the batched policy once, in the strong model of
  `def:g-pol` (values at the decision times, `def:g-pol`(b)), with its risk r(pi,h) = E_h[...]
  = r(Q^pi,h) (`lem:g-disc`); it says that the whole-path reading (discrete policies,
  `def:u-batched`) gives the same risk functions (`lem:g-bridge`). `rem:g-reading` updated.
- **PF1.4 (L), fixed.** `def:sc`: if N = 0 (T < K/delta) the policy plays arm 1; the tie rule
  for i_0 (smallest index) is in the definition.
- **PF1.5 (L), fixed.** `def:opt2` rewritten from `notebook/simulations.py` (the code of the
  experiments): the test runs once min N_k >= 1, U only in the second phase (N_1+N_2 >= 2), the
  tie rule is "arm 1 if N_1 = N_2" (the code's `N1 <= N2`), the grid point is given by rounding
  (np.rint, clipped as in the code). The referee proposed "test only once min N_k >= ceil(eps T)"
  and "random tie-break"; that is not what the code does, so the definition follows the code, and
  `sec:app-exp` now says that only the index policies break ties at random (arm positions are
  shuffled in every run, so the rule plays no role).
- **PF1.6 (L), fixed.** "between 6.1 and 24.4" against 1/27 (27 kappa lambda_K: 6.09 at K=2,
  24.18 at K=1000, limit 24.37), and the other published constants (SC1.2).
- **PF1.7 (P), fixed.** Cycles removed: `def:class` no longer uses `def:regret`; the proof of
  `lem:skor` no longer uses `thm:lowEF`; the proof of `thm:u-upper` no longer uses `thm:main`.
- **PF1.8 (P), fixed.** Edges added (prop:four, cor:g-cont, lem:g-disc in the proofs of
  thm:u-upper and prop:u-local; lem:simW, lem:staircase in prop:lowtilt; def:regular in thm:main;
  def:limit in def:risk); new blocks "Proof of Theorem 1.1(ii)" (`\proves{thm:main}`) and
  "Proof of Proposition prop:four(c)" (`\proves{prop:four}`).
- **PF1.9 (P), partly fixed.** (UA) and (V) are lemmas `lem:g-UA`, `lem:g-V`; the cost identity is
  `lem:K2-cost` and the risk formula `lem:K2-rho` (with a short proof); the proofs that use them
  list them.
- **PF1.10 (P), fixed** in `lem:K2-conv` Step 1.
- **PF1.11 (P), fixed.** V_K, B_K, V_K(H) defined as inf (attained by `lem:g-min`);
  `thm:main`(i) refers to `thm:lowEF` and `prop:lowtilt` for the quantitative form; the remark
  after `thm:lowEF` says that T_1 also depends on beta.

### Scope defects

- **SC1.7 (L), fixed.** [PD] removed (the claim of the remark after `thm:bounds` is marked "not
  proved here, not used"; the dashed curve of panel (b) is a numerical illustration only). Rod78
  marked "(to be checked)".
- **SC1.9 (G), fixed.** Cost per round of SC (after `def:sc`): O(1) amortized in Stage 1, O(1)
  per round plus m evaluations of the rules of the core in Stage 2, total
  O(K + (m+1)T + sum_j c_j(T')); of Opt_2 (after `def:opt2`): O(1) per round, table of O(eps^-2)
  entries computed once. Tie rules in both definitions.
- **SC1.10 (P), fixed.** "optimal policy" reworded (notation, Contribution 3, `sec:algo`, panel (b)).
- **SC1.11 (P), fixed** (`\noindent`).
- **SC1.12 (P), fixed.** The Setting lists the conventions changed (enumerated arms, rounds from
  1, notation of means, horizon-dependent policies, new classes), one line each.

## 2026-11-15, revision round 1, continued (role revise, fix round on an incomplete draft, Claude Opus 5.5)

The session of 2026-11-14 stopped before the scope defects SC1.1-SC1.6 and SC1.8. This session
answers them. It also corrects one item of the list above: **PF1.6 was marked fixed but had not been
applied** ("between 6 and 24" was still in the abstract and in Main result (c)). It is fixed now.
The statements of the owner are unchanged. The new nodes are two cited results,
`cite:GMS19-Lemma1` and `cite:LS19-Thm6.1`.

**Sources.** Four agents read the sources, using WebFetch only. A fifth attempt overflowed its
context on the PDF of the book LS and was split into two. They wrote `literature/notes/` for: Kol17,
KNS17, Kol16 (the referee's "Kol15": the paper is from 2016), Kol20 (Russian original, read whole),
Kol25 (abstract only), Adu25 (arXiv v16 and v1), KK23, HP23, LS19, ZL19, Fan53 (metadata only), LS
(Theorem 15.2, Exercise 15.2, Theorem 9.1, §4.6), GMS19 (Appendix B.1 added), GMS20, ACFS02
(metadata only), FvZ70 (abstract), Vog60, Vog60a, Bat83 (metadata). Things the agents found that
differ from the referee's report:
- LS19's bandit bound is Theorem 6.1 in the arXiv rendering, not Theorem 6. The PMLR PDF was not
  read.
- In Adu25 (v16), "left for future research" is in §5.4, right after (5.8), not in §7. "A lot more
  demanding" (§2.4) is about computing the least favourable prior for more than two arms.
- In the online edition of LS, MOSS is Algorithm 7 (§9.1). Exercise 15.2 gives (1/8)sqrt(kn) with
  means in [0, (1/2)sqrt(k/n)], with no hypothesis on n.
- GMS19, App. B.1, says that 1/20 "can actually be improved into 1/8" by Cesa-Bianchi–Lugosi Thm 6.11
  (not read). If true, this gives V_K >= sqrt(K)/4, which beats thm:bounds at K=2. The paper now
  says so.
- Kol20 states no theorem on the minimax limit: its Theorem 6 is the limit of a Bayes risk. The
  minimax claim rests on "the main theorem of game theory" and on non-rigorous reasoning.

### Scope defects

- **SC1.1 (G), fixed.** These parts were rewritten:
  - Closest known, item "Two arms": Kol17 Thms 1-2 proved; (5) taken from game theory; PDE (26)-(27)
    formal; Thm 3 "given without proof". Kol16 proves nothing new on the limit. Kol20 claims the
    limit is "established", by non-rigorous reasoning; its Thm 6 is a Bayes limit. Kol25 from its
    abstract only.
  - Main result: Context, Contribution 1 ("Theorem 1.1 proves Kolnogorov's claim for K=2"), and the
    abstract.
  - Attribution.

  KNS17 and Kol16 were added. Kol25's theorem numbers and its 3-arm values are **not** quoted: the
  full text could not be accessed, so the referee's citation "Kol25 Thms 1-3, Lemmas 1-4, Remarks 1, 3"
  is not followed.
- **SC1.2 (G), fixed.** New paragraph "Previous best values" in Closest known, in the normalization of
  V_K:
  - two arms: Bather/Vogel 0.612-0.752 (quoted in Kol17 (3) and KNS17 Thm 1), and FvZ70
    0.265-0.376 sqrt N, that is 0.53-0.752;
  - every K: LS Thm 15.2, LS Ex. 15.2, ACFS02 (to be checked), and the 1/8 of Cesa-Bianchi–Lugosi as
    reported by GMS19 for the upper side; LS19 Thm 6.1 and ZL19 Thm 11;
  - which bounds are asymptotic and which are not.

  The ratios are computed in this session: 27 kappa lambda_K is 6.09 to 24.37; against sqrt(K)/8
  1.27 to 7.22; against sqrt(K)/10 1.59 to 9.03; against sqrt(K)/4 0.64 at K=2, 3.61 in the limit.
  The abstract, Main result (c) and Sanity checks are corrected (PF1.6 too). The paper says plainly
  that for K=2 thm:bounds is weaker than Bather, and that prop:K2 improves Bather/Vogel only
  slightly.
- **SC1.3 (L), fixed.** The Attribution table became a list with every source of the report. Each
  carries the part read, or "(to be checked)", or "source not known" (Brownian bridge, noise
  injection, block-revealing relaxation, optimized height). The weak formulation is no longer
  credited to Adu25/HP23. The queries are recorded: the referee's, reused as the report allows, and
  the Crossref queries of this session. New entries: Kie57, Ste56, Hal69, Man87, EKNJ87, Vog60a
  (metadata from Crossref). PRCS16 and GKL16 are cited from their existing entries.
- **SC1.4 (L), fixed.** The credits are rewritten in Contribution 2, Closest known, the Idea of the
  proof of thm:bounds and Attribution: GMS19 (6) and Lemma 1 for the fundamental inequality; GMS20 §3
  (4)-(5) with Corollary 3 for averaging kl by joint convexity; ACFS02 Thm 5.1 (to be checked) for the
  uniform position; LS Ex. 15.2 for the average over positions. The text says that GMS19 App. B.1
  uses pigeonhole + Pinsker.
- **SC1.5 (L), fixed.** All cited keys are now entries of `bibliography.json` with rows in
  `index.md`:
  - 22 with fields from the owner's refs.bib, metadata `unchecked`;
  - the others with fields from Crossref, arXiv or the publisher's pages.

  Every citation of an unread part is followed by "(to be checked)" (script `tbc.py`, not kept:
  regex on `\cite`, then by hand). LS Chapter 4 became §4.6 (read), and MOSS became §9.1, Algorithm
  7 of the online edition.
- **SC1.6 (L), mostly fixed.**
  - New cited nodes `cite:GMS19-Lemma1` (used in Step 1 of thm:bounds) and `cite:LS19-Thm6.1`
    (used in the upper bound). Their statements are copied from the notes.
  - The step from adversarial to stochastic rewards is written out: reward table Y_{t,k}, losses
    1-Y, A_t independent of Y_{t,.}, max of expectations <= expectation of max.
  - ZL19 is cited at Thm 11 with its +48K, and "the constant of ZL19" became LS19 in Closest known
    and Sanity checks.
  - **Not done:** a node for Ky Fan's Theorem 2. Its text could not be read (PNAS, PMC and Europe PMC
    refuse access; the PMC PDF did not load through a reader proxy), so it stays a citation
    "(to be checked)". The note Fan53.md records a secondary restatement (arXiv math/0610136v2,
    Thm 4.3) only.
- **SC1.8 (L), fixed.** Adusumilli is described at its parts of arXiv v16, in Closest known and
  Context: (5.8) §5.4 is one-armed and parametric, with sharpness "left for future research"; (6.2)
  §6 is one-armed and nonparametric; §7 says "the paper only proves a lower bound"; §2.4 works
  "under a minimax theorem"; v1 §2.3 says "an open question". KK23 is added (Corollary 3.5;
  symmetric means summing to one), and HP23 is described at Thm 2.

### Proof defects left from the first part

- **PF1.6 (L)**: fixed now (see above).
- **PF1.9 (P)**: the cited nodes for textbook results (Skorokhod's embedding [Bil95 §37],
  martingale representation [KS91], FCLT [EK86], Skorokhod representation [Bil99], Lusin [Kec95],
  randomization [Kal02], Schwarz, the killed-BM expansion, the sech series) are not added. The books
  were not read here, so their statements cannot be copied verbatim. The citations are marked
  "(to be checked)". It is a P defect.

### Dead ends

- The book LS as a whole PDF overflows an agent's context. Narrow prompts through a text reader
  (r.jina.ai) worked.
- Kol25, Fan53, ACFS02 and the Bather and Vogel papers: no readable full text was reachable
  (timeouts, refused access, compressed PDFs). Their numbers are cited through papers that quote
  them (Kol17, KNS17, GMS19), and this is said in the text.

## 2026-11-15, repair (role revise, failed build and branch behind main, Claude Opus 5.5)

- **Build failure, fixed.** The check "Library metadata" (`certify.py check --base origin/main`)
  failed on `roadmaps/BatchedBandits/directions.md` ("entries were removed or reordered", "C1/C2
  was edited"): `main` had added candidate directions to that file after this branch forked, so
  the stale copy on the branch read as a removal. This paper never touched that file. Fix: rebase
  on `origin/main` (04c4a8e).
- **Conflicts of the rebase**: `literature/bibliography.json` and `literature/index.md` (entries
  added or updated both by P002 on `main` and by this paper). Merged key by key against the merge
  base (b5ac8df): no key was changed on both sides, so the result is the union, sorted by key as
  before, with `index.md` in the order of `bibliography.json`.
- `paper.tex`, `refs.bib` and `META.toml` are unchanged; no node changed.

## 2026-11-15, revision round 2 (role revise, Claude Opus 5.5)

Answers to the reports of `referee-scope` (SC2.*) and `referee-proofs` (PF2.*) on head `8628a22`. Branch rebased on `origin/main`
(e465809, candidate directions of P002; no conflict). Targeted edits only. No statement of the owner changes in content. Part (c) of
`prop:four` moves to a new node (PF2.2). New nodes: `cor:four-c`, `lem:K2-cell`.

### Proof defects

- **PF2.1 (G), fixed** (`thm:bounds`, proof of the upper bound). The referee is right: LS19's minimax regret is an infimum over all maps
  from histories to laws on the arms, not necessarily measurable in the signals, so it does not bound an infimum over Borel policies.
  The fix is the referee's Option 1. Take a policy π of LS19 that is η-close to √(2KT), and feed it the losses
  b_t = 1{V_t ≤ 1 − x_t}, with V_t uniforms drawn from U. Its histories are then finite, so the induced policy π̃ (actions drawn by
  inversion at W_t) is Borel. Given the table b_{t,k} = 1{V_t ≤ 1 − Y_{t,k}}, which is independent of W, the actions are those of π
  against an oblivious binary sequence. E b_{t,A_t} = 1 − E μ_{A_t}, because A_t is independent of (V_t, Y_{t,·}). So
  R_T(π̃,ν) ≤ √(2KT)+η, and η → 0. One shared uniform per round suffices: the marginal of each b_{t,k} is all the argument uses.
  The gloss after `cite:LS19-Thm6.1` now quotes the definition of a policy. Option 2 (ZL19) was not taken: it would replace a read
  cited theorem by another one, for the same bound.
- **PF2.2 (P), fixed.** The former `prop:four`(c) is the new node `cor:four-c`, stated after `prop:u-local`, with the old proof block
  (`\proves{cor:four-c}`). `prop:four` keeps the letters (a), (b), (d), and a sentence after it explains the change. The references
  are updated: Contributions, `lem:embed`, `rem:g-c`, the opening of sec:app-game and sec:app-upper, and `\uRG`. A `\uses`-graph
  script (statements and proofs, `\proves`-aware) finds 74 nodes, no unknown label and no cycle.
- **PF2.3 (P), fixed.**
  - (1) `lem:g-UA` is added to the proof of `lem:g-step`.
  - (2) The statement of `prop:K2` now uses def:K2-inf, prop:K2-Lnum, prop:K2-Unum and lem:K2-series. Its proof uses cor:examples
    and has the line for rewards in [0,1]: ½·0.634171 = 0.3170855 and ½·0.747721 = 0.3738605.
  - (3) The statement of `lem:K2-cost` uses lem:K2-gauss.
  - (4) The statement of `thm:main` uses thm:lowEF and prop:lowtilt (no cycle).
  - (5) In `lem:g-min`(iii), "the infima ... are attained".
- **PF2.4 (P), partly fixed.**
  - Hoeffding's lemma is a Mathlib fact, `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc` (Mathlib/Probability/Moments/SubGaussian.lean,
    checked in `.lake`). It is named in the proof of cor:examples, so it needs no node (AGENTS.md 5.2).
  - Fan's Theorem 2: see SC2.5.
  - **Not done:** cited nodes for the textbook results of PF1.9, because the books were not read.
- **PF2.5 (P), fixed.**
  - New node `lem:K2-cell`, in exact arithmetic. With r_J the truncated series and ε_J the remainder bounds of lem:K2-series, it gives
    r ≤ r_J + ε_J, and on a cell [v,w] ⊂ [0,4], sup r ≤ max(r_J+ε_J at v and w) + (2+16√S)(w−v)/2. The proof uses the Lipschitz
    bound, and the minimum of two affine functions is at most their value at the crossing point. Step 1 of prop:K2-Unum now uses it.
  - A paragraph after prop:K2 lists the exact nodes: lem:K2-box, prop:K2-relax, prop:K2-Lnum(i), lem:K2-conv, lem:K2-cell and
    lem:K2-tail. It says that (H_fp) covers only the two numerical inequalities, and that prop:K2 itself is not a statement to formalise.
- **PF2.6 (P), fixed.** A new item of the conventions, "Limits": thm:main, thm:bounds, cor:four-c and cor:examples are written with
  lim, while their quantitative forms (thm:lowEF, thm:u-upper, the non-asymptotic half of thm:bounds) are eventual inequalities.

### Scope defects

- **SC2.1 (L), fixed.**
  - An agent read parts of the four papers to which Kol16 §III credits the limit, in the Russian originals (English for MMAS'14), through
    r.jina.ai and the extraction tool (short quotations). New notes and entries: Kol12, Kol14, Kol14a, Kol15. What they show:
    - Kol12, Thm 2: two-sided bounds only, with "minimax = Bayes" taken from the author's earlier papers ([8] ARC 72(5) 2011 and
      [9] ALCOSP 2010, not read).
    - Kol14, Thm 3: states the local limit (verbatim in the note) and proves it in an appendix, from "the minimax risk equals the Bayes
      risk on the worst prior", taken from the main theorem of game theory.
    - Kol14a: no limit theorem; Lemmas 2–3 "without proof".
    - Kol15: the values 0.634 and 0.637 are "preliminary"; the reasoning is "non-rigorous"; Thm 2 proves the threshold form.
  - "Two arms" (Closest known) now has an item for these papers. The conclusion says what it rests on (Kol17, Kol16, Kol20, and the parts
    of the 2012–2015 papers that were read).
  - Attribution, first item: updated.
  - The ask-owner question of the referee (can the owner provide these papers?) stays open for the page images.
- **SC2.2 (L), fixed.**
  - (i) Attribution, screening item: Kol20 §2 (Theorem 2, Corollary 1; Lemma 1 uses Vogel's idea) and Kol16 §IV ("modified Vogel's
    strategy", numerical) are credited as the two-arm ancestors of Stage 1 and of the reduction. "Source not known" is kept only for
    the K-arm, gap-free form with variance equalization.
  - (ii) An agent read AB09 §1 ("(and thus also in the stochastic case)", crediting Auer et al. 1995). It is cited in the proof of
    thm:bounds and in Attribution. The other AB09 citations are no longer "(to be checked)": Theorem 5 (49√(nK)) and MOSS in §3 were
    read.
  - The randomized rounding: credited to the referee; no earlier source was searched for.
- **SC2.3 (L), fixed.** def:K2-tc is Vogel's threshold strategy (turn by turn until the difference of the total incomes exceeds
  α(DN)^{1/2}, then commit), as described in KNS17 Thm 1 and Kol16 §I, with a clock limit added. This is said in Attribution and in
  Previous best values.
- **SC2.4 (L), fixed.**
  - An agent read arXiv 2609.22690 (key LWKW26) §5.2. For K ≥ 2, the Bernoulli instances of CBL06 Thm 6.11 imply
    inf sup R_T ≥ (√2−1)√(KT)/√(32 log(4/3)) > 0.1365√(KT). The regret there is pseudo-regret, and no condition on T is stated.
  - CBL06 itself was not read: there is no open copy, and no verbatim statement was found. It is cited "(to be checked)".
  - Previous best values: the bound gives V_K ≥ 0.2730√K. thm:bounds is weaker at K=2 (0.2256 < 0.386), barely larger at K=3
    (0.491 vs 0.473), and larger for K ≥ 4, by a ratio increasing to κ/0.2730 ≈ 3.31. These numbers were recomputed this session.
  - Main result (c) now says that thm:bounds exceeds this constant only for K ≥ 3.
- **SC2.5 (L), not resolved (source not accessible).**
  - PNAS, both PMC hosts, Europe PMC (HTML, PDF, REST), JSTOR, Unpaywall and Semantic Scholar were all tried again: none gave the text.
  - Found instead: Fan's NBS Report 2104, "Minimax theorems" (10 Dec 1952), on archive.org (key Fan52, note Fan52.md). Its Theorem 2
    was read only through OCR: the opening sentence is verbatim, the rest paraphrased. It agrees with the statement recalled in
    prop:four(a). The proof of prop:four(a) now points to it, "(to be checked)".
  - No `cite:Fan53-Thm2` node: a node needs a verbatim statement from the source.
  - Alternative read in part, also through OCR: Sion 1958 (note Sio58.md, Thm 3.4 and its corollary). It would apply with the finest
    locally convex topology on finitely supported signed measures (every linear functional is continuous). Not used: its hypotheses
    ("convex spaces") were not seen on the page images.
  - **For the owner:** a scan of Fan (1953) pp. 42–47 would close SC2.5.
- **SC2.6 (P), fixed.** The remark after thm:bounds and the dashed curve of panel (b) are now called conjectural illustrations.

### Dead ends

- WebFetch returns at most about 125 characters of verbatim quotation, so long statements (Fan52 Thm 2, the Sion theorems) cannot be
  copied verbatim through it.
- curl was not available in this sandbox.
- dblp is behind bot protection; sbubeck.com refused the connection.

## 2026-11-16, revision round 3 (role revise, Claude Opus 5.5)

Rebased on `origin/main` (8360bdd); the conflicts in `literature/index.md` and `literature/notes/GMS19.md` were resolved as in
the earlier merge d016d89 (main had not changed these files since). The writing rules v1 apply: the paper was restructured to
the sections of AGENTS.md §5.2, keeping the owner's statements, proofs and appendices. No node was added, removed or relabelled
(74 nodes, `\uses` graph without cycle or unknown label, checked by a script); `cite:GMS19-Lemma1` and `cite:LS19-Thm6.1`
moved to the new appendix "Useful lemmas".

Order of the main text chosen (Ask-owner of SC3.3 not answered yet): Introduction (informal result with its constant on page 2,
contributions, outline) → Problem formulation → Main result (thm:main, page 5, every symbol defined before it) → The value of
the limit game → Policies → Two arms → How the proofs work → Related work and context → Numerical experiments → Conclusion →
Open questions → appendices. Related work comes after the results so that nothing is inserted between the owner's introduction
and setting and his results (CONTRIBUTING §8); only the Setting sits between them, as in the owner's draft.

### Scope defects

- **SC3.1 (G), fixed.** New `DOSSIER.md`: roadmap correspondence (D19 (a)–(c), what is not given, the ten acceptance criteria one
  by one, conventions changed), Closest known (K20–K24, K33, K37, the published bounds, Vogel/Bather/FvZ70, Kolnogorov line by line
  with the derivation attempt, diffusion asymptotics, the lower-bound technique), Sanity checks (moved), Weak points (moved,
  updated), Searches (rounds 1–3 with dates), Reading notes (what was and was not read, the caveats the paper used to print).
- **SC3.2 (R), fixed.** Removed from `paper.tex`: the paragraph "Roadmap items", Section "Closest known", Sections "Sanity checks"
  and "Weak points", the paragraph "Searches", every "(to be checked)", every admission of reading, "suggested by the proof
  referee", "the first version", "the author's manuscript", the sentence on graphics, the path of the author's machine. The open
  questions carry `\extends{D19}` (and `D5` for oq:anytime) instead of the ids in the text. Only the `\author` footnote still
  names "direction D19": the `\author` line of an owner's paper may not be changed.
- **SC3.3 (R), fixed.** thm:main now comes after all its definitions (Section 3, page 5), with the informal result and its
  constant on page 2; new Section "How the proofs work" (`sec:overview`): the three parts with the key results by number, how they
  combine, where the difficulty lies (three steps), and a map of the appendices; `\appendix` before the old Section 5; new appendix
  "Useful lemmas" (`sec:cited`); new Section "Related work and context" (`sec:related`) with a comparison table (Table 3) and,
  for each closest work, why it does not give thm:main; Section 4 renamed "The value of the limit game".
- **SC3.4 (L), fixed.** Every citation now rests on a read part, cites a read secondary source at its part, or is "see also":
  1/20 through GMS19 App. B.1 (ACFS02 "following the original proof of"); 0.612/0.752 through KNS17 Thm 1 and Kol17 (3)
  (Vog60, Bat83 "see also"); CBL06 through LWKW26 §5.2; Kol25 for the existence of a three-armed example only (abstract);
  Man87, EKNJ87, Kie57, Hal69, Ste56, Obl04, DP16, FG21, KW24, KZ21, CB97, Cov66, GPS16, BEZ20, BCZ97, BP13, Rod78: "see".
  Textbook facts (KS91, RY99, Kal02, Kec95, Bro86, EK86, Bil95, Bil99, RH17) kept, without "(to be checked)". Fan52/Fan53 no
  longer cited (SC3.5).
- **SC3.5 (L), fixed by the alternative the referee proposed.** prop:four(a) now uses Sion's minimax theorem as proved in Mathlib,
  `Sion.minimax'` (`.lake/packages/mathlib/Mathlib/Topology/Sion.lean`, read this session): X nonempty convex compact in a real
  TVS E, Y convex in a real TVS F, f(·,y) lsc and quasiconvex on X, f(x,·) usc and quasiconcave on Y, values in a complete
  densely ordered linear order (EReal); then inf sup = sup inf. Choices: E = finite signed measures on Ω with the weak topology
  σ(M, C_b) (locally convex; induces weak convergence on P(Ω), so W is compact there by lem:g-compact); F = finitely supported
  signed measures on R^K with the initial topology of the linear maps ℓ_Q(Π) = Σ Π({h}) r(Q,h), Q ∈ W (a vector topology; each
  ℓ_Q continuous by construction, hence f(Q,·) usc). Nonemptiness of W by lem:g-disc (added to the proof's `\uses`). By
  AGENTS.md §5.2 a Mathlib fact needs no node; Sio58 is cited as the original source.
- **SC3.6 (L), fixed.** Kol11 read (Russian original, through r.jina.ai and an extraction tool; note `Kol11.md`, new entries in
  `bibliography.json` and `index.md`). Theorem 1: the finite-horizon two-armed game (unit-variance Gaussian, compact
  Θ = {|m1−m2| ≤ 2c1, |m1+m2| ≤ 2c2}) has a value over all randomized strategies; argument: compact metrics + uniform continuity +
  Borovkov 1984. No limit in N. Kol12 and Kol14 take R^M_N over all strategies on Θ_N, with a restricted class only inside the
  sandwich bounds (from the notes). Consequence: the claim "Theorem 1.1 proves Kolnogorov's claim" is removed; Section 8 says that,
  as far as we can tell, Kol11 + Kol14 Thm 3 + Kol20 §2 give the K = 2 unit-variance Gaussian limit, that we did not check the
  proofs, and what thm:main adds (every K, every regular class, the game and its minimax theorem, uniform lower bound, a policy).
  The reader agent observed that Kol11's compactness step ("bounded and complete implies compact" for a weighted L¹ distance) does
  not hold as written in infinite dimension: recorded in DOSSIER.md only, as an unverified observation.
- **SC3.7 (L), fixed.** AG12 read (PMLR PDF, pp. 39.1–39.5; note `AG12.md`; Read column of `index.md`). The rounding is in
  **Section 1.2, Algorithm 2** of the PMLR version (the referee's "§2" is the proof-technique section); credited there in the proof of
  thm:bounds and in Sources of the techniques; "its use to obtain a Borel policy: source not known". The referee is no longer named.
- **SC3.8 (P), fixed** by the rebase (the reader build prints no `Uses:` line).
- **SC3.9 (P), fixed.** natbib with `plainnat`, `\citet`/`\citep` with loci; Kol11 and AG12 added to `refs.bib`; the two cited
  nodes moved to `sec:cited`, titled "From \citet[...]{KEY}, ...", with one sentence on what each is for and the renaming line.
- **SC3.10 (P), fixed.** Abstract of about 190 words, without citations or author names.
- **SC3.11 (P), fixed in part.** Figure 1 included (`notebook/experiences.pdf`, 39 kB, made by `notebook/figures.py`, which now
  writes into the notebook; the dashed curve's label says "conjectural"). The appendix "Experimental details" says how to
  reproduce the figure and where the runs are. Not fixed: the script of the threshold table (`table_seuils.py`) and its output
  `seuils_K2.npz`, read by `simulations.py`, are not in the repository (they are on the author's machine); only their printed
  output `table_seuils_sortie.txt` is. Ask-owner in the summary.
- **SC3.12 (P), fixed.** "certified" is defined once at the head of the appendix on two arms (proved in exact arithmetic from the
  output of a run, under (H_fp); not an interval enclosure); the titles of prop:K2-Lnum, prop:K2-Unum, def:K2-inf and of that
  appendix no longer say "certified"; the main text no longer uses the word.
- **SC3.13 (P), fixed.** The chain of lem:K2-cell and the expectation computation of the upper bound of thm:bounds are displayed in
  `align`, one step per line with its reason.
- **SC3.14 (P), fixed.** prop:four now prints its items (a)–(c) (the invariances are (c)); every reference is updated; the history
  sentence and the history in the title of cor:four-c are gone.

### Proof defects

- **PF3.1 (P), fixed** in both places: "a Borel map carrying the uniform law on [0,1] to the uniform law on [0,1]^{2T} (for
  instance, interleaving the binary digits)", and the same with [0,1]^T in the conventions of the upper-bound appendix.
- **PF3.2 (P), fixed.** (1) prop:K2 statement `\uses` cor:examples; (2) prop:K2-Unum statement `\uses` lem:K2-rho, lem:K2-series,
  lem:K2-conv; (3) the "Limits" convention no longer lists thm:bounds among the results stated with limits (it names the remark
  after it).
- **PF3.3 (P), fixed for Fan** (Sion through Mathlib, above). **Textbook facts: disputed** — AGENTS.md §5.2 allows facts at the
  level of a textbook that Mathlib or LML provide to be used by name without a node, and the scope referee rates them classics.

### Dead ends

- None new in the mathematics. The direct fetch of the Kol11 PDF timed out; r.jina.ai worked but returns short pieces.
