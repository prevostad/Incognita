Not refereed: working notes of the authors of P003-transfer-setting.

# 2026-11-15, write-paper, claude-opus-5-5

## Item

TransferBandits, F0 (the setting, kind `definitions`): first open item not covered
(`.agents/items.md`: F0 open; no open pull request serves it; P002 serves D8 only). Roadmap
approved 2026-11-14, KNOWN.md reviewed 2026-11-14.

## What the roadmap asks

Definitions table: source data (size $N'_k$ random, chosen by a strategy; first $N'_k$ values of an
i.i.d. stack read before round 0), transfer learner (an LML algorithm whose initial state is the
source data), drift condition $\mu_k-\mu'_k<L_k$, consistency = the class $\mathcal C_L$ of
arXiv:2610.21582 copied from the paper. A definitions paper: basic properties, witness and
exclusion for each, relations.

## Reading of the source (PMRM26, arXiv:2610.21582v1, HTML)

- §3.2: prior counts may depend on $T$, may come from an online game; the strategy $\pi'$ is
  unknown; $(N'_k)_k$ independent of the target $\nu$; bound $|\mu_k-\mu'_k|<L_k$ (strict).
- §4.2: $\mathcal P([0,1])_L$ uses $|\mu_k-\mu'_k|\le L_k$ (non-strict), and $\mathcal C_L$
  quantifies over "every prior strategy $\pi'$" (never defined formally). Theorem 2 assumes the
  prior strategy "comes from a bandit game played over $T'=f(T)$ rounds".
- The proof of Theorem 2 is in Appendix E (Lemma 22). **Could not be read**: the HTML text returned
  by the fetch tool stops inside Appendix C; the PDF could not be rendered (no poppler) and
  `pdftotext` needs a shell pipeline that is not allowed here. Only the sentence of §4.2 on
  Lemma 22 ("depends on the source sample size only through the expectation") was read.

So two mismatches to handle in the paper: strict vs non-strict, two-sided vs one-sided (pinned
convention), and the undefined "prior strategy".

## Modelling decisions

1. Source strategy = a *size rule*: $N':\Omega'\to\mathbb N^K$ with
   $\{N'=n\}\in\mathcal G_n:=\sigma(U',X'_{k,j}:j\le n_k)$ for every $n$. This is the stopping point
   of the $K$-parameter filtration. It contains deterministic sizes and prior bandit games (and
   games stopped at a stopping time). Chosen as the *largest* natural class for which the
   divergence decomposition holds: this makes $\mathcal C_L$ smallest, so learners proved to be in
   it are robust; lower bounds for $\mathcal C_L$ are then the weakest, but Theorem 2 of PMRM26 only
   needs the strategy at hand.
2. Law of the game defined as a composition product $P^D\otimes\kappa^T_{\pi,\nu}$ (not on an
   explicit stack space for the online phase): the chain rule applies at once and this encodes the
   independence requirement of §3.2.
3. $\mathcal C_L$ read literally: all pairs of $\mathcal P([0,1])_L$ (no unique optimal arm),
   "suboptimal" = $\mu_k<\mu^\star$, learner not depending on $T$, strategy depending on $T$.

## Main result chosen

The divergence decomposition
$\mathrm{KL}(\mathbb P,\tilde{\mathbb P})=\sum_k\mathbb E N'_k\,\mathrm{KL}(\nu'_k,\tilde\nu'_k)+\sum_k\mathbb E N_k(T)\,\mathrm{KL}(\nu_k,\tilde\nu_k)$
for every size rule with $\mathbb E N'_k<\infty$, and its failure for a look-ahead rule. It is what
the setting must deliver (the change of measure of K2 rests on it), and it justifies the
admissibility condition (the exclusion).

Proof route: (i) law of $D$ on each slice $\{n\}\times\prod[0,1]^{n_k}$ is
$g_n\cdot\bigotimes\nu_k'^{\otimes n_k}$ with $g_n\in[0,1]$ independent of $\nu'$ (Doob–Dynkin +
independence of $U'$ and the stacks); (ii) Wald: $\{N'_k\ge j\}^c\in\sigma(U',\text{other stacks},
X'_{k,<j})$, independent of $X'_{k,j}$; (iii) density of $P^D$ w.r.t. $\tilde P^D$ is the product of
the per-sample likelihood ratios; $\mathrm{KL}=\int\log R$, split into positive and negative
parts, negative part integrable since $\int(\log r)^-d\nu'\le 1/e$ and $\mathbb E N'_k<\infty$;
(iv) chain rule for the composition product + LML's divergence decomposition for each fixed $s$.

## Dead ends / things not done

- Tried first to require only $\mathbb E N'_k<\infty$ under the alternative too: not needed. Tried
  to drop $\mathbb E N'_k<\infty$: the split $\int F^+-\int F^-$ needs one side finite; with
  $\mathbb E N'_k=\infty$ the negative part may be non-integrable. Kept the hypothesis (bandit games
  over $T'$ rounds have $N'_k\le T'$).
- Considered proving $\mathcal C_L\subsetneq\mathcal C^{\rm det}_L$ (consistency against
  deterministic sizes only): a learner using fixed-$n$ confidence bounds on the source should be
  consistent for deterministic sizes and fail against a size rule that stops when the source of the
  optimal arm looks bad (needs a huge number of source samples, by the LIL). But with drift allowed
  and $\mathcal P([0,1])_L$ closed, the construction is delicate (the learner must also be consistent
  when $\mu'_1+L_1=\mu_1$). Left as an open question.
- Whether every size rule is, in law, a randomised sequential game: this is the question of
  randomised stopping points and optional increasing paths (a search found an EPFL thesis on
  "Randomization in the two-parameter optimal stopping problem"; not read). Left as an open
  question; it decides whether $\mathcal C_L$ depends on the choice "size rules" vs "bandit games".

## Numerical experiments

`check_decomposition.py` (output `check_decomposition.txt`): exact enumeration with Bernoulli
sources, $K=2$. Identity holds to $10^{-15}$ for a greedy prior game over $T'=5$ rounds and for a
game stopped at the first 1; fails for the look-ahead rule, with $\mathrm{KL}=2\,\mathrm{kl}(p,q)$ and
$\sum\mathbb E N'\mathrm{kl}=(2-p)\,\mathrm{kl}(p,q)$, as computed in the paper.

## Web queries (2026-11-15)

1. "bandit lower bound offline data collected adaptively KL divergence decomposition expected
   number of offline samples" → Agrawal, Juneja, Shanmugam, Suggala, arXiv:2306.09048 (BAI with
   offline data from an unknown adaptive policy, same instance; lower bound with
   $\mathbb E[N^o_a]+\mathbb E[N_a]$, offline term asserted in the expectation of the LLR, App. B.1
   (10)); Cheung–Lyu arXiv:2405.02594 (fixed offline sizes); Kausik et al. arXiv:2405.17324 (chain
   rule with offline data, latent linear bandits).
2. "Wald identity log-likelihood ratio adaptively sampled data stopping multi-armed bandit
   divergence decomposition random sample size" → KCG16 (Wald's lemma for the LLR at a stopping
   time, §2), follow-ups.
3. "warm-start bandit historical data lower bound change of measure historical samples policy
   unknown regret lower bound" → SJ12 (upper bounds only), warm-start papers; no change of measure
   with an unknown logging policy.
4. "multiparameter stopping point optional increasing path sequential allocation likelihood
   factorization independent of parameter" → two-parameter stopping (EPFL thesis), likelihood
   principle under optional stopping (not read).
5. "Transfer Learning in Bandits from Unknown Adaptive Policies Prevost lower bound change of
   measure" → PMRM26 itself; Lemma 22 mentioned in §4.2.
6. "selection bias adaptively collected data likelihood principle bandit data likelihood ignorable
   adaptive design" → Nie et al. AISTATS 2018 (bias of sample means of adaptively collected data;
   not read), inference papers.

## Reread (same session)

- Removed two overclaims: "size rules are exactly the class for which the decomposition holds"
  (not proved: only "holds for all size rules" and "fails for one size map that is not a rule").
- Closest known, honest derivation: for prior bandit games, the inequality "<=" (all a lower bound
  needs) follows from the 2K-armed divergence decomposition [GMS19 (8)] plus data processing; the
  equality also follows by sufficiency (the likelihood ratio of the ordered prior history is a
  function of D). So for bandit-game sources the content is known in a page; what the paper adds is
  the general class (size rules), the exclusion, and the setting itself (F0 is a definitions item).
- KCG16: Wald's lemma is in Appendix A (proof of Lemma 19, (18)), not in §2; checked on the arXiv
  v2 HTML.
- An independent proof read was requested from a sub-agent (answers below if it arrives in time).

## Independent proof read (sub-agent, same session) and answers

No F, no G in a formal node. Answers:
- D1 (L, lem:online-kl): LML's `klDiv_map_history_bandit` is for infinite-horizon sequences with
  rewards in R: the proof now extends sigma beyond T, embeds [0,1] in R, applies the lemma to
  `trajMeasure`, and identifies the law of the first T rounds with Q^T by induction.
- D2 (L, sanity): "same law on an unsampled arm under both instances" was false (the decision to
  sample arm 1 may read other stacks); reworded.
- D3 (G, oq:sequential): equality claimed for all size rules from a hypothesis on bounded ones;
  now stated for the class with bounded size rules.
- D4: the 1/e bound is now a node, `lem:kl-neg`. D5: weak point 3 corrected ((log R)^- is always
  integrable; only F^- may fail); the truncation idea for E N' = infinity recorded, not written.
- D6-D14: uses of cor:fundamental, lem:learner-exclusion restated without "deterministic first
  action", "Four points", weak point 1 (the propositions hold for both readings), E N' < infinity
  in the introduction, Dirac masses defined, prop:classes(b) phrased by the definition, quantifier
  on nu'_2..nu'_K in thm:main(b), full Lean name of the chain rule.

## 2026-11-15, repair (opus): failed build, branch behind main

- CI "Build and check" (Library metadata) failed: `certify.py check --base origin/main` reported
  `roadmaps/TransferBandits/directions.md` entries C1-C3 "removed or reordered / edited". The
  branch never touched that file: `main` had added entries (#26, #27) after the branch was cut, so
  the branch's older copy looked like a removal. Fixed by `git rebase origin/main` (no conflict).
- After the rebase: `certify.py bib` and `certify.py check --base origin/main` pass; the paper
  compiles (14 pages, no error, no undefined reference, no duplicate label). `paper.tex`,
  `refs.bib`, `META.toml` unchanged: no node changed.

# 2026-11-16, revise (round 1 answers, continuing the incomplete session of 2026-11-15), claude-opus-5-5

The session of 2026-11-15 (revise) stopped after the literature commit (entries R76, SGJC13,
FDS18, M86, KM98, W44, BW88, CW75, W81, GR97, GLR97; PMRM26 Appendix E and Lemma 22 read in the
arXiv e-print). This session wrote the revision. The branch was already on `origin/main`: no
rebase needed.

## Rules of 2026-11-15

`paper.tex` restructured to the order of AGENTS.md 5.2 (intro, related work with a comparison
table, problem formulation, main result, basic properties, proof overview, examples, conclusion and
open questions; appendices: useful lemmas, proof of the theorem, proofs of the properties, sources
of the techniques, notation); author-year citations (natbib, plainnat); link macros (`\dt`, `\sy`)
for the main symbols; the sections Closest known, Sanity checks, Weak points, Searches and the
roadmap paragraph moved to the new `DOSSIER.md`; no KNOWN id, roadmap id (outside `\extends`) or
"(to be checked)" left. Every node keeps its label and its statement; statements moved to the main
text and proofs to the appendices.

## Answers

- SC1.1 (G, novelty claim): fixed. Related work has a paragraph on ignorability (R76, SGJC13 Def. 2
  and Thm 1, FDS18 Thm 1) and one on multiparameter processes (M86, KM98; CW75 see also); "Gap with
  the literature" gives the honest route (ignorability gives `lem:source-law`, Wald gives
  `prop:source-kl`, the chain rule gives (a)) and claims no new idea for the identity; what remains
  is the unbounded case with E N' finite, the writing in the transfer setting and the MNAR instance
  (b). DOSSIER Closest known has the derivation attempt. The old sentence "What this route does not
  give is the class of size rules" is gone.
- SC1.2 (L): fixed. Wald's identity credited to W44 (a classic) and to KCG16 (18) for the bandit
  use (Related work, Appendix D, remark after `lem:wald`).
- SC1.3 (L): fixed. Size rules and `lem:prior-game` credited to M86 and KM98 (allocations are
  stopping points), with CW75 as "see also" (unread).
- SC1.4 (L): fixed. Factorisation credited to ignorability (R76, SGJC13, FDS18), with BW88 as "see
  also" for the stopping-rule principle (unread); the look-ahead map described as a mechanism that
  is not missing at random (R76).
- SC1.5 (L): fixed. Divergence decomposition credited to KCG16 Lemma 1, and to GMS19 (8) for the
  identity form.
- SC1.6 (P): addressed. Searched (DOSSIER, Searches, 2026-11-16) and read Merzbach 1983 (new entry
  M83): its Proposition 3, a result of Walsh, gives, in the continuous two-parameter quadrant under
  (F4), an optional increasing path from the origin to every finite stopping point. Our filtration
  satisfies (F4) for K = 2 (the stacks are independent, U' is common). So `oq:sequential` is
  restated for K >= 3, with the K = 2 case pointed to that theorem (its transfer to the discrete
  quadrant not written by us).
- SC1.7 (P): fixed (the clause on who read PMM25 is removed).
- SC1.8 (P): fixed. Lemma 22 of PMRM26 read: an identity, for a prior bandit game over T' rounds
  written with the online game as one game of T'+T rounds, the observation being the ordered
  history I_{N+1}, under absolute continuity of both pairs. Paper: Closest related work, Table 1,
  Appendix D; a new point in "Reading of the source": PMRM26's learner sees the ordered prior
  history, ours sees D.
- PF1.1 (P): fixed. `\uses` completed in the proofs of `lem:prior-game` (def:source-space),
  `lem:learner-exclusion` (def:source-space, def:size-rule), `prop:drift` (def:instance,
  def:laws), `prop:witness` (def:instance), `prop:exclusion` (def:drift, def:game, def:instance,
  def:laws) and `cor:fundamental` (def:game, def:source-data).
- PF1.2 (P): fixed. New node `lem:lml-history` (the clamp c, sigma-bar := sigma composed with c,
  nu-bar, the inclusion iota_T; the law of the first T rounds of an LML algorithm-environment
  sequence is the image of Q^T by iota_T, by induction). The proof of `lem:online-kl` now uses it,
  with the invariance of KL under iota_T (left inverse c). The old step "extend sigma beyond T" was
  unnecessary (sigma is already indexed by every t >= 1) and is dropped.
- PF1.3 (P): fixed. A paragraph after `def:laws`: the integral exists in [0, infinity] by
  `lem:kl-neg`, and KL equals Mathlib's klDiv.
- PF1.4 (P): fixed. Example `ex:all`: the round-robin pulls the arms in the order 1, 2, 1, 2, ...

Nodes changed: `lem:online-kl` (proof), `lem:lml-history` (new), and the `\uses` lines of PF1.1.
The other nodes keep their statements and proofs (moved; the link macros change the source, not
the mathematics).

## New observation (fidelity)

PMRM26 Appendix E feeds the learner of the online phase with I_t, which contains the ordered prior
history and its randomisation; the roadmap's transfer learner ("an LML algorithm whose initial
state is the source data") sees D. Our class of learners is therefore smaller than PMRM26's for
bandit-game sources (a learner of ours is one of theirs). Theorem (a) is about the observation
(D, H_T); the propositions on C_L hold for both readings. Asked to the owner in the summary.

## Dead ends

- Tried to prove the K = 2 case of `oq:sequential` directly on the lattice (at each point m of the
  path, choose a direction d with m + d <= N', measurably in G_m): the event {N'_1 > m_1} is not
  obviously G_m-measurable on {N' >= m}; Walsh's argument (as reported by Merzbach) uses (F4) and
  the two extreme paths. Not written; the question is restated for K >= 3 instead.

# 2026-11-16 (afternoon), revise (round 2 answers, continuing the incomplete session), claude-opus-5-5

The session of 2026-11-16 that answered round 1 was pushed as `223839483544`. The session that
followed it stopped before writing anything: the head had no answer to the round-2 reports
(`referee-scope` SC2.1–SC2.6, verdict major; `referee-proofs` PF2.1–PF2.2, verdict accept). This
session answers them. The branch is on `origin/main` (no rebase needed).

## Answers

- SC2.1 (L): fixed. MV81 was found as a scan with an OCR text layer on R. J. Vanderbei's publication
  page and read in full (index.md). It defines predictable stopping points, the end points of
  policies (§1.3). Theorem 4 (§5.1): on N^2 under (F4), all stopping points are predictable, for
  one measure, with a proof by conditional expectations. §5.2: the cyclic non-predictable stopping
  point of three independent Markov chains. KS81 is not readable (ScienceDirect 403), so it is
  cited as "see also". Related work (multiparameter paragraph) and Appendix D now credit MV81 for
  the notion (`lem:prior-game`, `prop:stopped-games`(a)), for the K = 2 theorem and for the
  example; KM98 stays the source for bandits.
  Beyond the citation, the open question `oq:sequential` is now answered by a new node:
  - new `def:stopped-game`: a stopping time of a prior game, and the stopped counts;
  - new `prop:stopped-games`, with three parts:
    - (a) stopped counts are a size rule;
    - (b) K = 2: every bounded size rule is, pointwise and with one rule for all source laws, the
      stopped counts of a prior game;
    - (c) K >= 3: the cyclic rule is not, even in law, with randomisation.
  - Proof of (b). MV81's separation of A_m = {N'_1 = m_1, N'_2 > m_2} and
    B_m = {N'_1 > m_1, N'_2 = m_2}, made pathwise. A_m depends on (y, b) only and B_m on (y, a)
    only (y the data in the box of m, a and b the further values of arms 1 and 2). They are
    disjoint, and Omega' is a product, so the projections on y are disjoint. These are analytic
    sets, and the Lusin separation theorem (K95, Th. 14.7, a classic) gives a Borel separator S_m.
    The game pulls arm 2 on S_m, arm 1 off it, and stops at the first r with Y_{C(r)} in E_{C(r)}.
  - Proof of (c). Dirac sources (nu'_2 = delta_1, nu'_3 = delta_0 and its rotations) force
    N^cyc_k = 0 almost surely for each k in turn. The first step of a game (stop at 0, or pull arm
    k) is a function of U' alone, so its probabilities q_k do not depend on nu'. All q_k are then
    0, a contradiction.
  - `oq:sequential` is removed: no label is reused, and it was rated "not a candidate".
  - Notebook check `check_stopped_games.py` on binary stacks, exhaustive policy search:
    - K = 2: 4000 random size rules, all sequential;
    - K = 3: 138 of 4000 not sequential;
    - the cyclic rule is a size rule and not sequential.
- SC2.2 (P): fixed.
  - A paragraph "Formal libraries" in Section 3 introduces Mathlib and LML, with URLs.
  - Lean names go through `\leanfn`, a footnote printed in the blueprint build only, so the reader
    build has none (checked: no "Lean:" in its text).
  - UCB is credited to ACF02, as a classic (new entries ACF02 and K95), with LML for the formal
    version with the constants used.
- SC2.3 (P): fixed. The introduction has a paragraph saying that (1) is known for bandit-game
  sources (PMRM26 Lemma 22) and follows from ignorability and Wald in general, and what is added.
  The second contribution item says the same. "Games stopped at a stopping time are size rules" is
  now `prop:stopped-games`(a), with the stopped game defined (`def:stopped-game`).
- SC2.4 (P): addressed in part.
  - "Reading of the source" moved to the end of Section 5 (`sec:reading`).
  - `def:prior-game` and `def:stopped-game` moved to Section 5, beside the results that use them.
  - Related work tightened: the third "closest" bullet (FDS18) is dropped, since the ignorability
    paragraph and "Gap with the literature" cover it.
  - Section 4 now starts at the top of page 7. Earlier would need cutting the required Related work
    (with its table) or the definitions that thm:main uses (Sections 3.1–3.3, plus 3.4 for the
    class).
- SC2.5 (P): fixed. Link macros and anchors for N', rho, D, P^D, Q, kappa, N_k(T), mu_k, Delta_k,
  Omega', U', X', P', hat m', pi^sigma, N^cyc. A script replaced them in the body; the verbatim
  quotation of def:consistency is left unchanged. Every symbol of the Notation table is a link.
- SC2.6 (P): fixed. Step 2 of `prop:source-kl` is an align with the reasons on the right, followed
  by a sentence of conclusion. The identities in the statements of `lem:kl-neg` and `lem:wald` are
  displayed.
- PF2.1 (P): fixed. In the proof of `prop:witness`, a paragraph explains why the LML run of UCB is a
  run of sigma-bar: they agree on histories with rewards in [0,1], which have full measure. The
  `\uses` now includes `lem:lml-history`.
- PF2.2 (P): fixed. `lem:lml-history` has a second paragraph for the reading in LML:
  - observations in a one-point space;
  - the measurable bijection j_t that forgets them;
  - policy of index t-1 = sigma-bar_t o j_{t-1};
  - LML's history law is j_T^{-1} # iota_T # Q^T.
  Its proof has the corresponding paragraph. `lem:online-kl` uses the invariance of KL under
  j_T^{-1} and iota_T (injective with measurable left inverses).

Nodes changed:
- new: `def:stopped-game`, `prop:stopped-games`;
- statement: `lem:lml-history` (second paragraph; the first part is unchanged);
- statements displayed, not changed: `lem:kl-neg`, `lem:wald`;
- proofs: `lem:lml-history`, `lem:online-kl`, `prop:source-kl` (Step 2 displayed), `prop:witness`,
  `thm:main` (wording of the chain-rule sentence);
- moved: `def:prior-game` (to Section 5, unchanged);
- `prop:witness` statement: the UCB sentence now credits ACF02 (same algorithm, same claim).
Link macros change the source of most nodes, not their mathematics.

## Dead ends

- Using MV81 Theorem 4 directly for `prop:stopped-games`(b): its policy is built from conditional
  expectations under one measure P'_{nu'}, so it may depend on nu' and is defined only almost
  surely. Hence the pathwise separation by the Lusin theorem.
- Trying to separate A_m and B_m by an explicit Borel set ({y : the section of B' at y is empty}):
  that set is co-analytic, not obviously Borel. Projecting along the compact factor [0,1]^N does not
  preserve Borel sets in general. Hence the Lusin separation theorem.

# 2026-11-16 (evening), revise (round 3 answers), claude-opus-5-5

The branch conflicted with `main` (literature/index.md and bibliography.json: both sides added
rows). Rebased onto `origin/main`; the conflicts were resolved as main's file plus this branch's
added and changed entries (no entry was changed on both sides). Only `referee-scope` reported on
the previous head (SC3.1-SC3.5, verdict major); `referee-proofs` accepted in round 2.

## Answers

- SC3.1 (G, missing comparison with Robins-Gill and Gill-Robins 1997): fixed as far as the sources
  could be read.
  - RG97 (new entry) and GR97 could not be read beyond their abstracts: Wiley, Springer,
    ResearchGate and the Utrecht repository (handle 1874/1643, found through Semantic Scholar)
    refused access. Secondary sources read: Sun-Tchetgen Tchetgen (arXiv:1411.5310, section 3.1:
    no RMM counterexample there), arXiv:2611.16278 (RMM a proper subclass of MAR), Jaeger 2005
    (JAIR, section 4: the CAR analogue, a cyclic coarsening example on three outcomes).
  - The paper now says, in Related work and in a new paragraph "Sources of Proposition 5.5" after
    `prop:stopped-games`: with stacks of depth one, a size rule is a MAR mechanism
    (`lem:source-law`) and a stopped prior game an RMM scheme; RG97 state that some ignorable
    mechanisms are not RMM (GR97 "see also"); (c) is that phenomenon for size rules, a class
    between RMM and MAR, and we claim nothing new in (c) beyond its writing for size rules.
    Appendix D: the row of (c) credits Ber76 and MV81 for the pattern and the argument, RG97 and
    GR97 for the in-law randomised version for MAR mechanisms, "written here for size rules". The
    abstract and the introduction say "a classical cyclic example".
  - The point that matters for the comparison: size rule implies everywhere MAR (lem:source-law),
    but not conversely in an obvious way (a size rule needs the event {N'=n}, not only its
    conditional probability, to be in G_n). So RMM is contained in size rules, which are contained
    in MAR; (c) separates the first two with a deterministic size rule. Whether RG97's example is a
    size rule is unknown to us.
  - Two variables (bearing on (b)): every everywhere-MAR mechanism on two variables is RMM, by the
    explicit scheme written in DOSSIER.md (Closest known). Not in the paper.
  - KS81: kept "see also"; DOSSIER says it was not checked whether its conditions settle (b), (c).
- SC3.2 (L, Berry's Gustave function): fixed. Ber76 is open on Numdam and was read (section II.2,
  OCR text layer; Proposition II.2.2(b), p. 57; the OCR garbles the third equation, Curien gives
  the cyclic form). New entries Ber76 (with a note) and Cur03 (read pp. 5-6 of arXiv v1). The
  correspondence is written in the paragraph after `prop:stopped-games`: the three minimal inputs
  of G(1,0,bot)=G(bot,1,0)=G(0,bot,1)=1 read exactly the arms observed by N^cyc on its first three
  cases, and Berry's argument (no critical index at (bot,bot,bot)) is ours.
- SC3.3 (P): fixed. The align of Step 2 of `prop:source-kl` has short reasons (the first relation
  on two lines), with the longer justifications in a sentence below; the integral in the proof of
  `lem:mixture` is displayed; the "Goal" of `prop:source-kl` is displayed and its Idea reworded.
  The log has no overfull box above 4pt left.
- SC3.4 (P): fixed. Theorem 4.1 now starts on page 5 (it was on page 7). Table 1 and the detailed
  comparison bullets moved after the theorem ("Comparison with the closest results"); Related work
  keeps one sentence per closest result and the "Gap" paragraph. Related work, the introduction and
  the abstract were tightened; the "Formal libraries" paragraph moved to Section 6; the remark on
  the stack realisation of the online phase moved to "Reading of the source" (sixth point).
- SC3.5 (P): fixed. The proof of `prop:stopped-games`(b) starts with an Idea paragraph.

Nodes changed: none in their mathematics. `prop:stopped-games`: proof (Idea paragraph added) and
the discussion after it. `prop:source-kl`: proof (display of Step 2, Goal). `lem:mixture`: proof
(display). `prop:witness`: statement wording ("the Lean library LML (Section 6)"). The rest is
text between nodes.

## Dead ends

- Reading the counterexample of RG97/GR97: every full-text copy found refused access (see above).
- Bringing thm:main to page 5 by trimming text alone: it stayed at the top of page 6, since all the
  definitions of Section 3 are required before Section 4; moving the detailed comparison after the
  theorem (as the referee proposed) was needed.
