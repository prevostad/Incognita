# Dossier of P003-transfer-setting, version 1

Refereed and versioned with `paper.tex`, never compiled into the PDF: what the referees and the
owner need and the reader does not. It changes only with a new version of `paper.tex` after
acceptance. Private KNOWN entries are cited by id only, never quoted (KNOWN.md of TransferBandits
has none flagged private).

## Roadmap correspondence

- Items served (`directions` of META.toml): **F0** (the setting, kind `definitions`). The four rows
  of the roadmap's Definitions table are given, each with a witness and an exclusion:
  - source data: Definitions `def:size-rule` (size rules, source strategies) and `def:source-data`
    (planned Lean name `Incognita.TransferBandits.Source`); witnesses `lem:prior-game` and
    `prop:stopped-games`(a) (prior bandit games, `def:prior-game`, stopped or not,
    `def:stopped-game`), exclusion `lem:lookahead` and `thm:main`(b); comparison with stopped bandit
    games `prop:stopped-games`(b), (c);
  - transfer learner: `def:learner` (`TransferAlgorithm`); exclusion `lem:learner-exclusion`;
  - drift condition: `def:drift` (`DriftBound` is $\mathrm{Drift}_L$; the two-sided strict
    condition and the closed set $\mathcal P_L$ are also defined); relations `prop:drift`;
  - consistency: `def:consistency` (`IsConsistent`), quoted verbatim from PMRM26 §4.2 (equal to
    `literature/notes/PMRM26.md`), with its formal reading; properties `prop:classes`, witness
    `prop:witness`, exclusion `prop:exclusion`.
- What the items ask that the paper does not give: F1 (the lower and upper bounds of
  arXiv:2610.21582 and the reduction from two-sided to one-sided drift for those bounds) is not
  done; `prop:drift` only compares the sets of instances. The paper says so in its conclusion.
- Acceptance criteria of the roadmap, one by one:
  1. *The Main result states the source model, the drift condition, the consistency class and the
     criterion*: met. `thm:main` holds for every size rule with $\mathbb E_{\nu'}N'_k<\infty$, at a
     fixed horizon $T$, for every pair of instances (no drift condition needed), for every transfer
     learner; the criterion is an identity between KL divergences.
  2. *Closest known names the known result it extends and why it is not a corollary*: met below
     (PMRM26 Lemma 22, K2, AJSS23, the ignorability results); in the paper, Section 2 (Closest
     related work, Gap with the literature, Table 1).
  3. *One explicit (target, source, size strategy) satisfying all hypotheses*: Example `ex:all`
     (Section `sec:examples`): Bernoulli target and source, round-robin prior games over
     $\lceil\log(T+1)\rceil$ rounds in the order $1,2,1,2,\dots$, source-ignoring UCB with $c=1$.
  4. *Lower bound class / upper-bound algorithm*: does not apply (no bound); `cor:fundamental`
     holds for every learner.
- Conventions of the roadmap changed, declared in Section 3 of the paper:
  - the closed two-sided set $\mathcal P_L$ is copied from PMRM26 §4.2 for the class
    $\mathcal C_L$, while the pinned drift condition is one-sided and strict; both are defined and
    `prop:drift` compares them;
  - the source is modelled as stacks read before the game, as pinned, but the online phase is a
    composition product $P^D\otimes\kappa^T$ rather than stacks (the paper states that the stack
    realisation gives the same law);
  - rounds are numbered from 1 (LML numbers them from 0).

## Closest known

- **K2 / PMRM26 Theorem 2 and Lemma 22.** Read on 2026-11-15 in the LaTeX source of arXiv v1
  (Appendix E; note `literature/notes/PMRM26.md`): Lemma 22 is an *identity*,
  $\mathrm{KL}(P^{I_{N+1}},\tilde P^{I_{N+1}})=\sum_i\mathbb E[N_i(T)]\mathrm{KL}(\nu_i,\tilde\nu_i)
  +\sum_i\mathbb E[N'_i]\mathrm{KL}(\nu'_i,\tilde\nu'_i)$, for a prior *bandit game* over $T'$
  rounds followed by the online game, written as one game of $T'+T$ rounds, with
  $\nu\ll\tilde\nu$, $\nu'\ll\tilde\nu'$ (the other case is dismissed: both sides infinite). The
  observation is $I_{N+1}$, the whole ordered history (actions, values, randomisation of both
  phases). *Derivation attempt*: for bandit-game sources, `thm:main`(a) follows from Lemma 22 by
  sufficiency: the likelihood ratio of $I_{N+1}$ is a product of per-sample ratios, a function of
  $(D,H_T)$, so the divergence of $(D,H_T)$ equals that of $I_{N+1}$ (data processing gives
  "$\le$", sufficiency the equality). It fails for size rules that are not bandit games (for
  $K\ge3$ they exist, even in law: `prop:stopped-games`(c); for $K=2$ every bounded size rule is a
  stopped game, `prop:stopped-games`(b), so for $K=2$ and bounded rules the derivation goes through
  for stopped games, with the ordered history coarsened to $D$) and for the observation: PMRM26's learner sees $I_t$, ours sees $D$ (a modelling
  difference now stated in the paper, Reading of the source, last item). So for bandit-game
  sources `thm:main`(a) is known (PMRM26 Lemma 22 plus sufficiency).
- **Ignorability (R76; SGJC13 Definition 2, Theorem 1; FDS18 §4–§6, Theorem 1).** The condition
  $\{N'=n\}\in\mathcal G_n$ is the everywhere-MAR condition for box-shaped observed sets; FDS18
  state MAR as adaptedness to a set-indexed filtration with observed data a stopping-set
  $\sigma$-algebra, and their Theorem 1 (finitely many variables) gives that the likelihood ratio is
  measurable for the observed data and free of the mechanism. *Derivation attempt (the honest
  route, as the scope referee asked, SC1.1)*: for a bounded size rule ($N'\le m$), only the
  finitely many variables of $B(m)$ and the randomisation matter; integrating out $U'$, FDS18
  Theorem 1 (or SGJC13) gives `lem:source-law`; Wald's identity (W44, classical; KCG16 (18) for the
  LLR) then gives `prop:source-kl`; the chain rule adds the online term. So for bounded size rules
  `thm:main`(a) follows in about a page from classical facts. What remains is the writing of this
  route in the transfer setting, the unbounded case with $\mathbb E_{\nu'}N'_k<\infty$ (countably
  many variables; the integrability of $F^-$ in `prop:source-kl`, Case 2), and the explicit MNAR
  instance `thm:main`(b) where the source term changes. The paper claims no new idea for the
  identity (Section 2, Gap with the literature).
- **AJSS23, App. B.1 (10).** Offline data from an unknown adaptive policy on the *same* instance,
  sequential; the offline term is asserted by taking expectations of the LLR. Not a corollary
  route: the laws differ here and size rules need not be sequential.
- **KCG16 Lemma 1, App. A (18); GMS19 (8), Lemma 1.** The bandit decomposition (GMS19 Remark 2
  credits (8) to KCG16 Lemma 1), Wald's lemma for the LLR of one sequential rule at a stopping
  time, and data processing. `thm:main` with $N'\equiv0$ is GMS19 (8).
- **K1 / PMM25 Theorem 3.** Gaussian, deterministic sizes; with $N'\equiv n$ the source term of
  `thm:main`(a) is $\sum_kn_k\mathrm{KL}(\nu'_k,\tilde\nu'_k)$. Unrelated otherwise. (The earlier
  sentence on who read PMM25's proof is removed: SC1.7.)
- **K7.** K7(a) (sizes $N'_a=T$ with probability $\varepsilon$, else $0$) is a size rule
  (randomisation only). K7(b) is the remark whose formal counterpart is `prop:classes`(b).
- **Multiparameter processes (MV81 read; M86, KM98, M83 read in part; CW75, W81, KS81 not
  read).** Size rules are stopping points of the $K$-parameter filtration; bandit allocations are
  stopping points and strategies optional increasing paths (KM98 §1, one sentence read). MV81
  (read in full on 2026-11-16, OCR text layer of the scan on Vanderbei's page): §1.3 defines
  strategies, policies and *predictable* stopping points (end points of policies); Theorem 4 (§5.1):
  on $\mathbb N^2$, under (F4), every stopping point is predictable, for one probability measure
  (the proof separates $A=\{v^1=\sigma^1_t,v^2>\sigma^2_t\}$ and $B=\{v^1>\sigma^1_t,v^2=\sigma^2_t\}$
  by a $\mathcal G_t$-measurable partition, using (F4) through conditional expectations); §5.2: for
  three independent Markov chains, the cyclic stopping point $(1,1,0)$, $(1,0,1)$, $(0,1,1)$,
  $(1,1,1)$ is not predictable, because $\mathcal F_0$ is trivial so the first step of a policy is
  constant. §1.7 adds that this is not so "for the i.i.d. case" of KS81: there the index set is the
  lattice with one i.i.d. variable per point, a different filtration from ours (independent stacks,
  one per coordinate, as in MV81's Markov chains).
  *Derivation attempt for `prop:stopped-games`.* (b) from MV81 Theorem 4: $(\mathcal G_n)$ satisfies
  (F4) under each $P'_{\nu'}$ (independent stacks, common $U'$), so for each $\nu'$ a size rule is
  $P'_{\nu'}$-a.s. the end point of a policy; but the policy is built from conditional expectations
  under $P'_{\nu'}$ and may depend on $\nu'$, and holds only almost surely. Our proof replaces (F4)
  by the product structure (the projections of $A_m$ and $B_m$ on the data of the box of $m$ are
  disjoint) and the Lusin separation theorem (K95, Theorem 14.7, a classic), which gives one Borel
  rule for all $\nu'$, pointwise. (c) from MV81 §5.2: their argument excludes deterministic first
  steps; with the randomisation $U'$ in $\mathcal G_0$ a policy may randomise its first step, and
  equality in law is weaker than equality; our proof uses Dirac source laws to force each first
  step to have probability $0$. The open question `oq:sequential` of the earlier head is answered
  by `prop:stopped-games` and removed.
- **Berry 1976 (Ber76, read: §II.2, OCR) and Curien 2003 (Cur03, read: pp. 5–6 of arXiv v1).** The
  "Gustave function" $G(1,0,\bot)=G(\bot,1,0)=G(0,\bot,1)=1$ on flat booleans is stable and not
  sequential (Ber76, Proposition II.2.2(b); the OCR garbles the third equation, Cur03 gives the
  cyclic form). Its three minimal inputs read exactly the arms $\{1,2\}$, $\{2,3\}$, $\{3,1\}$ that
  $N^{\rm cyc}$ observes on $\{b_1=1,b_2=0\}$, $\{b_2=1,b_3=0\}$, $\{b_3=1,b_1=0\}$. Berry's proof
  (the input $(\bot,\bot,\bot)$ has no critical index) is the deterministic core of the proof of
  `prop:stopped-games`(c). Earlier than MV81 §5.2. Now credited in Related work, in the paragraph
  "Sources of Proposition 5.5" after the proposition, and in Appendix D.
- **Robins–Gill 1997 (RG97) and Gill–Robins 1997 (GR97): abstracts only.** RG97 define randomised
  monotone missingness (RMM: observe one variable at a time, the next one or stopping chosen from
  the values seen, with randomisation) and state in the abstract that some ignorable missing-data
  processes are not RMM; GR97 (abstract, partly) show that every RMM scheme is a Markov one, and per
  search snippets of a ResearchGate copy, the CAR counter-example of GLR97 does not carry over to
  MAR, so they give a new counter-example for MAR. The bodies were not readable (Wiley, Springer,
  ResearchGate and the Utrecht repository refused access, 2026-11-16), so their counterexample,
  its number of variables, and whether they treat two variables are unknown to us. *Relation to
  `prop:stopped-games`.* With stacks of depth one ($N'\le\mathbf 1_K$): a size rule is an
  everywhere-MAR mechanism (`lem:source-law`: $P(N'=n\mid X')=g_n(x_{B(n)})$), and a stopped prior
  game is an RMM scheme. The converse "every everywhere-MAR mechanism is a size rule" is not
  automatic (a size rule asks that the *event* $\{N'=n\}$, not only its conditional probability, be
  $\mathcal G_n$-measurable; the obvious realisation by a uniform $U'_0$ and cumulated
  probabilities is not). So RMM $\subset$ size rules $\subset$ MAR, and `prop:stopped-games`(c)
  separates the first two, with a deterministic size rule; RG97/GR97 separate RMM from MAR. Whether
  their example is a size rule we could not check. *Recalibration (SC3.1)*: the paper now claims
  nothing new in (c) beyond its writing for size rules, credits Ber76/MV81 for the pattern and the
  argument and RG97/GR97 for the phenomenon in law with randomisation. *Two variables* (bearing on
  (b)): a direct computation shows that every everywhere-MAR mechanism on two variables with
  patterns $\emptyset,\{1\},\{2\},\{1,2\}$ is RMM: with $P(\emptyset\mid x)=c$, $P(\{1\}\mid
  x)=f(x_1)$, $P(\{2\}\mid x)=g(x_2)$, the constraint $c+f(x_1)+g(x_2)\le1$ for all $(x_1,x_2)$ gives
  $c+\sup f+\sup g\le1$, so the scheme "stop with probability $c$, observe 1 first with probability
  $p_1:=1-c-\sup g\ge\sup f$, observe 2 first with probability $\sup g$; after observing $x_1$ first,
  stop with probability $f(x_1)/p_1$, otherwise observe 2; after $x_2$ first, stop with probability
  $g(x_2)/\sup g$, otherwise observe 1" gives $P(\{1,2\}\mid x)=(p_1-f(x_1))+(\sup g-g(x_2))
  =1-c-f(x_1)-g(x_2)$, as required.
  This is the randomised, in-law, depth-one analogue of (b); (b) itself is pointwise, with one
  deterministic rule given $U'$, and for stacks of any depth. Not written in the paper.
- **KS81 (abstract only).** MV81 §1.7 credits KS81 with conditions for every stopping point to be
  predictable. Not checked (ScienceDirect refused access): we do not know whether they settle (b)
  or (c); KS81 stays "see also".
- No KNOWN entry implies `thm:main`: K2 is a consequence of a change of measure, not a statement of
  one, and its hypothesis on the strategy is narrower.

## Sanity checks

- Degenerate cases (also in Section `sec:examples` of the paper): $N'\equiv0$ gives GMS19 (8);
  deterministic sizes give $\sum_kn_k\mathrm{KL}$; $T=0$ gives `prop:source-kl`;
  $\mathrm{KL}(\nu'_1,\tilde\nu'_1)=\infty$ with $P'_{\nu'}(N'_1\ge1)>0$ gives $\infty=\infty$; arms
  never sampled give $0\cdot\infty=0$ and $P^D$ has no mass on slices with $n_1\ge1$ (under
  $\tilde\nu'$ the arm may be sampled when the decision reads other stacks; this does not matter);
  ties play no role in `thm:main`; in `def:consistency` only arms with $\mu_k<\mu^\star$ are
  constrained.
- Hand computation: the rule "sample arm 1 once, and once more if the first value is 1" gives
  $\mathrm{KL}=(1+p)\,\mathrm{kl}(p,q)$ and $\mathbb E N'_1=1+p$ (Example `ex:hand`); the look-ahead
  map gives $2\,\mathrm{kl}$ against $(2-p)\,\mathrm{kl}$ (Example `ex:lookahead`; $p=0.3$, $q=0.5$:
  $0.16457$ against $0.13988$).
- Exact enumeration (notebook `check_decomposition.py`, not refereed): Bernoulli stacks, $K=2$,
  a greedy prior game over 5 rounds and a game stopped at the first 1 agree to $10^{-15}$; the
  look-ahead rule fails as predicted. The proof referee's own enumeration (300 random size rules,
  many non-sequential, half randomised) agreed to $1.3\cdot10^{-15}$.
- KNOWN.md has no `[Lean]` entry. Consistency with K2 (the source enters through
  $\mathbb E N'_a$ only, as in `cor:fundamental`), K7(a) and K7(b): see Closest known.
- The explicit example with all hypotheses at once: Example `ex:all`.

## Weak points

1. `def:consistency` and `def:learner`, the modelling choices: "prior strategy" read as a size rule
   (PMRM26 never defines it), and the learner's observation is $D$ while PMRM26's proof
   (Appendix E) lets the learner see the ordered prior history. If PMRM26 means bandit games only,
   or learners that see the ordered history, its class $\mathcal C_L$ is larger than ours
   (`oq:deterministic` asks how much for the first choice). The propositions on $\mathcal C_L$
   (`prop:classes` to `prop:exclusion`) use only deterministic sizes and source-ignoring learners,
   so they hold for every reading. `Ask-owner` lines in the summaries.
2. `prop:stopped-games`(b), Step 1: the reduction of $A_m$ and $B_m$ to Borel sets $A'$, $B'$ of
   $(y,b)$ and $(y,a)$ (Doob–Dynkin for $\sigma(Y_m,b)$), and the use of the Lusin separation
   theorem on their projections (analytic sets of the Polish space $W_m$); the theorem is cited as a
   classic (K95, Theorem 14.7, number from citing works, not read). Also the measurability of the
   rule $\alpha_r$ (finitely many count vectors per round). (The former weak point on
   `lem:lml-history` and `lem:online-kl`, the identification with LML's histories, is now written
   out, observations of LML included, and was accepted by the proof referee up to PF2.1–PF2.2.)
3. `prop:source-kl`, Case 2: the density on the disjoint union $\mathcal S$, and the split
   $\int\log R=\int F^+-\int F^-$, which is where $\mathbb E_{\nu'}[N'_k]<\infty$ is used: $(\log R)^-$
   is always $P$-integrable (`lem:kl-neg`), but the sum $F^-$ of the per-sample negative parts may
   not be. Whether (a) holds without this hypothesis is not known to us (a truncation $N'\wedge m$
   with data processing seems to give it when only one arm's source law changes; not written).

## Searches

The web queries run, with their dates and what they found:

- "bandit lower bound offline data collected adaptively KL divergence decomposition expected
  number of offline samples" (2026-11-15): AJSS23, CL24, a paper on offline data in latent linear
  bandits (arXiv:2405.17324).
- "Wald identity log-likelihood ratio adaptively sampled data stopping multi-armed bandit
  divergence decomposition random sample size" (2026-11-15): KCG16 and works reusing its Wald step.
- "warm-start bandit historical data lower bound change of measure historical samples policy
  unknown regret lower bound" (2026-11-15): SJ12 and warm-start papers; no change of measure for an
  unknown logging policy.
- "multiparameter stopping point optional increasing path sequential allocation likelihood
  factorization independent of parameter" (2026-11-15): two-parameter optimal stopping (an EPFL
  thesis), not read.
- "Transfer Learning in Bandits from Unknown Adaptive Policies Prevost lower bound change of
  measure" (2026-11-15): PMRM26 and PMM25.
- "selection bias adaptively collected data likelihood principle bandit data likelihood ignorable
  adaptive design" (2026-11-15): bias of sample means under adaptive collection (Nie et al.), not
  read.
- The scope referee's queries of 2026-11-15 (report SC1, section Queries) on Rubin 1976, Seaman et
  al. 2013, Farewell et al. 2018, Mandelbaum 1986, Kaspi–Mandelbaum 1998, Wald 1944, Berger–Wolpert
  1988, Walsh 1981, Millet 1985, Dalang 1988, Gill–Robins 1997: followed up in the revision of
  2026-11-15 (entries R76, SGJC13, FDS18, M86, KM98, W44, BW88, CW75, W81, GR97, GLR97 of
  `literature/`; FDS18 and SGJC13 read through extracts; PMRM26 Appendix E read in the arXiv
  e-print).
- "Walsh 1981 "optional increasing paths" every stopping point two-parameter discrete (F4) lies on
  an optional increasing path" (2026-11-16): Merzbach 1983 (Ann. IHP B 19(3), Numdam, read:
  Proposition 3, "proved by Walsh", an optional increasing path between two finite stopping points
  under (F4), continuous quadrant; Theorem 4 and its proof; Lemma 11 proved in the discrete case);
  Dalang (EPFL), Kaspi–Mandelbaum; no statement for three parameters.
- "stopping point not reachable by optional increasing path three parameters counterexample
  multiparameter tactic accessible stopping points N^d" (2026-11-16): Krengel–Sucheston tactics,
  Cairoli–Dalang accessibility (the notion), a 2004 paper on accessibility for $\mathbb N^d$
  (abstract only); no counterexample found. Hence `oq:sequential` was restated for $K\ge3$ (it is
  now answered by `prop:stopped-games`, after MV81 was found and read).

- "Krengel Sucheston "Stopping rules and tactics for processes indexed by a directed set" Journal
  of Multivariate Analysis 1981" (2026-11-16): the Crossref record and the abstract of KS81; the
  ScienceDirect page refused access.
- "Mandelbaum Vanderbei "Optimal stopping and supermartingales over partially ordered sets"
  predictable stopping points" (2026-11-16): the Springer record of MV81, R. J. Vanderbei's
  publication page with a scan of MV81 (OCR text layer read in full), the Różański–Szajowski chapter
  ("as in Mandelbaum and Vanderbei (1981) we restrict ourselves to the class of predictable stopping
  points").
- "Kechris "Classical Descriptive Set Theory" "Lusin Separation Theorem" 14.7 disjoint analytic sets
  Borel set separating" (2026-11-16): several works citing K95, Theorem 14.7 as the Lusin separation
  theorem; the Wikipedia statement; the Crossref record of K95.
- Crossref records of ACF02, MV81, KS81 and K95 (2026-11-16), for their metadata.
- Round 3 (2026-11-16, after the scope report SC3):
  - "Gill Robins "Sequential models for coarsening and missingness" pdf", and the same with
    citeseerx, math.leidenuniv.nl or arxiv: GR97 on Springer and ResearchGate (both refused access),
    R. D. Gill's publication list (no full text), Semantic Scholar pointing to the Utrecht repository
    (handle 1874/1643; refused access).
  - "Robins Gill 1997 "Non-response models for the analysis of non-monotone ignorable missing data"
    randomized monotone missingness example not RMM": the RG97 abstract (Wiley refused access),
    Sun–Tchetgen Tchetgen arXiv:1411.5310 (read: §3.1, a bivariate example on polytomous
    regression, and the conclusion; no RMM counterexample), arXiv:2611.16278 (RMM a proper
    subclass of MAR; no counterexample).
  - "randomized monotone missingness MAR counterexample three variables OR two variables Robins
    Gill not representable sequentially": snippets of GR97 ("it took us some effort to find a new
    counter-example for MAR"), FDS18 §6 conjecture (incomparable observed sets).
  - "Gill van der Laan Robins "Coarsening at random: characterizations, conjectures" pdf
    counter-example not randomized monotone": Jaeger, JAIR 24 (2005), read §4 (Example 4.5,
    randomized monotone coarsening; Example 2.17, the standard CAR distribution that RMC cannot
    generate: three outcomes, observed pairs, a cyclic CAR example of coarsening, not of missing
    variables); Gill–Grünwald arXiv:math/0510276 (no MAR counterexample).
  - "Berry 1976 "Bottom-up computation of recursive programs" RAIRO Informatique théorique 10
    47-82": the Numdam record and its open scan (read §II.2, OCR). Curien arXiv:cs/0501034 (read
    pp. 5–6) and its Crossref record (Bull. Symbolic Logic 9(2), 2003). RG97's Crossref record.

## Reading notes

- PMRM26: §3.1, §3.2, §4.1, §4.2, §7 (HTML) and Appendix E with Lemma 22 (e-print), see the note.
- FDS18 (§2–§6, extracts), SGJC13 (Definitions 1–2, Theorems 1–2, extracts), R76 (abstract), M86
  (abstract), KM98 (abstract and one sentence of §1), M83 (pp. 223–227 and Lemma 11, text layer of
  the Numdam PDF): cited for what was read.
- MV81: read in full (OCR text layer; the displayed formulas are lost, the statements and the
  example of §5.2 are legible), cited for §1.3, Theorem 4 and §5.2.
- Not read, cited in the paper only as "see also": BW88 (stopping-rule principle), CW75 (stopping
  points), W81 (optional increasing paths), KS81 (tactics; abstract only). ACF02 (UCB) and K95 (the
  Lusin separation theorem) are cited as classics for standard facts. W44 (Wald's identity) is cited as a classic for a
  standard fact.
- RG97 and GR97 (randomised monotone missingness versus MAR): abstracts only; cited in the paper
  for the statement of their abstracts (some ignorable/MAR mechanisms are not RMM), with GR97 as
  "see also". GLR97 (CAR) is in `literature/`, not cited. Ber76 (§II.2, OCR) and Cur03 (pp. 5–6)
  are read for the Gustave function; a note `literature/notes/Ber76.md` records it.

## Changes

None: version 1 (refereeing rounds do not change the version). The answers to the reports of
rounds 1 to 3 are in the notebook (sections of 2026-11-16).
