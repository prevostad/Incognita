# Roadmap: StochasticBandits — problem-dependent optimality in stochastic multi-armed bandits

| | |
|---|---|
| Status | **approved** by its owner, 2026-11-14 |
| Owner | Adrien Prevost (GitHub: prevostad) |
| Written | 2026-11-14 by Claude (Anthropic, model Claude Opus 5.5) at the owner's request, from the published literature only; it absorbs the drafts RegretShape and StructuredBandits of 2026-11-13 (Appendix A); direction D19 added on 2026-11-14 at the owner's request |
| KNOWN.md | [KNOWN.md](KNOWN.md): reviewed by the owner on 2026-11-14 (written by an agent from the published literature, with no result of the owner) |
| Domain | `stochastic-bandits` (see roadmaps/README.md, "Domains") |
| arXiv class | `math.ST` (secondary `stat.ML`) |
| AI assistance | Claude wrote the roadmap; every reference of KNOWN.md was read in the parts recorded in [SOURCES.md](SOURCES.md) and `literature/index.md` (2026-11-14); the sources of D19 were not read (see D19); the owner approved the roadmap without checking every statement |

The drafts RegretShape and StructuredBandits were removed from the repository when this roadmap was
added (2026-11-14); their items are mapped in Appendix A. Owner decisions (2026-11-14): (1) the
objects shared with BatchedBandits are written by whichever roadmap needs them first, and the other
one reuses them: laws on $[0,1]$ are defined by F0 here, and $\mathcal K_{\inf}$ on $[0,1]$ is
BatchedBandits F2 or, if that paper is not accepted when F9 comes, F10 below; (2) the structured
directions D13–D17 are open now; (3) F5 is `external` with two sources, as proposed in F5.
**Priority (owner, 2026-11-14):** the exact constant of the minimax regret and whether a policy
attains it (D19) come before simultaneous minimax and problem-dependent guarantees (D5, D6).

## Motivation

For stochastic bandits with finitely many arms, the first-order problem-dependent regret is settled
in the classical models: a consistent algorithm pulls a suboptimal arm $a$ at least
$(1-o(1))\log T/\mathcal K_{\inf}(\nu_a, m^\star)$ times (K1), and KL-UCB, IMED and Thompson sampling
attain this for one-parameter exponential families and for laws on $[0,1]$ (K9–K13, K16). Almost
everything around this statement is open or only partly understood: the second-order term and the
finite-time shape (K4, K5, K7, K11, K21), classes of laws that are not one-parameter (K14–K19),
known structure between the arms, where optimism fails (K25, K35), the coexistence of
problem-dependent optimality with minimax optimality and anytime behaviour (K20–K24), and the
distribution of the regret beyond its mean (K32–K34).

The question of this roadmap: **what exactly is the optimal problem-dependent regret — at first
order, at second order and in distribution — beyond the classical model, and which simple
algorithms attain it?** It is broad on purpose. The owner wants a cumulative library: verified
building blocks (change-of-measure tools, $\mathcal K_{\inf}$ for new classes of laws, regret
decompositions) that later papers reuse, as long as each block is used and none is routine.

## Pinned conventions

Every paper of this roadmap uses these conventions unless it says explicitly which one it changes
and why.

- **Arms.** A finite type $\alpha$ of arms, $K := |\alpha| \ge 2$. Algorithms do not use an
  enumeration of the arms; tie rules are stated.
- **Instances, models, classes.** An instance is $\nu = (\nu_a)_{a\in\alpha}$, each $\nu_a$ a
  probability law on $\mathbb R$ with finite mean $m_a$; $m^\star := \max_a m_a$,
  $\Delta_a := m^\star - m_a$, $\mathcal A^\star(\nu)$ the set of optimal arms. A **model** is a set
  $\mathcal D$ of laws on $\mathbb R$. The **unstructured class** of models $(\mathcal D_a)_a$ is
  $\prod_a \mathcal D_a$. A **structured class** is any set $\mathcal E$ of instances, known to the
  learner; the unstructured class is a special case. Each paper names its class among, for example:
  Bernoulli laws; $\mathcal P[0,1]$, all laws on $[0,1]$; a one-parameter exponential family;
  laws on $(-\infty,1]$ with a finite mean ("semi-bounded"); Gaussian laws with unknown mean and
  variance; $\mathcal L_{\varepsilon,B} := \lbrace P : \mathbb E_P|X|^{1+\varepsilon} \le B\rbrace$;
  laws with kurtosis at most $\kappa$; or a structure.
- **Divergences.** $\mathrm{KL}$ is the Kullback–Leibler divergence ($+\infty$ without absolute
  continuity); $\mathrm{kl}(p,q)$ the Bernoulli one.
  $\mathcal K_{\inf}(P,\mu;\mathcal D) := \inf\lbrace \mathrm{KL}(P,Q) : Q\in\mathcal D,\ m(Q) > \mu\rbrace \in [0,\infty]$,
  $\inf\emptyset := \infty$, with a **strict** inequality, as in [LS, Theorem 16.2] and LMLExplore's
  `dInf`. A source that uses $m(Q) \ge \mu$ (for example AJK21) is translated, and the paper says so.
- **Learners.** An **anytime** algorithm is one LML `Algorithm`: it never sees the horizon. A
  **horizon-dependent** algorithm is a family $(\pi_T)_{T\ge 1}$; its regret at horizon $T$ is the
  regret of $\pi_T$ after $T$ rounds. Every upper bound says which kind it is.
- **Rounds, counts, regret.** Lean rounds are $0,1,2,\dots$; horizon $T$ means rounds
  $0,\dots,T-1$; $N_a(T)$ is LML's `pullCount` at $T$ (pulls in rounds $< T$). Papers may number
  rounds from 1 for the same quantities. $\hat R_T := \sum_{t<T}\Delta_{A_t}$ is the random
  pseudo-regret (LML's `regret`) and $R_T := \mathbb E\hat R_T = \sum_a \Delta_a\,\mathbb E N_a(T)$.
- **Classes of algorithms.** Consistency on $\mathcal E$: $R_T(\nu) = o(T^p)$ for every $p>0$ and
  every $\nu\in\mathcal E$ ([LS, Definition 16.1]; LMLExplore's `IsConsistent`). The other classes
  keep their source definitions: uniformly fast / super-fast convergent [GMS19, Definitions 1, 6];
  smarter than the uniform strategy, pairwise symmetric for optimal arms, monotonic
  [GMS19, Definitions 2–4]; $\alpha$-consistent [SAE13, Definition 5]; $f$-upper tailed counts or
  regret [SA11, Definition 1]. A lower bound names its class.
- **Graves–Lai constant.** For $\nu\in\mathcal E$ with a unique optimal arm $a^\star$:
  $\mathrm{Alt}(\nu;\mathcal E) := \lbrace \nu'\in\mathcal E : a^\star \text{ is not optimal for } \nu'\rbrace$ and
  $C(\nu;\mathcal E) := \inf\big\lbrace \sum_a w_a\Delta_a : w\in[0,\infty]^\alpha,\ \sum_a w_a\,\mathrm{KL}(\nu_a,\nu'_a)\ge 1\ \ \forall \nu'\in\mathrm{Alt}(\nu;\mathcal E)\big\rbrace \in [0,\infty]$,
  with $0\cdot\infty := 0$. For $\mathcal E = \prod_a\mathcal D_a$ it equals
  $\sum_{a:\Delta_a>0}\Delta_a/\mathcal K_{\inf}(\nu_a,m^\star;\mathcal D_a)$ (proved by F0; every
  structured paper checks this case). It agrees with [CMP17, (2)–(4)] when that source applies.
  Several optimal arms are a degenerate case (D17): a paper allowing them states its definition.
- **Criteria.** The Main result states its criterion: first order (liminf / limsup of
  $\mathbb E N_a(T)/\log T$ or $R_T/\log T$), second order ($\mathbb E N_a(T) - \log T/\mathcal K_{\inf}$),
  finite time (every $T$, constants explicit or existential and on what they depend), worst case
  over a class ($\sup_{\nu\in\mathcal E}R_T(\nu)$), or distributional ($\mathbb P(\hat R_T > x)$,
  $\mathbb P(N_a(T) > x)$, moments), with the range of $x$ and the uniformity in $T$.
- **Lean.** LMLExplore's Bandits conventions (`LMLRoadmaps/Bandits/README.md`, read 2026-11-14):
  arms `α` with `[Fintype α] [Nonempty α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]`,
  never `Fin K`; `ν : Kernel α ℝ` with LML's `Environment.bandit ν` (the name on LMLExplore's
  pinned revision `b4e0ab9`); means `(ν a)[id]`; bounded rewards
  `∀ a, ∀ᵐ x ∂(ν a), x ∈ Set.Icc 0 1`; asymptotic statements as eventual inequalities
  (`∀ c' > c, ∀ᶠ T in atTop, …`), never `liminf`/`limsup` of real sequences; divergences,
  $\Delta_a/\mathcal K_{\inf}$ and $C(\nu;\mathcal E)$ in `ℝ≥0∞`. What the dependencies already prove
  (Appendix B) is reused, never restated.

## Definitions

The core objects and their planned Lean names. The setting paper (F0) formalises them; it may change
a name or a shape only with a justification in its Setting. Dependency names were read on
LMLExplore at revision `b4e0ab9` (Incognita's pin) on 2026-11-14.

| Object | Convention | Planned Lean name |
|---|---|---|
| arms, instance | as in the Lean conventions; `[IsMarkovKernel ν]` | reuse (LML) |
| unstructured class | `{ν | ∀ a, ν a ∈ D a}` for `D : α → Set (Measure ℝ)` | `Incognita.StochasticBandits.productClass` (reuse LMLExplore's name if `LaiRobbins` has one) |
| models | laws on $[0,1]$; semi-bounded laws; $\mathcal L_{\varepsilon,B}$; kurtosis $\le\kappa$; Gaussian laws with unknown mean and variance | `unitLaws` (defined by F0; BatchedBandits reuses it, or this roadmap reuses BatchedBandits' `unitBandits` if that one is merged first), `semiBoundedLaws`, `momentLaws ε B`, `kurtosisLaws κ`, `gaussianLaws`, each defined by the first paper that needs it |
| $\mathcal K_{\inf}$ | `dInf D P μ`, valued in `ℝ≥0∞` | reuse `LMLExplore.Bandits.dInf` |
| consistency | `IsConsistent alg E` | reuse `LMLExplore.Bandits.IsConsistent` |
| horizon-dependent algorithm | `π : ℕ → Algorithm Unit α ℝ`, regret at `T` taken for `π T` | `Incognita.StochasticBandits.IsConsistentFamily` and family versions of the predicates below |
| classes of [GMS19] | super-fast convergent with constant `C`; smarter than uniform; pairwise symmetric for optimal arms; monotonic | `IsUniformlySuperFastConvergent`, `IsSmarterThanUniform`, `IsPairwiseSymmetricOptimal`, `IsMonotonic` |
| $\alpha$-consistency | $R_T = o(T^p)$ for every $p > \alpha$ | `IsAlphaConsistent` |
| alternatives | $\mathrm{Alt}(\nu;\mathcal E)$ | `Incognita.StochasticBandits.alt` |
| Graves–Lai constant | $C(\nu;\mathcal E)$ in `ℝ≥0∞` | `Incognita.StochasticBandits.gravesLai` |
| tails | $f$-upper tailed counts and regret [SA11, Definition 1] | `HasUpperTailedPullCount`, `HasUpperTailedRegret` |
| algorithms | LMLExplore's index and weight policies, `klucbFam`, `klucb`, `ucbF`, `moss`, `gaussianTS`; new ones by their formula (KNOWN K44–K56) | `Incognita.StochasticBandits.imed`, `npts`, `klucbSwitch`, … |

F0 also proves, for each definition, a witness and an exclusion (AGENTS.md §6.4): KL-UCB is
consistent on Bernoulli instances and "always pull arm $a$" is not; a super-fast convergent
algorithm on $[0,1]$-valued instances exists; $C(\nu;\mathcal E) = 0$ on a class where the optimal
arm alone identifies the instance; the product-class identity above.

## What is known

All entries are published results, read by the agent who wrote this roadmap; precise statements in
[KNOWN.md](KNOWN.md). There are no unpublished results of the owner in this roadmap.

- **Lower bounds.** Lai–Robbins / Burnetas–Katehakis for unstructured classes (K1, in Lean in
  LMLExplore); the fundamental inequality $\sum_a\mathbb E_\nu N_a(T)\,\mathrm{KL}(\nu_a,\nu'_a)\ge\mathrm{kl}(\mathbb E_\nu Z,\mathbb E_{\nu'}Z)$
  and its stopping-time form (K2); finite-time lower bounds (K3, K7); the initial almost linear
  regime (K4); a second-order term $-O(\log\log T)$ for super-fast convergent algorithms (K5);
  $\alpha$-consistent algorithms (K6); heavy tails (K8); Graves–Lai for structures (K25).
- **Upper bounds.** KL-UCB (K9, K10), IMED with a $-C\log\log T$ second-order term on bounded
  supports (K11), Thompson sampling (K12, K13), multi-parameter and non-parametric classes
  (K14–K19), simultaneous minimax and asymptotic optimality (K20–K24), structured algorithms
  (K26–K31).
- **Distribution of the regret.** Polynomial tails of UCB-type algorithms (K32); no anytime
  algorithm has regret tails better than polylogarithmic on $\mathcal P[0,1]^K$, while a
  horizon-dependent one can (K33); optimized algorithms have truncated-Cauchy tails, with a sharp
  tail–expectation trade-off (K34).
- **Negative results.** Optimism and Thompson sampling are not asymptotically optimal for linear
  bandits (K35); forced exploration of order $\log\log T$ is sometimes necessary (K36);
  explore-then-commit loses a factor 2 (K37); further impossibilities K38–K43.
- **Open problems stated in the literature:** K57–K71.

## Known results to formalise

Each item becomes an `external` paper (AGENTS.md §5.1) whose novelty is not checked, only its
fidelity to the source; then it is formalised. In order:

- **F0. The setting** (the setting paper of this roadmap, kind `definitions`): the Definitions above, the
  product-class identity for $C(\nu;\mathcal E)$, witnesses and exclusions.
- **F1. The fundamental inequality** [GMS19, (6) and (8)] for LML runs and any $[0,1]$-valued $Z$
  measurable with respect to the history, and its version at an almost surely finite stopping time
  [KCG16, Lemma 1] (K2). LMLExplore has the divergence decomposition and Bretagnolle–Huber, not
  this form (Appendix B): check at the pinned revision first.
- **F2. The initial regime** [GMS19, Theorems 2 and 4] (K4), with Definitions 2–4 of the source.
- **F3. The second-order lower bound** [GMS19, Theorem 5] with its Definitions 5–6 and Remark 3,
  for one well-behaved model (the bounded-support model is the first target) (K5).
- **F4. The $\alpha$-consistent lower bound** [SAE13, Theorem 6] (K6).
- **F5. The Graves–Lai lower bound for finite structured classes** [CMP17, Theorem 1], with the
  linear formula [LS, Corollary 25.2] and the unstructured bound (K1) as corollaries (K25). [CMP17]
  proves it by invoking [GL97, Theorem 1] (controlled Markov chains, not read); the paper follows
  instead the change-of-measure proof of [LS, Theorem 25.1], written there for linear bandits, and
  marks its extension to a general class as a filled gap (owner decision: `external` with two
  sources, as proposed, or `internal`). LMLExplore's one-alternative lemma
  `eventually_mul_log_le_integral_pullCount_of_klDiv` already holds for any class: reuse it.
- **F6. Explore-then-commit loses a factor 2** [GKL16, Theorem 4] (two Gaussian arms, unknown gap),
  after F1 (stopping-time form) (K37).
- **F7. No robust anytime policy** [SA11, Theorem 3.3 and Corollary 3.4] (K33).
- **F8. The end of optimism**: the three-arm linear example of [LS, Section 25.2] (also
  [LS17, Section 8]) as a theorem: the value $c(\mathcal A,\theta) = 2\gamma^2$ and the
  $\Omega(1/\varepsilon)$ asymptotic regret of every consistent optimistic algorithm whose
  confidence sets satisfy the two assumptions stated in the source (K35). The source's argument is
  partly informal: the paper makes the class of optimistic algorithms explicit and marks every gap
  it fills.
- **F9. IMED on $[0,1]$** [HT15, Theorem 3 and Corollary 4] restricted to laws on $[0,1]$ (K11),
  after $\mathcal K_{\inf}$ on $[0,1]$ (BatchedBandits F2, or F10 below); it depends on it.
- **F10. $\mathcal K_{\inf}$ on $[0,1]$** (kind `external`), only if BatchedBandits F2 has not been
  accepted when F9 comes: the content of BatchedBandits F2 (dual formula, continuity, deviation
  inequalities for $n\,\mathcal K_{\inf}(\hat\nu_n,\mu)$; Honda–Takemura 2010, 2015), written once and
  reused by both roadmaps.

## Open directions

Papers are welcome in these directions; the list is not exhaustive. Each direction names what is
known (KNOWN ids) and what would answer it. Before writing, search the literature after the
sources of KNOWN.md (works citing them): KNOWN.md was written on 2026-11-14 and is not exhaustive.

### A. The shape of the regret beyond the first order

- **D1. The constant of the second-order term.** Fix a model $\mathcal D$ (Bernoulli, $\mathcal P[0,1]$
  or one exponential family) and the class $\mathcal S_C$ of algorithms that are uniformly
  super-fast convergent on $\mathcal D^\alpha$ with constant $C$ [GMS19, Definition 6]. Known:
  every algorithm of $\mathcal S_C$ has
  $\mathbb E N_a(T)\ge(\log T - 9\log\log T - \log(KC) - o(1))/\mathcal K_{\inf}(\nu_a,m^\star) - \log 2/\mathcal K_{\inf}$
  (arithmetic from [GMS19, (18)], K5); horizon-dependent KL-UCB-switch has
  $\mathbb E N_a(T)\le(\log T-\log\log T)/\mathcal K_{\inf} + O(1)$ on $\mathcal P[0,1]$ (K21);
  anytime IMED has $R_T\le\sum_a\Delta_a\log T/\mathcal K_{\inf} - C'\log\log T$ for bounded
  supports, $C'$ existential (K11). Question: (a) for horizon-dependent families, the largest
  $\gamma$ such that some algorithm of $\mathcal S_C$ has
  $\mathbb E N_a(T)\le(\log T-\gamma\log\log T)/\mathcal K_{\inf}+O(1)$ for every instance and arm
  (is it 1?); (b) the same for anytime algorithms: is the anytime value smaller (a price at second
  order for not knowing $T$)? Answer: a lower bound and an upper bound with the same coefficient of
  $\log\log T$ in one model and one class (with a proof that the algorithm is in the class), or a
  proof that the second-order term is not of order $\log\log T$ in that class.
- **D2. Explicit negative second order for an anytime algorithm.** An anytime algorithm on
  $\mathcal P[0,1]$ (or on one exponential family) with a closed-form bound
  $\mathbb E N_a(T)\le\log T/\mathcal K_{\inf}(\nu_a,m^\star) - c\log\log T + B(\nu)$ for every
  $T\ge T_0(\nu)$, with $c>0$, $B$ and $T_0$ explicit. Known: [HT15, Theorem 5(ii)] is
  asymptotic with an existential constant (K11); the anytime bound of [GHMS22, Theorem 4] has a
  positive second-order term $O((\log T)^{6/7})$ (an upper bound: the algorithm may do better) (K21).
  Answer: the bound with its proof.
- **D3. The transition out of the linear regime.** For pairwise symmetric and monotonic algorithms
  [GMS19, Definitions 3–4], suboptimal arms collectively receive at least
  $\frac T2(1-A^\star/K)$ pulls whenever $T\le K/(8A^\star\mathcal K^{\max})$ (K4). Question: is
  this horizon sharp up to a universal constant, that is, is there an algorithm of the same class
  and a universal $c$ such that
  $\sum_{a\notin\mathcal A^\star}\mathbb E N_a(T)\le\frac T2(1-A^\star/K)$ for every
  $T\ge cK/(A^\star\mathcal K^{\max})$ and every instance? If not, which quantity of the instance
  governs the transition? Answer: matching upper and lower bounds on the transition horizon, up to
  universal constants, in one model.
- **D4. Finite-time instance optimality beyond unit-variance Gaussians.** ADA-UCB is minimax
  optimal, "sub-UCB" and asymptotically optimal for unit-variance Gaussian rewards, with a
  finite-time lower bound matching it up to constants (K7, K22). (a) The same three properties for
  one exponential family or for $\mathcal P[0,1]$, with $\mathcal K_{\inf}$ in place of
  $\Delta^2/2$ in the sub-UCB criterion (open problem stated in [L18, Section 6], K57).
  (b) An index strategy — the index of an arm depends only on that arm's samples and on $t$ (or
  $n-t$) — with the three properties for unit-variance Gaussians, or a proof that none exists
  (the "intriguing open question" of [L18, Section 2], K57). Answer: a theorem for (a); a
  construction or a refutation for (b).

### B. Simultaneous criteria and anytime algorithms

**Order (owner, 2026-11-14): D19 first.** Before asking for algorithms that are both minimax optimal
and problem-dependent optimal (D5, D6), find the exact constant of the minimax regret and whether a
policy attains it. Until D19 has settled the constant in a model, "minimax optimal" in D5 and D6
means optimal up to a constant factor, and a paper of D5 or D6 says so.

- **D19. The constant of the minimax regret, and a policy that attains it.** For a fixed model
  $\mathcal D$ (Bernoulli laws, $\mathcal P[0,1]$, or Gaussian laws of variance 1 with means in a
  bounded interval) and $K\ge2$, let $R^\star_{K,\mathcal D}(T) := \inf_\pi\sup_{\nu\in\mathcal D^\alpha}R_T(\pi,\nu)$,
  the infimum over horizon-dependent policies (with external randomization). It is of order
  $\sqrt{KT}$, but its constant is known only up to a factor larger than 28. Reported in the
  literature (to be checked in the sources): lower bounds $\frac1{20}\sqrt{KT}$ [ACFS02] and
  $\frac1{27}\sqrt{(K-1)T}$ for Gaussian rewards [LS, Theorem 15.2]; upper bounds $49\sqrt{KT}$ for
  MOSS with rewards in $[0,1]$ and a known horizon [AB09] (`moss_regret_le` in LMLExplore, check its
  constant) and $\sqrt{2KT}$ for rewards in $[0,1]$ [ZL19]. For two arms the question is old: Vogel
  [Vog60] proved the order $\sqrt T$, Fabius and van Zwet [FvZ70] and Bather [Bat83] bounded the
  constant, and Kolnogorov [Kol17, Kol20] studies the Gaussian two-armed bandit in the limit where the
  gap is of order $1/\sqrt T$ and computes a value numerically; diffusion limits of bandit
  experiments in this regime are studied in [Adu25] and [KZ21]. **None of these sources was read for
  KNOWN.md**: the bibliographer reads them first and records what each one proves (with its exact
  class of laws and normalization), and a paper of D19 starts from those notes. Question: (a) does
  $R^\star_{K,\mathcal D}(T)/\sqrt T$ converge as $T\to\infty$ for fixed $K$, and to which constant
  (a characterization, and how it depends on $\mathcal D$); (b) is the constant attained by an
  explicit policy, horizon-dependent or anytime, defined by its formula with its cost per round;
  (c) bounds on the constant for every $K$ that improve the known ones, and its order in $K$.
  Answer: (a) a theorem identifying the limit in at least one model; (b) a policy with
  $\sup_{\nu}R_T(\pi,\nu)\le(c^\star+\varepsilon)\sqrt T$ for every $\varepsilon>0$ and
  $T\ge T_0(\varepsilon)$, or a proof that no policy of a stated simple class attains $c^\star$;
  (c) explicit lower and upper bounds, non-asymptotic where possible.
  Sources: [ACFS02] P. Auer, N. Cesa-Bianchi, Y. Freund, R. E. Schapire, *The nonstochastic
  multiarmed bandit problem*, SIAM J. Comput. 32(1), 2002; [AB09] J.-Y. Audibert, S. Bubeck,
  *Minimax policies for adversarial and stochastic bandits*, COLT 2009; [ZL19] J. Zimmert,
  T. Lattimore, *Connections between mirror descent, Thompson sampling and the information ratio*,
  NeurIPS 2019; [Vog60] W. Vogel, *An asymptotic minimax theorem for the two armed bandit problem*,
  Ann. Math. Statist. 31, 1960; [FvZ70] J. Fabius, W. R. van Zwet, *Some remarks on the two-armed
  bandit*, Ann. Math. Statist. 41(6), 1970; [Bat83] J. A. Bather, *The minimax risk for the two-armed
  bandit problem*, in Mathematical Learning Models, Lecture Notes in Statistics 20, 1983; [Kol17]
  A. V. Kolnogorov, *Batch data processing and Gaussian two-armed bandit*, arXiv:1704.03631;
  [Kol20] A. V. Kolnogorov, *Gaussian two-armed bandit: limiting description*, Probl. Inf. Transm.
  56(3), 2020; [Adu25] K. Adusumilli, *Risk and optimal policies in bandit experiments*,
  arXiv:2112.06363; [KZ21] A. Kalvit, A. Zeevi, *A closer look at the worst-case behavior of
  multi-armed bandit algorithms*, NeurIPS 2021. These references are not yet in
  `literature/bibliography.json`: the bibliographer adds them, with verified metadata.
- **D5. The price of anytime.** Let $\pi$ be anytime with
  $\sup_{\nu\in\mathcal P[0,1]^\alpha}R_T(\nu)\le C\sqrt{KT}$ for every $T$. Is there such $\pi$ with
  $\mathbb E N_a(T)\le\log T/\mathcal K_{\inf}(\nu_a,m^\star)+O(\log\log T)$ for every instance with
  $m^\star<1$? Known: horizon-dependent bi-optimality with a $-\log\log T$ second-order term, and
  anytime bi-optimality with a bound whose second-order term is $+O((\log T)^{6/7})$ (K21). Answer:
  such an algorithm, or a lower
  bound forcing a second-order term $g(T)\to\infty$ on anytime minimax-optimal algorithms, with its
  order.
- **D6. Thompson sampling that is both minimax and asymptotically optimal.** (a) A randomized
  algorithm of Thompson type (posterior samples, or randomly weighted empirical laws as in K49,
  possibly clipped as in K52) that is anytime, has $R_T\le C\sqrt{KT}+\sum_a\Delta_a$ for every
  $T$ and $\lim_T R_T/\log T=\sum_a\Delta_a/\mathcal K_{\inf}(\nu_a,m^\star)$ on Bernoulli or
  $\mathcal P[0,1]$ instances. (b) For 1-sub-Gaussian rewards, a Thompson-type algorithm with both
  $R_T=O(\sqrt{KT})$ and $\lim R_T/\log T=\sum_a 2/\Delta_a$, without the iterated-logarithm
  factor of [JXSXG21, Theorem 3] (MOTS-J does it for Gaussian rewards only, K23; open question of
  [JXSXG21, Section 7], K69). Answer: algorithm and proof, or a counterexample for a natural
  candidate (for example clipped Gaussian MOTS with a fixed $\rho$).

### C. Asymptotic optimality beyond one-parameter families

- **D7. $\mathcal K_{\inf}$ of non-parametric and multi-parameter classes, as library material.**
  For each class $\mathcal D$ among semi-bounded laws (dual formula [HT15, Theorem 2], K11),
  $\mathcal L_{\varepsilon,B}$ (K17), Gaussian laws with unknown variance (explicit formula, K14, K15)
  and laws with kurtosis at most $\kappa$ (no formula known, K19, K62): a dual or variational
  formula for $\mathcal K_{\inf}(P,\mu;\mathcal D)$, its continuity in $(P,\mu)$ where it holds, and a
  deviation inequality $\mathbb P(n\,\mathcal K_{\inf}(\hat P_n,m(P);\mathcal D)\ge x)\le f(n)e^{-x}$
  with explicit $f$. The $[0,1]$ case is BatchedBandits F2 (or F10). Answer: one class per paper, each
  result used by an item of C (named in the paper).
- **D8. Exact first order where only constant factors are known.** (a) Kurtosis: for instances in
  $\mathcal H_\kappa^\alpha$ (kurtosis at most a known $\kappa$, positive variances), an algorithm
  with $\limsup_T R_T/\log T\le\sum_a\Delta_a/\mathcal K_{\inf}(\nu_a,m^\star;\mathcal H_\kappa)$,
  matching K1; or a proof that no consistent algorithm attains it (known: only up to a universal
  constant, K19; open problem of [L17, Section 4], K62). (b) Heavy tails: an algorithm exactly
  asymptotically optimal on $\mathcal L_{\varepsilon,B}^\alpha$ that recomputes its indices only at
  $o(T)$ rounds (the batched version of [AJK21] loses a factor $1+\tilde\varepsilon$, K17).
  Answer: theorem with the exact constant.
- **D9. Moment instead of exponential-moment assumptions.** Prove that IMED (K46) is asymptotically
  optimal on semi-bounded laws when the arms only have a finite moment of order $2+p$ for some
  $p>0$, instead of a finite moment generating function near 0, or give a counterexample
  (conjecture of [HT15, Section 9], K60). Answer: theorem or refutation.
- **D10. Randomized algorithms beyond one-parameter families.** (a) A non-parametric Thompson-type
  algorithm (in the spirit of K49) that is asymptotically optimal on semi-bounded laws or on
  $\mathcal L_{\varepsilon,B}$. (b) An explicit second-order term for non-parametric Thompson
  sampling on $\mathcal P[0,1]$: $\mathbb E N_a(T)\le\log T/\mathcal K_{\inf}+O((\log T)^\beta)$ with
  an explicit $\beta<1$ ([RH20, Theorem 5] gives $o(\log T)$, K16). (c) In a multi-parameter family
  other than the Gaussian one, the priors for which Thompson sampling is asymptotically optimal
  (the Gaussian answer is K14 and K40; open problem of [HT14, Section 5], K61; search the later
  literature first). Answer: theorem for one class, with the exact constant.

### D. The distribution of the regret

- **D11. High probability and asymptotic optimality together.** (a) Is there a horizon-dependent
  family, asymptotically optimal on $\mathcal P[0,1]^\alpha$ (or on Bernoulli instances), whose regret
  is $T$-upper tailed in the sense of [SA11, Definition 1]
  ($\mathbb P(\hat R_T\ge C\log T/\Delta)\le C'/T$)? Known: ucb-h (K55) is $T^\beta$-upper tailed for
  every $\beta>0$, but its index is of Hoeffding type and no first-order optimality is claimed for
  it; no anytime algorithm is $f$-upper tailed for an $f$ with $f\gg\log^\gamma$ for every $\gamma$
  (K33). (b) For anytime algorithms that are
  asymptotically optimal on $\mathcal P[0,1]$ (or Bernoulli), the exact tail exponent of
  $N_a(T)$, in the sense of [FG24, Theorem 1] (proved there for exponential families; on
  $\mathcal P[0,1]$ the essential infimum of the optimal arm matters, K32). Answer: theorem with the
  exact exponent and an explicit range of $x$.
- **D12. Moments of the regret.** For an asymptotically optimal algorithm (KL-UCB, IMED or
  Thompson sampling) on a given model, the exact growth order of $\mathbb E[\hat R_T^p]$, $p>1$, and
  the smallest possible order of $\mathrm{Var}(\hat R_T)$ among algorithms with
  $R_T\le(1+\varepsilon)\,C^\star\log T$ eventually. [FG24] states in its abstract that the
  $p$-th moment grows as a power of $T$; read its Section 4 first (not read for KNOWN.md): the
  direction is what it leaves open. Answer: matching bounds on the order.

### E. Structured bandits (finitely many arms, known structure)

- **D13. When is optimism enough?** For a structured class $\mathcal E$ (finitely many arms,
  Gaussian or one-parameter exponential-family rewards), give a condition, checkable on the
  Graves–Lai problem, under which a stated optimistic algorithm (for example KL-UCB with confidence
  sets intersected with $\mathcal E$) attains $C(\nu;\mathcal E)$ for every $\nu$, and show that the
  algorithm fails when the condition fails. Known: true for product classes (K9); false for linear
  classes (K35); unimodal structures need a local rule (K29). Answer: a characterization, or a
  sufficient condition plus a counterexample just outside it.
- **D14. How much forced exploration?** Some finite classes force $\Omega(\log\log T)$ pulls of an
  arm that the Graves–Lai allocation does not use (K36). Question: for every finite structured class
  with Gaussian rewards (or every class satisfying the regularity of [DSK20, Assumption 1]), is
  there an algorithm attaining $C(\nu;\mathcal E)$ whose expected number of pulls of every such arm
  is $O(\log\log T)$? Answer: algorithm and proof, or a class where more is necessary.
- **D15. Simple, exactly optimal structured algorithms.** Algorithms that solve the Graves–Lai
  problem only at a sparse set of rounds (for example $2^j$) or only approximately, with exact
  asymptotic optimality — not up to a factor $F(\varepsilon,\gamma)$ as [CMP17, Theorem 2] nor up to
  a constant as [JZ20, Theorem 1] (K26, K30) — under stated regularity of $\mathcal E$, with their
  computational cost per round; and finite-time bounds $C(\nu;\mathcal E)\log T+o(\log T)$ with an
  explicit remainder. Answer: theorem with explicit assumptions.
- **D16. Asymptotically optimal and never much worse than UCB.** For a finite structured class with
  Gaussian rewards, an algorithm attaining $C(\nu;\mathcal E)$ with
  $R_T(\nu)\le c_1R_T^{\mathrm{UCB}}(\nu)+c_2$ for every $\nu$ and $T$ (open problem of
  [JZ20, Section 6], K66; "most obvious open problem" of [DSK20, Section 4], K67); for finite
  linear bandits, the asymptotic optimality of IDS without the assumption $x^\star\ne 0$ (K31, K68).
  Answer: theorem, or a lower bound showing the two requirements are incompatible on some class.
- **D17. Degenerate structured instances.** Several optimal arms, $C(\nu;\mathcal E)\in\lbrace 0,\infty\rbrace$,
  alternatives on the boundary of $\mathcal E$: the right definition of the constant, the matching
  lower and upper bounds, and a characterization of the finite classes on which bounded regret is
  attainable for every instance (K30 gives bounded regret in one regime). Answer: theorem in the
  generality of finite classes.

### F. Lower-bound techniques as library material

- **D18. A change-of-measure toolkit for LML runs**, beyond F1: (a) quantile forms — lower bounds on
  $\mathbb P(N_a(T)\ge x)$ from the data-processing inequality applied to indicators, as used by
  K33 and K34; (b) a finite-time Graves–Lai bound for any class $\mathcal E$ under a constraint
  $R_T(\nu')\le C'T^p$ on a neighbourhood, generalizing [LS, Lemma 16.3 and Theorem 16.4] (K3)
  from Gaussian product classes; (c) the $\alpha$-consistent version $(1-\alpha)C(\nu;\mathcal E)$ of
  the Graves–Lai bound, generalizing K6. Each block must name the item (D or F) whose paper uses it.
  Answer: the statement in the generality of LML runs and arbitrary classes.

## What would be an important result

- The exact constant of the minimax regret in one model, or a policy that attains it (D19).
- Matching lower and upper bounds that close a direction: the coefficient of $\log\log T$ (D1), the
  transition horizon (D3), an exact first-order constant where only constant factors are known (D8),
  an exact tail exponent (D11), a characterization (D13, D14).
- A formal refutation of a natural conjecture: that an index strategy can be minimax, sub-UCB and
  asymptotically optimal (D4b); that a simple optimistic or Thompson rule is optimal on a natural
  structured class (D13); that a moment condition suffices (D9).
- A simple algorithm (stated by its formula, with a stated cost per round) that is exactly optimal
  where only complicated or constant-factor algorithms were known (D6, D8, D15).
- A tool proved once in library generality and used by at least two later papers (F1, D7, D18).

Not important on their own: known bounds re-derived with worse constants; the special case of a
known theorem whose proof applies verbatim (for example the Gaussian case of an exponential-family
result); a new algorithm supported by simulations only; first-order results "up to a constant
factor" in a model where the exact constant is known; a lemma that no item uses; anything already
in LMLExplore or planned by its Bandits roadmap (Appendix B).

## Out of scope

Batched bandits and limited adaptivity, on imposed or chosen grids (roadmap BatchedBandits); transfer
learning from historical data (roadmap TransferBandits); adversarial bandits and best-of-both-worlds
guarantees; contextual bandits with changing contexts, and structured classes with infinitely many
arms (finite linear, unimodal, Lipschitz-on-a-finite-metric or other structures on a finite arm set
are in scope); reinforcement learning and Markov decision processes; pure exploration and best-arm
identification, except as a tool for a regret result; non-stationary bandits; Bayesian regret and
Gittins indices. They may become roadmaps of their own. (The constant of the minimax regret, out of
scope in the first draft, is direction D19 since 2026-11-14.)

## Acceptance criteria for papers

Besides AGENTS.md §5, the referees check that a paper of this roadmap:

1. states, in its Main result, the model or structured class, the class of algorithms (consistency
   notion, anytime or horizon-dependent), and the criterion (order, constant, finite time or
   asymptotic, counts, regret or tails, with the range of $x$ for tails);
2. names, in Closest known, every KNOWN entry and dependency theorem (Appendix B) it extends, and
   shows where an attempt to derive the main result from them fails;
3. exhibits, in Sanity checks, one instance satisfying all hypotheses, and checks Bernoulli or
   Gaussian instances with $K=2$ against K1 (first order) and, for structured results, the product
   class against the identity $C(\nu;\prod_a\mathcal D_a)=\sum_a\Delta_a/\mathcal K_{\inf}$;
4. for a lower bound, makes the class of algorithms explicit; for an upper bound, defines the
   algorithm completely by its formula (parameters, tie rule, initialization, anytime or not) and
   states its cost per round when the direction mentions computation;
5. gives the constants explicitly, or says that they are existential and on what they depend;
6. never defines "optimal": optimality is a corollary pairing a lower and an upper bound in one
   class;
7. **is not routine**: if the scope referee can write a complete proof of the main result from
   KNOWN entries, the dependencies (Appendix B) and textbook facts in about half a page (for
   example one change of measure with Bretagnolle–Huber between two given instances), the result is
   a corollary of the literature (class **F**), unless the paper serves an F item;
8. **as a building block** (a lemma paper), is accepted only if (i) it is stated in the generality
   of the conventions (classes of laws, LML runs, not one instance), (ii) it names the item (D, F or
   C) whose paper uses it and the step where it is used, (iii) it is not available in Mathlib, LML,
   LMLExplore at the pinned revisions or in the library, and (iv) it passes criterion 7; a block
   that fails (ii) or (iii) is **F**;
9. improves only constants or lower-order terms only when its direction asks for them (D1, D2, D3,
   D8, D11, D12, D19), and then states the previous best value and the new one;
10. serving a direction, is not one of the "not important on their own" results above.

## Appendix A. Correspondence with the drafts RegretShape and StructuredBandits

| Draft item | Here |
|---|---|
| RegretShape F0 (classes of [GMS19] as predicates) | F0 |
| RegretShape F1 (fundamental inequality) | F1 |
| RegretShape F2 (large-horizon lower bound with $\log\log T$) | F3 |
| RegretShape F3 (small-horizon lower bounds) | F2 |
| RegretShape F4 (Lai–Robbins as a corollary) | dropped: already in LMLExplore (`LaiRobbins`, K1) |
| RegretShape F5 (one explicit second-order upper bound) | F9 (on hold) and D2 |
| RegretShape D1, D2 (order, sign, constant of the second-order term) | D1 (the order and the sign are now known in the classes of K5 and K11; the constant is open) |
| RegretShape D3 (trade-off with the rate of consistency) | D1 (dependence on $C$ in $\mathcal S_C$) and D18(c) |
| RegretShape D4 (the transition) | D3 |
| RegretShape D5 (model dependence) | D1 (one model per paper) and D7 |
| RegretShape D6 (batched and transfer bandits) | out of scope (other roadmaps) |
| StructuredBandits F0 (structure, alternatives, Graves–Lai constant) | F0 (a structure is a set $\mathcal E$ of kernels; no new type) |
| StructuredBandits F1 (Graves–Lai lower bound) | F5 |
| StructuredBandits F2 (properties of $C(\theta)$) | F0 (product identity), D15, D17 |
| StructuredBandits F3 (end of optimism) | F8 |
| StructuredBandits D1, D2, D3, D4, D5 | D13, D14, D15 and D16, D15, D17 |

## Appendix B. What the dependencies already provide

Read on LMLExplore at Incognita's pinned revision `b4e0ab9` (files `LMLExplore/Bandits/*.lean`,
declaration names only) and in its roadmap `LMLRoadmaps/Bandits/README.md`, 2026-11-14. Check at the
pinned revision before use.

- **Proved** (LMLExplore, namespace `LMLExplore.Bandits`): `IsConsistent`, `dInf` with its values
  for Gaussian, Bernoulli and exponential families (`dInf_range_gaussianReal`,
  `dInf_range_bernoulliMeasure`, `dInf_image_expFamily`); the Lai–Robbins bound for unstructured
  classes (`eventually_mul_log_le_integral_pullCount_of_isConsistent`,
  `eventually_mul_log_le_integral_regret_of_isConsistent`) and its one-alternative core valid for any
  class (`eventually_mul_log_le_integral_pullCount_of_klDiv`); the two-bandit inequality
  `mul_exp_neg_le_integral_regret_add_integral_regret`, [LS, Lemma 16.3]
  (`log_div_le_integral_pullCount`) and [LS, Theorem 16.4] for Gaussians
  (`le_integral_regret_gaussianBandit`); KL-UCB for exponential families and Bernoulli laws with its
  asymptotic optimality (`klucbFam`, `klucb`, `tendsto_klucbFam_regret_div_log`,
  `tendsto_klucb_regret_div_log_bernoulliBandit`); asymptotically optimal UCB (`ucbF`); Gaussian
  Thompson sampling with its asymptotic optimality (`gaussianTS`,
  `tendsto_gaussianTS_regret_div_log_gaussianBandit`); MOSS (`moss`, `moss_regret_le`); index and
  weight policies; Bretagnolle–Huber, chain rule and Bernoulli divergence
  (`LMLExplore/InformationTheory/KullbackLeibler/`).
- **Planned by LMLExplore's Bandits roadmap** (do not duplicate): Thompson sampling with the
  Jeffreys prior for exponential families [KKM13, Theorem 1] (Layer 5.3); linear bandits OFUL,
  phased elimination and minimax lower bounds (Layers 8–9).
- **Outside LMLExplore's scope**, hence open to this roadmap: high-probability lower bounds and
  asymptotic lower bounds for linear (and structured) bandits.
