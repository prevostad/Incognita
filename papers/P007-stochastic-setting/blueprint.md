# Blueprint of P007-stochastic-setting

Lean names of the paper's nodes. Statuses are computed by the audit, not stored here.

| Label | Kind | Lean name | Notes |
|---|---|---|---|
| def:laws | definition | MeasureTheory.Measure, InformationTheory.klDiv, LMLExplore.klBer, ProbabilityTheory.bernoulliMeasure | reused: a law is a probability measure on `ℝ`; $\mathcal P_1$ written inline as `IsProbabilityMeasure Q ∧ Integrable id Q`; $m(P)$ = `∫ x, id x ∂P` (`P[id]`); KL = `klDiv`; kl = `LMLExplore.klBer`; Ber(p) = `bernoulliMeasure (1 : ℝ) 0 p` |
| def:kinf | definition | LMLExplore.Bandits.dInf | reused: $\mathcal K_{\inf}(P,\mu;\mathcal D)$ = `dInf D P μ` (strict inequality, `inf ∅ = ∞`, in `ℝ≥0∞`); a model is a set `D` with `∀ Q ∈ D, IsProbabilityMeasure Q ∧ Integrable id Q` |
| def:models | definition | Incognita.BatchedBandits.unitLaws | $\mathcal P[0,1]$ reused from P006; $\mathcal B$ = `Set.range fun p : unitInterval ↦ bernoulliMeasure (1 : ℝ) 0 p` (as in LMLExplore's `dInf_range_bernoulliMeasure`); $\mathcal S$, $\mathcal L_{\varepsilon,B}$, $\mathcal H_\kappa$, $\mathcal G$ not defined in this pull request (no frozen statement uses them; see Open problems) |
| def:instance | definition | ProbabilityTheory.Kernel, Bandits.gap | reused (LML): an instance is `ν : Kernel α ℝ`, arms `[Fintype α] [Nontrivial α]`; $m^\star$ = `⨆ b, (ν b)[id]`; $\Delta_a$ = `gap ν a`; unique optimal arm $a^\star$: `∀ a ≠ aStar, 0 < gap ν a` |
| def:product | definition | Incognita.StochasticBandits.productClass | new; $\mathcal D^\alpha$ = `productClass (fun _ ↦ D)` |
| def:learner | definition | Learning.Algorithm | reused (LML): `Algorithm Unit α ℝ` (anytime); horizon-dependent learners not defined in this pull request |
| def:run | definition | Learning.trajMeasure, Learning.Environment.bandit | reused (LML): $\mathbb P_{\pi,\nu}$ = `trajMeasure alg (Environment.bandit ν)`; rounds from 0 |
| def:regret | definition | Learning.pullCount, Bandits.regret | reused (LML): $N_a(t)$ = `pullCount IT.action a t`; $\hat R_T$ = `regret ν IT.action T`; $R_T$ its integral |
| def:consistent | definition | LMLExplore.Bandits.IsConsistent | reused for consistency (`γ = 0`); `γ`-consistency (`IsAlphaConsistent` in the roadmap) and the horizon-dependent version not defined in this pull request |
| def:ufc | definition | Incognita.StochasticBandits.IsUniformlyFastConvergent, Incognita.StochasticBandits.IsUniformlySuperFastConvergent | new (`Incognita/StochasticBandits/UCB.lean`) |
| def:smarter | definition | (not defined in this pull request) | planned `IsSmarterThanUniform` |
| def:gl | definition | Incognita.StochasticBandits.alt, Incognita.StochasticBandits.gravesLai | new; `alt E ν` is defined for every `ν` (no optimal arm of `ν` optimal in `ν'`) and equals the paper's $\mathrm{Alt}(\nu;\mathcal E)$ under a unique optimal arm (`mem_alt_iff_of_unique`); `gravesLai E ν` in `ℝ≥0∞` |
| lem:gl-reduction | lemma | (added by prove) | |
| thm:main | frozen | Incognita.Statements.P007.gravesLai_productClass | proof: Incognita.P007.gravesLai_productClass |
| prop:gl-zero | frozen | Incognita.Statements.P007.gravesLai_eq_zero_of_identifies | proof: Incognita.P007.gravesLai_eq_zero_of_identifies |
| cor:lower | frozen | Incognita.Statements.P007.lower_bound_gravesLai | proof: Incognita.P007.lower_bound_gravesLai; route: thm:main and LMLExplore's `eventually_mul_log_le_integral_regret_of_isConsistent` |
| lem:kinf-basic | lemma | (added by prove) | (ii) is `Incognita.BatchedBandits.dInf_anti` (already in the library) |
| lem:kinf-unit | lemma | (added by prove) | the value on $\mathcal B$ is LMLExplore's `dInf_range_bernoulliMeasure`; on $\mathcal P[0,1]$, P006's `kinf_bernoulli` |
| lem:kinf-p1 | lemma | (added by prove) | |
| lem:kinf-gauss | lemma | (added by prove) | needs $\mathcal G$ (`gaussianLaws`), not defined here |
| lem:semi | lemma | (added by prove) | needs $\mathcal S$, $\mathcal L_{\varepsilon,B}$ |
| lem:kurt | lemma | (added by prove) | needs $\mathcal H_\kappa$ |
| lem:classes | lemma | (added by prove) | (i) for consistency is LMLExplore's `IsConsistent.mono` |
| lem:stack | lemma | (added by prove) | LML's `RewardByCountMeasure.lean` |
| def:ucb | definition | Incognita.StochasticBandits.hoeffdingIndex, Incognita.StochasticBandits.IsHoeffdingUCB, Incognita.StochasticBandits.hoeffdingUCB | new; "UCB with some tie rule" is `IsHoeffdingUCB alg` (every policy kernel concentrated on the argmax of the index (`eq:ucb`)); `hoeffdingUCB` is the instance with LML's `argmax` tie rule |
| prop:ucb | frozen | Incognita.Statements.P007.ucb_pullCount_le, Incognita.Statements.P007.ucb_isUniformlySuperFastConvergent, Incognita.Statements.P007.ucb_isConsistent, Incognita.Statements.P007.ucb_isUniformlyFastConvergent | one statement per claim: the bound for `T ≥ 1`; super-fast with the constant 13 (which is the bound for `T ≥ 2`); consistent on both classes; uniformly fast convergent on both classes; proofs: `Incognita.P007.` and the same names |
| lem:constant | frozen | Incognita.Statements.P007.not_isConsistent_const, Incognita.Statements.P007.not_isUniformlyFastConvergent_const, Incognita.Statements.P007.not_isUniformlySuperFastConvergent_const | the three exclusions of `Cons^b` with defined classes: not consistent, not uniformly fast convergent, not uniformly super-fast convergent with any constant; proofs: `Incognita.P007.` and the same names (the last two are the library checks `Incognita.StochasticBandits.not_isUniformlyFastConvergent_const` and `not_isUniformlySuperFastConvergent_const`); not frozen: items (i)–(ii) (computations; the first half of (i) is `Incognita.StochasticBandits.integral_pullCount_const_self`), the non-consistency of the uniform learner, and the claims that need `γ`-consistency for `γ > 0` or def:smarter |
| def:pairwise | definition | (not defined in this pull request) | planned `IsPairwiseSymmetricOptimal` |
| def:monotonic | definition | (not defined in this pull request) | planned `IsMonotonic` |
| def:tails | definition | (not defined in this pull request) | planned `HasUpperTailedPullCount`, `HasUpperTailedRegret` |
| def:family | definition | (not defined in this pull request) | planned `IsConsistentFamily` and family versions |
| lem:gms-classes | lemma | (added by prove) | needs def:pairwise, def:monotonic |
| lem:tails | lemma | (added by prove) | needs def:tails |
| prop:ucb-tails | frozen | Incognita.Statements.P007.ucb_tail_pullCount | the display only; the "Hence" sentence needs def:tails (Open problems); proof: Incognita.P007.ucb_tail_pullCount |
| lem:family | lemma | (added by prove) | needs def:family |
| cite:INC-P006-prop:kinf | cited | Incognita.Statements.P006.kinf_eq_top_of_one_le, Incognita.Statements.P006.kinf_eq_zero_of_lt_mean, Incognita.Statements.P006.kinf_bounds, Incognita.Statements.P006.kinf_bernoulli, Incognita.Statements.P006.kinf_bounds_of_gap_pos | the frozen statements of P006, items (i)–(v) |
| cite:GMS19-thm1 | cited | LMLExplore.Bandits.eventually_mul_log_le_integral_pullCount_of_isConsistent | reused, in the consistent (not uniformly fast convergent) form, which is what cor:lower uses |
| lem:mix | lemma | (added by prove) | P006's `klDiv_le_ofReal_neg_log_smul_add_smul` is the mixture bound |
| lem:kl | lemma | (added by prove) | |
| lem:ucb-basic | lemma | (added by prove) | |
| lem:ucb-decomp | lemma | (added by prove) | |
| lem:ucb-terms | lemma | (added by prove) | |

## Modelling decisions

- **Arms and instances.** As in the roadmap's Lean conventions and in P006: arms a type `α` with
  `[Fintype α]`, and `[Nontrivial α]` for the paper's $K\ge2$; `[MeasurableSpace α]
  [MeasurableSingletonClass α]` wherever an instance has to be built from a family of laws (a kernel
  on a finite discrete type is any family). An instance is `ν : Kernel α ℝ`; the paper's condition
  $\nu_a\in\mathcal P_1$ is written as a hypothesis (`IsProbabilityMeasure (ν a) ∧ Integrable id
  (ν a)`, or `[IsMarkovKernel ν]` plus integrability) where a statement needs it, or follows from
  `ν ∈ productClass D` and the hypothesis that the models lie in $\mathcal P_1$.
- **Means.** Bochner integrals `∫ x, id x ∂Q` (`Q[id]`), as in LML's `gap` and LMLExplore's
  `dInf`; they are the paper's means on $\mathcal P_1$, and every frozen statement restricts to
  $\mathcal P_1$ as the paper does (models are subsets of $\mathcal P_1$, Definition `def:kinf`).
- **$\mathcal K_{\inf}$** is LMLExplore's `dInf`, which has the strict inequality and
  `inf ∅ = ∞`, as the roadmap pins. No new definition.
- **Unique optimal arm.** `∀ a ≠ aStar, 0 < gap ν a`, with `aStar` a variable of the statement.
- **Alternatives.** `alt E ν := {ν' ∈ E | ∀ a, gap ν a = 0 → 0 < gap ν' a}`. It does not take
  `a⋆` as an argument, so that `gravesLai E ν` is a function of `E` and `ν` as in the paper; under a
  unique optimal arm it is the paper's set (`mem_alt_iff_of_unique`).
- **Graves–Lai constant.** `gravesLai E ν := ⨅ w ∈ feasible, ∑ a, w a * ENNReal.ofReal (gap ν a)`
  over `w : α → ℝ≥0∞` with `1 ≤ ∑ a, w a * klDiv (ν a) (ν' a)` for every `ν' ∈ alt E ν`: the
  paper's weights in $[0,\infty]$, with `0 * ∞ = 0` and `x + ∞ = ∞` of `ℝ≥0∞`, and `inf ∅ = ∞`.
- **Quotients.** $\Delta_a/\mathcal K_{\inf}$ is the division of `ℝ≥0∞` (`x / 0 = ∞` for `x ≠ 0`,
  `x / ∞ = 0`), as in LMLExplore's Lai–Robbins bound; the sum of thm:main runs over
  `Finset.univ.filter (fun a ↦ 0 < gap ν a)`, the arms `a ≠ a⋆`.
- **liminf.** cor:lower is in eventual form, `∀ c, ENNReal.ofReal c < C → ∀ᶠ T, c log T ≤ R_T`,
  as in LMLExplore and as the roadmap pins.
- **Learners.** LML's `Algorithm Unit α ℝ`, run by `trajMeasure`, which needs no
  `[StandardBorelSpace α]`. LMLExplore's Lai–Robbins bound assumes it; no frozen statement does,
  since it follows from `[Fintype α] [MeasurableSingletonClass α]` (Mathlib's
  `standardBorelSpace_of_discreteMeasurableSpace`).
- **The constant learner** $\pi^b$ is LML's `Algorithm.const (Measure.dirac b)`.
- **UCB and its tie rules.** The index (`eq:ucb`) is `hoeffdingIndex n h a` in `EReal`: `⊤` for an
  arm never pulled, `μ̂_a + √(2 log (n + 1) / N_a)` otherwise, built from LML's `pullCount'` and
  `empMean'` on histories. The paper's learner "UCB with the tie rule `(ρ_t)`" is `π = (ρ_t)`, so
  "for every tie rule" becomes "for every `alg` with `IsHoeffdingUCB alg`", the predicate that
  every policy kernel gives mass 1 to the argmax set. `hoeffdingUCB` (LMLExplore's
  `indexAlgorithm`) is one such learner.
- **Convergence classes.** `IsUniformlyFastConvergent alg E` and
  `IsUniformlySuperFastConvergent alg E C` quantify over the Markov kernels of `E`, the arms with
  `0 < gap ν a`, and `p ∈ (0, 1]` (resp. `T ≥ 2`), as in Definition `def:ufc`; expectations are
  integrals of `pullCount IT.action a T` under `trajMeasure`.

## Back-translations

### Incognita.Statements.P007.gravesLai_productClass (thm:main)

Read from the Lean: let `α` be a finite type with at least two elements and the discrete
σ-algebra, and for each arm `a` let `D a` be a set of probability measures on `ℝ` with finite
first moment. Let `ν` be a kernel from `α` to `ℝ` with `ν a ∈ D a` for every `a`, and `aStar` an arm
such that every other arm has a positive gap (largest mean minus its mean). Then the infimum, over
the weights `w : α → [0, ∞]` such that `∑_a w_a KL(ν_a, ν'_a) ≥ 1` for every kernel `ν'` with
`ν' a ∈ D a` for all `a` in which every optimal arm of `ν` has a positive gap, of
`∑_a w_a Δ_a`, equals the sum over the arms of positive gap of `Δ_a / dInf (D a) (ν a) m⋆`, in
`[0, ∞]`.

Differences with the paper's node: none in substance. The alternatives are described through all
optimal arms of `ν`, which under the hypothesis is the arm `a⋆` alone; the sum over `a ≠ a⋆` is
written over the arms of positive gap, the same set; the "in particular" sentence is the case of a
constant family.

### Incognita.Statements.P007.gravesLai_eq_zero_of_identifies (prop:gl-zero)

Read from the Lean: for a finite type `α` with at least two elements, a set `E` of kernels whose
laws are probability measures with finite mean, and a kernel `ν` with the same property and a unique
optimal arm `aStar`: if every `ν' ∈ E` with `ν' aStar = ν aStar` equals `ν`, then
`gravesLai E ν = 0`.

Differences with the paper's node: none; the finite-mean hypotheses are the paper's convention that
instances are families of laws of $\mathcal P_1$. As in the paper, `ν ∈ E` is not assumed.

### Incognita.Statements.P007.lower_bound_gravesLai (cor:lower)

Read from the Lean: for a finite type `α` with at least two elements (discrete σ-algebra), a
set `D` of probability measures with finite mean, an algorithm consistent (LMLExplore's sense) on
the kernels with all arms in `D`, a Markov kernel `ν` with all arms in `D` and a unique optimal arm,
and a real `c` with `ofReal c < gravesLai (productClass (fun _ ↦ D)) ν`: eventually in `n`,
`c log n` is at most the expected regret `E[∑_{t<n} Δ_{A_t}]` of the algorithm on `ν`.

Differences with the paper's node: the `liminf` in $[0,\infty]$ is in eventual form; the two are
equivalent (for `C > 0` every `c < C` is covered; for `C = 0` the paper's claim is trivial since
the regret is nonnegative, and the Lean statement claims nothing).

### Incognita.Statements.P007.not_isConsistent_const (lem:constant, consistency part)

Read from the Lean: for a finite type `α` with at least two elements, a set `E` of kernels that
contains a Markov kernel `ν` with finite means in which the arm `b` has a positive gap, the
algorithm that always plays `b` is not consistent on `E` in LMLExplore's sense.

Differences with the paper's node: this is the part "$\pi^b$ is not consistent (γ = 0)" of the
consequence of `lem:constant`; the exclusions of uniform fast and super-fast convergence are the two
statements below. Not frozen: the computations (i)–(ii) of the lemma (they use no new class; the
first half of (i) is the library lemma `integral_pullCount_const_self`), the non-consistency of the
uniform learner, and the claims on `γ`-consistency for `γ > 0` and on def:smarter, which need
definitions not made here.

### Incognita.Statements.P007.not_isUniformlyFastConvergent_const (lem:constant, fast convergence)

Read from the Lean: for a finite type `α` with at least two elements (discrete σ-algebra), a set
`E` of kernels that contains a Markov kernel `ν` with finite means in which the arm `b` has a
positive gap, the algorithm that always plays `b` is not uniformly fast convergent on `E`: it is
false that `E[N_a(T)] / T^p → 0` for every Markov `ν' ∈ E`, every arm `a` of positive gap in `ν'`
and every `p ∈ (0, 1]`.

Differences with the paper's node: none; the other parts of the lemma are as above.

### Incognita.Statements.P007.not_isUniformlySuperFastConvergent_const (lem:constant, super-fast convergence)

Read from the Lean: under the same hypotheses, there is no real `C` such that the algorithm that
always plays `b` satisfies `E[N_a(T)] ≤ C log T / Δ_a²` for every Markov `ν' ∈ E`, every arm `a` of
positive gap in `ν'` and every `T ≥ 2`.

Differences with the paper's node: the paper takes `C > 0`; excluding every real `C` is the
stronger statement, and it is still true.

### Incognita.Statements.P007.ucb_pullCount_le (prop:ucb, first display)

Read from the Lean: for a finite type of at least two arms (discrete σ-algebra), every algorithm
whose policies are concentrated on the maximisers of `hoeffdingIndex`, every Markov kernel whose
laws are all concentrated on `[0, 1]`, every arm `a` of positive gap and every `T ≥ 1`, the expected
number of pulls of `a` in the rounds `0, …, T - 1` is at most
`8 log T / Δ_a² + 2 / Δ_a² + 5 / 4`.

Differences with the paper's node: none.

### Incognita.Statements.P007.ucb_isUniformlySuperFastConvergent (prop:ucb)

Read from the Lean: for such an algorithm, every Markov kernel with laws on `[0, 1]`, every arm of
positive gap and every `T ≥ 2`, `E[N_a(T)] ≤ 13 log T / Δ_a²`.

Differences with the paper's node: none (the paper's second inequality and "uniformly super-fast
convergent with the constant 13" are this one statement).

### Incognita.Statements.P007.ucb_isConsistent (prop:ucb)

Read from the Lean: such an algorithm is consistent (LMLExplore's `IsConsistent`) on the kernels
with laws on `[0, 1]`, and on the kernels whose laws are Bernoulli laws `Ber(p)`, `p ∈ [0, 1]`.

Differences with the paper's node: none.

### Incognita.Statements.P007.ucb_isUniformlyFastConvergent (prop:ucb)

Read from the Lean: such an algorithm is uniformly fast convergent on the same two classes: for
every Markov kernel of the class, every arm of positive gap and every `p ∈ (0, 1]`,
`E[N_a(T)] / T^p → 0`.

Differences with the paper's node: none.

### Incognita.Statements.P007.ucb_tail_pullCount (prop:ucb-tails)

Read from the Lean: for such an algorithm, every Markov kernel with laws on `[0, 1]`, every arm `a`
of positive gap and every `T ≥ 2`, the probability under the run that
`N_a(T) ≥ 10 log T / Δ_a²` is at most `1 / (log T)²`.

Differences with the paper's node: the "Hence" sentence (membership in the classes of Definition
`def:tails`) is not frozen, since those classes are not defined in this pull request.

## Open problems

- **Not defined in this pull request**: `def:smarter`, `def:pairwise`, `def:monotonic`,
  `def:tails`, `def:family`, `γ`-consistency (`def:consistent` for `γ > 0`) and the models
  $\mathcal S$, $\mathcal L_{\varepsilon,B}$, $\mathcal H_\kappa$, $\mathcal G$. No frozen
  statement uses them. The lemmas that need them (lem:kinf-gauss, lem:semi, lem:kurt,
  lem:gms-classes, lem:tails, lem:family, parts of lem:classes and lem:constant) and the "Hence"
  sentence of prop:ucb-tails wait for a later statements pull request that defines them.
- No node seems false or ill-posed.
