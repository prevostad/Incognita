# Blueprint of P001-minimax-constant

Lean names of the paper's nodes. Statuses are computed by the audit, not stored here.

Phase 1 is split in two pull requests (AGENTS.md §6.1, at most about 800 lines of Lean each). The
first one (this file's first version) adds the definitions of the model and of the limit game with
their checks and catalogue entries; the second one adds the constants of `def:kappa`, the frozen
statements, their witnesses and the back-translations. Rows marked *planned* name what the second
pull request freezes; they are not on `main` yet.

| Label | Kind | Lean name | Notes |
|---|---|---|---|
| def:regret | definition | Incognita.StochasticBandits.minimaxRegret | new; learners are LML's `Algorithm Unit α ℝ`, the regret is LML's `regret`; $R_T(\pi,\nu)$ inline as `∫ ω, regret ν IT.action T ω ∂(trajMeasure alg (Environment.bandit ν))`; $\mathcal C^K$ = `productClass fun _ ↦ C` (P007) |
| def:class | definition | Incognita.StochasticBandits.subGaussClass | new |
| def:regular | definition | Incognita.StochasticBandits.RegularR1, Incognita.StochasticBandits.RegularR2, Incognita.StochasticBandits.IsRegular | new; (R1), (R2), and both |
| def:lowR2 | definition | Incognita.StochasticBandits.ContainsExpFamily, Incognita.StochasticBandits.ContainsPerturbations | new; the two cases of (R2); the family is LMLExplore's `Measure.expFamily ν₀ id θ` |
| def:alloc | definition | Incognita.StochasticBandits.LimitGame.Omega, Incognita.StochasticBandits.LimitGame.allocations, Incognita.StochasticBandits.LimitGame.filtration | new |
| def:limit | definition | Incognita.StochasticBandits.LimitGame.IsLimitPolicy | new; brackets written by martingales (Modelling decisions) |
| def:risk | definition | Incognita.StochasticBandits.LimitGame.likelihood, Incognita.StochasticBandits.LimitGame.loss, Incognita.StochasticBandits.LimitGame.risk, Incognita.StochasticBandits.LimitGame.value, Incognita.StochasticBandits.LimitGame.bayesValue | new; in `ℝ≥0∞` |
| def:batched | definition | Incognita.StochasticBandits.LimitGame.valueOn, Incognita.StochasticBandits.LimitGame.localValue | new; $V_K(H)$ and $V_K^{\mathrm{loc}}$; the batched value $V^\flat(H)$ is not defined (Open problems) |
| def:g-pol | definition | (not defined) | strong model, discrete and batched policies (Open problems) |
| def:kappa | definition | (planned, second pull request) | planned `Incognita.StochasticBandits.uStar`, `kappa`, `lambdaK`; `h` is Mathlib's `Real.binEntropy` |
| def:sc | definition | (not defined) | Screen-Core (Open problems) |
| def:opt2 | definition | (not defined) | Opt₂ has no proved guarantee in the paper; nothing to freeze |
| thm:main | frozen (planned) | Incognita.Statements.P001.tendsto_minimaxRegret | the limit, for a regular class, in eventual form |
| thm:main | frozen (planned) | Incognita.Statements.P001.lower_bound | part (i): the lower bound under (R2) alone |
| thm:main | frozen (planned) | Incognita.Statements.P001.upper_bound | part (ii): the upper bound under (R1) alone, as a bound on $R^\star$; the claim on Screen-Core waits for def:sc |
| cor:examples | frozen (planned) | Incognita.Statements.P001.examples_unitLaws, examples_bernoulli, examples_bernoulli_half, examples_interval, examples_gaussian, examples_gaussian_box | one statement per class, and the non-asymptotic Gaussian bound |
| prop:four | frozen (planned) | Incognita.Statements.P001.four_minimax, four_local, four_translate, four_invariant, four_mono | (a); (b) without $V^\flat$; (c) in three statements |
| thm:bounds | frozen (planned) | Incognita.Statements.P001.bounds, bounds_gaussian | the two-sided bound, and the non-asymptotic Gaussian bound |
| cor:four-c | frozen (planned) | Incognita.Statements.P001.local_gaussian | the local Gaussian minimax regret, in eventual form |
| prop:K2 | not frozen | | the paper says it is not a statement to formalise (it rests on (H$_{\mathrm{fp}}$), about two computer runs) |
| thm:u-upper | not frozen yet | | needs def:sc and def:u-batched (Open problems) |
| thm:lowEF, prop:lowtilt, prop:u-local, cor:u-gauss, cor:g-cont, prop:K2-relax, prop:K2-Lnum, prop:K2-Unum | lemma | (added by prove) | appendix results; cor:u-gauss is the Gaussian part of cor:examples (planned `examples_gaussian_box`) |
| lem:* | lemma | (added by prove) | |
| cite:GMS19-Lemma1, cite:LS19-Thm6.1 | cited | (added by prove) | |

Checks of the definitions (AGENTS.md §6.4), proved in this pull request:

- `Incognita/StochasticBandits/Minimax.lean`: `minimaxRegret_singleton`,
  `ofReal_le_minimaxRegret_gaussian` (the lower bound $\frac1{16}\sqrt{(K-1)T}$ of [LS, Theorem
  15.2] from LMLExplore), `minimaxRegret_gaussian_ne_zero`; `gaussianReal_mem_subGaussClass`,
  `unitLaws_subset_subGaussClass`, `dirac_not_mem_subGaussClass`; `regularR1_subGaussClass`,
  `not_regularR1_dirac`, `containsPerturbations_univ`, `not_regularR2_dirac`, `isRegular_gaussian`
  (the Gaussian laws with means in $[a,b]$ and variance at most $\bar\sigma^2$),
  `isRegular_unitLaws` (the laws on $[0,1]$, with $\bar\sigma=\frac12$).
- `Incognita/StochasticBandits/LimitGameChecks.lean`: `singleArm_mem_allocations`,
  `uniform_mem_allocations`, `zero_not_mem_allocations`; `isLimitPolicy_singleArmPolicy`,
  `IsLimitPolicy.integral_sq_eq`, `not_isLimitPolicy_dirac`; `risk_zero`, `risk_singleArmPolicy`;
  `value_eq_valueOn_univ`, `valueOn_mono`, `bayesValue_dirac`, `localValue_le_value`,
  `valueOn_singleton_zero`.
- `Incognita/ForTauCeti/Probability/BrownianMotion/Martingale.lean`: the martingales $W$ and
  $W_t^2-t$ of a filtered Brownian motion (Tau Ceti's `IsFilteredPreBrownianReal`), used by the
  witness of `IsLimitPolicy`.

## Modelling decisions

- **Arms.** A finite type `α` with `[Fintype α] [DecidableEq α] [MeasurableSpace α]
  [MeasurableSingletonClass α]`, and `[Nontrivial α]` for $K\ge2$, as the roadmap pins. The paper
  enumerates the arms because its policies break ties by the smallest index; no frozen statement
  involves a policy of the paper, and the values do not depend on the enumeration
  ([INC-P001, Proposition `prop:four`(c)]). $\mathbb R^K$ is `α → ℝ`. The planned monotonicity
  $V_K\le V_{K+1}$ is `value α ≤ value (Option α)`.
- **Rounds.** LML's rounds `0, …, T - 1`; the paper's $N_k(T)$ counts the pulls in rounds
  $1,\dots,T$: the same quantity.
- **Learners and the minimax regret.** A horizon-dependent policy $(\pi_T)_T$ is evaluated at
  horizon $T$ by $\pi_T$ only, so $R^\star(T)=\inf_\pi\sup_\nu R_T(\pi,\nu)$ at a fixed $T$ is an
  infimum over single LML learners `Algorithm Unit α ℝ`. An LML learner draws each action from a
  kernel of the history (past actions and rewards): by Kuhn's theorem (the history recalls the
  learner's own actions), these behavioural policies give the same laws of the interaction as the
  policies with an external randomization $U$ of the paper, so the infimum is the same.
  `minimaxRegret E T` is in `ℝ≥0∞`, `⨅ alg, ⨆ ν ∈ E, ⨆ (_ : IsMarkovKernel ν), ofReal R_T`; the
  regret is bounded (finitely many arms), so its Bochner integral is the expectation. $R_T$ is
  LML's `regret`, $\sum_{s<T}\Delta_{A_s}$, whose expectation is $\sum_k\Delta_k\mathbb E N_k(T)$.
- **Classes.** A class of laws is a `Set (Measure ℝ)`; $\mathcal C^K$ is P007's
  `productClass fun _ ↦ C`. Means are Bochner integrals `∫ x, x ∂ν`; variances are `evariance id ν`
  in `[0, ∞]` (so that "variance at least $\sigma_0^2$" also holds for an infinite variance, which
  Case 3 of the proof of `thm:main`(i) allows); the sub-Gaussian condition of `def:class` is
  Mathlib's `HasSubgaussianMGF (fun x ↦ x - mean) (σ_p²).toNNReal ν`, which contains the
  integrability of $e^{\lambda(X-\mu)}$ that the inequality presupposes.
- **(R1).** `RegularR1 C σ̄ := 0 < σ̄ ∧ ∃ a b σ_p, a < b ∧ σ̄ ≤ σ_p ∧ C ⊆ subGaussClass a b σ̄ σ_p`;
  `0 < σ̄` is part of `def:class`.
- **(R2)** is read as the paper's own precise form, Definition `def:lowR2`: for every
  $\sigma_0\in(0,\bar\sigma)$ a probability $\nu_0\in\mathcal C$ with a finite mean and
  `ofReal σ₀² ≤ evariance id ν₀`, and (a) `ContainsExpFamily C ν₀` or (b)
  `ContainsPerturbations C ν₀`. The range $(0,\bar\sigma)$ of $\sigma_0$: a standard deviation is
  nonnegative, and $\sigma_0\le0$ asks nothing more (a negative $\sigma_0$ with $\sigma_0^2>\bar\sigma^2$
  would make (R2) contradict (R1), which the paper does not mean).
  - (a) The family is the tilt $\nu_\theta\propto e^{\theta x}\nu_0(dx)$ of $\nu_0$ itself, LMLExplore's
    `ν₀.expFamily id θ` (Mathlib's `Measure.tilted`); `def:lowR2`(a) writes it from any base measure
    with $\nu_{\theta_0}=\nu_0$, which is the same family reparametrized by $\theta-\theta_0$. "Natural
    parameter space contains a neighbourhood of $0$" is `0 ∈ interior (integrableExpSet id ν₀)`. The
    three intervals $(-\beta_0,\beta_0)$, $(-\beta_0,0]$, $[0,\beta_0)$ are the two sides and the one
    side. For $\theta$ outside the natural parameter space `expFamily` is a junk measure, but
    $\beta_0$ can always be shrunk into the neighbourhood, so the existential is the paper's.
  - (b) $(1+tg)\nu_0$ is `ν₀.withDensity (fun x ↦ ENNReal.ofReal (1 + t * g x))`; "bounded Borel
    $g$" is `Measurable g ∧ ∃ G, ∀ x, |g x| ≤ G`; the paper's "is a probability measure in
    $\mathcal C$ for every $|t|\le t_g$" is "is in $\mathcal C$": for $|t|\le t_g\le1/\sup|g|$ the
    density is nonnegative with integral $1$, and $t_g$ can always be shrunk.
- **The canonical space.** `Omega α := C(I, α → ℝ) × C(I, α → ℝ)` (time `I = unitInterval`), with
  Mathlib's Borel σ-algebra of the compact-open topology on each factor
  (`ContinuousMap.measurableSpace`; it is also the σ-algebra of the evaluations). The paper's
  $\Omega=C_0([0,1],\mathbb R^K)\times\mathcal A$ is the closed (`measurableSet_setOf_mem_allocations`)
  subset where $X(0)=0$ and $\tau\in\mathcal A$; a probability on $\Omega$ is a probability on
  `Omega α` carried by it (`IsLimitPolicy.ae_mem`), and the coordinate filtration restricts to the
  paper's.
- **Allocations.** `allocations α`: `∀ k, Monotone (τ · k)`, `τ 0 = 0`, `∀ t, ∑ k, τ t k = t`; the
  values in $[0,1]^K$ follow (`mem_Icc_of_mem_allocations`).
- **Filtration.** `filtration α` is Mathlib's `Filtration.natural` of the coordinates
  $(X(t),\tau(t))$: the raw filtration $\sigma((X(s),\tau(s)),s\le t)$ of `def:alloc`. The usual
  augmentation is not needed (the paper's Lemma `lem:g-UA`).
- **Limit policies.** "X is a continuous $(\mathcal F_t)$-martingale with
  $\langle X_k,X_j\rangle=\mathbf 1\{k=j\}\tau_k$" is written by the martingales that define the
  brackets: each `X_k` and each `X_k X_j - 1{k = j} τ_k` is a Mathlib `Martingale` for `filtration α`
  under `Q` (`IsLimitPolicy.martingale`, `IsLimitPolicy.martingale_mul`). This is the paper's own
  characterization, Lemma `lem:g-compact`(i) (processes $X_k$, $X_k^2-\tau_k$, $X_kX_j$ for
  $k\ne j$): the bracket of continuous local martingales is the unique continuous adapted process of
  finite variation $A$ with $MN-A$ a local martingale, $\tau$ is such a process, and the local
  martingales are true martingales because $\tau\le1$ (Burkholder–Davis–Gundy). Mathlib has no
  quadratic variation of continuous-time martingales, so this form is also the only one available.
  Paths are continuous by definition of `Omega`.
- **Risk and values.** `likelihood α h ω = exp(∑ h_k X_k(1) - (∑ h_k² τ_k(1)) / 2)`,
  `loss α h ω = ∑ (⨆ i, h i - h k) τ_k(1)`, `risk α Q h = ∫⁻ ofReal (likelihood * loss) ∂Q` in
  `ℝ≥0∞` (the integrand is nonnegative on the allocations, so this is the paper's expectation, finite
  or not). `value`, `valueOn H`, `bayesValue prior` are `⨅ Q (_ : IsLimitPolicy α Q)` of
  `⨆ h`, `⨆ h ∈ H`, `∫⁻ h, risk α Q h ∂prior`, all in `ℝ≥0∞`: the paper's infima, attained by its
  Lemma `lem:g-min` but not assumed attained here. `localValue α = ⨆ M > 0, valueOn α [-M, M]^α`
  (`Set.univ.pi fun _ ↦ Set.Icc (-M) M`).
- **Limits** (planned statements) are in eventual form, as the roadmap pins and the paper allows
  (Section `sec:setting`): $\lim_T R^\star(T)/\sqrt T=L$ in $[0,\infty]$ is
  `(∀ c < L, ∀ᶠ T in atTop, c * ofReal √T ≤ R⋆ T) ∧ (∀ c > L, ∀ᶠ T in atTop, R⋆ T ≤ c * ofReal √T)`
  with `c : ℝ≥0∞`, and $L=\bar\sigma V_K$ is `ENNReal.ofReal σ̄ * value α`.
- **Witnesses of the limit game.** Mathlib defines Brownian motion (`IsPreBrownianReal`,
  `IsBrownianReal`) but does not construct one, and a limit policy contains a Brownian motion
  ($\sum_k\tau_k(t)=t$). The witness `isLimitPolicy_singleArmPolicy` is therefore stated for any
  Brownian motion relative to a filtration (Tau Ceti's `IsFilteredPreBrownianReal`) with continuous
  paths starting at $0$: the policy that gives all the time to one arm. The same holds for
  `valueOn_singleton_zero` and `risk_singleArmPolicy`. The non-vacuity witnesses of the planned
  frozen statements do not need a limit policy: their hypotheses are about the classes of laws.

## Back-translations

None yet: the frozen statements come in the second pull request.

## Open problems

- **The batched value $V^\flat(H)$ and the strong model** (`def:g-pol`, the batched policies of
  `def:batched`, `def:u-batched`, `def:u-disc`): the strong model is the space
  $[0,1]\times C([0,\infty),\mathbb R)^K$ with the Wiener measures with drifts, which Mathlib does not
  construct. Without it, `prop:four`(b) is frozen without the batched value ($V_K=V_K^{\mathrm{loc}}=
  \lim_M V_K([-M,M]^K)$), and `cor:g-cont` is not frozen. A later pull request can define batched
  policies on any probability space carrying an independent uniform variable and independent
  Brownian motions (the risk only depends on their law).
- **Screen-Core** (`def:sc`) and `thm:u-upper`: Screen-Core runs the discretization (`def:u-disc`) of
  a continuous batched limit policy (`def:u-batched`) on virtual arms with added Gaussian noise.
  Defining it as an LML learner needs the batched policies above; the planned `upper_bound` freezes
  the consequence for $R^\star$ ($\limsup R^\star(T)/\sqrt T\le\bar\sigma V_K$ under (R1)), and the
  claim that Screen-Core attains it waits for these definitions.
- **`thm:bounds` and `def:kappa`**: planned for the second pull request ($u^\star$ as the positive root
  of $e^u=1+2u$, $\kappa=2a^\star/(1+(a^\star)^2)$, $\lambda_K=\exp(-K\,\mathrm h(1/K)/(K-1))$ with
  Mathlib's `Real.binEntropy`).
- **Exclusion of `value`**: that $V_K$ is not $0$ is the lower bound of `thm:bounds`, a frozen
  statement; no cheaper exclusion is known without a construction of Brownian motion.
