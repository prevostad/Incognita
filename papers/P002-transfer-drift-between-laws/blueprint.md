# Blueprint of P002-transfer-drift-between-laws

Lean names of the paper's nodes. Statuses are computed by the audit, not stored here.

| Label | Kind | Lean name | Notes |
|---|---|---|---|
| def:laws | definition | `Incognita.TransferBandits.probVecs`, `lawVec`, `vecMean`, `vecKL`, `vecKs` | `𝒫_S`, the vector of a law, `m`, `KL`, `K_S`; `Incognita/TransferBandits/LawDrift.lean` |
| def:ipm | definition | `Incognita.TransferBandits.ipm`, `IsTestClass`, `tvClass`, `ksClass`, `w1Class`, `meanClass`, `HasMeanProperty` | `d_𝓕` and the four examples; `(M)` is `HasMeanProperty` |
| def:model | definition | `Incognita.TransferBandits.supportBandits`, `bestMean`; reused from P003: `TransferAlgorithm`, `gameMeasure`, `constSize`, `onlineCount` | laws of the game are kernels carried by `S` |
| def:class | definition | `Incognita.TransferBandits.lawDriftClass`, `IsLawConsistent` | `Θ`, `Cons(N')` |
| def:constant | definition | `Incognita.TransferBandits.altPairs`, `programme`, `driftConstant`, `armConstant`, `IsKLProj` | `Γ_a(μ)`, `J_a(x,c;μ)`, `D_a(c)`; `Q⋆`, `Q'⋆` through `IsKLProj` |
| def:algo | definition | `Incognita.TransferBandits.klucbLawTransfer` | with `explorationRate`, `lawIndex`, `empVec`, `lawStat`, `statIndex`, `lawPolicyMeasure`; `Incognita/TransferBandits/LawTransferAlgorithm.lean` |
| prop:lower | frozen | `Incognita.Statements.P002.lower_bound` | |
| thm:main | frozen | (i) `Incognita.Statements.P002.upper_bound_klucb`; (ii) `Incognita.Statements.P002.upper_bound_transfer` | |
| cor:optimal | frozen | `Incognita.Statements.P002.optimal_isLawConsistent`, `…optimal_tendsto_pulls`, `…optimal_tendsto_regret`, `…optimal_regret_lower` | one theorem per claim |
| prop:order | frozen | (a) `Incognita.Statements.P002.order_mean`; (b) `…order_le_mean`; (c) `…order_chain` | |
| prop:criteria | frozen | (a) `Incognita.Statements.P002.criteria_gain_over_mean`; (b) `…criteria_source_helps` (first sentence), `…criteria_source_helps_mean` (the mean gap) | |
| prop:threshold | frozen | (a) `Incognita.Statements.P002.threshold_iff`; (b) `…threshold_mean_w1`; (c) `…threshold_tv` | `ω_d` is `reachGain`, `G^d` is `thresholdKL` |
| prop:order (b) | proof | `Incognita.P002.order_le_mean` | `Incognita/P002/Order.lean`; `Incognita.TransferBandits.driftConstant_le_of_ipm_le` (formalisation.tex, flem:order-mono) and `vecKs_lawVec_pos` (`K_0 > 0`, flem:ks-pos), in `Incognita/TransferBandits/LawDriftOrder.lean` |
| prop:order (c) | proof | `Incognita.P002.order_chain` | `Incognita/P002/Order.lean`; `driftConstant_le_of_ipm_le` with `ipm_ksClass_le_ipm_tvClass`, `ipm_w1Class_le_ipm_ksClass` (Abel summation `abs_sum_mul_sub_le`, formalisation.tex, flem:abel) and `abs_vecMean_sub_le_ipm_w1Class` (lem:ipm-order) |
| prop:order (a) | proof | `Incognita.P002.order_mean` | `Incognita/P002/Order.lean`; `Incognita.TransferBandits.ofReal_driftConstant_meanClass` from `programme_meanClass` (`J^mean(x,c) = x K_0 + c K'_0`, formalisation.tex, flem:programme-mean), which uses `exists_vecMean_eq_vecKL_le` (flem:mix) instead of the projections `Q⋆`, `Q'⋆`; `K_0, K'_0 < ∞` by `vecKs_ne_top` (flem:ks-finite); all in `Incognita/TransferBandits/LawDriftMean.lean` |
| prop:criteria (b), mean gap | proof | `Incognita.P002.criteria_source_helps_mean` | `Incognita/P002/Criteria.lean`; `Incognita.TransferBandits.ofReal_driftConstant_meanClass_lt_iff` (formalisation.tex, flem:criteria-mean): below `μ⋆ + L_a` from prop:order (a), above it from `ofReal_driftConstant_meanClass_lt` (flem:mean-high, a direct bound, as the paper's route through lem:criterion-point and `Q⋆` is not needed); `LawDriftMean.lean` |
| prop:tv (a) | proof | `Incognita.P002.tv_projections` | `Incognita/P002/TV.lean`; `Incognita.TransferBandits.vecMean_eq_of_isKLProj` (`m(Q'⋆) = μ⋆ - L_a` when `K'_0 > 0`, part of lem:projection, formalisation.tex, flem:proj-level), `vecMean_sub_le_mul_ipm_tvClass` and `eq_of_vecMean_sub_eq_mul_ipm_tvClass` (flem:tv-width); `Incognita/TransferBandits/LawDriftTV.lean` |
| lem:ipm-order | lemma | (added by prove), the order only: `Incognita.TransferBandits.abs_vecMean_sub_le_ipm_w1Class`, `…ipm_w1Class_le_ipm_ksClass`, `…ipm_ksClass_le_ipm_tvClass` | the Abel identity itself is replaced by the bound `abs_sum_mul_sub_le` (flem:abel); the mean property of the four examples: `hasMeanProperty_meanClass`, `hasMeanProperty_tvClass` (`LawDriftChecks.lean`) and the three inequalities above |
| prop:threshold (b) | proof | `Incognita.P002.threshold_mean_w1` | `Incognita/P002/Threshold.lean`; mean gap: `Incognita.TransferBandits.reachGain_meanClass` (`LawDriftChecks.lean`); `W₁`: `Incognita.TransferBandits.reachGain_w1Class` from `reachGain_eq_min` (formalisation.tex, flem:reach-min, flem:reach-w1); `G^d = K'_0`: `thresholdKL_eq_vecKs` (flem:threshold-ks); all in `Incognita/TransferBandits/LawDriftReach.lean` |
| prop:threshold (c) | proof | `Incognita.P002.threshold_tv` | `Incognita/P002/Threshold.lean`; `Incognita.TransferBandits.reachGain_tvClass` (`LawDriftReach.lean`, formalisation.tex, flem:reach-tv), from `ipm_tvClass` (lem:ipm (c)) |
| prop:bernoulli | frozen | `Incognita.Statements.P002.bernoulli_no_gain` | |
| prop:w1 | frozen | `Incognita.Statements.P002.w1_no_gain` | |
| prop:tv | frozen | (a) `Incognita.Statements.P002.tv_projections`; (b) `…tv_strict_gain`; (c) `…tv_strict_gain_self` | |
| cite:GMS19-6 | lemma | (added by prove) | |
| cite:GMS19-11 | lemma | (added by prove) | |
| lem:ipm | lemma | (added by prove) | |
| lem:ipm-order | lemma | (added by prove) | |
| lem:lsc | lemma | (added by prove) | |
| lem:types | lemma | (added by prove) | |
| lem:projection | lemma | (added by prove) | parts only: `K_S(ρ, ℓ) > 0` when `m(ρ) < ℓ` (`Incognita.TransferBandits.vecKs_pos`), `K_S(ρ, ℓ) < ∞` when `ℓ < x_max` (`vecKs_ne_top`), and a projection with `0 < K_S < ∞` has mean exactly `ℓ` (`vecMean_eq_of_isKLProj`); existence and uniqueness not proved |
| lem:lr | lemma | (added by prove) | |
| lem:J | lemma | (added by prove) | |
| lem:J-zero | lemma | (added by prove) | |
| lem:D | lemma | (added by prove) | |
| lem:index | lemma | (added by prove) | |
| def:proof-notation | definition | (added by prove) | notation of the proof of thm:main, local to it |
| lem:decomposition | lemma | (added by prove) | |
| lem:optimal-arm | lemma | (added by prove) | |
| lem:sub-reduction | lemma | (added by prove) | |
| lem:sub-kl | lemma | (added by prove) | |
| lem:sub-constant | lemma | (added by prove) | |
| lem:deviation | lemma | (added by prove) | |
| lem:source | lemma | (added by prove) | |
| lem:delta | lemma | (added by prove) | |
| lem:kl-lower | lemma | (added by prove) | |
| lem:criterion-point | lemma | (added by prove) | |
| lem:weak-duality | lemma | (added by prove) | |

## Modelling decisions

Files: `Incognita/TransferBandits/LawDrift.lean` (laws on `S`, IPMs, `Θ`, `Cons(N')`, the
constant), `Incognita/TransferBandits/LawTransferAlgorithm.lean` (the algorithm),
`Incognita/TransferBandits/LawDriftChecks.lean` (checks of §6.4), `Incognita/P002/Witnesses.lean`.
P002 has no library dependency (`depends_on = []`), but it lives in the roadmap TransferBandits,
whose definitions paper P003 fixed the Lean model of the game: P002 reuses it, so that the
results of P003 (the divergence decomposition, cor:fundamental) apply to its learners.

1. **Support and laws.** `S : Finset ℝ`, with `S ⊆ [0,1]` and `2 ≤ S.card` as hypotheses of
   every statement (def:laws). A law on `S` is a probability vector `q : S → ℝ` (`probVecs S`,
   functions on the subtype of `S`); Mathlib's `stdSimplex` is deprecated at the pinned version,
   so `probVecs` is defined by the paper's formula. The mean `vecMean q = ∑_y q(y) y`.
2. **Instances.** As in P003 (decision 2 of its blueprint): an instance is a Markov kernel
   `ν : Kernel α ℝ`; here its laws are carried by `S` (`supportBandits S α`: `ν a Sᶜ = 0`). The
   vector of a law is `lawVec S P = y ↦ P {y}` (as a real number), the paper's identification of
   a law on `S` with its vector. The mean of arm `k` is the Bochner integral `(ν k)[id]` (as in
   P003; it equals `m(ν_k)` for a law carried by `S`), `μ⋆ = bestMean ν = ⨆ k, (ν k)[id]`, and
   "`μ_a < μ⋆`" is `(ν a)[id] < bestMean ν`.
3. **KL and `K_S`.** `vecKL r q ∈ ℝ≥0∞` is the paper's finite sum over `{r > 0}`, `∞` when
   `q(y) = 0 < r(y)`; `vecKs S ρ ℓ` is the infimum in `ℝ≥0∞` over `probVecs S ∩ {m ≥ ℓ}`
   (`inf ∅ = ∞`). Mathlib's `klDiv` is not used for the programme (the paper defines `KL` by the
   sum); relating the two on finite supports is a lemma for `prove`.
4. **Integral probability metrics.** `ipm 𝓕 q q' = ⨆ f : 𝓕, |∑_y f(y)(q(y) - q'(y))|`, a real
   supremum; every statement assumes `IsTestClass 𝓕` (`𝓕` nonempty, values in `[0,1]`), so the
   supremum is that of a nonempty bounded set. The four examples are the sets of def:ipm:
   `tvClass S` (all `f : S → [0,1]`), `ksClass S` (the indicators of `(-∞, s]`, `s ∈ ℝ`),
   `w1Class S` (the `1`-Lipschitz `f : S → [0,1]`, Lipschitz for `|y - z|` on `S`),
   `meanClass S = {y ↦ y}`. "A pseudo-distance of def:ipm" / "every `d`" is `ipm 𝓕` for every
   `𝓕` with `IsTestClass 𝓕`; a superscript `D^d_a` is `armConstant 𝓕`.
5. **The constant.** `altPairs 𝓕 l μ` is `Γ_a(μ)` with `l = L_a`; `programme 𝓕 l r r' μ x c` is
   `J_a(x, c; μ)` in `ℝ≥0∞` with `ENNReal.ofReal x * KL + ENNReal.ofReal c * KL` (so `0 · ∞ = 0`,
   the paper's convention) and `inf ∅ = ∞`; `driftConstant … μ c = sInf {x > 0 : 1 ≤ J}` is a
   real infimum (for a suboptimal arm the set is nonempty, so `sInf ∅ = 0` never enters);
   `armConstant 𝓕 L ν ν' a c` reads it at `r = ν_a`, `r' = ν'_a`, `l = L_a`, `μ = μ⋆`.
6. **Source sizes and the game.** The sizes are deterministic, `N' : ℕ → α → ℕ`; the game at
   horizon `T` is P003's `gameMeasure ν' (constSize (N' T)) ν π T` (a constant size rule), and
   `N_a(T)` is `onlineCount a` of the online history (rounds `0, …, T-1`, the paper's rounds
   `1, …, T`). Learners are P003's `TransferAlgorithm α` (kernels of the source data and the
   history): the paper's learners (measurable functions of the source sample, of `V_0, …, V_{t-1}`
   and of the past observations) are such kernels, and conversely.
7. **Asymptotic statements.** `E[N_a(T)]` is the lower integral in `ℝ≥0∞`, and the ratios
   `E[N_a(T)] / log T` are divisions in `ℝ≥0∞` by `ENNReal.ofReal (Real.log T)`, so `limsup`,
   `liminf` and limits are those of the complete lattice `ℝ≥0∞`, without the junk values of real
   `limsup` (AGENTS.md §6.5); the finitely many horizons `T ≤ 1` (`log T = 0`) do not matter. Real
   constants enter through `ENNReal.ofReal`, and `1/K_S` is the inverse in `ℝ≥0∞` (`1/∞ = 0`, the
   paper's reading). The rates `N'_a(T)/log T → c_a` are real limits; `c̄_a` of prop:lower is the
   `limsup` in `ℝ≥0∞`, assumed `< ∞`, read through `toReal`. The regret `R_T` and `𝓡` are sums in
   `ℝ≥0∞` with the nonnegative weights `ENNReal.ofReal (μ⋆ - μ_k)`, where the gap `μ⋆ - μ_k` is
   LML's `Bandits.gap ν k` (`(⨆ i, (ν i)[id]) - (ν k)[id]`, equal to `bestMean ν - (ν k)[id]` by
   definition), so that LML's gap API applies to these statements as written.
8. **Consistency.** `IsLawConsistent 𝓕 L N' π` is `Cons(N')` verbatim, written like P003's
   `IsConsistent`: Bochner expectations of the (bounded) pull counts divided by `T ^ c`, tending to
   `0`, for every pair of `Θ = lawDriftClass 𝓕 L`, every suboptimal arm and every `c > 0`.
   The class `𝒞_𝟏` of P003 is inside every `Cons(N')` (`isLawConsistent_of_isConsistent_one`), so
   the source-ignoring KL-UCB of LMLExplore witnesses it.
9. **The algorithm** (`klucbLawTransfer 𝓕 L`). Round `n` (0-based) is the paper's round `n + 1`.
   For `n < K` it pulls the arm `(Fintype.equivFin α).symm n` (the paper's "pull arm `t`" for an
   enumeration of the arms). For `n ≥ K` it computes the index with the history of `t = n`
   rounds (the paper's "end of round `t ≥ K`") and draws an arm uniformly (`uniformOn`) among
   the maximisers (the paper's uniform tie-breaking with `V_t`). The index `lawIndex` is the
   supremum in `EReal` of the means of the feasible `q` (`sup ∅ = ⊥`, the paper's
   `max ∅ = -∞`; lem:index says the maximum is attained). The counts `N_k(t) KL`,
   `N'_k KL` are products in `ℝ≥0∞`, so `N'_k KL(ν̂'_k, q') = 0` when `N'_k = 0` (the paper's
   convention), and the empirical source law is then the zero vector, which plays no role. The
   policy factors through the counts `lawStat` (sizes `sourceCount`, values of the source equal to
   each `y ∈ S`, pulls `onlineCount` of P003, pulls with reward `y`), a countable set of
   statistics, which makes it measurable
   (`Kernel.ofFunOfCountable`). Values outside `S` are not counted; they have probability `0`
   under every instance on `S`.
10. **Projections.** `Q⋆` and `Q'⋆` (def:constant) are not defined as Lean objects: the
    statements that use them quantify over every `Q` with `IsKLProj (ν_a) μ⋆ Q` (and `Q'` with
    `IsKLProj (ν'_a) (μ⋆ - L_a) Q'`), which by lem:projection (existence and uniqueness) are
    exactly `Q⋆` and `Q'⋆`. This avoids a choice function with a junk value. Since these
    premises sit after the binders, each witness of the four statements that use them
    (`criteria_gain_over_mean`, `criteria_source_helps`, `tv_projections`, `tv_strict_gain`)
    exhibits the projections, in the binding case `ℓ > m(ρ)`: for `ρ = δ_0` on a support with
    maximum `x_max > 0` and a level `ℓ ∈ [0, x_max]`, the projection is
    `(1 - ℓ/x_max) δ_0 + (ℓ/x_max) δ_{x_max}` (`Incognita.TransferBandits.isKLProj_single_zero`,
    from `q(0) ≤ 1 - m(q)/x_max`). The Dirac vectors are Mathlib's `Pi.single y 1`.
11. **`x_max`, `x_min`.** In the statements of Section 6 of the paper they are `S.max' hSne` and
    `S.min' hSne`, with a hypothesis `hSne : S.Nonempty` that only names the proof (it follows
    from `2 ≤ S.card`). "`μ⋆ < x_max`" is `bestMean ν < S.max' hSne`.
12. **`[Nonempty α]`.** The statements that mention the algorithm carry the instance
    `[Nonempty α]` (the kernels of the algorithm need it); it follows from `2 ≤ Fintype.card α`.
13. **Nodes with several claims** get one theorem per item (thm:main, prop:order,
    prop:threshold, prop:tv) or per claim (cor:optimal: four; prop:criteria (b): its first
    sentence and its reading for the mean gap). A claim with several conclusions in one item is
    one conjunction (prop:order (c), prop:threshold (b), prop:tv (a)).
14. **Hypotheses of the corollary kept.** `optimal_isLawConsistent` keeps the hypotheses of
    cor:optimal although its conclusion does not use them (the paper states it under them).

## Back-translations

Each frozen statement read from the Lean alone (definitions unfolded), then compared with the
paper's node. Common hypotheses (`H`): a finite type `α` of arms with at least two elements; a
finite set `S ⊆ [0,1]` of reals with at least two points; `L : α → ℝ` positive. For the
statements of Section 4–5 of the paper also a nonempty set `𝓕` of functions `S → [0,1]`, and
`d = d_𝓕`.

- **`upper_bound_klucb`** (thm:main (i)). Under `H`, for kernels `ν, ν'` whose laws are
  probability measures carried by `S`, if some arm `i` has the largest mean and
  `d(ν_i, ν'_i) < L_i`, then for every sequence of deterministic source sizes `N'` and every arm
  `a` whose mean is below the largest, the `limsup` in `[0,∞]` of the expected number of pulls of
  `a` by `klucbLawTransfer 𝓕 L` in the game with sizes `N'(T)` divided by `log T` is at most
  `1 / K_S(ν_a, μ⋆)` (`0` if `K_S = ∞`). Differences: none of substance (decisions 2, 6, 7, 9).
- **`upper_bound_transfer`** (thm:main (ii)). Same hypotheses, plus `N'_a(T)/log T → c`; then the
  same `limsup` is at most `D_a(c)` (`armConstant 𝓕 L ν ν' a c`). Differences: `c ∈ [0,∞)` is
  implied by the limit of nonnegative reals.
- **`lower_bound`** (prop:lower). Under `H`, for every `N'`, every learner `π ∈ Cons(N')`, every
  `(ν, ν') ∈ Θ` and every suboptimal arm `a` with `c̄ = limsup N'_a(T)/log T < ∞` (in `[0,∞]`),
  `D_a(c̄) ≤ liminf E_π[N_a(T)] / log T`. Differences: none of substance; the setting hypotheses
  (`K ≥ 2`, `L > 0`, `S`, `𝓕`) are those of def:model, def:laws, def:ipm.
- **`optimal_isLawConsistent`** (cor:optimal, claim 1). Under `H`, if `(ν, ν') ∈ Θ` and the
  suboptimal arms have rates `c_k`, then `klucbLawTransfer 𝓕 L ∈ Cons(N'')` for every `N''`.
  Differences: none (decision 14).
- **`optimal_tendsto_pulls`** (claim 2). Same hypotheses; for a suboptimal arm `a`,
  `E[N_a(T)] / log T → D_a(c_a)` in `[0,∞]` for `klucbLawTransfer`. Differences: none.
- **`optimal_tendsto_regret`** (claim 3). Same hypotheses; `(∑_k Δ_k E[N_k(T)]) / log T`
  tends to `∑_{a : μ_a < μ⋆} Δ_a D_a(c_a)` in `[0,∞]`, with `Δ_k = μ⋆ - μ_k` (LML's
  `Bandits.gap`). Differences: none.
- **`optimal_regret_lower`** (claim 4). Same hypotheses; for every `π ∈ Cons(N')`,
  `𝓡 ≤ liminf R_T^π / log T`. Differences: none.

For the statements of Section 6 of the paper, `H` also includes: `ν, ν'` kernels carried by `S`,
an arm `a` with `μ_a < μ⋆ < x_max`; `K_0 = K_S(ν_a, μ⋆)`, `K'_0 = K_S(ν'_a, μ⋆ - L_a)`. "`D^𝓕`"
below is `armConstant 𝓕 L ν ν' a`, a function of `c`.

- **`order_mean`** (prop:order (a)). If `m(ν'_a) ≤ μ⋆ + L_a`, then for every `c ≥ 0`,
  `D^mean(c) = (1 - c K'_0)_+ / K_0` (in `[0,∞]`). Differences: written in `ℝ≥0∞`; equal to the
  paper's real identity since `K_0 ∈ (0,∞)` and `K'_0 < ∞` (lem:projection).
- **`order_le_mean`** (prop:order (b)). For every `𝓕` with the mean property, `D^𝓕(c) ≤ D^mean(c)`
  for every `c ≥ 0`. Differences: none.
- **`order_chain`** (prop:order (c)). For every `c ≥ 0`,
  `D^TV(c) ≤ D^KS(c) ≤ D^W₁(c) ≤ D^mean(c)`. Differences: none.
- **`criteria_gain_over_mean`** (prop:criteria (a)). For `𝓕` with the mean property,
  `m(ν'_a) ≤ μ⋆ + L_a`, `c > 0` and `c K'_0 < 1`: for every KL projection `Q` of `ν_a` at level
  `μ⋆` and `Q'` of `ν'_a` at level `μ⋆ - L_a`, `D^𝓕(c) < D^mean(c) ↔ L_a < d(Q, Q')`.
  Differences: decision 10.
- **`criteria_source_helps`** (prop:criteria (b), first sentence). For every `𝓕` and `c > 0`, for
  every KL projection `Q` of `ν_a` at level `μ⋆`, `D^𝓕(c) < 1/K_0 ↔ L_a < d(Q, ν'_a)`.
  Differences: decision 10; the comparison is in `ℝ≥0∞`.
- **`criteria_source_helps_mean`** (prop:criteria (b), second sentence). For `c > 0`,
  `D^mean(c) < 1/K_0 ↔ L_a < |m(ν'_a) - μ⋆|`, and, when `m(ν'_a) ≤ μ⋆ + L_a`,
  `D^mean(c) < 1/K_0 ↔ m(ν'_a) < μ⋆ - L_a`. Differences: none.
- **`threshold_iff`** (prop:threshold (a)). For every `𝓕` and `c ≥ 0`, `D^𝓕(c) = 0` iff
  `1 ≤ c G^𝓕`, `G^𝓕 = inf {KL(ν'_a, q') : q' ∈ 𝒫_S, μ⋆ ≤ m(q') + ω(q')}`,
  `ω(q') = sup {m(q) - m(q') : q ∈ 𝒫_S, d(q, q') ≤ L_a}`. Differences: sup/inf for the paper's
  max/min (attained, by the paper).
- **`threshold_mean_w1`** (prop:threshold (b)). For the mean gap and for `W₁`, for every
  `q' ∈ 𝒫_S`, `ω(q') = min(L_a, x_max - m(q'))`, and `G = K'_0`. Differences: none.
- **`threshold_tv`** (prop:threshold (c)). For every `q' ∈ 𝒫_S`, `ω_TV(q')` is the supremum of
  `∑_y w(y)(x_max - y)` over `0 ≤ w ≤ q'` with `∑_y w(y) ≤ L_a`. Differences: sup for max.
- **`bernoulli_no_gain`** (prop:bernoulli). If `m(ν'_a) ≤ μ⋆ + L_a`, `{0, 1} ⊆ S`, `ν_a` and
  `ν'_a` are carried by `{0, 1}`, then for every `𝓕` with the mean property and every `c ≥ 0`,
  `D^𝓕(c) = D^mean(c)`. Differences: none.
- **`w1_no_gain`** (prop:w1). If `ν'_a = ν_a`, then `D^W₁(c) = D^mean(c)` for every `c ≥ 0`.
  Differences: none.
- **`tv_projections`** (prop:tv (a)). If `K'_0 > 0`, then for all projections `Q`, `Q'` (as
  above), `L_a / (x_max - x_min) ≤ TV(Q, Q')`, and equality forces `Q(y) = Q'(y)` for every `y`
  other than `x_min`, `x_max`. Differences: decision 10; `TV` is `ipm (tvClass S)` (equal to the
  `TV` of def:laws by lem:ipm (c)).
- **`tv_strict_gain`** (prop:tv (b)). If `K'_0 > 0`, then for all projections `Q`, `Q'`: if
  `x_max - x_min < 1` or `Q(y) ≠ Q'(y)` for some `y` of `S` strictly between `x_min` and `x_max`,
  then `D^TV(c) < D^mean(c)` for every `c > 0` with `c K'_0 < 1`. Differences: decision 10;
  `c < 1/K'_0` written `c K'_0 < 1` in `ℝ≥0∞`. The witness
  (`Incognita.P002.tv_strict_gain_satisfiable`) satisfies the premises of the conclusion too:
  `S = {0, 1/4, 1/2}` (`x_max - x_min = 1/2 < 1`), `ν_a = ν'_a = δ_0`, `μ⋆ = 1/4`, `L ≡ 1/8`, the
  projections `½ δ_0 + ½ δ_{1/2}` and `¾ δ_0 + ¼ δ_{1/2}`, `K'_0 = log (4/3)` and `c = 1`.
- **`tv_strict_gain_self`** (prop:tv (c)). If `K'_0 > 0`, `ν'_a = ν_a`, and there are two distinct
  reals `y, z` strictly between `x_min` and `x_max` with `ν_a {y} > 0` and `ν_a {z} > 0`, then
  `D^TV(c) < D^mean(c)` for every `c > 0` with `c K'_0 < 1`. Differences: "`ν_a` charges two points
  of `(x_min, x_max)`" made explicit; `c < 1/K'_0` written `c K'_0 < 1` in `ℝ≥0∞`. The witness
  (`Incognita.P002.tv_strict_gain_self_satisfiable`) uses `ν_a = (δ_{1/8} + δ_{1/4})/2` on
  `S = {0, 1/8, 1/4, 1/2, 1}`, `μ⋆ = 1/2`, `L ≡ 1/8`, and the bound
  `K_S(r, ℓ) ≥ (ℓ - b)/(1 - b)` for a law carried by `(-∞, b]`, `b < ℓ`
  (`Incognita.TransferBandits.vecKs_pos_of_support_le`, from `KL(r, q) ≥ 1 - q(supp r)`).

## Open problems

None among the frozen nodes. Not a problem of the paper, but recorded here:

- The catalogue entries of `altPairs`, `bestMean`, `lawVec`, `vecMean`, `IsTestClass`,
  `meanClass`, `explorationRate`, `empVec`, `lawStat`, `statIndex` and `lawPolicyMeasure` are not
  written: they are auxiliary objects whose checks are those of the entries that use them.
