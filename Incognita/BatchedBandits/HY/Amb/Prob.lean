/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.HY.Amb.Series
public import Incognita.BatchedBandits.HY.Events.XOne
public import Incognita.BatchedBandits.HY.Ranks.XOne
public import Incognita.BatchedBandits.KInf.Dual

/-! # The probabilities of the traces of `Acc_ℓ^c` and `KC_ℓ^c` as functions of `L_ℓ`

[INC-P000, proof of Lemma `lem:amb`, Step 5], for the traces on the run of the events `Acc_ℓ` and
`KC_ℓ` of Definition `def:amb` (the forms in which
`hyAlg_ae_ofReal_mul_threshold_le_count_mul_testKinf` uses them), for every learner on
an instance `ν` of `𝒫`:

* `measure_exists_mem_le_pullCount_abs_sub_gt_le_mul_exp_neg_rpow`: with `ζ_ℓ = c_ζ y^(-1/4)` and
  `U ≥ (y/4)^β` (the paper's `U_(ℓ-1) ≥ (L_ℓ/4)^β`), the probability that some arm `c` and some
  cutoff `s ∈ T` have `N_c(s) ≥ U/2` and `|m̂_c(s) - m_c| > ζ_ℓ` is at most
  `p_A(y) = 2K (1 + √y / (2c_ζ²)) exp(-c_ζ² 4^(-β) y^(β-1/2))`
  (`measure_exists_mem_le_pullCount_abs_sub_gt_le` and `mul_exp_neg_div_one_sub_exp_neg_le`);
* `measure_exists_mem_le_pullCount_pseudoKinf_lt_or_lt_le_mul_exp_neg`: with `ζ'_ℓ = (Δ/32)
  y^(-1/4)`, `y ≥ 16` and a count threshold
  `u ≥ c₂ y`, the probability that some cutoff `s ∈ T` has `N_a(s) ≥ u` and
  `|𝒦_inf(ν̂_a(s), μ) - 𝒦_inf(ν_a, μ)| > ζ'_ℓ` is at most `|T| p̄_K(y)`, with
  `p̄_K(y) = C₂ (1 + 1/c₁) y log² y exp(-c₁ c₂ √y / log² y)`
  (`measure_exists_mem_le_pullCount_pseudoKinf_lt_or_lt_le` and
  `one_add_ceil_mul_exp_neg_div_le`). The paper's `T = {t_(ℓ-1), t_ℓ}` gives the factor `2`,
  absorbed in the constant `D`
  of `Grid.exists_sum_activated_rpow_add_mul_exp_neg_le`.
* `Grid.eventually_measure_exists_mem_le_pullCount_abs_sub_gt_le`,
  `Grid.eventually_measure_exists_mem_le_pullCount_pseudoKinf_lt_or_lt_le`: the same along the
  grid, for every large `ℓ`, at the paper's accuracies `ζ_ℓ = c_ζ γ_ℓ` and `ζ'_ℓ = γ_ℓ Δ / 32`
  with the default `γ_ℓ` (`γ_ℓ = L_ℓ^(-1/4)`, condition (e) of Definition `def:amb`), the
  net size `U_(ℓ-1) ≥ (L_ℓ/4)^β` and a count threshold `n_ℓ ≥ c₂ L_ℓ`.
-/

@[expose] public section

open Learning MeasureTheory ProbabilityTheory LMLExplore LMLExplore.Bandits Filter

open scoped Topology

open scoped ENNReal

namespace Incognita.BatchedBandits

variable {α : Type*} [DecidableEq α] [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]

/-- [INC-P000, proof of Lemma `lem:amb`, Step 5, the trace of `Acc_ℓ^c`] For every learner on an
instance `ν` of `𝒫`, a set `T` of cutoffs, `c_ζ > 0`, `y > 0`, `ζ = c_ζ y^(-1/4)` and
`U ≥ (y/4)^β`: the probability that some arm `c` and some `s ∈ T` have `N_c(s) ≥ U/2` and
`|m̂_c(s) - m_c| > ζ` is at most `p_A(y) = 2K (1 + √y / (2c_ζ²)) exp(-c_ζ² 4^(-β) y^(β-1/2))`. -/
lemma measure_exists_mem_le_pullCount_abs_sub_gt_le_mul_exp_neg_rpow {alg : Algorithm Unit α ℝ}
    {ν : Kernel α ℝ} [IsMarkovKernel ν] (hν : ν ∈ unitBandits α) (T : Set ℕ)
    {cζ y β ζ U : ℝ} (hc : 0 < cζ) (hy : 0 < y) (hζ : ζ = cζ * y ^ (-(1 / 4 : ℝ)))
    (hU : (y / 4) ^ β ≤ U) :
    trajMeasure alg (Environment.bandit ν) {ω | ∃ c, ∃ s ∈ T, U / 2 ≤ pullCount IT.action c s ω ∧
      ζ < |HY.pseudoMean 0 (history IT.obs IT.action IT.feedback s ω) s c - ∫ y, id y ∂(ν c)|} ≤
    ENNReal.ofReal (2 * Fintype.card α * (1 + Real.sqrt y / (2 * cζ ^ 2)) *
      Real.exp (-(cζ ^ 2 * (4 : ℝ) ^ (-β) * y ^ (β - 1 / 2)))) := by
  have hU0 : 0 < U := lt_of_lt_of_le (Real.rpow_pos_of_pos (by positivity) β) hU
  have hζ0 : 0 < ζ := by rw [hζ]; exact mul_pos hc (Real.rpow_pos_of_pos hy _)
  refine (measure_exists_mem_le_pullCount_abs_sub_gt_le (alg := alg) hν T (u := U / 2)
    (by positivity) hζ0).trans ?_
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (mul_exp_neg_div_one_sub_exp_neg_le
      (Nat.cast_nonneg _) hc hy hζ hU)

omit [Fintype α] in
/-- [INC-P000, proof of Lemma `lem:amb`, Step 5, the trace of `KC_ℓ^c`] For every learner on an
instance `ν` of `𝒫`, a finite set `T` of cutoffs, an arm `a`, `μ ∈ [0, 1)`, `Δ > 0`, `y ≥ 16`,
`ζ = (Δ/32) y^(-1/4)` and a count threshold `u ≥ c₂ y`
(`c₂ > 0`): the probability that some `s ∈ T` has `N_a(s) ≥ u` and
`|𝒦_inf(ν̂_a(s), μ) - 𝒦_inf(ν_a, μ)| > ζ` is at most `|T| p̄_K(y)`, with the constants `a₀`,
`A₁`, `c₁`, `C₂` of `one_add_ceil_mul_exp_neg_div_le` (Step 6). The paper takes `μ = m⋆`, `Δ = d_a =
𝒦_inf(ν_a, m⋆)`,
`T = {t_(ℓ-1), t_ℓ}`,
`u = n_ℓ`, `y = L_ℓ`. -/
lemma measure_exists_mem_le_pullCount_pseudoKinf_lt_or_lt_le_mul_exp_neg [Countable α]
    {alg : Algorithm Unit α ℝ} {ν : Kernel α ℝ}
    [IsMarkovKernel ν] (hν : ν ∈ unitBandits α) (T : Finset ℕ) (a : α)
    {Δ μ y c₂ u ζ a₀ A₁ c₁ C₂ : ℝ} (hΔ : 0 < Δ) (hμ0 : 0 ≤ μ) (hμ : μ < 1)
    (hy : 16 ≤ y) (hc₂ : 0 < c₂) (hu : c₂ * y ≤ u)
    (hζ : ζ = Δ / 32 * y ^ (-(1 / 4 : ℝ))) (ha₀ : a₀ = min (Δ / 128) 1)
    (hA₁ : A₁ = 1 / 4 + (Real.log (1 / (1 - μ)) + Real.log (2 / a₀)) / Real.log 16)
    (hc₁ : c₁ = Δ ^ 2 / (2048 * A₁ ^ 2)) (hC₂ : C₂ = 3 + 512 / (Δ * a₀ * (1 - μ))) :
    trajMeasure alg (Environment.bandit ν) {ω | ∃ s ∈ T, u ≤ pullCount IT.action a s ω ∧
      (HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback s ω) s a μ <
          ENNReal.ofReal ((dInf unitLaws (ν a) μ).toReal - ζ) ∨
        ENNReal.ofReal ((dInf unitLaws (ν a) μ).toReal + ζ) <
          HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback s ω) s a μ)} ≤
    ENNReal.ofReal (T.card * (C₂ * (1 + 1 / c₁) * y * Real.log y ^ 2 *
      Real.exp (-(c₁ * c₂ * Real.sqrt y / Real.log y ^ 2)))) := by
  have hy0 : 0 < y := by linarith
  have hζ0 : 0 < ζ := by rw [hζ]; exact mul_pos (by positivity) (Real.rpow_pos_of_pos hy0 _)
  have hu0 : 0 < u := lt_of_lt_of_le (by positivity) hu
  refine (measure_exists_mem_le_pullCount_pseudoKinf_lt_or_lt_le
      (alg := alg) hν T a hμ0 hμ hζ0 hu0).trans ?_
  set R := Real.log (1 / (1 - μ)) - Real.log (1 - Real.exp (-(ζ / 4))) with hR
  set ρ := ζ ^ 2 / (2 * R ^ 2) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hden : 0 ≤ 1 - Real.exp (-ρ) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hρ0))
  have hp0 : 0 ≤ Real.exp (-(ρ * u)) / (1 - Real.exp (-ρ)) := div_nonneg (Real.exp_pos _).le hden
  have hq0 : 0 ≤ ((⌈8 / (ζ * (1 - Real.exp (-(ζ / 4))) * (1 - μ))⌉₊ + 1 : ℕ) : ℝ) *
      Real.exp (-(ρ * u)) / (1 - Real.exp (-ρ)) :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le) hden
  rw [← ENNReal.ofReal_add hp0 hq0, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  exact one_add_ceil_mul_exp_neg_div_le hΔ hμ0 hμ hy hc₂ hu hζ hR hρ ha₀ hA₁ hc₁ hC₂

/-- [INC-P000, proof of Lemma `lem:amb`, Step 5, the trace of `Acc_ℓ^c`, for every large `ℓ`] On a
grid with `x_ℓ → 1`, for `β ≥ 0`, `c_ζ > 0`, every learner on an instance `ν` of `𝒫` and sets
`T_ℓ` of cutoffs: for every large `ℓ`, the probability that some arm `c` and some `s ∈ T_ℓ` have
`N_c(s) ≥ U_(ℓ-1)/2` and `|m̂_c(s) - m_c| > c_ζ γ_ℓ` (default `γ_ℓ`) is at most `p_A(L_ℓ)`.
The paper takes `T_ℓ = {t_(ℓ-1), t_ℓ}` and `c_ζ = d_a (1 - m⋆) / 64`. -/
lemma Grid.eventually_measure_exists_mem_le_pullCount_abs_sub_gt_le {K' : ℕ} (g : Grid K')
    (hg : Tendsto g.ratio atTop (𝓝 1)) {β : ℝ} (hβ : 0 ≤ β) {alg : Algorithm Unit α ℝ}
    {ν : Kernel α ℝ} [IsMarkovKernel ν] (hν : ν ∈ unitBandits α) (T : ℕ → Set ℕ) {cζ : ℝ}
    (hc : 0 < cζ) :
    ∀ᶠ ℓ in atTop, trajMeasure alg (Environment.bandit ν) {ω | ∃ c, ∃ s ∈ T ℓ,
      (g.netSize β (ℓ - 1) : ℝ) / 2 ≤ pullCount IT.action c s ω ∧
      cζ * g.hyGamma ℓ <
        |HY.pseudoMean 0 (history IT.obs IT.action IT.feedback s ω) s c - ∫ y, id y ∂(ν c)|} ≤
    ENNReal.ofReal (2 * Fintype.card α * (1 + Real.sqrt (g.logEnd ℓ) / (2 * cζ ^ 2)) *
      Real.exp (-(cζ ^ 2 * (4 : ℝ) ^ (-β) * g.logEnd ℓ ^ (β - 1 / 2)))) := by
  filter_upwards [g.eventually_hyGamma_eq, g.eventually_div_four_rpow_le_netSize hg hβ,
    g.tendsto_logEnd_atTop.eventually_gt_atTop 0] with ℓ hγ hU hL
  rw [hγ]
  exact measure_exists_mem_le_pullCount_abs_sub_gt_le_mul_exp_neg_rpow hν (T ℓ) hc hL rfl hU

omit [Fintype α] in
/-- [INC-P000, proof of Lemma `lem:amb`, Step 5, the trace of `KC_ℓ^c`, for every large `ℓ`] On
every grid, for every learner on an instance `ν` of `𝒫`, an arm `a`, `μ ∈ [0, 1)`, `Δ > 0`,
`c₂ > 0`, finite sets `T_ℓ` of cutoffs and count thresholds
`u_ℓ ≥ c₂ L_ℓ`: for every large `ℓ`, the probability that some `s ∈ T_ℓ` has `N_a(s) ≥ u_ℓ` and
`|𝒦_inf(ν̂_a(s), μ) - 𝒦_inf(ν_a, μ)| > γ_ℓ Δ / 32` (default `γ_ℓ`) is at most
`|T_ℓ| p̄_K(L_ℓ)`, with the constants of `one_add_ceil_mul_exp_neg_div_le`. The paper takes `μ =
m⋆`, `Δ = d_a = 𝒦_inf(ν_a, m⋆)`,
`T_ℓ = {t_(ℓ-1), t_ℓ}` and `u_ℓ = n_ℓ`. -/
lemma Grid.eventually_measure_exists_mem_le_pullCount_pseudoKinf_lt_or_lt_le [Countable α] {K' : ℕ}
    (g : Grid K')
    {alg : Algorithm Unit α ℝ} {ν : Kernel α ℝ} [IsMarkovKernel ν] (hν : ν ∈ unitBandits α)
    (T : ℕ → Finset ℕ) (a : α) {Δ μ c₂ a₀ A₁ c₁ C₂ : ℝ} {u : ℕ → ℝ} (hΔ : 0 < Δ) (hμ0 : 0 ≤ μ)
    (hμ : μ < 1) (hc₂ : 0 < c₂)
    (hu : ∀ᶠ ℓ in atTop, c₂ * g.logEnd ℓ ≤ u ℓ) (ha₀ : a₀ = min (Δ / 128) 1)
    (hA₁ : A₁ = 1 / 4 + (Real.log (1 / (1 - μ)) + Real.log (2 / a₀)) / Real.log 16)
    (hc₁ : c₁ = Δ ^ 2 / (2048 * A₁ ^ 2)) (hC₂ : C₂ = 3 + 512 / (Δ * a₀ * (1 - μ))) :
    ∀ᶠ ℓ in atTop, trajMeasure alg (Environment.bandit ν) {ω | ∃ s ∈ T ℓ,
      u ℓ ≤ pullCount IT.action a s ω ∧
      (HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback s ω) s a μ <
          ENNReal.ofReal ((dInf unitLaws (ν a) μ).toReal - g.hyGamma ℓ * Δ / 32) ∨
        ENNReal.ofReal ((dInf unitLaws (ν a) μ).toReal + g.hyGamma ℓ * Δ / 32) <
          HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback s ω) s a μ)} ≤
    ENNReal.ofReal ((T ℓ).card * (C₂ * (1 + 1 / c₁) * g.logEnd ℓ * Real.log (g.logEnd ℓ) ^ 2 *
      Real.exp (-(c₁ * c₂ * Real.sqrt (g.logEnd ℓ) / Real.log (g.logEnd ℓ) ^ 2)))) := by
  filter_upwards [g.eventually_hyGamma_eq, hu, g.tendsto_logEnd_atTop.eventually_ge_atTop 16]
    with ℓ hγ huℓ hL
  have hζ : g.hyGamma ℓ * Δ / 32 = Δ / 32 * g.logEnd ℓ ^ (-(1 / 4 : ℝ)) := by rw [hγ]; ring
  rw [hζ]
  exact measure_exists_mem_le_pullCount_pseudoKinf_lt_or_lt_le_mul_exp_neg hν
      (T ℓ) a hΔ hμ0 hμ hL hc₂ huℓ rfl ha₀ hA₁ hc₁ hC₂

end Incognita.BatchedBandits
