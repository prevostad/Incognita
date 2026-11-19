/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.HY.Grid
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # The long paced phases of HY when `x > 1`

[INC-P000, Lemma `lem:ranksA`, Step 2]: on a grid with `x_ℓ → x > 1` and the default activation
exponents `ϑ_ℓ`, the conditions (R2) of Definition `def:ranksA` hold for every large batch: the
batch is activated with a long paced phase, `t_(ℓ+1) - s_ℓ ≥ K (U_(ℓ+1) + K)`, and the condition
`s_ℓ log s_ℓ ≥ 2 (K - 1) U_(ℓ+1)` of the queue lemma holds. These are the structural hypotheses
of the lemmas of `Incognita.BatchedBandits.HY.Structure` and
`Incognita.BatchedBandits.HY.GoodBatch`.

* `eventually_mul_rpow_add_one_le_exp`: a power of `L` is eventually below `exp(b L)`, `b > 0`.
* `Grid.eventually_two_le_imedEnd_and_le_t_sub_imedEnd`: (R2) for every large batch, for every `β`
  and every number of arms `K'`.
* `Grid.eventually_ratio_le`, `Grid.eventually_le_mul_logEnd_rpow`,
  `Grid.eventually_add_mul_logEnd_le_netSize`: (R1) `x_ℓ ≤ x₊`, (T1)–(T2) and (T4) of
  Definition `def:ranksA` for every large `ℓ` (`β > 1`); `Grid.eventually_le_netSize`,
  `Grid.eventually_le_mul_logEnd`: (T3).
* `Grid.tendsto_hyGamma`, `Grid.eventually_threshold_ge`: the default `γ_ℓ → 0`, and (R3) for
  every large `ℓ`.
* `Grid.netSize_le_one_add_rpow`, `Grid.sum_netSize_mul_le`: Lemma `lem:sumsA`(a), the sum of
  the nets weighted by bounds `p_k ≤ C U_k⁴ t_(k+1)^(-(1+η))` of their probabilities;
  `Grid.sum_batch_mul_le`: Lemma `lem:sumsA`(b), the sum of the batches weighted by bounds of the
  probabilities of the failures `ℱ_i`.
-/

@[expose] public section

open Real Filter

open scoped Topology

namespace Incognita.BatchedBandits

/-- For `b > 0`, every `C` and every `β`, `C (L^β + 1) ≤ exp(b L)` for every large `L`: the
exponential dominates the powers. -/
lemma eventually_mul_rpow_add_one_le_exp (C β : ℝ) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ L in atTop, C * (L ^ β + 1) ≤ Real.exp (b * L) := by
  have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero β b hb
  have h2 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 b hb
  have hsum := h1.add h2
  rw [add_zero] at hsum
  have hC : 0 < 1 / (|C| + 1) := by positivity
  filter_upwards [(tendsto_order.1 hsum).2 _ hC, eventually_ge_atTop 0] with L hL hL0
  rw [rpow_zero, one_mul] at hL
  replace hL : (L ^ β + 1) * Real.exp (-b * L) < 1 / (|C| + 1) := by rwa [add_mul, one_mul]
  have hexp : 0 < Real.exp (b * L) := exp_pos _
  have hprod : (L ^ β + 1) * Real.exp (-b * L) * Real.exp (b * L) = L ^ β + 1 := by
    rw [mul_assoc, ← Real.exp_add]
    simp
  have hLb : 0 ≤ L ^ β + 1 := by positivity
  have h3 : L ^ β + 1 ≤ Real.exp (b * L) / (|C| + 1) := by
    rw [← hprod, div_eq_mul_one_div, mul_comm (Real.exp (b * L))]
    exact mul_le_mul_of_nonneg_right hL.le hexp.le
  calc C * (L ^ β + 1) ≤ |C| * (L ^ β + 1) := mul_le_mul_of_nonneg_right (le_abs_self C) hLb
    _ ≤ |C| * (Real.exp (b * L) / (|C| + 1)) :=
        mul_le_mul_of_nonneg_left h3 (abs_nonneg C)
    _ ≤ Real.exp (b * L) := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith [abs_nonneg C]

namespace Grid

variable {K : ℕ} (g : Grid K)

/-- [INC-P000, proof of Lemma `lem:ranksA`, Step 2] On a grid with `x_ℓ → x > 1`, with the default
activation exponents `ϑ_ℓ`, for every real `β` (the paper's `β ≥ 2` is not used) and every `K'`,
every large `ℓ` has `s_ℓ ≥ 2`,
`s_ℓ log s_ℓ ≥ 2 (K' - 1) U_(ℓ+1)` and `t_(ℓ+1) - s_ℓ ≥ K' (U_(ℓ+1) + K')` (so the batch `ℓ + 1` is
activated): the conditions (R2) of Definition `def:ranksA` at `ℓ + 1` (with `K' = K`; `ϑ_ℓ ≥ 0`
holds for every `ℓ`, `Grid.hyTheta_mem`). Since `ϑ_ℓ → 0`, `s_ℓ ≤ t_ℓ^(1+ϑ_ℓ) ≤ exp((1 + c) L_ℓ)`
with `c = (x - 1)/4`, while `t_(ℓ+1) = exp(x_(ℓ+1) L_ℓ) ≥ exp((1 + 2c) L_ℓ)`, and
`U_(ℓ+1) ≤ L_ℓ^β + 1` is a power of `L_ℓ`. -/
lemma eventually_two_le_imedEnd_and_le_t_sub_imedEnd {x : ℝ} (hx : 1 < x)
    (hg : Tendsto g.ratio atTop (𝓝 x)) (β : ℝ) (K' : ℕ) :
    ∀ᶠ ℓ in atTop, 2 ≤ g.imedEnd g.hyTheta ℓ ∧
      (2 * (K' - 1 : ℕ) * g.netSize β (ℓ + 1) : ℝ) ≤
        g.imedEnd g.hyTheta ℓ * Real.log (g.imedEnd g.hyTheta ℓ) ∧
      K' * (g.netSize β (ℓ + 1) + K') ≤ g.t (ℓ + 1) - g.imedEnd g.hyTheta ℓ := by
  set c := (x - 1) / 4 with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  have hL := g.tendsto_logEnd_atTop
  have hratio : ∀ᶠ ℓ in atTop, 1 + 2 * c < g.ratio (ℓ + 1) :=
    (tendsto_order.1 (hg.comp (tendsto_add_atTop_nat 1))).1 _ (by rw [hc]; linarith)
  have ht : ∀ᶠ ℓ in atTop, Real.exp (Real.exp 1) ≤ (g.t ℓ : ℝ) :=
    (tendsto_natCast_atTop_atTop.comp g.strictMono.tendsto_atTop).eventually_ge_atTop _
  have hL1 : ∀ᶠ ℓ in atTop, Real.exp (1 / c) ≤ g.logEnd ℓ := hL.eventually_ge_atTop _
  have hL2 : ∀ᶠ ℓ in atTop, Real.log 2 / c ≤ g.logEnd ℓ := hL.eventually_ge_atTop _
  have hL3 : ∀ᶠ ℓ in atTop, (1 : ℝ) ≤ g.logEnd ℓ := hL.eventually_ge_atTop _
  have hP1 : ∀ᶠ ℓ in atTop, (2 * (K' - 1 : ℕ) : ℝ) * (g.logEnd ℓ ^ β + 1) ≤
      Real.exp (1 * g.logEnd ℓ) :=
    hL.eventually (eventually_mul_rpow_add_one_le_exp _ β one_pos)
  have hP2 : ∀ᶠ ℓ in atTop, ((K' : ℝ) * (1 + K')) * (g.logEnd ℓ ^ β + 1) ≤
      Real.exp (c * g.logEnd ℓ) :=
    hL.eventually (eventually_mul_rpow_add_one_le_exp _ β hc0)
  filter_upwards [eventually_ge_atTop 1, hratio, ht, hL1, hL2, hL3, hP1, hP2] with
    ℓ hℓ hr hte hl1 hl2 hl3 hp1 hp2
  set L := g.logEnd ℓ with hLdef
  set σ := g.imedEnd g.hyTheta ℓ with hσ
  set U := g.netSize β (ℓ + 1) with hU
  have hθ0 : 0 ≤ g.hyTheta ℓ := (g.hyTheta_mem ℓ).1.le
  have htσ : g.t ℓ ≤ σ := g.t_le_imedEnd hθ0
  have ht2 : 2 ≤ g.t ℓ := g.two_le_t hℓ
  have hL0 : 0 ≤ L := by linarith
  -- `U_(ℓ+1) ≤ L^β + 1`
  have hUle : (U : ℝ) ≤ L ^ β + 1 := by
    rw [hU, g.netSize_succ β hℓ]
    exact (Nat.ceil_lt_add_one (by positivity)).le
  -- `t_ℓ = exp L`
  have htL : (g.t ℓ : ℝ) = Real.exp L := (g.exp_logEnd hℓ).symm
  refine ⟨ht2.trans htσ, ?_, ?_⟩
  · -- `σ log σ ≥ t log t = exp(L) L ≥ exp L ≥ 2 (K' - 1) (L^β + 1)`
    have htσr : (g.t ℓ : ℝ) ≤ σ := by exact_mod_cast htσ
    have htpos : (0 : ℝ) < g.t ℓ := by exact_mod_cast (show 0 < g.t ℓ by omega)
    have hlog : Real.log (g.t ℓ) ≤ Real.log σ := Real.log_le_log htpos htσr
    have hlogt : Real.log (g.t ℓ) = L := rfl
    have h1 : (g.t ℓ : ℝ) * Real.log (g.t ℓ) ≤ σ * Real.log σ :=
      mul_le_mul htσr hlog (by rw [hlogt]; exact hL0) (htpos.le.trans htσr)
    rw [hlogt, htL] at h1
    have h2 : Real.exp L ≤ Real.exp L * L := le_mul_of_one_le_right (exp_pos _).le hl3
    rw [one_mul] at hp1
    have h3 : (2 * (K' - 1 : ℕ) : ℝ) * U ≤ (2 * (K' - 1 : ℕ) : ℝ) * (L ^ β + 1) :=
      mul_le_mul_of_nonneg_left hUle (by positivity)
    linarith
  · -- `σ + K' (U + K') ≤ exp((1 + c) L) + exp(c L) ≤ 2 exp((1 + c) L) ≤ t_(ℓ+1)`
    have hθc : g.hyTheta ℓ ≤ c := by
      rw [g.hyTheta_eq hte, ← hLdef]
      have hlogL : 1 / c ≤ Real.log L := by
        rw [← Real.log_exp (1 / c)]
        exact Real.log_le_log (exp_pos _) hl1
      have hlogpos : 0 < Real.log L := (by positivity : (0 : ℝ) < 1 / c).trans_le hlogL
      rw [div_le_iff₀ hlogpos]
      rw [div_le_iff₀ hc0] at hlogL
      linarith
    have hσle : (σ : ℝ) ≤ Real.exp ((1 + c) * L) := by
      have h1 : (σ : ℝ) ≤ (g.t ℓ : ℝ) ^ (1 + g.hyTheta ℓ) := Nat.floor_le (by positivity)
      rw [htL, ← Real.exp_mul] at h1
      refine h1.trans (Real.exp_le_exp.mpr ?_)
      nlinarith
    have hKU : ((K' * (U + K') : ℕ) : ℝ) ≤ Real.exp (c * L) := by
      push_cast
      refine le_trans ?_ hp2
      have hLb : 0 ≤ L ^ β := by positivity
      have hK0 : (0 : ℝ) ≤ K' := Nat.cast_nonneg _
      have h1 : (K' : ℝ) * (U + K') ≤ K' * (L ^ β + 1 + K') :=
        mul_le_mul_of_nonneg_left (by linarith) hK0
      nlinarith [mul_nonneg (mul_nonneg hK0 hK0) hLb]
    have hexp2 : 2 ≤ Real.exp (c * L) := by
      rw [← Real.exp_log (show (0 : ℝ) < 2 by norm_num)]
      refine Real.exp_le_exp.mpr ?_
      rw [div_le_iff₀ hc0] at hl2
      linarith
    have hcL : Real.exp (c * L) ≤ Real.exp ((1 + c) * L) := Real.exp_le_exp.mpr (by nlinarith)
    have htnext : Real.exp ((1 + 2 * c) * L) ≤ g.t (ℓ + 1) := by
      rw [← g.exp_logEnd (by omega), g.logEnd_succ_eq (j := ℓ) hℓ, ← hLdef]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hr.le hL0)
    have hsplit : Real.exp ((1 + 2 * c) * L) = Real.exp ((1 + c) * L) * Real.exp (c * L) := by
      rw [← Real.exp_add]
      ring_nf
    have hfinal : ((σ + K' * (U + K') : ℕ) : ℝ) ≤ g.t (ℓ + 1) := by
      push_cast at hKU ⊢
      have : Real.exp ((1 + c) * L) * 2 ≤ Real.exp ((1 + c) * L) * Real.exp (c * L) :=
        mul_le_mul_of_nonneg_left hexp2 (exp_pos _).le
      linarith
    have hfinal' : σ + K' * (U + K') ≤ g.t (ℓ + 1) := by exact_mod_cast hfinal
    omega

@[deprecated (since := "2026-11-19")]
alias eventually_imedEnd_R2 := eventually_two_le_imedEnd_and_le_t_sub_imedEnd

/-- [INC-P000, proof of Lemma `lem:ranksA`, Step 1, (R1)] On a grid with `x_ℓ → x`, every
`x₊ > x` has `x_ℓ ≤ x₊` for every large `ℓ` (the paper's `x₊ = 2x`). -/
lemma eventually_ratio_le {x : ℝ} (hg : Tendsto g.ratio atTop (𝓝 x)) {xp : ℝ} (hxp : x < xp) :
    ∀ᶠ ℓ in atTop, g.ratio ℓ ≤ xp :=
  ((tendsto_order.1 hg).2 _ hxp).mono fun _ h ↦ h.le

/-- [INC-P000, proof of Lemma `lem:ranksA`, Step 4, (T1)–(T2)] For `β > 1`, `D > 0` and every
`C`, `C ≤ D L_ℓ^(β-1)` for every large `ℓ` (the paper's (T1) with `D = κ_ε`, `C = 1`, and (T2) with
`D = Δ_ε`, `C = 2 x₊³`). -/
lemma eventually_le_mul_logEnd_rpow {β : ℝ} (hβ : 1 < β) {D : ℝ} (hD : 0 < D) (C : ℝ) :
    ∀ᶠ ℓ in atTop, C ≤ D * g.logEnd ℓ ^ (β - 1) := by
  have h := (tendsto_rpow_atTop (by linarith : 0 < β - 1)).comp g.tendsto_logEnd_atTop
  filter_upwards [h.eventually_ge_atTop (C / D)] with ℓ hℓ
  rw [div_le_iff₀ hD] at hℓ
  simp only [Function.comp_apply] at hℓ
  linarith

/-- [INC-P000, proof of Lemma `lem:ranksA`, Step 4, (T4)] On a grid with `x_ℓ → x`, for `β > 1`,
every `C ≥ 0` and every `K'`, `K' + 1 + C L_(ℓ+1) ≤ U_(ℓ+1)` for every large `ℓ` (the paper's (T4)
with `C = 8 x₊² / ε'²`): `L_(ℓ+1) = x_(ℓ+1) L_ℓ ≤ (|x| + 1) L_ℓ` and `U_(ℓ+1) ≥ L_ℓ^β`. -/
lemma eventually_add_mul_logEnd_le_netSize {x : ℝ} (hg : Tendsto g.ratio atTop (𝓝 x)) {β : ℝ}
    (hβ : 1 < β) {C : ℝ} (hC : 0 ≤ C) (K' : ℕ) :
    ∀ᶠ ℓ in atTop, K' + 1 + C * g.logEnd (ℓ + 1) ≤ g.netSize β (ℓ + 1) := by
  have hx1 : ∀ᶠ ℓ in atTop, g.ratio (ℓ + 1) ≤ |x| + 1 :=
    (tendsto_add_atTop_nat 1).eventually
      (g.eventually_ratio_le hg (by linarith [le_abs_self x] : x < |x| + 1))
  have hL1 : ∀ᶠ ℓ in atTop, (1 : ℝ) ≤ g.logEnd ℓ := g.tendsto_logEnd_atTop.eventually_ge_atTop _
  have hLb := g.eventually_le_mul_logEnd_rpow hβ one_pos (K' + 1 + C * (|x| + 1))
  filter_upwards [eventually_ge_atTop 1, hx1, hL1, hLb] with ℓ hℓ hx hl hb
  rw [one_mul] at hb
  set L := g.logEnd ℓ with hLdef
  have hL0 : 0 < L := by linarith
  have hU : L ^ β ≤ g.netSize β (ℓ + 1) := by
    rw [g.netSize_succ β hℓ]
    exact Nat.le_ceil _
  have hLb' : L ^ β = L * L ^ (β - 1) := by
    rw [Real.rpow_sub_one hL0.ne', mul_div_cancel₀ _ hL0.ne']
  have hL1' : g.logEnd (ℓ + 1) ≤ (|x| + 1) * L := by
    rw [g.logEnd_succ_eq (j := ℓ) hℓ, ← hLdef]
    exact mul_le_mul_of_nonneg_right hx hL0.le
  have hK0 : (0 : ℝ) ≤ K' := Nat.cast_nonneg _
  have hx0 : 0 ≤ |x| + 1 := by positivity
  calc (K' : ℝ) + 1 + C * g.logEnd (ℓ + 1) ≤ (K' + 1) * L + C * ((|x| + 1) * L) := by
        have := mul_le_mul_of_nonneg_left hL1' hC
        nlinarith
    _ = L * (K' + 1 + C * (|x| + 1)) := by ring
    _ ≤ L * L ^ (β - 1) := mul_le_mul_of_nonneg_left hb hL0.le
    _ = L ^ β := hLb'.symm
    _ ≤ g.netSize β (ℓ + 1) := hU

/-- [INC-P000, proof of Lemma `lem:ranksA`, Step 4, (T3)] For `β > 0` and every `C`,
`C ≤ U_ℓ` for every large `ℓ` (the paper's (T3), first part, with `C = 2 w₀ / min(ε, ε')`). -/
lemma eventually_le_netSize {β : ℝ} (hβ : 0 < β) (C : ℝ) :
    ∀ᶠ ℓ in atTop, C ≤ g.netSize β ℓ := by
  have h := (tendsto_rpow_atTop hβ).comp g.tendsto_logEnd_atTop
  have h1 : ∀ᶠ ℓ in atTop, C ≤ g.logEnd (ℓ - 1) ^ β :=
    (h.comp (tendsto_sub_atTop_nat 1)).eventually_ge_atTop C
  filter_upwards [eventually_ge_atTop 2, h1] with ℓ hℓ h2
  obtain ⟨j, rfl⟩ : ∃ j, ℓ = j + 1 := ⟨ℓ - 1, by omega⟩
  rw [g.netSize_succ β (by omega)]
  rw [Nat.add_sub_cancel] at h2
  exact h2.trans (Nat.le_ceil _)

/-- [INC-P000, proof of Lemma `lem:ranksA`, Step 4, (T3)] For `D > 0` and every `C`,
`C ≤ D L_ℓ` for every large `ℓ` (the paper's (T3), second part, with `D = ε / κ(m⋆ + ε̄)` and
`C = w₀ κ(m⋆ + ε̄)`): `eventually_le_mul_logEnd_rpow` at `β = 2`. -/
lemma eventually_le_mul_logEnd {D : ℝ} (hD : 0 < D) (C : ℝ) :
    ∀ᶠ ℓ in atTop, C ≤ D * g.logEnd ℓ := by
  filter_upwards [g.eventually_le_mul_logEnd_rpow one_lt_two hD C] with ℓ hℓ
  rwa [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one] at hℓ

/-- The default consistency margins tend to `0`: `γ_ℓ = min(1/2, max(L_ℓ, 1)^(-1/4)) → 0`. -/
lemma tendsto_hyGamma : Tendsto g.hyGamma atTop (𝓝 0) := by
  have h : Tendsto (fun ℓ ↦ max (g.logEnd ℓ) 1 ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      (tendsto_atTop_mono (fun ℓ ↦ le_max_left _ _) g.tendsto_logEnd_atTop)
  have h2 : Tendsto (fun ℓ ↦ min (1 / 2 : ℝ) (max (g.logEnd ℓ) 1 ^ (-(1 / 4 : ℝ)))) atTop
      (𝓝 (min (1 / 2) 0)) := tendsto_const_nhds.min h
  rw [min_eq_right (by norm_num)] at h2
  exact h2

/-- [INC-P000, proof of Lemma `lem:ranksA`, Step 3, (R3)] On a grid with `x_ℓ → x > 0`, for
margins `γ_ℓ → 0`, `η > 0` and every `C`, the threshold `h̄_ℓ = (1 - γ_ℓ) y_(ℓ-1) L_ℓ` beats two
batches ahead for every large `ℓ`: `(1 + 2η)(h̄_ℓ - C) ≥ (1 + η) L_(ℓ+2)` (the paper's (R3) with
`C = w₀ κ(m⋆ + ε̄)`, `η = η_g`), since `h̄_ℓ / L_(ℓ+2) = (1 - γ_ℓ) x_(ℓ-1)² / (x_(ℓ+1) x_(ℓ+2)) → 1`
and `L_ℓ → ∞`. -/
lemma eventually_threshold_ge {x : ℝ} (hx : 0 < x) (hg : Tendsto g.ratio atTop (𝓝 x))
    {γ : ℕ → ℝ} (hγ : Tendsto γ atTop (𝓝 0)) {η : ℝ} (hη : 0 < η) (C : ℝ) :
    ∀ᶠ ℓ in atTop, (1 + η) * g.logEnd (ℓ + 2) ≤
      (1 + 2 * η) * ((1 - γ ℓ) * g.ratio (ℓ - 1) ^ 2 * g.logEnd ℓ - C) := by
  -- the ratio `f_ℓ = (1 - γ_ℓ) x_(ℓ-1)² / (x_(ℓ+1) x_(ℓ+2)) → 1`
  have hf : Tendsto (fun ℓ ↦ (1 - γ ℓ) * g.ratio (ℓ - 1) ^ 2 /
      (g.ratio (ℓ + 1) * g.ratio (ℓ + 2))) atTop (𝓝 ((1 - 0) * x ^ 2 / (x * x))) := by
    refine ((tendsto_const_nhds.sub hγ).mul ((hg.comp (tendsto_sub_atTop_nat 1)).pow 2)).div
      ((hg.comp (tendsto_add_atTop_nat 1)).mul (hg.comp (tendsto_add_atTop_nat 2)))
      (by positivity)
  have hf1 : (1 - 0) * x ^ 2 / (x * x) = 1 := by
    field_simp
    norm_num
  rw [hf1] at hf
  set δ := η / (2 * (1 + 2 * η)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hfδ : ∀ᶠ ℓ in atTop, 1 - δ < (1 - γ ℓ) * g.ratio (ℓ - 1) ^ 2 /
      (g.ratio (ℓ + 1) * g.ratio (ℓ + 2)) := (tendsto_order.1 hf).1 _ (by linarith)
  have hL2 : ∀ᶠ ℓ in atTop, (1 + 2 * η) * C / (η / 2) ≤ g.logEnd (ℓ + 2) :=
    (g.tendsto_logEnd_atTop.comp (tendsto_add_atTop_nat 2)).eventually_ge_atTop _
  filter_upwards [eventually_ge_atTop 1, hfδ, hL2] with ℓ hℓ hδℓ hl
  have hr1 : 0 < g.ratio (ℓ + 1) := (zero_lt_one).trans (g.one_lt_ratio (by omega))
  have hr2 : 0 < g.ratio (ℓ + 2) := (zero_lt_one).trans (g.one_lt_ratio (by omega))
  have hL2eq : g.logEnd (ℓ + 2) = g.ratio (ℓ + 1) * g.ratio (ℓ + 2) * g.logEnd ℓ := by
    rw [show ℓ + 2 = ℓ + 1 + 1 from rfl, g.logEnd_succ_eq (j := ℓ + 1) (by omega),
      g.logEnd_succ_eq (j := ℓ) hℓ]
    ring
  have hden : 0 < g.ratio (ℓ + 1) * g.ratio (ℓ + 2) := mul_pos hr1 hr2
  have hmain : (1 - δ) * g.logEnd (ℓ + 2) ≤ (1 - γ ℓ) * g.ratio (ℓ - 1) ^ 2 * g.logEnd ℓ := by
    rw [lt_div_iff₀ hden] at hδℓ
    rw [hL2eq]
    have hL0 : 0 ≤ g.logEnd ℓ := (g.logEnd_pos hℓ).le
    nlinarith
  rw [div_le_iff₀ (by positivity)] at hl
  have h1 : (1 + 2 * η) * (1 - δ) = 1 + 2 * η - η / 2 := by
    rw [hδ]
    field_simp
  have h2 := mul_le_mul_of_nonneg_left hmain (by linarith : (0 : ℝ) ≤ 1 + 2 * η)
  rw [← mul_assoc, h1] at h2
  nlinarith

/-- `U_j ≤ (1 + L_ℓ)^β` for `j ≤ ℓ + 1` and `β ≥ 1`: `U_j ≤ L_(j-1)^β + 1 ≤ (1 + L_(j-1))^β`. -/
lemma netSize_le_one_add_rpow {β : ℝ} (hβ : 1 ≤ β) {j ℓ : ℕ} (hjℓ : j ≤ ℓ + 1) :
    (g.netSize β j : ℝ) ≤ (1 + g.logEnd ℓ) ^ β := by
  have hL0 : ∀ i, 0 ≤ g.logEnd i := g.logEnd_nonneg
  have h1 : (1 : ℝ) ≤ (1 + g.logEnd ℓ) ^ β :=
    Real.one_le_rpow (by linarith [hL0 ℓ]) (by linarith)
  rcases Nat.lt_or_ge j 2 with hj | hj
  · unfold netSize
    rw [ite_eq_left (by omega), Nat.cast_one]
    exact h1
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [g.netSize_succ β (by omega)]
  have hceil := (Nat.ceil_lt_add_one (Real.rpow_nonneg (hL0 i) β)).le
  have hsup : g.logEnd i ^ β + 1 ≤ (1 + g.logEnd i) ^ β := by
    have := Real.add_rpow_le_rpow_add (zero_le_one) (hL0 i) hβ
    rw [Real.one_rpow] at this
    linarith
  have hmono : (1 + g.logEnd i) ^ β ≤ (1 + g.logEnd ℓ) ^ β :=
    Real.rpow_le_rpow (by linarith [hL0 i])
      (by linarith [g.logEnd_monotone (show i ≤ ℓ by omega)]) (by linarith)
  linarith

/-- [INC-P000, Lemma `lem:sumsA`(a), the sum] For `β ≥ 1`, `η > 0`, `C ≥ 0` and nonnegative
`p_k ≤ C U_k⁴ t_(k+1)^(-(1+η))` for `k ∈ [k₀, L)`, `k₀ ≥ 1` (the bound of
Lemma `lem:probasA`(b) on `P(𝒱_k) + P(Π_k)`, with `C = (1 + K) C_η`),
`∑_(k₀ ≤ k < L) U_(k+2) p_k ≤ C σ_(5β)(η)` with `σ_p(θ) = (2/θ) e^(θ/2) (2p / (e θ))^p`
(Lemma `lem:sums`(ii)): `U_(k+2), U_k ≤ (1 + L_(k+1))^β` and `B_(k+1) ≥ 1`. -/
lemma sum_netSize_mul_le {β η C : ℝ} (hβ : 1 ≤ β) (hη : 0 < η) (hC : 0 ≤ C) {p : ℕ → ℝ}
    (hp0 : ∀ k, 0 ≤ p k) {k₀ L : ℕ} (hk₀ : 1 ≤ k₀)
    (hp : ∀ k ∈ Finset.Ico k₀ L,
      p k ≤ C * (g.netSize β k : ℝ) ^ 4 * (g.t (k + 1) : ℝ) ^ (-(1 + η))) :
    ∑ k ∈ Finset.Ico k₀ L, (g.netSize β (k + 2) : ℝ) * p k ≤
      C * (2 / η * Real.exp (η / 2) * (2 * (5 * β) / (Real.exp 1 * η)) ^ (5 * β)) := by
  -- Each term is at most `C f(k + 1)`, with
  -- `f(ℓ) = (t_ℓ - t_(ℓ-1)) (1 + log t_ℓ)^(5β) t_ℓ^(-(1+η))` (from `U_j ≤ (1 + L_(k+1))^β` for
  -- `j ≤ k + 2`), and the sum of the `f(ℓ)` is bounded by `sum_mul_one_add_log_rpow_le`.
  set f : ℕ → ℝ := fun ℓ ↦ ((g.t ℓ : ℝ) - g.t (ℓ - 1)) * (1 + Real.log (g.t ℓ)) ^ (5 * β) *
    (g.t ℓ : ℝ) ^ (-(1 + η)) with hf
  have hf0 : ∀ ℓ, 1 ≤ ℓ → 0 ≤ f ℓ := fun ℓ hℓ ↦ by
    have : (g.t (ℓ - 1) : ℝ) ≤ g.t ℓ := by
      exact_mod_cast g.strictMono.monotone (Nat.sub_le ℓ 1)
    have hlog : 0 ≤ 1 + Real.log (g.t ℓ) := by
      have := Real.log_natCast_nonneg (g.t ℓ)
      linarith
    exact mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hlog _))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hterm : ∀ k ∈ Finset.Ico k₀ L, (g.netSize β (k + 2) : ℝ) * p k ≤ C * f (k + 1) := by
    intro k hk
    have hk1 : 1 ≤ k := hk₀.trans (Finset.mem_Ico.mp hk).1
    set M := 1 + g.logEnd (k + 1) with hM
    have hM1 : 1 ≤ M := by
      have : 0 ≤ g.logEnd (k + 1) := g.logEnd_nonneg _
      linarith
    have hM0 : 0 < M := by linarith
    have hU2 := g.netSize_le_one_add_rpow hβ (j := k + 2) (ℓ := k + 1) le_rfl
    have hU0 := g.netSize_le_one_add_rpow hβ (j := k) (ℓ := k + 1) (by omega)
    have htpos : (0 : ℝ) < g.t (k + 1) := g.t_pos (by omega)
    have htr : 0 ≤ (g.t (k + 1) : ℝ) ^ (-(1 + η)) := Real.rpow_nonneg htpos.le _
    have hB : (1 : ℝ) ≤ (g.t (k + 1) : ℝ) - g.t k := by
      have : g.t k + 1 ≤ g.t (k + 1) := g.strictMono (Nat.lt_succ_self k)
      have : ((g.t k + 1 : ℕ) : ℝ) ≤ g.t (k + 1) := by exact_mod_cast this
      push_cast at this
      linarith
    have hU4 : (g.netSize β k : ℝ) ^ 4 ≤ M ^ (4 * β) := by
      calc (g.netSize β k : ℝ) ^ 4 ≤ (M ^ β) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hU0 4
        _ = M ^ (4 * β) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hM0.le]
          congr 1
          push_cast
          ring
    have hpk := hp k hk
    have hpk0 : 0 ≤ p k := hp0 k
    have h5 : M ^ β * M ^ (4 * β) = M ^ (5 * β) := by
      rw [← Real.rpow_add hM0]
      ring_nf
    -- `L_ℓ` is `log t_ℓ`, by definition
    have hlogt : Real.log (g.t (k + 1)) = g.logEnd (k + 1) := rfl
    calc (g.netSize β (k + 2) : ℝ) * p k
        ≤ M ^ β * (C * M ^ (4 * β) * (g.t (k + 1) : ℝ) ^ (-(1 + η))) := by
          refine mul_le_mul hU2 (hpk.trans ?_) hpk0 (by positivity)
          gcongr
      _ = C * (M ^ β * M ^ (4 * β)) * (g.t (k + 1) : ℝ) ^ (-(1 + η)) := by ring
      _ = C * (1 * M ^ (5 * β) * (g.t (k + 1) : ℝ) ^ (-(1 + η))) := by rw [h5]; ring
      _ ≤ C * f (k + 1) := by
          refine mul_le_mul_of_nonneg_left ?_ hC
          rw [hf]
          simp only [Nat.add_sub_cancel, hlogt, ← hM]
          gcongr
  -- the sum of the `f (k + 1)` over `[k₀, L)` is at most the sum of the `f ℓ` over `[2, L]`
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hC
  rw [Finset.sum_Ico_add' (fun ℓ ↦ f ℓ) k₀ L 1]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (t := Finset.Ico 2 (L + 1)) ?_ ?_) ?_
  · intro ℓ hℓ
    simp only [Finset.mem_Ico] at hℓ ⊢
    omega
  · intro ℓ hℓ _
    exact hf0 ℓ (by simp only [Finset.mem_Ico] at hℓ; omega)
  · exact g.sum_mul_one_add_log_rpow_le (by positivity) hη (L + 1)

/-- [INC-P000, Lemma `lem:sumsA`(b), the sum] For `β ≥ 1`, `η > 0`, `C, c ≥ 0` and
`a_i ≤ c e^(-ε² L_(i-2)^β)` (the bound of Lemma `lem:probasA`(a) on `P(𝒜_(i-1)^c) + P(𝒜_i^c)`,
`c = 2 c_𝒜(ε)`, `U_(i-1) ≥ L_(i-2)^β`) and `v_i ≤ C U_i⁴ t_(i+1)^(-(1+η))` (as in
`Grid.sum_netSize_mul_le`) for `i ∈ [k₀, L)`, `k₀ ≥ 3`, if `L_(i+1) ≤ x₊³ L_(i-2)` there
(Lemma `lem:ranksA`) and `S ≥ 2 x₊³ y - ε² y^β` for every `y ≥ 0` (the paper's `S'_ε`), then
`∑_(k₀ ≤ i < L) B_(i+1) (a_i + v_i) ≤ (c / 2) e^S + C σ_(4β)(η)`:
`B_(i+1) e^(-ε² L_(i-2)^β) ≤ e^S B_(i+1) t_(i+1)^(-2)` and `∑ B t^(-2) ≤ t_1^(-1) ≤ 1/2`
(Lemma `lem:sums`(i)). -/
lemma sum_batch_mul_le {β η C c xp ε S : ℝ} (hβ : 1 ≤ β) (hη : 0 < η) (hC : 0 ≤ C)
    (hc : 0 ≤ c) {a v : ℕ → ℝ} {k₀ L : ℕ} (hk₀ : 3 ≤ k₀)
    (ha : ∀ i ∈ Finset.Ico k₀ L, a i ≤ c * Real.exp (-(ε ^ 2 * g.logEnd (i - 2) ^ β)))
    (hv : ∀ i ∈ Finset.Ico k₀ L,
      v i ≤ C * (g.netSize β i : ℝ) ^ 4 * (g.t (i + 1) : ℝ) ^ (-(1 + η)))
    (hxp : ∀ i ∈ Finset.Ico k₀ L, g.logEnd (i + 1) ≤ xp ^ 3 * g.logEnd (i - 2))
    (hS : ∀ y : ℝ, 0 ≤ y → 2 * xp ^ 3 * y - ε ^ 2 * y ^ β ≤ S) :
    ∑ i ∈ Finset.Ico k₀ L, ((g.t (i + 1) : ℝ) - g.t i) * (a i + v i) ≤
      c / 2 * Real.exp S +
        C * (2 / η * Real.exp (η / 2) * (2 * (4 * β) / (Real.exp 1 * η)) ^ (4 * β)) := by
  set f1 : ℕ → ℝ := fun ℓ ↦ ((g.t ℓ : ℝ) - g.t (ℓ - 1)) * (g.t ℓ : ℝ) ^ (-(1 + 1 : ℝ)) with hf1
  set f2 : ℕ → ℝ := fun ℓ ↦ ((g.t ℓ : ℝ) - g.t (ℓ - 1)) * (1 + Real.log (g.t ℓ)) ^ (4 * β) *
    (g.t ℓ : ℝ) ^ (-(1 + η)) with hf2
  have hB : ∀ ℓ, (0 : ℝ) ≤ (g.t ℓ : ℝ) - g.t (ℓ - 1) := fun ℓ ↦ by
    have : (g.t (ℓ - 1) : ℝ) ≤ g.t ℓ := by
      exact_mod_cast g.strictMono.monotone (Nat.sub_le ℓ 1)
    linarith
  have hf10 : ∀ ℓ, 0 ≤ f1 ℓ := fun ℓ ↦ mul_nonneg (hB ℓ) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hf20 : ∀ ℓ, 0 ≤ f2 ℓ := fun ℓ ↦ by
    have hlog : 0 ≤ 1 + Real.log (g.t ℓ) := by
      have := Real.log_natCast_nonneg (g.t ℓ)
      linarith
    exact mul_nonneg (mul_nonneg (hB ℓ) (Real.rpow_nonneg hlog _))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hterm : ∀ i ∈ Finset.Ico k₀ L, ((g.t (i + 1) : ℝ) - g.t i) * (a i + v i) ≤
      c * Real.exp S * f1 (i + 1) + C * f2 (i + 1) := by
    intro i hi
    have hi3 : 3 ≤ i := hk₀.trans (Finset.mem_Ico.mp hi).1
    have hBi : (0 : ℝ) ≤ (g.t (i + 1) : ℝ) - g.t i := by simpa using hB (i + 1)
    have htpos : (0 : ℝ) < g.t (i + 1) := g.t_pos (by omega)
    -- the events `𝒜^c`
    have hA : ((g.t (i + 1) : ℝ) - g.t i) * a i ≤ c * Real.exp S * f1 (i + 1) := by
      have hL2 : 0 ≤ g.logEnd (i - 2) := g.logEnd_nonneg _
      have hexp : Real.exp (-(ε ^ 2 * g.logEnd (i - 2) ^ β)) ≤
          Real.exp S * (g.t (i + 1) : ℝ) ^ (-(1 + 1 : ℝ)) := by
        rw [Real.rpow_def_of_pos htpos, ← Real.exp_add, Real.exp_le_exp]
        have h1 := hS _ hL2
        have h2 := hxp i hi
        have hlog : Real.log (g.t (i + 1)) = g.logEnd (i + 1) := rfl
        rw [hlog]
        nlinarith
      calc ((g.t (i + 1) : ℝ) - g.t i) * a i
          ≤ ((g.t (i + 1) : ℝ) - g.t i) * (c * Real.exp (-(ε ^ 2 * g.logEnd (i - 2) ^ β))) :=
            mul_le_mul_of_nonneg_left (ha i hi) hBi
        _ ≤ ((g.t (i + 1) : ℝ) - g.t i) *
            (c * (Real.exp S * (g.t (i + 1) : ℝ) ^ (-(1 + 1 : ℝ)))) := by
            gcongr
        _ = c * Real.exp S * f1 (i + 1) := by rw [hf1]; simp only [Nat.add_sub_cancel]; ring
    -- the events `𝒱`, `Π`
    have hV : ((g.t (i + 1) : ℝ) - g.t i) * v i ≤ C * f2 (i + 1) := by
      set M := 1 + g.logEnd (i + 1) with hM
      have hM0 : 0 < M := by
        have : 0 ≤ g.logEnd (i + 1) := g.logEnd_nonneg _
        linarith
      have hU0 := g.netSize_le_one_add_rpow hβ (j := i) (ℓ := i + 1) (by omega)
      have hU4 : (g.netSize β i : ℝ) ^ 4 ≤ M ^ (4 * β) := by
        calc (g.netSize β i : ℝ) ^ 4 ≤ (M ^ β) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hU0 4
          _ = M ^ (4 * β) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hM0.le]
            congr 1
            push_cast
            ring
      have htr : 0 ≤ (g.t (i + 1) : ℝ) ^ (-(1 + η)) := Real.rpow_nonneg htpos.le _
      have hlogt : Real.log (g.t (i + 1)) = g.logEnd (i + 1) := rfl
      calc ((g.t (i + 1) : ℝ) - g.t i) * v i
          ≤ ((g.t (i + 1) : ℝ) - g.t i) * (C * M ^ (4 * β) * (g.t (i + 1) : ℝ) ^ (-(1 + η))) := by
            refine mul_le_mul_of_nonneg_left ((hv i hi).trans ?_) hBi
            gcongr
        _ = C * f2 (i + 1) := by
            rw [hf2]
            simp only [Nat.add_sub_cancel, hlogt, ← hM]
            ring
    rw [mul_add]
    linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hsub : ∀ f : ℕ → ℝ, (∀ ℓ, 0 ≤ f ℓ) →
      ∑ i ∈ Finset.Ico k₀ L, f (i + 1) ≤ ∑ ℓ ∈ Finset.Ico 2 (L + 1), f ℓ := fun f hf0 ↦ by
    rw [Finset.sum_Ico_add' (fun ℓ ↦ f ℓ) k₀ L 1]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun ℓ _ _ ↦ hf0 ℓ
    intro ℓ hℓ
    simp only [Finset.mem_Ico] at hℓ ⊢
    omega
  have h1 : ∑ i ∈ Finset.Ico k₀ L, f1 (i + 1) ≤ 1 / 2 := by
    refine (hsub f1 hf10).trans ((g.sum_mul_rpow_le one_pos (L + 1)).trans ?_)
    rw [div_one, Real.rpow_neg_one]
    have : (2 : ℝ) ≤ g.t 1 := by exact_mod_cast g.two_le_t_one
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have h2 : ∑ i ∈ Finset.Ico k₀ L, f2 (i + 1) ≤
      2 / η * Real.exp (η / 2) * (2 * (4 * β) / (Real.exp 1 * η)) ^ (4 * β) :=
    (hsub f2 hf20).trans (g.sum_mul_one_add_log_rpow_le (by positivity) hη (L + 1))
  have hce : 0 ≤ c * Real.exp S := mul_nonneg hc (Real.exp_pos _).le
  have := mul_le_mul_of_nonneg_left h1 hce
  have := mul_le_mul_of_nonneg_left h2 hC
  linarith

end Grid

end Incognita.BatchedBandits
