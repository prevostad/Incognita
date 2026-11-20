/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Monotone
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.EReal.Basic

/-! # Elementary bounds on the logarithms of the dual formula of `𝒦_inf`

Real inequalities on `log (1 - λ (y - μ))`, the integrand of the dual formula of `𝒦_inf`
[INC-P000, Definition `def:kinf`], for a reward `y ≤ 1`, a level `μ` and a dual variable
`λ ∈ [0, 1/(1-μ))`. They use only Mathlib, so that the deviation bounds of `𝒦_inf`
(`Incognita.BatchedBandits.DualGrid`, `Deviations`, `KInf.Deviations`) do not depend on the
algorithm HY.

## Main statements

* `one_sub_mul_sub_pos`: `1 - λ (y - μ) > 0`.
* `log_le_log_one_sub_mul`: the scaling inequality
  `log ϖ + log (1 - λ (y - μ)) ≤ log (1 - ϖ λ (y - μ))` for `ϖ ∈ (0, 1]`
  [INC-P000, Lemma `lem:kinf`(vi)].
* `sub_two_mul_sq_le_log_one_add`: `log (1 + u) ≥ u - 2 u²` for `u ≥ -1/2`.

Other elementary bounds of [INC-P000]:

* `log_le_sqrt`: `log y ≤ √y` for `y > 0` (Lemma `lem:constC`(a));
* `min_div_two_le_one_sub_exp_neg`: `1 - e^(-v) ≥ min(v, 1) / 2` for `v ≥ 0`;
* `one_div_one_sub_exp_neg_le`: `1 / (1 - e^(-v)) ≤ 1 + 1 / v` for `v > 0` (Lemma `lem:sumC`);
* `ofReal_sub_log_le_div`: the index form `y v ≤ x + y log N` of (W1) gives `(v - log N)⁺ ≤ x / y`.
* `mul_log_le_mul_of_le`: `C log x ≤ D x` passes from `x ≥ e` to every `N ≥ x` (`log y / y` is
  nonincreasing on `[e, ∞)`).
-/

@[expose] public section

open scoped ENNReal

namespace Incognita.BatchedBandits

/-- `1 - λ (y - μ) > 0` for `y ≤ 1` and `λ ∈ [0, 1/(1-μ))`. -/
lemma one_sub_mul_sub_pos {lam μ y : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam * (1 - μ) < 1)
    (hy : y ≤ 1) : 0 < 1 - lam * (y - μ) := by
  have : lam * (y - μ) ≤ lam * (1 - μ) := mul_le_mul_of_nonneg_left (by linarith) hlam
  linarith

/-- **Scaling** [INC-P000, Lemma `lem:kinf`(vi)]: for `λ ∈ [0, 1/(1-μ))`, `ϖ ∈ (0, 1]` and
`y ≤ 1`, `log (1 - ϖ λ (y - μ)) ≥ log ϖ + log (1 - λ (y - μ))`. -/
lemma log_le_log_one_sub_mul {lam μ ϖ y : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam * (1 - μ) < 1)
    (hϖ : 0 < ϖ) (hϖ1 : ϖ ≤ 1) (hy1 : y ≤ 1) :
    Real.log ϖ + Real.log (1 - lam * (y - μ)) ≤ Real.log (1 - ϖ * lam * (y - μ)) := by
  have hpos : 0 < 1 - lam * (y - μ) := one_sub_mul_sub_pos hlam hlam1 hy1
  rw [← Real.log_mul hϖ.ne' hpos.ne']
  exact Real.log_le_log (mul_pos hϖ hpos) (by nlinarith)

/-- `log (1 + u) ≥ u - 2 u²` for `u ≥ -1/2` (the step of the proof of
[INC-P000, Lemma `lem:kinf`(iv)]). -/
lemma sub_two_mul_sq_le_log_one_add {u : ℝ} (hu : -(1 / 2) ≤ u) :
    u - 2 * u ^ 2 ≤ Real.log (1 + u) := by
  have h1 : 0 < 1 + u := by linarith
  have h := Real.one_sub_inv_le_log_of_pos h1
  have : u - 2 * u ^ 2 ≤ 1 - (1 + u)⁻¹ := by
    rw [show 1 - (1 + u)⁻¹ = u / (1 + u) by field_simp; ring, le_div_iff₀ h1]
    nlinarith [sq_nonneg u]
  linarith

/-- `log y ≤ √y` for `y > 0`. -/
lemma log_le_sqrt {y : ℝ} (hy : 0 < y) : Real.log y ≤ Real.sqrt y := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have h1 : Real.log y = 2 * Real.log (Real.sqrt y) := by
    conv_lhs => rw [← Real.mul_self_sqrt hy.le]
    rw [Real.log_mul hs.ne' hs.ne']
    ring
  have h2 : Real.log (Real.sqrt y) = Real.log (Real.sqrt y / 2) + Real.log 2 := by
    rw [← Real.log_mul (by positivity) (by norm_num), div_mul_cancel₀ _ (by norm_num)]
  have h3 := Real.log_le_sub_one_of_pos (show 0 < Real.sqrt y / 2 by positivity)
  have h4 : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num) (by norm_num)
    linarith
  linarith

/-- `1 - e^(-v) ≥ min(v, 1) / 2` for `v ≥ 0`: `e^(-v) ≤ 1/(1 + v)`, so
`1 - e^(-v) ≥ v / (1 + v)`. -/
lemma min_div_two_le_one_sub_exp_neg {v : ℝ} (hv : 0 ≤ v) :
    min v 1 / 2 ≤ 1 - Real.exp (-v) := by
  have h1 : Real.exp (-v) ≤ 1 / (1 + v) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by linarith) (by linarith [Real.add_one_le_exp v])
  have h2 : min v 1 / 2 ≤ 1 - 1 / (1 + v) := by
    have h3 : 1 - 1 / (1 + v) = v / (1 + v) := by field_simp; ring
    rw [h3, le_div_iff₀ (by linarith)]
    rcases le_total v 1 with h | h
    · rw [min_eq_left h]
      nlinarith
    · rw [min_eq_right h]
      linarith
  linarith

/-- `1 / (1 - e^(-v)) ≤ 1 + 1 / v` for `v > 0` (since `e^v - 1 ≥ v`). -/
lemma one_div_one_sub_exp_neg_le {v : ℝ} (hv : 0 < v) :
    1 / (1 - Real.exp (-v)) ≤ 1 + 1 / v := by
  set E := Real.exp v with hE
  have hEv : 1 + v ≤ E := by linarith [Real.add_one_le_exp v]
  have hEpos : 0 < E := Real.exp_pos v
  have h1 : 1 - Real.exp (-v) = (E - 1) / E := by
    rw [Real.exp_neg, ← hE]
    field_simp
  rw [h1, one_div_div, div_le_iff₀ (by linarith)]
  have h2 : 1 ≤ (E - 1) / v := by
    rw [le_div_iff₀ hv]
    linarith
  have h3 : (1 + 1 / v) * (E - 1) = (E - 1) + (E - 1) / v := by ring
  rw [h3]
  linarith

/-- The index form of (W1) gives the divided form: if `y > 0` and
`y v ≤ x + y log N` in `EReal` (with `x ∈ [0, ∞]`), then `(v - log N)⁺ ≤ x / y` in `ℝ≥0∞`. -/
lemma ofReal_sub_log_le_div {x : ℝ≥0∞} {y v N : ℝ} (hy : 0 < y)
    (h : ((y * v : ℝ) : EReal) ≤ (x : EReal) + ((y * Real.log N : ℝ) : EReal)) :
    ENNReal.ofReal (v - Real.log N) ≤ x / ENNReal.ofReal y := by
  by_cases hx : x = ⊤
  · rw [hx, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top]
    exact le_top
  rw [← ENNReal.ofReal_toReal hx, EReal.coe_ennreal_ofReal,
    max_eq_left ENNReal.toReal_nonneg, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
  rw [← ENNReal.ofReal_toReal hx, ← ENNReal.ofReal_div_of_pos hy]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [le_div_iff₀ hy]
  nlinarith

/-- `log y / y` is nonincreasing on `[e, ∞)`: for `C ≥ 0`, `e ≤ x ≤ N` and `C log x ≤ D x`,
also `C log N ≤ D N` (condition (c) of Definition `def:amb` at a count `N ≥ n_ℓ`). -/
lemma mul_log_le_mul_of_le {C D x N : ℝ} (hC : 0 ≤ C) (hx : Real.exp 1 ≤ x) (hxN : x ≤ N)
    (h : C * Real.log x ≤ D * x) : C * Real.log N ≤ D * N := by
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le hx
  have hN0 : 0 < N := hx0.trans_le hxN
  have hanti := Real.log_div_self_antitoneOn (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr (hx.trans hxN))
    hxN
  simp only at hanti
  rw [div_le_div_iff₀ hN0 hx0] at hanti
  have h1 := mul_le_mul_of_nonneg_left hanti hC
  have h2 := mul_le_mul_of_nonneg_right h hN0.le
  have h3 : C * Real.log N * x ≤ D * N * x := by linarith
  exact le_of_mul_le_mul_right h3 hx0

end Incognita.BatchedBandits
