/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

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
-/

@[expose] public section

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

end Incognita.BatchedBandits
