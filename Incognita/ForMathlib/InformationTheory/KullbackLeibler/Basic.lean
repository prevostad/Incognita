/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import TauCeti.InformationTheory.KullbackLeibler.Tilted

/-! # Relative entropy under a bounded density

If `c • μ ≤ ν` for probability measures `μ`, `ν` and a constant `c > 0`, then `μ ≪ ν` with density
`dμ/dν ≤ 1 / c`, so that `KL(μ ‖ ν) = ∫ log (dμ/dν) dμ ≤ log (1 / c)`.

## Main statements

* `Incognita.klDiv_le_ofReal_neg_log_of_smul_le`: `KL(μ ‖ ν) ≤ -log c` when `c • μ ≤ ν`.
* `Incognita.klDiv_le_ofReal_neg_log_smul_add_smul`: for the mixture
  `ν_u = (1 - u) • μ + u • ρ` of two probability measures, `KL(μ ‖ ν_u) ≤ -log (1 - u)` for
  `u ∈ [0, 1)`.
-/

@[expose] public section

open MeasureTheory Real InformationTheory
open scoped ENNReal NNReal

namespace Incognita

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}

/-- **Relative entropy under a bounded density**: if `c • μ ≤ ν` for probability measures `μ`, `ν`
and `c > 0`, then `KL(μ ‖ ν) ≤ log (1 / c)`. -/
lemma klDiv_le_ofReal_neg_log_of_smul_le [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {c : ℝ≥0} (hc : 0 < c) (h : c • μ ≤ ν) :
    klDiv μ ν ≤ ENNReal.ofReal (-log c) := by
  -- `μ ≪ ν` with `dμ/dν ≤ 1 / c`, so the log-likelihood ratio is at most `-log c`, `μ`-a.e.
  have hμν : μ ≪ ν := by
    intro s hs
    have h1 := h s
    rw [hs, smul_apply, nonpos_iff_eq_zero, smul_eq_zero] at h1
    exact h1.resolve_left (by exact_mod_cast hc.ne')
  -- `c * dμ/dν ≤ 1`, `ν`-almost everywhere.
  have hle : ∀ᵐ x ∂ν, (c : ℝ≥0∞) * μ.rnDeriv ν x ≤ 1 := by
    filter_upwards [Measure.rnDeriv_le_one_of_le h, Measure.rnDeriv_smul_left μ ν c] with x hx hx'
    rw [hx'] at hx
    simpa [ENNReal.smul_def] using hx
  have hllr : ∀ᵐ x ∂μ, llr μ ν x ≤ -log c := by
    filter_upwards [hμν.ae_le hle, Measure.rnDeriv_pos hμν,
      hμν.ae_le (Measure.rnDeriv_lt_top μ ν)] with x hx hpos hlt
    rw [llr_def, ← log_inv]
    have hpos' : 0 < (μ.rnDeriv ν x).toReal := ENNReal.toReal_pos hpos.ne' hlt.ne
    refine log_le_log hpos' ?_
    have h2 : (c : ℝ) * (μ.rnDeriv ν x).toReal ≤ 1 := by
      have := ENNReal.toReal_mono ENNReal.one_ne_top hx
      rwa [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_one] at this
    rw [le_inv_comm₀ hpos' (by exact_mod_cast hc)]
    · rw [inv_eq_one_div, le_div_iff₀ hpos']
      linarith
  have hint : Integrable (llr μ ν) μ :=
    TauCeti.integrable_llr_of_ae_le hμν (integrable_const _) hllr
  rw [klDiv_of_ac_of_integrable hμν hint]
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [probReal_univ, add_sub_cancel_right]
  calc ∫ x, llr μ ν x ∂μ ≤ ∫ _, -log c ∂μ := integral_mono_ae hint (integrable_const _) hllr
    _ = -log c := by simp

/-- **Relative entropy to a mixture**: for probability measures `μ`, `ρ` and `u ∈ [0, 1)`, the
mixture `ν_u = (1 - u) • μ + u • ρ` satisfies `KL(μ ‖ ν_u) ≤ log (1 / (1 - u))`, since
`(1 - u) • μ ≤ ν_u`. The weights are in `ℝ≥0`. -/
lemma klDiv_le_ofReal_neg_log_smul_add_smul [IsProbabilityMeasure μ] (ρ : Measure α)
    [IsProbabilityMeasure ρ] {u : ℝ≥0} (hu : u < 1) :
    klDiv μ ((1 - u) • μ + u • ρ) ≤ ENNReal.ofReal (-log ((1 - u : ℝ≥0) : ℝ)) := by
  have : IsProbabilityMeasure ((1 - u) • μ + u • ρ) := by
    constructor
    rw [add_apply, smul_apply, smul_apply, measure_univ, measure_univ, ENNReal.smul_def,
      ENNReal.smul_def, smul_eq_mul, smul_eq_mul, mul_one, mul_one, ← ENNReal.coe_add,
      tsub_add_cancel_of_le hu.le, ENNReal.coe_one]
  exact klDiv_le_ofReal_neg_log_of_smul_le (tsub_pos_of_lt hu) (Measure.le_add_right le_rfl)

end Incognita
