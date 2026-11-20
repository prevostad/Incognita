/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import TauCeti.InformationTheory.KullbackLeibler.ChangeOfReference
public import TauCeti.InformationTheory.KullbackLeibler.Tilted
public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Convex

/-! # Relative entropy under a bounded density

If `c • μ ≤ ν` for probability measures `μ`, `ν` and a constant `c > 0`, then `μ ≪ ν` with density
`dμ/dν ≤ 1 / c`, so that `KL(μ ‖ ν) = ∫ log (dμ/dν) dμ ≤ log (1 / c)`.

## Main statements

* `Incognita.ae_llr_le_neg_log_of_smul_le`: `llr μ ν ≤ -log c`, `μ`-almost everywhere, when
  `c • μ ≤ ν`; `Incognita.ae_llr_le_neg_log_of_withDensity_le`: `llr P Q ≤ -log f` when
  `P.withDensity f ≤ Q`.
* `Incognita.klDiv_le_add_ofReal_neg_log_of_smul_le`: `KL(μ ‖ Q) ≤ KL(μ ‖ ν) - log c` when
  `c • ν ≤ Q` (by Tau Ceti's chain rule `TauCeti.llr_add_llr`); the other bounds are its cases.
* `Incognita.klDiv_le_ofReal_neg_log_of_smul_le`: `KL(μ ‖ ν) ≤ -log c` when `c • μ ≤ ν`.
* `Incognita.klDiv_smul_add_smul_le_add`: `KL(μ ‖ (1 - u) • ν + u • ρ) ≤ KL(μ ‖ ν) - log (1 - u)`
  for probability measures `μ`, `ν`, `ρ` and `u ∈ [0, 1)`.
* `Incognita.klDiv_le_ofReal_neg_log_smul_add_smul`: for the mixture
  `ν_u = (1 - u) • μ + u • ρ` of two probability measures, `KL(μ ‖ ν_u) ≤ -log (1 - u)` for
  `u ∈ [0, 1)`.
-/

@[expose] public section

open MeasureTheory Real InformationTheory
open scoped ENNReal NNReal

namespace Incognita

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}

/-- **Log-likelihood ratio under a bounded density**: if `c • μ ≤ ν` for a constant `c > 0`, then
`dμ/dν ≤ 1 / c`, so `llr μ ν ≤ -log c`, `μ`-almost everywhere. -/
lemma ae_llr_le_neg_log_of_smul_le [SigmaFinite ν] {c : ℝ≥0} (hc : 0 < c)
    (h : c • μ ≤ ν) : ∀ᵐ x ∂μ, llr μ ν x ≤ -log c := by
  -- `μ ≤ c⁻¹ • ν` is σ-finite
  have : SigmaFinite μ := by
    refine Measure.sigmaFinite_of_le (c⁻¹ • ν) (Measure.le_iff'.mpr fun s ↦ ?_)
    have h1 : c • μ s ≤ ν s := by simpa using Measure.le_iff'.mp h s
    calc μ s = c⁻¹ • (c • μ s) := by rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
      _ ≤ c⁻¹ • ν s := by
        simp only [ENNReal.smul_def, smul_eq_mul] at h1 ⊢
        gcongr
      _ = (c⁻¹ • ν) s := (smul_apply _ _ _).symm
  have hμν : μ ≪ ν := (Measure.absolutelyContinuous_smul (ENNReal.coe_ne_zero.mpr hc.ne')).trans
    (Measure.absolutelyContinuous_of_le (by rwa [← ENNReal.smul_def]))
  -- `c * dμ/dν ≤ 1`, `ν`-almost everywhere.
  have hle : ∀ᵐ x ∂ν, (c : ℝ≥0∞) * μ.rnDeriv ν x ≤ 1 := by
    filter_upwards [Measure.rnDeriv_le_one_of_le h, Measure.rnDeriv_smul_left' μ ν c] with x hx hx'
    rw [hx'] at hx
    simpa [ENNReal.smul_def] using hx
  filter_upwards [hμν.ae_le hle, Measure.rnDeriv_pos hμν,
    hμν.ae_le (Measure.rnDeriv_lt_top μ ν)] with x hx hpos hlt
  rw [llr_def, ← log_inv]
  have hpos' : 0 < (μ.rnDeriv ν x).toReal := ENNReal.toReal_pos hpos.ne' hlt.ne
  refine log_le_log hpos' ?_
  have h2 : (c : ℝ) * (μ.rnDeriv ν x).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top hx
    rwa [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_one] at this
  rw [le_inv_comm₀ hpos' (by exact_mod_cast hc), inv_eq_one_div, le_div_iff₀ hpos']
  linarith

/-- **Log-likelihood ratio under a density bound**: if `P.withDensity f ≤ Q` for finite measures
`P`, `Q` and a measurable `f : α → ℝ≥0` with `f ≠ 0` `P`-almost everywhere, then
`dP/dQ ≤ 1 / f`, so `llr P Q ≤ -log f`, `P`-almost everywhere. -/
lemma ae_llr_le_neg_log_of_withDensity_le {P Q : Measure α} [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {f : α → ℝ≥0} (hf : Measurable f) (hf0 : ∀ᵐ x ∂P, f x ≠ 0)
    (hle : P.withDensity (fun x ↦ (f x : ℝ≥0∞)) ≤ Q) :
    ∀ᵐ x ∂P, llr P Q x ≤ -log (f x) := by
  set R := P.withDensity (fun x ↦ (f x : ℝ≥0∞)) with hR
  have : IsFiniteMeasure R := isFiniteMeasure_of_le Q hle
  have hf0' : ∀ᵐ x ∂P, (f x : ℝ≥0∞) ≠ 0 := hf0.mono fun x hx ↦ ENNReal.coe_ne_zero.mpr hx
  have hPR : P ≪ R := withDensity_absolutelyContinuous' hf.coe_nnreal_ennreal.aemeasurable hf0'
  have hPQ : P ≪ Q := hPR.trans (Measure.absolutelyContinuous_of_le hle)
  have hchain := Measure.rnDeriv_mul_rnDeriv (κ := Q) hPR
  have hRQ1 := Measure.rnDeriv_le_one_of_le hle
  have hPRd := Measure.rnDeriv_withDensity_right P P hf.coe_nnreal_ennreal.aemeasurable hf0'
    (Filter.Eventually.of_forall fun x ↦ ENNReal.coe_ne_top)
  filter_upwards [hPQ.ae_le hchain, hPQ.ae_le hRQ1, hPRd, Measure.rnDeriv_self P, hf0,
    Measure.rnDeriv_pos hPQ, hPQ.ae_le
        (Measure.rnDeriv_lt_top P Q)] with x hch h1 hd hpp hfx hpos hlt
  -- `dP/dQ = (dP/dR) (dR/dQ) ≤ 1 / f`
  have hle' : P.rnDeriv Q x ≤ ((f x : ℝ≥0∞))⁻¹ := by
    have h1' : R.rnDeriv Q x ≤ 1 := h1
    rw [← hch, Pi.mul_apply, hd, hpp, mul_one]
    calc ((f x : ℝ≥0∞))⁻¹ * R.rnDeriv Q x ≤ ((f x : ℝ≥0∞))⁻¹ * 1 := by gcongr
      _ = _ := mul_one _
  have hfx' : ((f x : ℝ≥0∞))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (ENNReal.coe_ne_zero.mpr hfx)
  have hreal : (P.rnDeriv Q x).toReal ≤ ((f x : ℝ))⁻¹ := by
    refine (ENNReal.toReal_mono hfx' hle').trans_eq ?_
    rw [ENNReal.toReal_inv, ENNReal.coe_toReal]
  rw [llr_def, ← log_inv]
  exact log_le_log (ENNReal.toReal_pos hpos.ne' hlt.ne) hreal

/-- **Relative entropy under a change of reference with a bounded density**: if `c • ν ≤ Q` for
probability measures `ν`, `Q` and `c > 0`, then `KL(μ ‖ Q) ≤ KL(μ ‖ ν) - log c` for every
probability measure `μ`. -/
lemma klDiv_le_add_ofReal_neg_log_of_smul_le [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Q : Measure α} [IsProbabilityMeasure Q] {c : ℝ≥0} (hc : 0 < c) (h : c • ν ≤ Q) :
    klDiv μ Q ≤ klDiv μ ν + ENNReal.ofReal (-log c) := by
  by_cases hac : μ ≪ ν
  swap
  · rw [klDiv_of_not_ac hac, top_add]
    exact le_top
  by_cases hint : Integrable (llr μ ν) μ
  swap
  · rw [klDiv_of_not_integrable hint, top_add]
    exact le_top
  have hνQ : ν ≪ Q := (Measure.absolutelyContinuous_smul (ENNReal.coe_ne_zero.mpr hc.ne')).trans
    (Measure.absolutelyContinuous_of_le (by rwa [← ENNReal.smul_def]))
  have hμQ : μ ≪ Q := hac.trans hνQ
  -- `llr μ Q = llr μ ν + llr ν Q` and `llr ν Q ≤ -log c`, `μ`-almost everywhere
  have hllr : ∀ᵐ x ∂μ, llr μ Q x ≤ llr μ ν x + -log c := by
    filter_upwards [TauCeti.llr_add_llr hac hνQ, hac.ae_le (ae_llr_le_neg_log_of_smul_le hc h)]
      with x hx hb
    rw [← hx, Pi.add_apply]
    linarith
  have hintQ : Integrable (llr μ Q) μ :=
    TauCeti.integrable_llr_of_ae_le hμQ (hint.add (integrable_const _)) hllr
  rw [klDiv_of_ac_of_integrable hμQ hintQ, klDiv_of_ac_of_integrable hac hint]
  simp only [probReal_univ, add_sub_cancel_right]
  calc ENNReal.ofReal (∫ x, llr μ Q x ∂μ)
      ≤ ENNReal.ofReal (∫ x, llr μ ν x ∂μ + -log c) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc ∫ x, llr μ Q x ∂μ ≤ ∫ x, (llr μ ν x + -log c) ∂μ :=
              integral_mono_ae hintQ (hint.add (integrable_const _)) hllr
          _ = ∫ x, llr μ ν x ∂μ + -log c := by
              rw [integral_add hint (integrable_const _)]
              simp
    _ ≤ _ := ENNReal.ofReal_add_le

/-- **Relative entropy under a bounded density**: if `c • μ ≤ ν` for probability measures `μ`, `ν`
and `c > 0`, then `KL(μ ‖ ν) ≤ log (1 / c)`: the case `ν = μ` of
`klDiv_le_add_ofReal_neg_log_of_smul_le`. -/
lemma klDiv_le_ofReal_neg_log_of_smul_le [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {c : ℝ≥0} (hc : 0 < c) (h : c • μ ≤ ν) :
    klDiv μ ν ≤ ENNReal.ofReal (-log c) := by
  simpa [klDiv_self] using klDiv_le_add_ofReal_neg_log_of_smul_le (μ := μ) hc h

/-- **Relative entropy to a mixture**: for probability measures `μ`, `ρ` and `u ∈ [0, 1)`, the
mixture `ν_u = (1 - u) • μ + u • ρ` satisfies `KL(μ ‖ ν_u) ≤ log (1 / (1 - u))`, since
`(1 - u) • μ ≤ ν_u`; `ν_u` is a probability measure by Tau Ceti's
`isProbabilityMeasure_smul_add_smul`. The weights are in `ℝ≥0`. -/
lemma klDiv_le_ofReal_neg_log_smul_add_smul [IsProbabilityMeasure μ] (ρ : Measure α)
    [IsProbabilityMeasure ρ] {u : ℝ≥0} (hu : u < 1) :
    klDiv μ ((1 - u) • μ + u • ρ) ≤ ENNReal.ofReal (-log ((1 - u : ℝ≥0) : ℝ)) := by
  have : IsProbabilityMeasure ((1 - u) • μ + u • ρ) := by
    rw [ENNReal.smul_def, ENNReal.smul_def]
    exact TauCeti.MeasureTheory.isProbabilityMeasure_smul_add_smul
      (by rw [← ENNReal.coe_add, tsub_add_cancel_of_le hu.le, ENNReal.coe_one]) μ ρ
  exact klDiv_le_ofReal_neg_log_of_smul_le (tsub_pos_of_lt hu) (Measure.le_add_right le_rfl)

/-- **Relative entropy to a mixture**: for probability measures `μ`, `ν`, `ρ` and `u ∈ [0, 1)`,
`KL(μ ‖ (1 - u) • ν + u • ρ) ≤ KL(μ ‖ ν) + log (1 / (1 - u))`: the mixture dominates
`(1 - u) • ν` (`klDiv_le_add_ofReal_neg_log_of_smul_le`). -/
lemma klDiv_smul_add_smul_le_add [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ρ : Measure α) [IsProbabilityMeasure ρ] {u : ℝ≥0} (hu : u < 1) :
    klDiv μ ((1 - u) • ν + u • ρ) ≤ klDiv μ ν + ENNReal.ofReal (-log ((1 - u : ℝ≥0) : ℝ)) := by
  have : IsProbabilityMeasure ((1 - u) • ν + u • ρ) := by
    rw [ENNReal.smul_def, ENNReal.smul_def]
    exact TauCeti.MeasureTheory.isProbabilityMeasure_smul_add_smul
      (by rw [← ENNReal.coe_add, tsub_add_cancel_of_le hu.le, ENNReal.coe_one]) ν ρ
  exact klDiv_le_add_ofReal_neg_log_of_smul_le (tsub_pos_of_lt hu) (Measure.le_add_right le_rfl)

end Incognita
