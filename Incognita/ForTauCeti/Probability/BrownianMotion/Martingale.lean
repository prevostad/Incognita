/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Mathlib.Probability.Independence.Integration
public import TauCeti.Probability.BrownianMotion.Filtered

/-! # The martingales `W` and `W² - t` of a filtered Brownian motion

For a pre-Brownian motion `W` relative to a filtration `ℱ` (Tau Ceti's
`IsFilteredPreBrownianReal`), the martingale identities of `W` and of `W_t² - t` on the sets of
`ℱ_s`: `∫_A W_t = ∫_A W_s` and `∫_A (W_t² - t) = ∫_A (W_s² - s)` for `s ≤ t` and `A ∈ ℱ_s`. They
follow from the independence of the increment `W_t - W_s` and `ℱ_s`, and from its law
`N(0, t - s)`.

## Main statements

* `TauCeti.Probability.IsFilteredPreBrownianReal.setIntegral_eq`: `∫_A W_t = ∫_A W_s`.
* `TauCeti.Probability.IsFilteredPreBrownianReal.setIntegral_sq_sub_eq`:
  `∫_A (W_t² - t) = ∫_A (W_s² - s)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

open scoped NNReal

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ}

lemma measurable (hW : IsFilteredPreBrownianReal ℱ W P) (t : ℝ≥0) : Measurable (W t) :=
  (hW.adapted t).mono (ℱ.le t) le_rfl

lemma memLp (hW : IsFilteredPreBrownianReal ℱ W P) (t : ℝ≥0) : MemLp (W t) 2 P :=
  (hW.hasLaw_eval t).memLp (memLp_id_gaussianReal 2)

/-- An `ℱ_s`-measurable variable is independent of every function of the increment
`W_t - W_s`. -/
lemma integral_mul_comp_sub (hW : IsFilteredPreBrownianReal ℱ W P)
    {s t : ℝ≥0} (hst : s ≤ t) {Z : Ω → ℝ} (hZ : Measurable[ℱ s] Z) {g : ℝ → ℝ}
    (hg : Measurable g) :
    ∫ ω, Z ω * g (W t ω - W s ω) ∂P = (∫ ω, Z ω ∂P) * ∫ ω, g (W t ω - W s ω) ∂P := by
  have hind : Z ⟂ᵢ[P] (fun ω ↦ g (W t ω - W s ω)) := by
    rw [IndepFun_iff_Indep]
    refine indep_of_indep_of_le_right (indep_of_indep_of_le_left (hW.indep_sub hst).symm
      hZ.comap_le) ?_
    exact (hg.comp (comap_measurable (W t - W s))).comap_le
  exact ProbabilityTheory.IndepFun.integral_fun_mul_eq_mul_integral hind
    (hZ.mono (ℱ.le s) le_rfl).aestronglyMeasurable
    (hg.comp ((hW.measurable t).sub (hW.measurable s))).aestronglyMeasurable

lemma integral_increment (hW : IsFilteredPreBrownianReal ℱ W P)
    {s t : ℝ≥0} (hst : s ≤ t) : ∫ ω, (W t ω - W s ω) ∂P = 0 := by
  have := (hW.toIsPreBrownianReal.hasLaw_sub_of_le hst).integral_eq
  simp only [Pi.sub_apply] at this
  rw [this, integral_id_gaussianReal]

lemma integral_sub_sq (hW : IsFilteredPreBrownianReal ℱ W P)
    {s t : ℝ≥0} (hst : s ≤ t) : ∫ ω, (W t ω - W s ω) ^ 2 ∂P = t - s := by
  have hlaw := hW.toIsPreBrownianReal.hasLaw_sub_of_le hst
  have h := hlaw.integral_comp (f := fun x : ℝ ↦ x ^ 2) (by fun_prop)
  simp only [Function.comp_def, Pi.sub_apply] at h
  rw [h]
  have hv := variance_id_gaussianReal (μ := 0) (v := t - s)
  rw [variance_eq_sub (memLp_id_gaussianReal 2)] at hv
  simp only [integral_id_gaussianReal, Pi.pow_apply, id] at hv
  rw [NNReal.coe_sub hst] at hv
  linarith

/-- A set integral as an integral against an indicator. -/
lemma setIntegral_eq_integral_indicator_mul {A : Set Ω} (hA : MeasurableSet A) (f : Ω → ℝ) :
    ∫ ω in A, f ω ∂P = ∫ ω, A.indicator (fun _ ↦ (1 : ℝ)) ω * f ω ∂P := by
  rw [← integral_indicator hA]
  congr 1
  ext ω
  by_cases h : ω ∈ A <;> simp [h]

/-- The martingale property of `W` on the sets of `ℱ_s`: `∫_A W_t = ∫_A W_s`. -/
lemma setIntegral_eq (hW : IsFilteredPreBrownianReal ℱ W P)
    {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[ℱ s] A) :
    ∫ ω in A, W t ω ∂P = ∫ ω in A, W s ω ∂P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hA' := ℱ.le s A hA
  have hZ : Measurable[ℱ s] (A.indicator fun _ ↦ (1 : ℝ)) := measurable_const.indicator hA
  have hint : ∀ r, Integrable (W r) P := fun r ↦ (hW.memLp r).integrable one_le_two
  have hd : Integrable (fun ω ↦ W t ω - W s ω) P := (hint t).sub (hint s)
  have hsplit : ∫ ω in A, W t ω ∂P =
      ∫ ω in A, W s ω ∂P + ∫ ω in A, (W t ω - W s ω) ∂P := by
    rw [← integral_add (hint s).integrableOn hd.integrableOn]
    simp
  rw [hsplit, setIntegral_eq_integral_indicator_mul hA' (fun ω ↦ W t ω - W s ω),
    hW.integral_mul_comp_sub hst hZ (g := fun x ↦ x) measurable_id]
  rw [hW.integral_increment hst]
  simp

/-- The martingale property of `W² - t` on the sets of `ℱ_s`:
`∫_A (W_t² - t) = ∫_A (W_s² - s)`. -/
lemma setIntegral_sq_sub_eq (hW : IsFilteredPreBrownianReal ℱ W P)
    {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[ℱ s] A) :
    ∫ ω in A, (W t ω ^ 2 - t) ∂P = ∫ ω in A, (W s ω ^ 2 - s) ∂P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hA' := ℱ.le s A hA
  have hZ : Measurable[ℱ s] (A.indicator fun _ ↦ (1 : ℝ)) := measurable_const.indicator hA
  have hinc : MemLp (fun ω ↦ W t ω - W s ω) 2 P := (hW.memLp t).sub (hW.memLp s)
  have h0 : Integrable (fun ω ↦ W s ω ^ 2 - (s : ℝ)) P :=
    (hW.memLp s).integrable_sq.sub (integrable_const _)
  have h1 : Integrable (fun ω ↦ (W t ω - W s ω) ^ 2 - (t - s : ℝ)) P :=
    hinc.integrable_sq.sub (integrable_const _)
  have h2 : Integrable (fun ω ↦ 2 * (W s ω * (W t ω - W s ω))) P :=
    ((hW.memLp s).integrable_mul hinc).const_mul 2
  have h01 : Integrable (fun ω ↦ W s ω ^ 2 - (s : ℝ) + ((W t ω - W s ω) ^ 2 - (t - s : ℝ))) P :=
    h0.add h1
  have hdecomp : ∀ ω, W t ω ^ 2 - t = (W s ω ^ 2 - s) + ((W t ω - W s ω) ^ 2 - (t - s : ℝ)) +
      2 * (W s ω * (W t ω - W s ω)) := fun ω ↦ by ring
  simp_rw [hdecomp]
  rw [integral_add h01.integrableOn h2.integrableOn, integral_add h0.integrableOn h1.integrableOn,
    integral_const_mul, setIntegral_eq_integral_indicator_mul hA'
      (fun ω ↦ (W t ω - W s ω) ^ 2 - (t - s : ℝ)),
    setIntegral_eq_integral_indicator_mul hA' (fun ω ↦ W s ω * (W t ω - W s ω)),
    hW.integral_mul_comp_sub hst hZ (g := fun x ↦ x ^ 2 - (t - s : ℝ)) (by fun_prop)]
  have hZs : Measurable[ℱ s] fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω * W s ω :=
    hZ.mul (hW.adapted s)
  have hc := hW.integral_mul_comp_sub hst hZs (g := fun x ↦ x) measurable_id
  simp_rw [← mul_assoc]
  rw [hc, hW.integral_increment hst,
    MeasureTheory.integral_sub hinc.integrable_sq (integrable_const _),
    hW.integral_sub_sq hst]
  simp

end TauCeti.Probability.IsFilteredPreBrownianReal
