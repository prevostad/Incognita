/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import LMLExplore.InformationTheory.KullbackLeibler.Bernoulli

/-! # Data processing for the means of a `[0, 1]`-valued statistic

## Main statements

* `Incognita.klDiv_bernoulli_integral_le`: `kl(E_μ Z, E_ν Z) ≤ KL(μ, ν)` for a measurable `Z` with
  values in `[0, 1]`, from LMLExplore's `klBer_integral_le_klDiv` and Mathlib's `klDiv_map_le`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory

namespace Incognita

/-- **Data processing for the means** [INC-P003, cite:GMS19-Lemma1]: for probability measures
`μ, ν` and a measurable `Z` with values in `[0, 1]`, `kl(E_μ Z, E_ν Z) ≤ KL(μ, ν)`, with
`kl(x, y)` the divergence between the Bernoulli laws of parameters `x` and `y`. -/
lemma klDiv_bernoulli_integral_le {X : Type*} [MeasurableSpace X] (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {Z : X → ℝ} (hZ : Measurable Z)
    (hZ01 : ∀ x, Z x ∈ Set.Icc 0 1) :
    klDiv (Ber((1 : ℝ), 0, Set.projIcc 0 1 zero_le_one (∫ x, Z x ∂μ)))
        (Ber((1 : ℝ), 0, Set.projIcc 0 1 zero_le_one (∫ x, Z x ∂ν))) ≤ klDiv μ ν := by
  rw [← LMLExplore.klBer_def]
  have h1 : ∫ x, Z x ∂μ = (μ.map Z)[id] := by
    rw [integral_map hZ.aemeasurable aestronglyMeasurable_id]
    rfl
  have h2 : ∫ x, Z x ∂ν = (ν.map Z)[id] := by
    rw [integral_map hZ.aemeasurable aestronglyMeasurable_id]
    rfl
  have hae : ∀ ρ : Measure X, ∀ᵐ y ∂(ρ.map Z), y ∈ Set.Icc (0 : ℝ) 1 := fun ρ ↦ by
    exact (ae_map_iff hZ.aemeasurable measurableSet_Icc).mpr (ae_of_all _ hZ01)
  rw [h1, h2]
  exact (LMLExplore.klBer_integral_le_klDiv (hae μ) (hae ν)).trans (klDiv_map_le _ _ hZ)

end Incognita
