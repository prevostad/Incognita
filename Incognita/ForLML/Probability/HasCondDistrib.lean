/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.HasCondDistrib

/-! # Conditional distribution of a constant

Complements to LML's `LeanMachineLearning.ForMathlib.Probability.HasCondDistrib`.

## Main statements

* `ProbabilityTheory.hasCondDistrib_const_dirac`: a constant random variable `c` has the
  conditional law `δ_c` given any measurable random variable.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

/-- A constant random variable has the conditional law `δ_c` given any measurable `X`. -/
lemma hasCondDistrib_const_dirac {Ω β γ : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace β]
    [MeasurableSpace γ] {P : Measure Ω} [IsFiniteMeasure P] {X : Ω → β} (hX : Measurable X)
    (c : γ) : HasCondDistrib (fun _ ↦ c) X (Kernel.const β (Measure.dirac c)) P where
  aemeasurable := (hX.prodMk measurable_const).aemeasurable
  map_eq := by
    rw [Measure.compProd_const, Measure.prod_dirac, Measure.map_map measurable_prodMk_right hX]
    rfl

end ProbabilityTheory
