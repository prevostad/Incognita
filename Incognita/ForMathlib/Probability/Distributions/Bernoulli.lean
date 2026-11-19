/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Mathlib.Probability.Distributions.Bernoulli

/-! # A Bernoulli law is concentrated on its two atoms

## Main statements

* `Incognita.ae_eq_or_eq_bernoulliMeasure`: almost every point of `Ber(x, y, p)` is `x` or `y`.
* `Incognita.ae_bernoulliMeasure_eq_zero_or_eq_one`: almost every point of `Ber(1, 0, p)` is `0` or
  `1`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

open scoped unitInterval

namespace Incognita

/-- A Bernoulli law `Ber(x, y, p)` on a space with measurable singletons is concentrated on
`{x, y}`. -/
lemma ae_eq_or_eq_bernoulliMeasure {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (x y : X) (p : I) : ∀ᵐ z ∂Ber(x, y, p), z = x ∨ z = y := by
  rw [ae_iff]
  refine bernoulliMeasure_apply_of_notMem_of_notMem p ?_ (by simp) (by simp)
  exact ((measurableSet_singleton x).union (measurableSet_singleton y)).compl.congr
    (by ext z; simp; tauto)

/-- A Bernoulli law on `{0, 1} ⊆ ℝ` is concentrated on `{0, 1}`. -/
lemma ae_bernoulliMeasure_eq_zero_or_eq_one (p : I) : ∀ᵐ x ∂Ber((1 : ℝ), 0, p), x = 0 ∨ x = 1 :=
  (ae_eq_or_eq_bernoulliMeasure (1 : ℝ) 0 p).mono fun _ h ↦ h.symm

@[deprecated (since := "2026-11-19")]
alias ae_bernoulli_zero_or_one := ae_bernoulliMeasure_eq_zero_or_eq_one

end Incognita
