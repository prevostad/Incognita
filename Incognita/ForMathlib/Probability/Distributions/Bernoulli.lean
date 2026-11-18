/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Mathlib.Probability.Distributions.Bernoulli

/-! # The Bernoulli law on `{0, 1}` is concentrated on `{0, 1}`

## Main statements

* `Incognita.ae_bernoulli_zero_or_one`: almost every point of `Ber(1, 0, p)` is `0` or `1`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

open scoped unitInterval

namespace Incognita

/-- A Bernoulli law on `{0, 1} ⊆ ℝ` is concentrated on `{0, 1}`. -/
lemma ae_bernoulli_zero_or_one (p : I) : ∀ᵐ x ∂Ber((1 : ℝ), 0, p), x = 0 ∨ x = 1 := by
  rw [ae_iff]
  refine bernoulliMeasure_apply_of_notMem_of_notMem p ?_ (by simp) (by simp)
  exact ((measurableSet_singleton 0).union (measurableSet_singleton 1)).compl.congr
    (by ext x; simp; tauto)

end Incognita
