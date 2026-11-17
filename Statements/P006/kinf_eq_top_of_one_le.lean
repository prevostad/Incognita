/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.Instances
public import LMLExplore.Bandits.LaiRobbins

/-! # P006, `prop:kinf`(i): `𝒦_inf(P, μ) = ∞` for `μ ≥ 1`

One frozen statement of the paper P006 (`papers/P006-batched-setting`); its
docstring gives the statement in words and every difference of form with the paper. -/

@[expose] public section

/-- [INC-P006, Proposition `prop:kinf`(i)] Let `P ∈ 𝓜` and `μ ∈ ℝ`. If `μ ≥ 1`, then
`𝒦_inf(P, μ) = +∞`.

Differences of form with the paper:
* `𝓜` is `unitLaws` (probability measures on `ℝ` with `∀ᵐ x, x ∈ [0, 1]`, the paper's
  `Q([0, 1]) = 1`); the mean `m(Q)` is the Bochner integral `∫ x, id x ∂Q`; `𝒦_inf(P, μ)` is
  LMLExplore's `dInf unitLaws P μ = ⨅ Q ∈ {Q ∈ unitLaws | μ < Q[id]}, klDiv P Q` in `ℝ≥0∞`
  (Mathlib's `klDiv`, with `inf ∅ = ∞`), which is the paper's primal definition [INC-P006,
  Definition `def:kinf`]. -/
theorem Incognita.Statements.P006.kinf_eq_top_of_one_le {P : MeasureTheory.Measure ℝ}
    (hP : P ∈ Incognita.BatchedBandits.unitLaws) {μ : ℝ} (hμ : 1 ≤ μ) :
    LMLExplore.Bandits.dInf Incognita.BatchedBandits.unitLaws P μ = ⊤ := by
  sorry
