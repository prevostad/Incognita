/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.Consistency

/-! # P003, prop:drift (b): `𝒫_L` satisfies `Drift_{L'}` for every larger `L'`

[INC-P003, Proposition (prop:drift), item (b)]. Let `L ∈ (0,∞)^K`. Then
`𝒫_L ⊂ {(ν, ν') : Drift_{L'}}` for every `L' ∈ (0,∞)^K` with `L'_k > L_k` for all `k`.

Differences of form with the paper: arms are a finite type `α` with `2 ≤ Fintype.card α` (the
paper's `K ≥ 2`); `L L' : α → ℝ` with `∀ a, 0 < L a` and `∀ a, L a < L' a` (which gives
`L' ∈ (0,∞)^K`); `𝒫_L` is `meanBand L`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Incognita.TransferBandits

namespace Incognita.Statements.P003

/-- [INC-P003, prop:drift (b)] Every pair of `𝒫_L` satisfies `Drift_{L'}` when `L' > L`
componentwise. -/
theorem drift_of_mem_meanBand {α : Type*} [Fintype α] [MeasurableSpace α]
    (hK : 2 ≤ Fintype.card α) {L L' : α → ℝ} (hL : ∀ a, 0 < L a) (hLL' : ∀ a, L a < L' a)
    {ν ν' : Kernel α ℝ} (h : (ν, ν') ∈ meanBand L) :
    DriftBound L' ν ν' := by
  sorry

end Incognita.Statements.P003
