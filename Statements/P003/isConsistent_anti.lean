/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.Consistency

/-! # P003, prop:classes (a): `𝒞_L` is antitone in `L`

[INC-P003, Proposition (prop:classes), item (a)]. If `L ≤ L'` (in `(0,∞)^K`, componentwise), then
`𝒞_{L'} ⊂ 𝒞_L`.

Differences of form with the paper: arms are a finite type `α` with `2 ≤ Fintype.card α` (the
paper's `K ≥ 2`); `L L' : α → ℝ` with positive values; `𝒞_L` is the set of transfer learners
`{π | IsConsistent L π}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Incognita.TransferBandits

namespace Incognita.Statements.P003

/-- [INC-P003, prop:classes (a)] If `L ≤ L'`, then `𝒞_{L'} ⊂ 𝒞_L`. -/
theorem isConsistent_anti {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (hK : 2 ≤ Fintype.card α) {L L' : α → ℝ}
    (hL : ∀ a, 0 < L a) (hL' : ∀ a, 0 < L' a) (hLL' : ∀ a, L a ≤ L' a) :
    {π : TransferAlgorithm α | IsConsistent L' π} ⊆ {π | IsConsistent L π} := by
  sorry

end Incognita.Statements.P003
