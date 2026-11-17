/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.Consistency

/-! # P003, prop:witness (last claim): the class `𝒞_L` is not empty

[INC-P003, Proposition (prop:witness), "in particular `𝒞_L ≠ ∅`"]. For every `L ∈ (0,∞)^K` there
is a transfer learner in `𝒞_L`.

Differences of form with the paper: arms are a finite type `α` with `2 ≤ Fintype.card α` (the
paper's `K ≥ 2`), not only `Fin K`; `L : α → ℝ` with positive values.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Incognita.TransferBandits

namespace Incognita.Statements.P003

/-- [INC-P003, prop:witness] For every `L ∈ (0,∞)^K`, some transfer learner belongs to `𝒞_L`. -/
theorem exists_isConsistent {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (hK : 2 ≤ Fintype.card α) {L : α → ℝ} (hL : ∀ a, 0 < L a) :
    ∃ π : TransferAlgorithm α, IsConsistent L π := by
  sorry

end Incognita.Statements.P003
