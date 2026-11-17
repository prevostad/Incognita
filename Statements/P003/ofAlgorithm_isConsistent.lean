/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.Consistency

/-! # P003, prop:witness (first claim): source-ignoring learners of consistent algorithms

[INC-P003, Proposition (prop:witness), first sentence]. If a bandit algorithm `σ` is consistent on
`𝒫^K`, its source-ignoring learner `π^σ` belongs to `𝒞_{𝟏_K}`, hence to `𝒞_L` for every
`L ∈ (0,∞)^K`.

Differences of form with the paper: arms are a finite type `α` with `2 ≤ Fintype.card α` (the
paper's `K ≥ 2`); bandit algorithms are LML's `Algorithm Unit α ℝ`, consistency on `𝒫^K` is
`IsConsistentOnUnit` (pull counts under LML's law of the trajectory), and `π^σ` is
`TransferAlgorithm.ofAlgorithm σ`; `𝟏_K` is `fun _ ↦ 1`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Incognita.TransferBandits

namespace Incognita.Statements.P003

/-- [INC-P003, prop:witness] The source-ignoring learner of a bandit algorithm consistent on `𝒫^K`
is in `𝒞_𝟏`, and in `𝒞_L` for every `L ∈ (0,∞)^K`. -/
theorem ofAlgorithm_isConsistent {α : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (hK : 2 ≤ Fintype.card α) {σ : Algorithm Unit α ℝ}
    (hσ : IsConsistentOnUnit σ) :
    IsConsistent (fun _ ↦ 1) (TransferAlgorithm.ofAlgorithm σ) ∧
      ∀ L : α → ℝ, (∀ a, 0 < L a) → IsConsistent L (TransferAlgorithm.ofAlgorithm σ) := by
  sorry

end Incognita.Statements.P003
