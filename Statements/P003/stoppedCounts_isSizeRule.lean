/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.PriorGame

/-! # P003, prop:stopped-games (a): stopped counts form a size rule

[INC-P003, Proposition (prop:stopped-games), item (a)]. The stopped counts of a prior game over
`T'` rounds (def:stopped-game) form a size rule, with `|N'| ≤ T'`.

Differences of form with the paper: arms are a finite type `α` with `2 ≤ Fintype.card α` (the
paper's `K ≥ 2`); the strategy is a `PriorStrategy α`, the stopping time `τ` satisfies
`PriorStrategy.IsStoppingTime g T' τ`, and `|n| = ∑_k n_k`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Incognita.TransferBandits

namespace Incognita.Statements.P003

/-- [INC-P003, prop:stopped-games (a)] The stopped counts of a prior game over `T'` rounds form a
size rule whose total is at most `T'`. -/
theorem stoppedCounts_isSizeRule {α : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (hK : 2 ≤ Fintype.card α) (g : PriorStrategy α) {T' : ℕ}
    {τ : SourceSpace α → ℕ} (hτ : g.IsStoppingTime T' τ) :
    IsSizeRule (g.stoppedCounts τ) ∧ ∀ ω, ∑ a, g.stoppedCounts τ ω a ≤ T' := by
  sorry

end Incognita.Statements.P003
