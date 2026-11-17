/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.PriorGame

/-! # P003, lem:prior-game (b): the counts of a prior bandit game form a size rule

[INC-P003, Lemma (lem:prior-game), item (b)]. The counts `N'` of a prior bandit game over `T'`
rounds (def:prior-game) form a size rule, with `N'_k ≤ T'`.

Differences of form with the paper: arms are a finite type `α` with `2 ≤ Fintype.card α` (the
paper's `K ≥ 2`); the strategy `(α_r)_{r ≤ T'}` is a `PriorStrategy α` (one measurable map per
0-based round, the rounds `r ≥ T'` being unused), and its counts are `PriorStrategy.counts g T'`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Incognita.TransferBandits

namespace Incognita.Statements.P003

/-- [INC-P003, lem:prior-game (b)] The counts of a prior bandit game over `T'` rounds form a size
rule, and each count is at most `T'`. -/
theorem priorCounts_isSizeRule {α : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (hK : 2 ≤ Fintype.card α) (g : PriorStrategy α) (T' : ℕ) :
    IsSizeRule (g.counts T') ∧ ∀ ω a, g.counts T' ω a ≤ T' := by
  sorry

end Incognita.Statements.P003
