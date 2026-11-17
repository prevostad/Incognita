/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.Examples

/-! # P003, lem:lookahead: the look-ahead map is a bounded size map and not a size rule

[INC-P003, Lemma (lem:lookahead)]. The look-ahead map `N^la` (`N^la_1 = 1` if `X'_{1,2} > 1/2`,
`2` otherwise, `N^la_k = 0` for `k ≥ 2`) is a bounded size map and not a size rule.

Differences of form with the paper: the paper's arm `1` is an arbitrary arm `a₁` of a finite type
`α` with `2 ≤ Fintype.card α` (the paper's `K ≥ 2`), and `X'_{1,2}` is the value of index `1` of
its stack (indices from `0`); "size map" is measurability; "bounded" is
`∃ M, ∀ ω a, N^la ω a ≤ M`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Incognita.TransferBandits

namespace Incognita.Statements.P003

/-- [INC-P003, lem:lookahead] The look-ahead map is measurable and bounded, and not a size rule. -/
theorem lookahead_not_isSizeRule {α : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (hK : 2 ≤ Fintype.card α) (a₁ : α) :
    Measurable (lookahead a₁) ∧ (∃ M : ℕ, ∀ ω a, lookahead a₁ ω a ≤ M) ∧
      ¬ IsSizeRule (lookahead a₁) := by
  sorry

end Incognita.Statements.P003
