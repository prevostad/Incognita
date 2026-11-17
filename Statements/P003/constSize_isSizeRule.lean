/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.Examples

/-! # P003, lem:prior-game (a): deterministic sizes form a size rule

[INC-P003, Lemma (lem:prior-game), item (a)]. A constant map `N' ≡ n⁰ ∈ ℕ^K` is a size rule.

Differences of form with the paper: arms are a finite type `α` with `2 ≤ Fintype.card α` (the
paper's `K ≥ 2`); the constant map is `constSize n⁰`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Incognita.TransferBandits

namespace Incognita.Statements.P003

/-- [INC-P003, lem:prior-game (a)] A constant size map is a size rule. -/
theorem constSize_isSizeRule {α : Type*} [Fintype α] [MeasurableSpace α]
    (hK : 2 ≤ Fintype.card α) (n : α → ℕ) :
    IsSizeRule (constSize n : SourceSpace α → α → ℕ) := by
  sorry

end Incognita.Statements.P003
