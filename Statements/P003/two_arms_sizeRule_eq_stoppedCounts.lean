/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.PriorGame

/-! # P003, prop:stopped-games (b): with two arms, bounded size rules are stopped games

[INC-P003, Proposition (prop:stopped-games), item (b)]. Let `K = 2` and let `N'` be a size rule with
`T' := sup_{Ω'} |N'| < ∞`. There are a prior game over `T'` rounds and a stopping time `τ` of it
whose stopped counts equal `N'` at every point of `Ω'`.

Differences of form with the paper: arms are a finite type `α` with `Fintype.card α = 2`;
`|n| = ∑_k n_k`; the boundedness `sup |N'| < ∞` is `∃ M, ∀ ω, ∑_k N' ω k ≤ M`, and `T'` is the
supremum `sSup (Set.range fun ω ↦ ∑_k N' ω k)` in `ℕ`; the prior game is a `PriorStrategy α`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Incognita.TransferBandits

namespace Incognita.Statements.P003

/-- [INC-P003, prop:stopped-games (b)] With two arms, every bounded size rule is, at every point,
the stopped counts of a prior game over `sup |N'|` rounds. -/
theorem two_arms_sizeRule_eq_stoppedCounts {α : Type*} [Fintype α] [DecidableEq α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (hK : Fintype.card α = 2)
    {N : SourceSpace α → α → ℕ} (hN : IsSizeRule N) (hbdd : ∃ M : ℕ, ∀ ω, ∑ a, N ω a ≤ M) :
    ∃ (g : PriorStrategy α) (τ : SourceSpace α → ℕ),
      g.IsStoppingTime (sSup (Set.range fun ω ↦ ∑ a, N ω a)) τ ∧
        ∀ ω, g.stoppedCounts τ ω = N ω := by
  sorry

end Incognita.Statements.P003
