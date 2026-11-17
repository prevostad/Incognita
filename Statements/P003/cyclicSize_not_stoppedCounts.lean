/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.Examples
public import Incognita.TransferBandits.PriorGame

/-! # P003, prop:stopped-games (c): with three arms, a size rule that no stopped game gives

[INC-P003, Proposition (prop:stopped-games), item (c)]. Let `K ≥ 3` and `b_k = 1{X'_{k,1} > 1/2}`
for `k = 1, 2, 3`. The cyclic map `N^cyc` (`e₁ + e₂` on `{b₁ = 1, b₂ = 0}`, `e₂ + e₃` on
`{b₂ = 1, b₃ = 0}`, `e₃ + e₁` on `{b₃ = 1, b₁ = 0}`, `e₁ + e₂ + e₃` elsewhere) is a size rule with
`|N^cyc| ≤ 3`. There is no prior game, over any number `T'` of rounds, with a stopping time whose
stopped counts have, for every `ν' ∈ 𝒫^K`, the same law under `P'_{ν'}` as `N^cyc`.

Differences of form with the paper: the paper's arms `1, 2, 3` are three distinct arms
`a₁, a₂, a₃` of a finite type `α` with `3 ≤ Fintype.card α`; `X'_{k,1}` is the value of index `0` of
the stack of `k`; `N^cyc` is `cyclicSize a₁ a₂ a₃`; `|n| = ∑_k n_k`; the law of a size map under
`P'_{ν'}` is the image measure `(sourceMeasure ν').map`, and `𝒫^K` is `unitBandits α`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Incognita.TransferBandits

namespace Incognita.Statements.P003

/-- [INC-P003, prop:stopped-games (c)] The cyclic map is a size rule with total at most `3`, and no
stopped prior game has its law under every source instance. -/
theorem cyclicSize_not_stoppedCounts {α : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (hK : 3 ≤ Fintype.card α) {a₁ a₂ a₃ : α}
    (h₁₂ : a₁ ≠ a₂) (h₂₃ : a₂ ≠ a₃) (h₁₃ : a₁ ≠ a₃) :
    IsSizeRule (cyclicSize a₁ a₂ a₃) ∧ (∀ ω, ∑ a, cyclicSize a₁ a₂ a₃ ω a ≤ 3) ∧
      ¬ ∃ (T' : ℕ) (g : PriorStrategy α) (τ : SourceSpace α → ℕ), g.IsStoppingTime T' τ ∧
        ∀ ν' ∈ unitBandits α, (sourceMeasure ν').map (g.stoppedCounts τ) =
          (sourceMeasure ν').map (cyclicSize a₁ a₂ a₃) := by
  sorry

end Incognita.Statements.P003
