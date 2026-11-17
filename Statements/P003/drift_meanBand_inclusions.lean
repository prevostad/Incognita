/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.Consistency

/-! # P003, prop:drift (c): when `Drift_L` and `𝒫_L` contain each other

[INC-P003, Proposition (prop:drift), item (c)]. Let `L ∈ (0,∞)^K`. Within `𝒫^K × 𝒫^K`:
`{Drift_L} ⊂ 𝒫_L` if and only if `L_k ≥ 1` for every `k`; `𝒫_L ⊂ {Drift_L}` if and only if
`L_k > 1` for every `k`; in particular, for `L ∈ (0,1)^K` neither set contains the other.

Differences of form with the paper: arms are a finite type `α` with `2 ≤ Fintype.card α` (the
paper's `K ≥ 2`); `L : α → ℝ` with `∀ a, 0 < L a`; the set `{Drift_L}` is the set of pairs of
`𝒫^K × 𝒫^K` (`unitBandits α`) satisfying `DriftBound L`, and the inclusions are written as
implications; the three claims are the three conjuncts.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Incognita.TransferBandits

namespace Incognita.Statements.P003

/-- [INC-P003, prop:drift (c)] `{Drift_L} ⊂ 𝒫_L` iff `L ≥ 1`, `𝒫_L ⊂ {Drift_L}` iff `L > 1`, and
for `L < 1` neither inclusion holds. -/
theorem drift_meanBand_inclusions {α : Type*} [Fintype α] [MeasurableSpace α]
    (hK : 2 ≤ Fintype.card α) {L : α → ℝ} (hL : ∀ a, 0 < L a) :
    ((∀ ν ν' : Kernel α ℝ, ν ∈ unitBandits α → ν' ∈ unitBandits α →
        DriftBound L ν ν' → (ν, ν') ∈ meanBand L) ↔ ∀ a, 1 ≤ L a) ∧
      ((∀ ν ν' : Kernel α ℝ, (ν, ν') ∈ meanBand L → DriftBound L ν ν') ↔ ∀ a, 1 < L a) ∧
      ((∀ a, L a < 1) →
        (¬ ∀ ν ν' : Kernel α ℝ, ν ∈ unitBandits α → ν' ∈ unitBandits α →
            DriftBound L ν ν' → (ν, ν') ∈ meanBand L) ∧
          ¬ ∀ ν ν' : Kernel α ℝ, (ν, ν') ∈ meanBand L → DriftBound L ν ν') := by
  sorry

end Incognita.Statements.P003
