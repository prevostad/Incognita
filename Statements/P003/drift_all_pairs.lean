/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.Consistency

/-! # P003, prop:drift (d): when a condition holds for every pair

[INC-P003, Proposition (prop:drift), item (d)]. Let `L ∈ (0,∞)^K`. Then `𝒫_L = 𝒫^K × 𝒫^K` if and
only if `L ≥ 𝟏_K`; `Drift_L` holds for every pair of `𝒫^K × 𝒫^K` if and only if `L_k > 1` for
every `k`.

Differences of form with the paper: arms are a finite type `α` with `2 ≤ Fintype.card α` (the
paper's `K ≥ 2`); `L : α → ℝ` with `∀ a, 0 < L a`; `𝒫^K` is `unitBandits α`, `𝒫_L` is
`meanBand L`, and `L ≥ 𝟏_K` is `∀ a, 1 ≤ L a`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Incognita.TransferBandits

namespace Incognita.Statements.P003

/-- [INC-P003, prop:drift (d)] `𝒫_L` is every pair iff `L ≥ 1`; `Drift_L` holds for every pair iff
`L > 1`. -/
theorem drift_all_pairs {α : Type*} [Fintype α] [MeasurableSpace α]
    (hK : 2 ≤ Fintype.card α) {L : α → ℝ} (hL : ∀ a, 0 < L a) :
    (meanBand L = unitBandits α ×ˢ unitBandits α ↔ ∀ a, 1 ≤ L a) ∧
      ((∀ ν ν' : Kernel α ℝ, ν ∈ unitBandits α → ν' ∈ unitBandits α → DriftBound L ν ν') ↔
        ∀ a, 1 < L a) := by
  sorry

end Incognita.Statements.P003
