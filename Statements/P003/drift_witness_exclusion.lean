/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.Consistency

/-! # P003, prop:drift (e): a witness and an exclusion for the drift conditions

[INC-P003, Proposition (prop:drift), item (e)]. Let `L ∈ (0,∞)^K`. Every pair with `ν' = ν`
satisfies the three conditions (`Drift_L`, the two-sided strict condition, `𝒫_L`); the pair with
`ν_k = δ_1` and `ν'_k = δ_0` for every `k` is in `𝒫_{𝟏_K}` and does not satisfy `Drift_{𝟏_K}`.

Differences of form with the paper: arms are a finite type `α` with `2 ≤ Fintype.card α` (the
paper's `K ≥ 2`); `L : α → ℝ` with `∀ a, 0 < L a`; pairs with `ν' = ν` are taken in `𝒫^K`
(`unitBandits α`); `δ_x` is the constant kernel `Kernel.const α (Measure.dirac x)`, and `𝟏_K` is
the constant function `fun _ ↦ 1`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Incognita.TransferBandits

namespace Incognita.Statements.P003

/-- [INC-P003, prop:drift (e)] Pairs with `ν' = ν` satisfy every condition; `(δ_1, δ_0)` is in
`𝒫_𝟏` and does not satisfy `Drift_𝟏`. -/
theorem drift_witness_exclusion {α : Type*} [Fintype α] [MeasurableSpace α]
    (hK : 2 ≤ Fintype.card α) {L : α → ℝ} (hL : ∀ a, 0 < L a) :
    (∀ ν ∈ unitBandits α, DriftBound L ν ν ∧ TwoSidedDriftBound L ν ν ∧ (ν, ν) ∈ meanBand L) ∧
      (Kernel.const α (Measure.dirac (1 : ℝ)), Kernel.const α (Measure.dirac (0 : ℝ))) ∈
          meanBand (fun _ ↦ 1) ∧
        ¬ DriftBound (fun _ ↦ 1) (Kernel.const α (Measure.dirac (1 : ℝ)))
          (Kernel.const α (Measure.dirac (0 : ℝ))) := by
  sorry

end Incognita.Statements.P003
