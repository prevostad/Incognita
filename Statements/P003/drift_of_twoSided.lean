/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.Consistency

/-! # P003, prop:drift (a): the two-sided strict condition implies the other two

[INC-P003, Proposition (prop:drift), item (a)]. Let `L ∈ (0,∞)^K`. For a pair `(ν, ν')` of
instances on `[0,1]`, the two-sided strict condition `|μ_k - μ'_k| < L_k` (for every `k`) implies
`Drift_L` and `(ν, ν') ∈ 𝒫_L`.

Differences of form with the paper: arms are a finite type `α` with `2 ≤ Fintype.card α` (the
paper's `K ≥ 2`); `L : α → ℝ` with `∀ a, 0 < L a`; the instances `𝒫^K` are `unitBandits α`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Incognita.TransferBandits

namespace Incognita.Statements.P003

/-- [INC-P003, prop:drift (a)] The two-sided strict drift condition implies `Drift_L` and
membership in `𝒫_L`. -/
theorem drift_of_twoSided {α : Type*} [Fintype α] [MeasurableSpace α]
    (hK : 2 ≤ Fintype.card α) {L : α → ℝ} (hL : ∀ a, 0 < L a)
    {ν ν' : Kernel α ℝ} (hν : ν ∈ unitBandits α) (hν' : ν' ∈ unitBandits α)
    (h : TwoSidedDriftBound L ν ν') :
    DriftBound L ν ν' ∧ (ν, ν') ∈ meanBand L := by
  sorry

end Incognita.Statements.P003
