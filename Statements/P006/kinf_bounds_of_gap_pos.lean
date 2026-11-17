/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.Instances
public import LMLExplore.Bandits.LaiRobbins

/-! # P006, `prop:kinf`(v): `0 < 2 Δ_a² ≤ K_a ≤ log ((1 - m_a) / (1 - m⋆)) < ∞` on `𝒫`

One frozen statement of the paper P006 (`papers/P006-batched-setting`); its
docstring gives the statement in words and every difference of form with the paper. -/

@[expose] public section

/-- [INC-P006, Proposition `prop:kinf`(v)] For every `ν ∈ 𝒫` and every suboptimal arm `a`,
`0 < 2 Δ_a² ≤ K_a ≤ log ((1 - m_a) / (1 - m⋆)) < ∞`, where `K_a = 𝒦_inf(ν_a, m⋆)`.

Differences of form with the paper:
* The arms are a finite type `α` (`Finite α`) with the discrete σ-algebra
  (`MeasurableSingletonClass α`), the paper's convention [INC-P006, Definition `def:instance`].
  The convention `K ≥ 2` is not added: a suboptimal arm exists only if `K ≥ 2`.
* An instance is a kernel `ν : Kernel α ℝ`, and `𝒫` is `unitBandits α`;
  `m_a = ∫ x, id x ∂(ν a)`, `m⋆ = ⨆ b, ∫ x, id x ∂(ν b)`, `Δ_a = gap ν a = m⋆ - m_a` (LML's
  `gap`), and "suboptimal" is `0 < gap ν a`.
* `𝓜` is `unitLaws` (probability measures on `ℝ` with `∀ᵐ x, x ∈ [0, 1]`, the paper's
  `Q([0, 1]) = 1`); the mean `m(Q)` is the Bochner integral `∫ x, id x ∂Q`; `𝒦_inf(P, μ)` is
  LMLExplore's `dInf unitLaws P μ = ⨅ Q ∈ {Q ∈ unitLaws | μ < Q[id]}, klDiv P Q` in `ℝ≥0∞`
  (Mathlib's `klDiv`, with `inf ∅ = ∞`), which is the paper's primal definition [INC-P006,
  Definition `def:kinf`]. So `K_a` is `dInf unitLaws (ν a) m⋆`.
* The real numbers in the bounds (all `≥ 0` under the hypotheses) are compared with `𝒦_inf`
  through `ENNReal.ofReal`. The paper's `log (…) < ∞` is recorded as the finiteness it gives,
  `K_a ≠ ∞`. -/
theorem Incognita.Statements.P006.kinf_bounds_of_gap_pos {α : Type*} [Finite α]
    [MeasurableSpace α] [MeasurableSingletonClass α] {ν : ProbabilityTheory.Kernel α ℝ}
    (hν : ν ∈ Incognita.BatchedBandits.unitBandits α) {a : α} (ha : 0 < Bandits.gap ν a) :
    0 < ENNReal.ofReal (2 * Bandits.gap ν a ^ 2) ∧
      ENNReal.ofReal (2 * Bandits.gap ν a ^ 2) ≤
        LMLExplore.Bandits.dInf Incognita.BatchedBandits.unitLaws (ν a)
          (⨆ b, ∫ x, id x ∂(ν b)) ∧
      LMLExplore.Bandits.dInf Incognita.BatchedBandits.unitLaws (ν a)
          (⨆ b, ∫ x, id x ∂(ν b)) ≤
        ENNReal.ofReal
          (Real.log ((1 - ∫ x, id x ∂(ν a)) / (1 - ⨆ b, ∫ x, id x ∂(ν b)))) ∧
      LMLExplore.Bandits.dInf Incognita.BatchedBandits.unitLaws (ν a)
          (⨆ b, ∫ x, id x ∂(ν b)) ≠ ⊤ := by
  sorry
