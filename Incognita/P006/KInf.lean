/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.KInf

/-! # P006, `prop:kinf`: `𝒦_inf` on the laws on `[0, 1]`

Proofs of the five frozen statements of [INC-P006, Proposition `prop:kinf`], each with exactly the
type of `Incognita.Statements.P006.<name>`. Each is a specialisation of a lemma of
`Incognita.BatchedBandits.KInf`, stated there for `dInf unitLaws P μ` and a law `P` on `[0, 1]`.

* (i) `kinf_eq_top_of_one_le`; (ii) `kinf_eq_zero_of_lt_mean`; (iii) `kinf_bounds`;
* (iv) `kinf_bernoulli`; (v) `kinf_bounds_of_gap_pos`.

The hypothesis `P ∈ 𝓜` of (i) and the instance `[MeasurableSingletonClass α]` of (v) are not used:
these theorems are marked `nolint unusedArguments`, their signature being fixed by the frozen
statement.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory LMLExplore LMLExplore.Bandits

namespace Incognita.P006

open Incognita.BatchedBandits

/-- [INC-P006, Proposition `prop:kinf`(i)] `𝒦_inf(P, μ) = ∞` for `μ ≥ 1`. The hypothesis
`P ∈ 𝓜` is not used. -/
@[nolint unusedArguments]
theorem kinf_eq_top_of_one_le {P : MeasureTheory.Measure ℝ}
    (_hP : P ∈ Incognita.BatchedBandits.unitLaws) {μ : ℝ} (hμ : 1 ≤ μ) :
    LMLExplore.Bandits.dInf Incognita.BatchedBandits.unitLaws P μ = ⊤ :=
  dInf_unitLaws_eq_top_of_one_le P hμ

/-- [INC-P006, Proposition `prop:kinf`(ii)] `𝒦_inf(P, μ) = 0` for `μ < m(P)`. -/
theorem kinf_eq_zero_of_lt_mean {P : MeasureTheory.Measure ℝ}
    (hP : P ∈ Incognita.BatchedBandits.unitLaws) {μ : ℝ} (hμ : μ < ∫ x, id x ∂P) :
    LMLExplore.Bandits.dInf Incognita.BatchedBandits.unitLaws P μ = 0 :=
  dInf_unitLaws_eq_zero_of_lt_integral hP hμ

/-- [INC-P006, Proposition `prop:kinf`(iii)] For `p = m(P) ≤ μ < 1`,
`2 (μ - p)² ≤ kl(p, μ) ≤ 𝒦_inf(P, μ) ≤ log ((1 - p) / (1 - μ))`, and `𝒦_inf(P, μ) < ∞`. -/
theorem kinf_bounds {P : MeasureTheory.Measure ℝ}
    (hP : P ∈ Incognita.BatchedBandits.unitLaws) {μ : ℝ} (hpμ : ∫ x, id x ∂P ≤ μ) (hμ : μ < 1) :
    ENNReal.ofReal (2 * (μ - ∫ x, id x ∂P) ^ 2) ≤ LMLExplore.klBer (∫ x, id x ∂P) μ ∧
      LMLExplore.klBer (∫ x, id x ∂P) μ ≤
        LMLExplore.Bandits.dInf Incognita.BatchedBandits.unitLaws P μ ∧
      LMLExplore.Bandits.dInf Incognita.BatchedBandits.unitLaws P μ ≤
        ENNReal.ofReal (Real.log ((1 - ∫ x, id x ∂P) / (1 - μ))) ∧
      LMLExplore.Bandits.dInf Incognita.BatchedBandits.unitLaws P μ ≠ ⊤ := by
  have hp := integral_id_mem_Icc_of_mem_unitLaws hP
  have hup := dInf_unitLaws_le_ofReal_log hP hpμ hμ
  refine ⟨?_, klBer_le_dInf_unitLaws hP hpμ, hup, ne_top_of_le_ne_top ENNReal.ofReal_ne_top hup⟩
  rw [show (μ - ∫ x, id x ∂P) ^ 2 = (∫ x, id x ∂P - μ) ^ 2 by ring]
  exact ofReal_two_mul_sq_le_klBer hp ⟨hp.1.trans hpμ, hμ.le⟩

/-- [INC-P006, Proposition `prop:kinf`(iv)] `𝒦_inf(Ber(p), μ) = kl(p, μ)` for `p ≤ μ < 1`. -/
theorem kinf_bernoulli {p : unitInterval} {μ : ℝ}
    (hpμ : (p : ℝ) ≤ μ) (hμ : μ < 1) :
    LMLExplore.Bandits.dInf Incognita.BatchedBandits.unitLaws
        (ProbabilityTheory.bernoulliMeasure (1 : ℝ) 0 p) μ = LMLExplore.klBer p μ :=
  dInf_unitLaws_bernoulliMeasure hpμ hμ

/-- [INC-P006, Proposition `prop:kinf`(v)] For `ν ∈ 𝒫` and a suboptimal arm `a`,
`0 < 2 Δ_a² ≤ K_a ≤ log ((1 - m_a) / (1 - m⋆))` and `K_a < ∞`: item (iii) at `μ = m⋆`, since
`m_a ≤ m⋆ < 1`. The instance `[MeasurableSingletonClass α]` is not used. -/
@[nolint unusedArguments]
theorem kinf_bounds_of_gap_pos {α : Type*} [Finite α]
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
  have hle : ∫ x, id x ∂(ν a) ≤ ⨆ b, ∫ x, id x ∂(ν b) :=
    le_ciSup (Finite.bddAbove_range fun b ↦ ∫ x, id x ∂(ν b)) a
  obtain ⟨h1, h2, h3, h4⟩ := kinf_bounds (hν.1 a) hle hν.2
  exact ⟨ENNReal.ofReal_pos.2 (by positivity), h1.trans h2, h3, h4⟩

end Incognita.P006
