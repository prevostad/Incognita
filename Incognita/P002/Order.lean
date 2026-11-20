/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.LawDriftOrder

/-! # P002: the ordering of the constants

Proofs of [INC-P002, prop:order (b)] (`order_le_mean`) and [INC-P002, prop:order (c)]
(`order_chain`), from `Incognita.TransferBandits.driftConstant_le_of_ipm_le` (a larger
pseudo-distance gives a smaller constant, once `K_0 > 0`) and the order
`|m(q) - m(q')| ≤ W₁ ≤ KS ≤ TV` of [INC-P002, lem:ipm-order].

The hypotheses `K ≥ 2` (`_hK`), `|S| ≥ 2` (`_hS2`), `L > 0` (`_hL`), the source instance being
carried by `S` (`_hν'`) and `μ⋆ < x_max` (`_hmax`) are not used, nor, in `order_le_mean`, that
`𝓕` is a test class (`_h𝓕`: the mean property is enough).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Incognita.TransferBandits

open scoped ENNReal

namespace Incognita.P002

/-- [INC-P002, prop:order (b)] For every `d` with the mean property, `D^d_a(c) ≤ D^mean_a(c)`. -/
theorem order_le_mean
    {α : Type*} [Fintype α] [MeasurableSpace α] (_hK : 2 ≤ Fintype.card α)
    {S : Finset ℝ} (hS : ∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) (_hS2 : 2 ≤ S.card)
    (hSne : S.Nonempty) {L : α → ℝ}
    (_hL : ∀ k, 0 < L k) {ν ν' : Kernel α ℝ} (hν : ν ∈ supportBandits S α)
    (_hν' : ν' ∈ supportBandits S α) {a : α} (ha : (ν a)[id] < bestMean ν)
    (_hmax : bestMean ν < S.max' hSne)
    {𝓕 : Set (S → ℝ)} (_h𝓕 : IsTestClass 𝓕) (hM : HasMeanProperty 𝓕) :
    ∀ c : ℝ, 0 ≤ c → armConstant (𝓕) L ν ν' a c ≤ armConstant (meanClass S) L ν ν' a c :=
  fun _ _ ↦ driftConstant_le_of_ipm_le
    (fun q hq q' hq' ↦ (ipm_meanClass q q').trans_le (hM q hq q' hq'))
    (vecKs_lawVec_pos hS hν ha)

/-- [INC-P002, prop:order (c)] `D^TV_a(c) ≤ D^KS_a(c) ≤ D^W₁_a(c) ≤ D^mean_a(c)`. -/
theorem order_chain
    {α : Type*} [Fintype α] [MeasurableSpace α] (_hK : 2 ≤ Fintype.card α)
    {S : Finset ℝ} (hS : ∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) (_hS2 : 2 ≤ S.card)
    (hSne : S.Nonempty) {L : α → ℝ}
    (_hL : ∀ k, 0 < L k) {ν ν' : Kernel α ℝ} (hν : ν ∈ supportBandits S α)
    (_hν' : ν' ∈ supportBandits S α) {a : α} (ha : (ν a)[id] < bestMean ν)
    (_hmax : bestMean ν < S.max' hSne) :
    ∀ c : ℝ, 0 ≤ c →
      armConstant (tvClass S) L ν ν' a c ≤ armConstant (ksClass S) L ν ν' a c ∧
        armConstant (ksClass S) L ν ν' a c ≤ armConstant (w1Class S) L ν ν' a c ∧
        armConstant (w1Class S) L ν ν' a c ≤ armConstant (meanClass S) L ν ν' a c := by
  have hK0 := vecKs_lawVec_pos hS hν ha
  exact fun _ _ ↦
    ⟨driftConstant_le_of_ipm_le (fun q _ q' _ ↦ ipm_ksClass_le_ipm_tvClass q q') hK0,
      driftConstant_le_of_ipm_le (fun q hq q' hq' ↦ ipm_w1Class_le_ipm_ksClass hS hq hq') hK0,
      driftConstant_le_of_ipm_le (fun q _ q' _ ↦
        (ipm_meanClass q q').trans_le (abs_vecMean_sub_le_ipm_w1Class hS q q')) hK0⟩

end Incognita.P002
