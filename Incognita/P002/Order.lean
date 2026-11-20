/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.LawDriftMean

/-! # P002: the ordering of the constants

Proofs of [INC-P002, prop:order (a)] (`order_mean`), from
`Incognita.TransferBandits.ofReal_driftConstant_meanClass` (the programme of the mean gap splits,
`J^mean(x, c) = x K_0 + c K'_0`), of [INC-P002, prop:order (b)] (`order_le_mean`) and of
[INC-P002, prop:order (c)] (`order_chain`), from
`Incognita.TransferBandits.driftConstant_le_of_ipm_le` (a larger pseudo-distance gives a smaller
constant, once `K_0 > 0`) and the order `|m(q) - m(q')| ≤ W₁ ≤ KS ≤ TV` of
[INC-P002, lem:ipm-order].

The hypotheses `K ≥ 2` (`_hK`), `|S| ≥ 2` (`_hS2`), `L > 0` (`_hL`), the source instance being
carried by `S` (`_hν'`) and `μ⋆ < x_max` (`_hmax`) are not used, nor, in `order_le_mean`, that
`𝓕` is a test class (`_h𝓕`: the mean property is enough).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Incognita.TransferBandits

open scoped ENNReal

namespace Incognita.P002

/-- [INC-P002, prop:order (a)] Under `m(ν'_a) ≤ μ⋆ + L_a`, the constant of the mean gap splits:
`D^mean_a(c) = (1 - c K'_0)_+ / K_0`. `K_0` and `K'_0` are finite as `μ⋆ - L_a < μ⋆ < x_max`
(`vecKs_ne_top`); `K ≥ 2` (`_hK`) and `|S| ≥ 2` (`_hS2`) are not used. -/
theorem order_mean
    {α : Type*} [Fintype α] [MeasurableSpace α] (_hK : 2 ≤ Fintype.card α)
    {S : Finset ℝ} (hS : ∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) (_hS2 : 2 ≤ S.card)
    (hSne : S.Nonempty) {L : α → ℝ}
    (hL : ∀ k, 0 < L k) {ν ν' : Kernel α ℝ} (hν : ν ∈ supportBandits S α)
    (hν' : ν' ∈ supportBandits S α) {a : α} (ha : (ν a)[id] < bestMean ν)
    (hmax : bestMean ν < S.max' hSne)
    (hν'a : (ν' a)[id] ≤ bestMean ν + L a) :
    ∀ c : ℝ, 0 ≤ c →
      ENNReal.ofReal (armConstant (meanClass S) L ν ν' a c) =
        (1 - ENNReal.ofReal c * vecKs S (lawVec S (ν' a)) (bestMean ν - L a)) /
          vecKs S (lawVec S (ν a)) (bestMean ν) := by
  intro c hc
  have := hν.1
  have := hν'.1
  have hr := lawVec_mem_probVecs (hν.2 a)
  have hr' := lawVec_mem_probVecs (hν'.2 a)
  have hy₁ : ((⟨S.max' hSne, S.max'_mem hSne⟩ : S) : ℝ) = S.max' hSne := rfl
  exact ofReal_driftConstant_meanClass hS hr hr' (hL a).le
    (by rw [← integral_id_eq_vecMean (hν.2 a)]; exact ha)
    (by rw [← integral_id_eq_vecMean (hν'.2 a)]; exact hν'a)
    (vecKs_ne_top hy₁ hr hmax) (vecKs_ne_top hy₁ hr' (by linarith [hL a])) hc

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
