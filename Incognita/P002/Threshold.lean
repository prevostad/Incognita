/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.LawDriftReach

/-! # P002: the threshold of `o(log T)` for the mean gap, `W₁` and total variation

Proofs of [INC-P002, prop:threshold (b)] (`threshold_mean_w1`) and
[INC-P002, prop:threshold (c)] (`threshold_tv`), from the general identities of
`Incognita.TransferBandits.LawDriftReach` with `x_max = S.max' hSne`.

The hypotheses `K ≥ 2` (`_hK`), `|S| ≥ 2` (`_hS2`), the instances being carried by `S` (`_hν`,
`_hν'`) and `μ_a < μ⋆` (`_ha`) are not used; `threshold_tv` does not use `S ⊆ [0,1]` (`_hS`),
`L > 0` (`_hL`) nor `μ⋆ < x_max` (`_hmax`) either (the identity holds for every budget, the two
sets being empty for a negative one). `threshold_mean_w1` uses only `L_a ≥ 0` and `μ⋆ ≤ x_max`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Incognita.TransferBandits

open scoped ENNReal

namespace Incognita.P002

/-- [INC-P002, prop:threshold (b)] For the mean gap and `W₁`, `ω_d(q') = min(L_a, x_max - m(q'))`
and `G^d = K'_0`. -/
theorem threshold_mean_w1
    {α : Type*} [Fintype α] [MeasurableSpace α] (_hK : 2 ≤ Fintype.card α)
    {S : Finset ℝ} (hS : ∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) (_hS2 : 2 ≤ S.card)
    (hSne : S.Nonempty) {L : α → ℝ}
    (hL : ∀ k, 0 < L k) {ν ν' : Kernel α ℝ} (_hν : ν ∈ supportBandits S α)
    (_hν' : ν' ∈ supportBandits S α) {a : α} (_ha : (ν a)[id] < bestMean ν)
    (hmax : bestMean ν < S.max' hSne) :
    (∀ q' ∈ probVecs S,
        reachGain (meanClass S) (L a) q' = min (L a) (S.max' hSne - vecMean q')) ∧
      thresholdKL (meanClass S) (L a) (lawVec S (ν' a)) (bestMean ν) =
        vecKs S (lawVec S (ν' a)) (bestMean ν - L a) ∧
      (∀ q' ∈ probVecs S,
        reachGain (w1Class S) (L a) q' = min (L a) (S.max' hSne - vecMean q')) ∧
      thresholdKL (w1Class S) (L a) (lawVec S (ν' a)) (bestMean ν) =
        vecKs S (lawVec S (ν' a)) (bestMean ν - L a) := by
  have hSb : ∀ y ∈ S, y ≤ S.max' hSne := fun y hy ↦ S.le_max' y hy
  have hmean : ∀ q' ∈ probVecs S,
      reachGain (meanClass S) (L a) q' = min (L a) (S.max' hSne - vecMean q') :=
    fun _ hq' ↦ reachGain_meanClass hSb (y₁ := ⟨_, S.max'_mem hSne⟩) rfl (hL a).le hq'
  have hw1 : ∀ q' ∈ probVecs S,
      reachGain (w1Class S) (L a) q' = min (L a) (S.max' hSne - vecMean q') :=
    fun _ hq' ↦ reachGain_w1Class hS hSb (y₁ := ⟨_, S.max'_mem hSne⟩) rfl (hL a).le hq'
  exact ⟨hmean, thresholdKL_eq_vecKs hmax.le hmean _, hw1, thresholdKL_eq_vecKs hmax.le hw1 _⟩

/-- [INC-P002, prop:threshold (c)] For total variation, `ω_TV(q')` is the largest gain of mean of a
mass at most `L_a` taken under `q'` and moved to `x_max`. -/
theorem threshold_tv
    {α : Type*} [Fintype α] [MeasurableSpace α] (_hK : 2 ≤ Fintype.card α)
    {S : Finset ℝ} (_hS : ∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) (_hS2 : 2 ≤ S.card)
    (hSne : S.Nonempty) {L : α → ℝ}
    (_hL : ∀ k, 0 < L k) {ν ν' : Kernel α ℝ} (_hν : ν ∈ supportBandits S α)
    (_hν' : ν' ∈ supportBandits S α) {a : α} (_ha : (ν a)[id] < bestMean ν)
    (_hmax : bestMean ν < S.max' hSne) :
    ∀ q' ∈ probVecs S, reachGain (tvClass S) (L a) q' =
      sSup {m | ∃ w : S → ℝ, (∀ y, 0 ≤ w y ∧ w y ≤ q' y) ∧ ∑ y, w y ≤ L a ∧
        m = ∑ y, w y * (S.max' hSne - y)} :=
  fun _ hq' ↦ reachGain_tvClass (fun y hy ↦ S.le_max' y hy) (y₁ := ⟨_, S.max'_mem hSne⟩) rfl hq'

end Incognita.P002
