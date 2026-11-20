/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.LawDriftMean

/-! # P002: when the source helps the mean gap

Proof of [INC-P002, prop:criteria (b)] for the mean gap (`criteria_source_helps_mean`), from
`Incognita.TransferBandits.ofReal_driftConstant_meanClass_lt_iff`: `D^mean_a(c) < 1/K_0` if and
only if `L_a < |m(ν'_a) - μ⋆|`, for `c > 0`.

The hypotheses `K ≥ 2` (`_hK`) and `|S| ≥ 2` (`_hS2`) are not used.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Incognita.TransferBandits

open scoped ENNReal

namespace Incognita.P002

/-- [INC-P002, prop:criteria (b), second sentence] For the mean gap and `c > 0`,
`D^mean_a(c) < 1/K_0` if and only if `L_a < |m(ν'_a) - μ⋆|`, and, when `m(ν'_a) ≤ μ⋆ + L_a`, if and
only if `m(ν'_a) < μ⋆ - L_a`. -/
theorem criteria_source_helps_mean
    {α : Type*} [Fintype α] [MeasurableSpace α] (_hK : 2 ≤ Fintype.card α)
    {S : Finset ℝ} (hS : ∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) (_hS2 : 2 ≤ S.card)
    (hSne : S.Nonempty) {L : α → ℝ}
    (hL : ∀ k, 0 < L k) {ν ν' : Kernel α ℝ} (hν : ν ∈ supportBandits S α)
    (hν' : ν' ∈ supportBandits S α) {a : α} (ha : (ν a)[id] < bestMean ν)
    (hmax : bestMean ν < S.max' hSne) {c : ℝ} (hc : 0 < c) :
    (ENNReal.ofReal (armConstant (meanClass S) L ν ν' a c) <
        (vecKs S (lawVec S (ν a)) (bestMean ν))⁻¹ ↔ L a < |(ν' a)[id] - bestMean ν|) ∧
      ((ν' a)[id] ≤ bestMean ν + L a →
        (ENNReal.ofReal (armConstant (meanClass S) L ν ν' a c) <
          (vecKs S (lawVec S (ν a)) (bestMean ν))⁻¹ ↔ (ν' a)[id] < bestMean ν - L a)) := by
  have := hν.1
  have := hν'.1
  have hr := lawVec_mem_probVecs (hν.2 a)
  have hr' := lawVec_mem_probVecs (hν'.2 a)
  have hy₁ : ((⟨S.max' hSne, S.max'_mem hSne⟩ : S) : ℝ) = S.max' hSne := rfl
  have h1 := ofReal_driftConstant_meanClass_lt_iff hS hr hr' (hL a).le
    (by rw [← integral_id_eq_vecMean (hν.2 a)]; exact ha) (vecKs_ne_top hy₁ hr hmax)
    (vecKs_ne_top hy₁ hr' (by linarith [hL a])) hc
  rw [← integral_id_eq_vecMean (hν'.2 a)] at h1
  refine ⟨h1, fun h ↦ h1.trans ?_⟩
  rw [lt_abs]
  constructor
  · rintro (h' | h') <;> linarith
  · intro h'
    right
    linarith

end Incognita.P002
