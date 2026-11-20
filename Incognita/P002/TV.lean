/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.LawDriftTV

/-! # P002: the total variation between the projections

Proof of [INC-P002, prop:tv (a)] (`tv_projections`): when `K'_0 > 0`,
`TV(Q⋆, Q'⋆) ≥ L_a / (x_max - x_min)`, with equality only if `Q⋆` and `Q'⋆` agree strictly inside
`(x_min, x_max)`. From `Incognita.TransferBandits.vecMean_eq_of_isKLProj` (`m(Q'⋆) = μ⋆ - L_a`, so
`m(Q⋆) - m(Q'⋆) ≥ L_a`) and `vecMean_sub_le_mul_ipm_tvClass` with its equality case.

The hypotheses `K ≥ 2` (`_hK`), `S ⊆ [0,1]` (`_hS`), the target instance being carried by `S`
(`_hν`) and `μ_a < μ⋆` (`_ha`) are not used.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Incognita.TransferBandits

open scoped ENNReal

namespace Incognita.P002

/-- [INC-P002, prop:tv (a)] If `K'_0 > 0`, then `L_a / (x_max - x_min) ≤ TV(Q⋆, Q'⋆)`, and equality
forces `Q⋆(y) = Q'⋆(y)` at every `y` of `S` other than `x_min` and `x_max`. -/
theorem tv_projections
    {α : Type*} [Fintype α] [MeasurableSpace α] (_hK : 2 ≤ Fintype.card α)
    {S : Finset ℝ} (_hS : ∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) (hS2 : 2 ≤ S.card)
    (hSne : S.Nonempty) {L : α → ℝ}
    (hL : ∀ k, 0 < L k) {ν ν' : Kernel α ℝ} (_hν : ν ∈ supportBandits S α)
    (hν' : ν' ∈ supportBandits S α) {a : α} (_ha : (ν a)[id] < bestMean ν)
    (hmax : bestMean ν < S.max' hSne)
    (hK'0 : 0 < vecKs S (lawVec S (ν' a)) (bestMean ν - L a)) :
    ∀ Q Q' : S → ℝ, IsKLProj (lawVec S (ν a)) (bestMean ν) Q →
      IsKLProj (lawVec S (ν' a)) (bestMean ν - L a) Q' →
      L a / (S.max' hSne - S.min' hSne) ≤ ipm (tvClass S) Q Q' ∧
        (ipm (tvClass S) Q Q' = L a / (S.max' hSne - S.min' hSne) →
          ∀ y : S, (y : ℝ) ≠ S.min' hSne → (y : ℝ) ≠ S.max' hSne → Q y = Q' y) := by
  intro Q Q' hQ hQ'
  have := hν'.1
  have hr' := lawVec_mem_probVecs (hν'.2 a)
  have hy₁ : ((⟨S.max' hSne, S.max'_mem hSne⟩ : S) : ℝ) = S.max' hSne := rfl
  have hm' := vecMean_eq_of_isKLProj hr' hQ' hK'0
    (vecKs_ne_top hy₁ hr' (by linarith [hL a]))
  have hSI : ∀ y ∈ S, y ∈ Set.Icc (S.min' hSne) (S.max' hSne) :=
    fun y hy ↦ ⟨S.min'_le y hy, S.le_max' y hy⟩
  have hw : 0 < S.max' hSne - S.min' hSne := sub_pos.2 (S.min'_lt_max'_of_card (by omega))
  have hgap : L a ≤ vecMean Q - vecMean Q' := by rw [hm']; linarith [hQ.2.1]
  have hle := vecMean_sub_le_mul_ipm_tvClass hSI hQ.1 hQ'.1
  refine ⟨(div_le_iff₀ hw).2 (by rw [mul_comm]; linarith), fun heq y hy₀ hy₁ ↦ ?_⟩
  have hTV : (S.max' hSne - S.min' hSne) * ipm (tvClass S) Q Q' = L a := by
    rw [heq]
    field_simp
  exact eq_of_vecMean_sub_eq_mul_ipm_tvClass hSI hQ.1 hQ'.1 (le_antisymm hle (by linarith))
    hy₀ hy₁

end Incognita.P002
