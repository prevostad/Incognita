/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.LawDriftMean

/-! # The total variation between the two projections

The tools of [INC-P002, prop:tv (a)]: when `K'_0 > 0` the projection `Q'⋆` has mean exactly
`μ⋆ - L_a`, so the projections are `L_a` apart in mean, and the total variation is at least the mean
gap divided by the width `x_max - x_min` of the support, with equality only if the two laws agree
strictly inside `(x_min, x_max)`.

## Main statements

* `vecMean_eq_of_isKLProj`: a projection `Q` of `ρ` at a level `ℓ` with `0 < K_S(ρ, ℓ) < ∞` has
  mean exactly `ℓ` (part of [INC-P002, lem:projection]).
* `vecMean_sub_le_mul_ipm_tvClass`: `m(q) - m(q') ≤ (b₁ - b₀) TV(q, q')` on `S ⊆ [b₀, b₁]`.
* `eq_of_vecMean_sub_eq_mul_ipm_tvClass`: in case of equality, `q(y) = q'(y)` for `y ∈ (b₀, b₁)`.
-/

@[expose] public section

open scoped ENNReal

namespace Incognita.TransferBandits

variable {S : Finset ℝ}

/-- A projection at a binding level sits on the level (part of [INC-P002, lem:projection]): if
`Q` minimises `KL(ρ, ·)` on `{q ∈ 𝒫_S : m(q) ≥ ℓ}` and `0 < K_S(ρ, ℓ) < ∞`, then `m(Q) = ℓ`.
Otherwise `m(ρ) < ℓ < m(Q)`, and the mixture of `Q` and `ρ` of mean `ℓ` has divergence at most
`(1 - s) KL(ρ, Q)` with `s > 0` (`vecKL_mix_le_mul`), less than the minimum. -/
lemma vecMean_eq_of_isKLProj {ρ Q : S → ℝ} (hρ : ρ ∈ probVecs S) {ℓ : ℝ}
    (hQ : IsKLProj ρ ℓ Q) (hpos : 0 < vecKs S ρ ℓ) (hfin : vecKs S ρ ℓ ≠ ∞) :
    vecMean Q = ℓ := by
  refine le_antisymm (not_lt.1 fun hlt ↦ ?_) hQ.2.1
  have hρℓ : vecMean ρ < ℓ := not_le.1 fun hle ↦ hpos.ne' (vecKs_eq_zero hρ hle)
  have h : vecMean ρ < vecMean Q := hρℓ.trans hlt
  have hd : 0 < vecMean Q - vecMean ρ := sub_pos.2 h
  set s := (vecMean Q - ℓ) / (vecMean Q - vecMean ρ) with hs_def
  have hs0 : 0 < s := div_pos (by linarith) hd
  have hs1 : s ≤ 1 := (div_le_one hd).2 (by linarith)
  have hmix := smul_add_smul_mem_probVecs hQ.1 hρ hs0.le hs1
  have hle := (hQ.2.2 _ hmix (vecMean_mix_eq h ℓ).ge).trans (vecKL_mix_le_mul ρ Q hs0.le hs1)
  rw [← vecKs_eq_of_isKLProj hQ, ← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul (by linarith),
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by linarith) ENNReal.toReal_nonneg)] at hle
  have hk : 0 < (vecKs S ρ ℓ).toReal := ENNReal.toReal_pos hpos.ne' hfin
  nlinarith

/-- The gap of means against the total variation, as a sum of nonnegative terms: on
`S ⊆ [b₀, b₁]`, `(b₁ - b₀) TV(q, q') - (m(q) - m(q')) = ∑_y ((b₁ - y) (q - q')_+(y) +
(y - b₀) (q' - q)_+(y))` for probability vectors. -/
lemma mul_ipm_tvClass_sub_vecMean_sub {q q' : S → ℝ} (hq : q ∈ probVecs S)
    (hq' : q' ∈ probVecs S) (b₀ b₁ : ℝ) :
    (b₁ - b₀) * ipm (tvClass S) q q' - (vecMean q - vecMean q') =
      ∑ y : S, ((b₁ - y) * max (q y - q' y) 0 + (y - b₀) * max (q' y - q y) 0) := by
  have hmass : ∑ y, q y = ∑ y, q' y := hq.2.trans hq'.2.symm
  have hTV := ipm_tvClass hmass
  have hTV' := ipm_tvClass hmass.symm
  have hsymm : ipm (tvClass S) q' q = ipm (tvClass S) q q' := by
    simp only [ipm]
    refine iSup_congr fun f ↦ ?_
    rw [← abs_neg, ← Finset.sum_neg_distrib]
    exact congrArg _ (Finset.sum_congr rfl fun y _ ↦ by ring)
  have hpart : ∀ y : S, q y - q' y = max (q y - q' y) 0 - max (q' y - q y) 0 := fun y ↦ by
    rcases le_total 0 (q y - q' y) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have e1 : vecMean q - vecMean q' =
      ∑ y : S, (y : ℝ) * max (q y - q' y) 0 - ∑ y : S, (y : ℝ) * max (q' y - q y) 0 := by
    rw [vecMean_sub, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ ↦ by rw [← mul_sub, ← hpart y]
  have e2 : (b₁ - b₀) * ipm (tvClass S) q q' =
      b₁ * ∑ y, max (q y - q' y) 0 - b₀ * ∑ y, max (q' y - q y) 0 := by
    rw [← hTV, ← hTV', hsymm]
    ring
  rw [e1, e2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun y _ ↦ by ring

/-- On `S ⊆ [b₀, b₁]`, `m(q) - m(q') ≤ (b₁ - b₀) TV(q, q')` for probability vectors
[INC-P002, prop:tv (a), proof]: the mass `TV(q, q')` that moves goes up by at most `b₁ - b₀`. -/
lemma vecMean_sub_le_mul_ipm_tvClass {b₀ b₁ : ℝ} (hS : ∀ y ∈ S, y ∈ Set.Icc b₀ b₁)
    {q q' : S → ℝ} (hq : q ∈ probVecs S) (hq' : q' ∈ probVecs S) :
    vecMean q - vecMean q' ≤ (b₁ - b₀) * ipm (tvClass S) q q' := by
  have := mul_ipm_tvClass_sub_vecMean_sub hq hq' b₀ b₁
  have hnn : 0 ≤ ∑ y : S, ((b₁ - y) * max (q y - q' y) 0 + (y - b₀) * max (q' y - q y) 0) :=
    Finset.sum_nonneg fun y _ ↦ add_nonneg
      (mul_nonneg (by linarith [(hS y y.2).2]) (le_max_right _ _))
      (mul_nonneg (by linarith [(hS y y.2).1]) (le_max_right _ _))
  linarith

/-- The equality case of `vecMean_sub_le_mul_ipm_tvClass` [INC-P002, prop:tv (a), proof]: if
`m(q) - m(q') = (b₁ - b₀) TV(q, q')` on `S ⊆ [b₀, b₁]`, then `q(y) = q'(y)` at every `y` strictly
between `b₀` and `b₁`: each nonnegative term of `mul_ipm_tvClass_sub_vecMean_sub` vanishes. -/
lemma eq_of_vecMean_sub_eq_mul_ipm_tvClass {b₀ b₁ : ℝ} (hS : ∀ y ∈ S, y ∈ Set.Icc b₀ b₁)
    {q q' : S → ℝ} (hq : q ∈ probVecs S) (hq' : q' ∈ probVecs S)
    (heq : vecMean q - vecMean q' = (b₁ - b₀) * ipm (tvClass S) q q') {y : S}
    (hy₀ : (y : ℝ) ≠ b₀) (hy₁ : (y : ℝ) ≠ b₁) : q y = q' y := by
  have h := mul_ipm_tvClass_sub_vecMean_sub hq hq' b₀ b₁
  rw [← heq, sub_self, eq_comm,
    Finset.sum_eq_zero_iff_of_nonneg fun z _ ↦ add_nonneg
      (mul_nonneg (by linarith [(hS z z.2).2]) (le_max_right _ _))
      (mul_nonneg (by linarith [(hS z z.2).1]) (le_max_right _ _))] at h
  have hz := h y (Finset.mem_univ y)
  have h1 : 0 < b₁ - y := sub_pos.2 (lt_of_le_of_ne (hS y y.2).2 hy₁)
  have h0 : 0 < (y : ℝ) - b₀ := sub_pos.2 (lt_of_le_of_ne (hS y y.2).1 (Ne.symm hy₀))
  obtain ⟨hP, hN⟩ := (add_eq_zero_iff_of_nonneg (mul_nonneg h1.le (le_max_right _ _))
    (mul_nonneg h0.le (le_max_right _ _))).1 hz
  rw [mul_eq_zero, or_iff_right h1.ne'] at hP
  rw [mul_eq_zero, or_iff_right h0.ne'] at hN
  have := le_max_left (q y - q' y) 0
  have := le_max_left (q' y - q y) 0
  linarith

end Incognita.TransferBandits
