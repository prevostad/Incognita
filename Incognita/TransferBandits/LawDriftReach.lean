/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.LawDriftChecks
public import TauCeti.Algebra.Order.BigOperators.Sum.PosPart

/-! # The reach `ω_d` and the threshold `G^d` for the mean gap, `W₁` and total variation

The largest increase of the mean allowed by a drift bound `l`,
`ω_d(q') = max {m(q) - m(q') : q ∈ 𝒫_S, d(q, q') ≤ l}` (`reachGain`), and the threshold divergence
`G^d` (`thresholdKL`) of [INC-P002, prop:threshold], computed for three of the pseudo-distances of
[INC-P002, def:ipm].

## Main statements

* `reachGain_eq_min`: `ω_d(q') = min (l, x_max - m(q'))` for every `d_𝓕` that dominates the
  increase of the mean and moves the mixture `(1 - t) q' + t δ_{x_max}` by at most
  `t (x_max - m(q'))`.
* `reachGain_w1Class`: the same identity for `W₁` (the mean gap is `reachGain_meanClass`).
* `thresholdKL_eq_vecKs`: when `ω_d(q') = min (l, x_max - m(q'))` and `μ ≤ x_max`,
  `G^d = K_S(ν'_a, μ - l)`.
* `reachGain_tvClass`: `ω_TV(q') = sup {∑_y w(y) (x_max - y) : 0 ≤ w ≤ q', ∑_y w(y) ≤ l}`.

The point `x_max` is a real `b` with `S ⊆ (-∞, b]`, attained at a point `y₁` of `S`.
-/

@[expose] public section

namespace Incognita.TransferBandits

variable {S : Finset ℝ}

/-- The mixture `(1 - t) q' + t δ_{y₁}` of a probability vector and a Dirac vector, `t ∈ [0,1]`, is
a probability vector. -/
lemma mix_single_mem_probVecs {q' : S → ℝ} (hq' : q' ∈ probVecs S) (y₁ : S) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : (1 - t) • q' + t • Pi.single y₁ 1 ∈ probVecs S := by
  refine ⟨fun y ↦ ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    have := hq'.1 y
    split_ifs <;> nlinarith
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hq'.2, Fintype.sum_pi_single']
    ring

/-- `ω_d(q') = min (l, x_max - m(q'))` for a pseudo-distance `d_𝓕` that dominates the increase of
the mean, `m(q) - m(q') ≤ d(q, q')`, and moves the mixture `(1 - t) q' + t δ_{x_max}` by at most
`t (x_max - m(q'))` [INC-P002, prop:threshold (b), proof]: the mean cannot move by more than `l`,
nor above `x_max`, and the mixture with `t (x_max - m(q')) = min (l, x_max - m(q'))` reaches the
bound. -/
lemma reachGain_eq_min {b : ℝ} (hS : ∀ y ∈ S, y ≤ b) {y₁ : S} (hy₁ : (y₁ : ℝ) = b)
    {𝓕 : Set (S → ℝ)} {l : ℝ} (hl : 0 ≤ l) {q' : S → ℝ} (hq' : q' ∈ probVecs S)
    (hmean : ∀ q ∈ probVecs S, vecMean q - vecMean q' ≤ ipm 𝓕 q q')
    (hmix : ∀ t, 0 ≤ t → t ≤ 1 →
      ipm 𝓕 ((1 - t) • q' + t • Pi.single y₁ 1) q' ≤ t * (b - vecMean q')) :
    reachGain 𝓕 l q' = min l (b - vecMean q') := by
  set g := min l (b - vecMean q') with hg
  have hbm : 0 ≤ b - vecMean q' := sub_nonneg.mpr (vecMean_le_of_le hS hq')
  have hg0 : 0 ≤ g := le_min hl hbm
  have hup : ∀ q ∈ probVecs S, ipm 𝓕 q q' ≤ l → vecMean q - vecMean q' ≤ g := fun q hq hd ↦
    le_min ((hmean q hq).trans hd) (by linarith [vecMean_le_of_le hS hq])
  refine le_antisymm (reachGain_le hg0 hup) ?_
  -- the mixture with `t = g / (b - m(q'))`
  set t := g / (b - vecMean q') with ht
  have ht0 : 0 ≤ t := div_nonneg hg0 hbm
  have ht1 : t ≤ 1 := div_le_one_of_le₀ (min_le_right _ _) hbm
  have htg : t * (b - vecMean q') = g := by
    rcases hbm.eq_or_lt with h | h
    · rw [← h, mul_zero, hg, ← h, min_eq_right hl]
    · exact div_mul_cancel₀ _ h.ne'
  have hqm : vecMean ((1 - t) • q' + t • Pi.single y₁ 1) - vecMean q' = g := by
    rw [vecMean_add, vecMean_smul, vecMean_smul, vecMean_single, hy₁, ← htg]
    ring
  refine le_csSup ⟨g, ?_⟩ ⟨_, mix_single_mem_probVecs hq' y₁ ht0 ht1, ?_, hqm.symm⟩
  · rintro m ⟨q, hq, hd, rfl⟩
    exact hup q hq hd
  · exact (hmix t ht0 ht1).trans (htg.trans_le (min_le_left _ _))

/-- On `S ⊆ [0,1]`, `W₁` dominates the mean gap: `y ↦ y` is a `1`-Lipschitz test function
[INC-P002, lem:ipm-order]. -/
lemma abs_vecMean_sub_le_ipm_w1Class (hS : ∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) (q q' : S → ℝ) :
    |vecMean q - vecMean q'| ≤ ipm (w1Class S) q q' := by
  rw [vecMean_sub]
  exact le_ciSup_of_le (bddAbove_ipm w1Class_isTestClass.2 q q')
    ⟨fun y ↦ (y : ℝ), fun y ↦ hS y y.2, fun _ _ ↦ le_rfl⟩ le_rfl

/-- `W₁((1 - t) q' + t δ_{x_max}, q') ≤ t (x_max - m(q'))`: for a `1`-Lipschitz `f`,
`f(x_max) - ∑_y q'(y) f(y) ≤ ∑_y q'(y) (x_max - y)` [INC-P002, prop:threshold (b), proof]. -/
lemma ipm_w1Class_mix_single_le {b : ℝ} (hS : ∀ y ∈ S, y ≤ b) {y₁ : S} (hy₁ : (y₁ : ℝ) = b)
    {q' : S → ℝ} (hq' : q' ∈ probVecs S) {t : ℝ} (ht : 0 ≤ t) :
    ipm (w1Class S) ((1 - t) • q' + t • Pi.single y₁ 1) q' ≤ t * (b - vecMean q') := by
  have : Nonempty (w1Class S) := w1Class_isTestClass.1.to_subtype
  have hb : b - vecMean q' = ∑ y, q' y * (b - y) := by
    simp only [vecMean, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hq'.2, one_mul]
  refine ciSup_le fun f ↦ ?_
  have hsum : ∑ y, (f : S → ℝ) y * (((1 - t) • q' + t • Pi.single y₁ 1 : S → ℝ) y - q' y) =
      t * ∑ y, q' y * ((f : S → ℝ) y₁ - (f : S → ℝ) y) := by
    have h1 : ∀ y, (f : S → ℝ) y * (((1 - t) • q' + t • Pi.single y₁ 1 : S → ℝ) y - q' y) =
        t * ((f : S → ℝ) y * (Pi.single y₁ 1 : S → ℝ) y) - t * (q' y * (f : S → ℝ) y) := fun y ↦ by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    simp only [h1, Finset.sum_sub_distrib, ← Finset.mul_sum, mul_sub, ← Finset.sum_mul, hq'.2,
      one_mul, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte]
  rw [hsum, abs_mul, abs_of_nonneg ht, hb]
  refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun y _ ↦ ?_)) ht
  rw [abs_mul, abs_of_nonneg (hq'.1 y)]
  refine mul_le_mul_of_nonneg_left ((f.2.2 y₁ y).trans_eq ?_) (hq'.1 y)
  rw [hy₁, abs_of_nonneg (sub_nonneg.mpr (hS y y.2))]

/-- For `W₁` on `S ⊆ [0,1]`, `ω(q') = min (l, x_max - m(q'))` [INC-P002, prop:threshold (b)]. -/
lemma reachGain_w1Class (hS : ∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) {b : ℝ} (hSb : ∀ y ∈ S, y ≤ b)
    {y₁ : S} (hy₁ : (y₁ : ℝ) = b) {l : ℝ} (hl : 0 ≤ l) {q' : S → ℝ} (hq' : q' ∈ probVecs S) :
    reachGain (w1Class S) l q' = min l (b - vecMean q') :=
  reachGain_eq_min hSb hy₁ hl hq'
    (fun q _ ↦ (le_abs_self _).trans (abs_vecMean_sub_le_ipm_w1Class hS q q'))
    fun _ ht _ ↦ ipm_w1Class_mix_single_le hSb hy₁ hq' ht

/-- When `ω_d(q') = min (l, x_max - m(q'))` for every `q' ∈ 𝒫_S` and `μ ≤ x_max`, the threshold
divergence is `G^d = K_S(r', μ - l)`: the condition `m(q') + ω_d(q') ≥ μ` reads `m(q') ≥ μ - l`
[INC-P002, prop:threshold (b), proof]. -/
lemma thresholdKL_eq_vecKs {b : ℝ} {𝓕 : Set (S → ℝ)} {l μ : ℝ} (hμ : μ ≤ b)
    (h : ∀ q' ∈ probVecs S, reachGain 𝓕 l q' = min l (b - vecMean q')) (r' : S → ℝ) :
    thresholdKL 𝓕 l r' μ = vecKs S r' (μ - l) := by
  have hset : {q' ∈ probVecs S | μ ≤ vecMean q' + reachGain 𝓕 l q'} =
      {q ∈ probVecs S | μ - l ≤ vecMean q} := by
    ext q'
    refine and_congr_right fun hq' ↦ ?_
    rw [h q' hq']
    constructor
    · intro hle
      linarith [min_le_left l (b - vecMean q')]
    · intro hle
      rcases min_cases l (b - vecMean q') with ⟨hm, -⟩ | ⟨hm, -⟩ <;> rw [hm] <;> linarith
  rw [thresholdKL, vecKs, hset]

/-- For total variation, `ω_TV(q')` is the largest gain `∑_y w(y) (x_max - y)` of a mass `w ≤ q'` of
total at most `l` moved to `x_max` [INC-P002, prop:threshold (c)]: `TV(q, q') ≤ l` means that `q` is
`q'` minus `w = (q' - q)_+` plus a mass `(q - q')_+` of the same total, and the gain of the mean is
largest when that mass sits at `x_max`. -/
lemma reachGain_tvClass {b : ℝ} (hS : ∀ y ∈ S, y ≤ b) {y₁ : S} (hy₁ : (y₁ : ℝ) = b) {l : ℝ}
    {q' : S → ℝ} (hq' : q' ∈ probVecs S) :
    reachGain (tvClass S) l q' = sSup {m | ∃ w : S → ℝ, (∀ y, 0 ≤ w y ∧ w y ≤ q' y) ∧
      ∑ y, w y ≤ l ∧ m = ∑ y, w y * (b - y)} := by
  set B := {m | ∃ w : S → ℝ, (∀ y, 0 ≤ w y ∧ w y ≤ q' y) ∧ ∑ y, w y ≤ l ∧
    m = ∑ y, w y * (b - y)} with hB
  have hby : ∀ y : S, 0 ≤ b - y := fun y ↦ sub_nonneg.mpr (hS y y.2)
  have hBbdd : BddAbove B := ⟨∑ y, q' y * (b - y), by
    rintro _ ⟨w, hw, -, rfl⟩
    exact Finset.sum_le_sum fun y _ ↦ mul_le_mul_of_nonneg_right (hw y).2 (hby y)⟩
  have hAbdd : BddAbove {m | ∃ q ∈ probVecs S, ipm (tvClass S) q q' ≤ l ∧
      m = vecMean q - vecMean q'} := ⟨b - vecMean q', by
    rintro _ ⟨q, hq, -, rfl⟩
    linarith [vecMean_le_of_le hS hq]⟩
  refine le_antisymm (Real.sSup_le ?_ (Real.sSup_nonneg ?_)) (Real.sSup_le ?_ ?_)
  · -- `q ↦ w = (q' - q)_+`
    rintro _ ⟨q, hq, hd, rfl⟩
    have hsum : ∑ y, q y = ∑ y, q' y := hq.2.trans hq'.2.symm
    have hcomm : ∑ y, max (q' y - q y) 0 = ∑ y, max (q y - q' y) 0 := by
      simpa only [neg_sub] using Finset.sum_max_neg_eq_sum_max Finset.univ
        (fun y ↦ q y - q' y) (by rw [Finset.sum_sub_distrib, hsum, sub_self])
    rw [ipm_tvClass hsum, ← hcomm] at hd
    refine le_csSup_of_le hBbdd ⟨fun y ↦ max (q' y - q y) 0, fun y ↦ ⟨le_max_right _ _,
      max_le (by linarith [hq.1 y]) (hq'.1 y)⟩, hd, rfl⟩ ?_
    have hpt : ∀ y : S, (y : ℝ) * (q y - q' y) ≤
        b * max (q y - q' y) 0 - y * max (q' y - q y) 0 := fun y ↦ by
      have hy := hS y y.2
      rcases le_total 0 (q y - q' y) with h | h
      · rw [max_eq_left h, max_eq_right (by linarith)]; nlinarith
      · rw [max_eq_right h, max_eq_left (by linarith)]; nlinarith
    calc vecMean q - vecMean q' = ∑ y : S, (y : ℝ) * (q y - q' y) := vecMean_sub q q'
      _ ≤ ∑ y : S, (b * max (q y - q' y) 0 - y * max (q' y - q y) 0) :=
          Finset.sum_le_sum fun y _ ↦ hpt y
      _ = ∑ y, max (q' y - q y) 0 * (b - y) := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← hcomm, Finset.mul_sum,
            ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun y _ ↦ by ring
  · rintro _ ⟨w, hw, -, rfl⟩
    exact Finset.sum_nonneg fun y _ ↦ mul_nonneg (hw y).1 (hby y)
  · -- `w ↦ q = q' - w + (∑ w) δ_{x_max}`
    rintro _ ⟨w, hw, hwl, rfl⟩
    set s := ∑ y, w y with hs
    set q : S → ℝ := q' - w + s • Pi.single y₁ 1 with hq
    have hs0 : 0 ≤ s := Finset.sum_nonneg fun y _ ↦ (hw y).1
    have hqp : q ∈ probVecs S := by
      refine ⟨fun y ↦ ?_, ?_⟩
      · simp only [hq, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
        have := (hw y).2
        split_ifs <;> nlinarith
      · simp only [hq, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
          Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hq'.2,
          Fintype.sum_pi_single', ← hs]
        ring
    refine le_csSup_of_le hAbdd ⟨q, hqp, ?_, rfl⟩ ?_
    · rw [ipm_tvClass (hqp.2.trans hq'.2.symm)]
      calc ∑ y, max (q y - q' y) 0 ≤ ∑ y, s * (Pi.single y₁ 1 : S → ℝ) y :=
            Finset.sum_le_sum fun y _ ↦ by
              simp only [hq, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
              exact max_le (by linarith [(hw y).1])
                (mul_nonneg hs0 ((single_mem_probVecs y₁).1 y))
        _ = s := by rw [← Finset.mul_sum, Fintype.sum_pi_single', mul_one]
        _ ≤ l := hwl
    · rw [hq, vecMean_add, vecMean_smul, vecMean_single, hy₁]
      simp only [vecMean, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, mul_sub, hs,
        Finset.sum_mul, one_mul]
      linarith
  · exact reachGain_nonneg _ l hq'

end Incognita.TransferBandits
