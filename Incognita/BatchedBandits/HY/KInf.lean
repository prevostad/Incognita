/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.HY
public import Incognita.BatchedBandits.LogInequalities

/-! # The divergences of HY: rational and real suprema, Lemmas `lem:kinf` and `lem:pseudo`

Properties of `HY.pseudoKinf w₀ h r c μ`, the divergence `𝒦_inf(ν̃_c, μ)` of the pseudo-empirical
law `ν̃_c = (N_c ν̂_c + w₀ δ_0) / (N_c + w₀)` of the rewards of `c` in the rounds `< r`, by the dual
formula with **rational** `λ` [INC-P000, Definition `def:kinf`] (the dual formula of 𝒦_inf is
[HT10, Theorem 8]). The
rewards of the history are in `[0, 1]` (as on every run, almost surely), the pseudo-count is
`w₀ ≥ 0`, and the level is `μ ∈ [0, 1)`. With `F(λ) = HY.pseudoLogMean w₀ h r c λ μ`
(`= E_{ν̃_c}[log (1 - λ (X - μ))]`):

* `HY.continuousAt_pseudoLogMean`, `HY.ofReal_pseudoLogMean_le_pseudoKinf`,
  `HY.pseudoKinf_le_of_forall`, `HY.pseudoKinf_eq_iSup_real`: the supremum over the rational
  `λ ∈ [0, 1 / (1 - μ))` equals the supremum over the real ones (the remark of Definition
  `def:kinf`), since `F` is continuous on that interval.
* Lemma `lem:kinf` for `ν̃_c`: (i) `HY.pseudoKinf_le_ofReal_log`, `𝒦_inf ≤ κ(μ) = log (1/(1-μ))`;
  (ii) is `HY.pseudoKinf_eq_zero_of_le_pseudoMean`; (iii) `HY.pseudoKinf_mono`, monotone in the
  level; (iv) `HY.ofReal_sq_div_eight_le_pseudoKinf`, `𝒦_inf ≥ (μ - q)² / 8` if the mean is
  `≤ q < μ`; (v) `HY.pseudoKinf_le_pseudoKinf_sub_add`, the shift of the level; (vi)
  `log_le_log_one_sub_mul` (in `Incognita.BatchedBandits.LogInequalities`), the scaling
  inequality.
* Lemma `lem:pseudo` (the pseudo-observation against the empirical law, `w₀ = 0`):
  (i) `HY.pseudoKinf_zero_le`, (ii) `HY.mul_pseudoKinf_le`,
  (iii) `HY.pseudoMean_le_pseudoMean_zero`, `HY.pseudoMean_zero_sub_le_pseudoMean`, and the last
  claim `HY.pseudoMean_zero_sub_le_of_le`.
-/

@[expose] public section

open MeasureTheory Learning Finset Filter

open scoped ENNReal Topology

namespace Incognita.BatchedBandits

namespace HY

variable {α : Type*} [DecidableEq α] {n : ℕ} {h : Hist Unit α ℝ n} {r : ℕ} {c : α}

/-- The count is the sum of the indicators. -/
lemma count_eq_sum_ind : (count h r c : ℝ) = ∑ i, ind h r c i := by
  simp only [count, ind]
  push_cast
  rfl

lemma ind_nonneg (i : Fin n) : 0 ≤ ind h r c i := by
  unfold ind
  split_ifs <;> norm_num

lemma ind_le_one (i : Fin n) : ind h r c i ≤ 1 := by
  unfold ind
  split_ifs <;> norm_num

@[deprecated (since := "2026-11-19")] alias one_sub_mul_pos := one_sub_mul_sub_pos

/-- The function `λ ↦ F(λ)` of the dual formula is continuous at every `λ ∈ [0, 1/(1-μ))`, for
rewards `≤ 1` and `μ ≥ 0`. -/
lemma continuousAt_pseudoLogMean (w₀ : ℝ) {μ : ℝ} (hμ0 : 0 ≤ μ)
    (hy : ∀ i, (h i).feedback ≤ 1) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q * (1 - μ) < 1) :
    ContinuousAt (fun q ↦ pseudoLogMean w₀ h r c q μ) q := by
  unfold pseudoLogMean
  refine ContinuousAt.div_const (ContinuousAt.add ?_ ?_) _
  · refine tendsto_finsetSum _ fun i _ ↦ ?_
    refine continuousAt_const.mul (ContinuousAt.log (by fun_prop) ?_)
    exact (one_sub_mul_sub_pos hq0 hq1 (hy i)).ne'
  · refine continuousAt_const.mul (ContinuousAt.log (by fun_prop) ?_)
    have : 0 ≤ q * μ := mul_nonneg hq0 hμ0
    linarith

/-- The divergence is at most `B` if every real `λ ∈ [0, 1/(1-μ))` gives `F(λ) ≤ B`. -/
lemma pseudoKinf_le_of_forall {w₀ μ : ℝ} (hμ : μ < 1) {B : ℝ≥0∞}
    (hB : ∀ q : ℝ, 0 ≤ q → q * (1 - μ) < 1 → ENNReal.ofReal (pseudoLogMean w₀ h r c q μ) ≤ B) :
    pseudoKinf w₀ h r c μ ≤ B := by
  rw [pseudoKinf, ite_eq_left hμ]
  refine iSup_le fun q ↦ ?_
  split_ifs with hq
  · exact hB q hq.1 hq.2
  · exact bot_le

/-- **Real `λ` in the rational supremum** [INC-P000, Definition `def:kinf`, "the supremum can be
taken over rational `λ`"]: for rewards `≤ 1` and `μ ∈ [0, 1)`, every real `λ ∈ [0, 1/(1-μ))` has
`F(λ) ≤ 𝒦_inf(ν̃_c, μ)`, by the continuity of `F` and the density of the rationals. -/
lemma ofReal_pseudoLogMean_le_pseudoKinf {w₀ μ : ℝ} (hμ : μ < 1) (hμ0 : 0 ≤ μ)
    (hy : ∀ i, (h i).feedback ≤ 1) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q * (1 - μ) < 1) :
    ENNReal.ofReal (pseudoLogMean w₀ h r c q μ) ≤ pseudoKinf w₀ h r c μ := by
  rw [pseudoKinf, ite_eq_left hμ]
  refine le_of_forall_lt fun a ha ↦ ?_
  have hatop : a ≠ ⊤ := ha.ne_top
  have hlt : a.toReal < pseudoLogMean w₀ h r c q μ :=
    (ENNReal.lt_ofReal_iff_toReal_lt hatop).mp ha
  have hev : ∀ᶠ q' in 𝓝 q, a.toReal < pseudoLogMean w₀ h r c q' μ :=
    (continuousAt_pseudoLogMean w₀ hμ0 hy hq0 hq1).eventually (Ioi_mem_nhds hlt)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have h1μ : 0 < 1 - μ := by linarith
  have hqb : q < 1 / (1 - μ) := by rw [lt_div_iff₀ h1μ]; exact hq1
  obtain ⟨q', hq'1, hq'2⟩ := exists_rat_btwn (lt_min (by linarith : q < q + δ) hqb)
  have hq'δ : (q' : ℝ) < q + δ := hq'2.trans_le (min_le_left _ _)
  have hq'b : (q' : ℝ) < 1 / (1 - μ) := hq'2.trans_le (min_le_right _ _)
  have hq'0 : 0 ≤ (q' : ℝ) := hq0.trans hq'1.le
  have hq'1' : (q' : ℝ) * (1 - μ) < 1 := by rwa [lt_div_iff₀ h1μ] at hq'b
  have hdist : dist (q' : ℝ) q < δ := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  calc a < ENNReal.ofReal (pseudoLogMean w₀ h r c q' μ) :=
        (ENNReal.lt_ofReal_iff_toReal_lt hatop).mpr (hball hdist)
    _ ≤ _ := by
        refine le_iSup_of_le (f := fun q : ℚ ↦ if 0 ≤ (q : ℝ) ∧ (q : ℝ) * (1 - μ) < 1 then
          ENNReal.ofReal (pseudoLogMean w₀ h r c q μ) else 0) q' ?_
        rw [ite_eq_left ⟨hq'0, hq'1'⟩]

/-- **The rational and the real suprema agree** [INC-P000, Definition `def:kinf`; P000, Open
problems]: for rewards `≤ 1` and `μ ∈ [0, 1)`, `𝒦_inf(ν̃_c, μ)` is the supremum of `F(λ)` over the
real `λ ∈ [0, 1/(1-μ))`. -/
lemma pseudoKinf_eq_iSup_real {w₀ μ : ℝ} (hμ : μ < 1) (hμ0 : 0 ≤ μ)
    (hy : ∀ i, (h i).feedback ≤ 1) :
    pseudoKinf w₀ h r c μ = ⨆ q : ℝ, if 0 ≤ q ∧ q * (1 - μ) < 1 then
      ENNReal.ofReal (pseudoLogMean w₀ h r c q μ) else 0 := by
  refine le_antisymm (pseudoKinf_le_of_forall hμ fun q hq0 hq1 ↦ ?_) (iSup_le fun q ↦ ?_)
  · refine le_iSup_of_le q ?_
    rw [ite_eq_left ⟨hq0, hq1⟩]
  · split_ifs with hq
    · exact ofReal_pseudoLogMean_le_pseudoKinf hμ hμ0 hy hq.1 hq.2
    · exact bot_le

/-! ### Lemma `lem:kinf` for the pseudo-empirical law -/

/-- [INC-P000, Lemma `lem:kinf`(i)] For rewards in `[0, 1]`, `w₀ ≥ 0`, `N_c + w₀ > 0` and
`μ ∈ [0, 1)`, `𝒦_inf(ν̃_c, μ) ≤ κ(μ) = log (1/(1-μ))`: every term is at most
`log (1 + λ μ) ≤ κ(μ)`. -/
lemma pseudoKinf_le_ofReal_log {w₀ μ : ℝ} (hw₀ : 0 ≤ w₀) (hμ : μ < 1) (hμ0 : 0 ≤ μ)
    (hy : ∀ i, (h i).feedback ∈ Set.Icc (0 : ℝ) 1) (hpos : 0 < (count h r c : ℝ) + w₀) :
    pseudoKinf w₀ h r c μ ≤ ENNReal.ofReal (Real.log (1 / (1 - μ))) := by
  refine pseudoKinf_le_of_forall hμ fun q hq0 hq1 ↦ ENNReal.ofReal_le_ofReal ?_
  have h1μ : 0 < 1 - μ := by linarith
  have hκ : Real.log (1 + q * μ) ≤ Real.log (1 / (1 - μ)) := by
    refine Real.log_le_log (by nlinarith) ?_
    rw [le_div_iff₀ h1μ]
    nlinarith
  have hterm : ∀ i, ind h r c i * Real.log (1 - q * ((h i).feedback - μ)) ≤
      ind h r c i * Real.log (1 / (1 - μ)) := by
    intro i
    refine mul_le_mul_of_nonneg_left (le_trans ?_ hκ) (ind_nonneg i)
    refine Real.log_le_log (one_sub_mul_sub_pos hq0 hq1 (hy i).2) ?_
    nlinarith [(hy i).1]
  rw [pseudoLogMean, div_le_iff₀ hpos]
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ hterm i
  rw [← Finset.sum_mul, ← count_eq_sum_ind] at hsum
  nlinarith [mul_le_mul_of_nonneg_left hκ hw₀]

/-- [INC-P000, Lemma `lem:kinf`(iii)] For rewards in `[0, 1]`, `w₀ ≥ 0` and
`0 ≤ μ ≤ μ' < 1`, `𝒦_inf(ν̃_c, μ) ≤ 𝒦_inf(ν̃_c, μ')`: for `λ ∈ [0, 1/(1-μ))`, with
`λ' = λ (1 - μ) / (1 - μ')`, `1 - λ (y - μ) ≤ 1 - λ' (y - μ')` on `[0, 1]`. -/
lemma pseudoKinf_mono {w₀ μ μ' : ℝ} (hw₀ : 0 ≤ w₀) (hμ0 : 0 ≤ μ) (hμμ' : μ ≤ μ') (hμ' : μ' < 1)
    (hy : ∀ i, (h i).feedback ∈ Set.Icc (0 : ℝ) 1) :
    pseudoKinf w₀ h r c μ ≤ pseudoKinf w₀ h r c μ' := by
  have hμ : μ < 1 := hμμ'.trans_lt hμ'
  have h1μ' : 0 < 1 - μ' := by linarith
  refine pseudoKinf_le_of_forall hμ fun q hq0 hq1 ↦ ?_
  set q' := q * (1 - μ) / (1 - μ') with hq'
  have hq'0 : 0 ≤ q' := div_nonneg (mul_nonneg hq0 (by linarith)) h1μ'.le
  have hq'1 : q' * (1 - μ') = q * (1 - μ) := by rw [hq']; field_simp
  have hqq' : q ≤ q' := by
    rw [hq', le_div_iff₀ h1μ']
    exact mul_le_mul_of_nonneg_left (by linarith) hq0
  refine le_trans ?_ (ofReal_pseudoLogMean_le_pseudoKinf hμ' (hμ0.trans hμμ')
    (fun i ↦ (hy i).2) hq'0 (by rw [hq'1]; exact hq1))
  refine ENNReal.ofReal_le_ofReal ?_
  -- termwise comparison
  have hkey : ∀ y : ℝ, y ∈ Set.Icc (0 : ℝ) 1 →
      Real.log (1 - q * (y - μ)) ≤ Real.log (1 - q' * (y - μ')) := by
    intro y hy'
    refine Real.log_le_log (one_sub_mul_sub_pos hq0 hq1 hy'.2) ?_
    have e1 : q' * (y - μ') = q' * (y - 1) + q * (1 - μ) := by rw [← hq'1]; ring
    have e2 : q * (y - μ) = q * (y - 1) + q * (1 - μ) := by ring
    have : q' * (y - 1) ≤ q * (y - 1) := mul_le_mul_of_nonpos_right hqq' (by linarith [hy'.2])
    linarith
  unfold pseudoLogMean
  have hden : 0 ≤ (count h r c : ℝ) + w₀ := by positivity
  refine div_le_div_of_nonneg_right (add_le_add ?_ ?_) hden
  · exact Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hkey _ (hy i)) (ind_nonneg i)
  · refine mul_le_mul_of_nonneg_left ?_ hw₀
    have := hkey 0 ⟨le_rfl, zero_le_one⟩
    simpa using this

@[deprecated (since := "2026-11-19")] alias sub_two_mul_sq_le_log_one_add :=
  BatchedBandits.sub_two_mul_sq_le_log_one_add

/-- [INC-P000, Lemma `lem:kinf`(iv)] For rewards in `[0, 1]`, `w₀ ≥ 0`, `N_c + w₀ > 0`,
`μ ∈ [0, 1)` and `m̃_c ≤ q < μ`, `𝒦_inf(ν̃_c, μ) ≥ (μ - q)² / 8`: the dual formula at
`λ₀ = (μ - q) / 4`, with `log (1 + u) ≥ u - 2u²`. -/
lemma ofReal_sq_div_eight_le_pseudoKinf {w₀ μ q : ℝ} (hw₀ : 0 ≤ w₀) (hμ : μ < 1) (hμ0 : 0 ≤ μ)
    (hy : ∀ i, (h i).feedback ∈ Set.Icc (0 : ℝ) 1) (hpos : 0 < (count h r c : ℝ) + w₀)
    (hpq : pseudoMean w₀ h r c ≤ q) (hqμ : q < μ) :
    ENNReal.ofReal ((μ - q) ^ 2 / 8) ≤ pseudoKinf w₀ h r c μ := by
  set l := (μ - q) / 4 with hl
  -- the pseudo-mean is nonnegative, so `μ - q ≤ 1`
  have hmean0 : 0 ≤ pseudoMean w₀ h r c := by
    unfold pseudoMean
    exact div_nonneg (Finset.sum_nonneg fun i _ ↦ mul_nonneg (ind_nonneg i) (hy i).1) hpos.le
  have hl0 : 0 ≤ l := by rw [hl]; linarith
  have hl4 : l ≤ 1 / 4 := by rw [hl]; linarith
  have hl1 : l * (1 - μ) < 1 := by nlinarith
  refine le_trans (ENNReal.ofReal_le_ofReal ?_)
    (ofReal_pseudoLogMean_le_pseudoKinf hμ hμ0 (fun i ↦ (hy i).2) hl0 hl1)
  -- termwise: `log (1 - l (y - μ)) ≥ -l (y - μ) - 2 l²`
  have hterm : ∀ y : ℝ, y ∈ Set.Icc (0 : ℝ) 1 →
      -(l * (y - μ)) - 2 * l ^ 2 ≤ Real.log (1 - l * (y - μ)) := by
    intro y hy'
    have hb : |y - μ| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hy'.1, hy'.2]
    have hu : |l * (y - μ)| ≤ l := by
      rw [abs_mul, abs_of_nonneg hl0]
      nlinarith [abs_nonneg (y - μ)]
    have hu' : -(1 / 2) ≤ -(l * (y - μ)) := by
      have := neg_abs_le (l * (y - μ))
      have := le_abs_self (l * (y - μ))
      linarith
    have hsq : (l * (y - μ)) ^ 2 ≤ l ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hu 2
    have := BatchedBandits.sub_two_mul_sq_le_log_one_add hu'
    rw [show 1 + -(l * (y - μ)) = 1 - l * (y - μ) by ring, neg_sq] at this
    linarith
  unfold pseudoLogMean
  rw [le_div_iff₀ hpos]
  have hsum : ∑ i, ind h r c i * (-(l * ((h i).feedback - μ)) - 2 * l ^ 2) ≤
      ∑ i, ind h r c i * Real.log (1 - l * ((h i).feedback - μ)) :=
    Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hterm _ (hy i)) (ind_nonneg i)
  have h0 : -(l * (0 - μ)) - 2 * l ^ 2 ≤ Real.log (1 + l * μ) := by
    have := hterm 0 ⟨le_rfl, zero_le_one⟩
    rwa [show 1 - l * (0 - μ) = 1 + l * μ by ring] at this
  have hlin : ∑ i, ind h r c i * (-(l * ((h i).feedback - μ)) - 2 * l ^ 2) =
      -l * ∑ i, ind h r c i * (h i).feedback + (l * μ - 2 * l ^ 2) * ∑ i, ind h r c i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [hlin, ← count_eq_sum_ind] at hsum
  have hm : ∑ i, ind h r c i * (h i).feedback ≤ q * ((count h r c : ℝ) + w₀) := by
    have := hpq
    rw [pseudoMean, div_le_iff₀ hpos] at this
    exact this
  have hw := mul_le_mul_of_nonneg_left h0 hw₀
  have hkey : (μ - q) ^ 2 / 8 = l * (μ - q) - 2 * l ^ 2 := by rw [hl]; ring
  rw [hkey]
  nlinarith

/-- [INC-P000, Lemma `lem:kinf`(v)] For rewards in `[0, 1]`, `w₀ ≥ 0`, `N_c + w₀ > 0` and
`0 < ε ≤ μ < 1`, `𝒦_inf(ν̃_c, μ - ε) ≥ 𝒦_inf(ν̃_c, μ) - ε / (1 - μ)`, written
`𝒦_inf(ν̃_c, μ) ≤ 𝒦_inf(ν̃_c, μ - ε) + ε / (1 - μ)`: for `λ ∈ [0, 1/(1-μ))`, with
`α = (1 - μ) / (1 - μ + ε)` and `λ' = α λ`, `1 - λ' (y - μ + ε) ≥ α (1 - λ (y - μ))`, and
`log α ≥ -ε / (1 - μ)`. -/
lemma pseudoKinf_le_pseudoKinf_sub_add {w₀ μ ε : ℝ} (hw₀ : 0 ≤ w₀) (hε : 0 < ε) (hεμ : ε ≤ μ)
    (hμ : μ < 1) (hy : ∀ i, (h i).feedback ∈ Set.Icc (0 : ℝ) 1)
    (hpos : 0 < (count h r c : ℝ) + w₀) :
    pseudoKinf w₀ h r c μ ≤
      pseudoKinf w₀ h r c (μ - ε) + ENNReal.ofReal (ε / (1 - μ)) := by
  have h1μ : 0 < 1 - μ := by linarith
  have h1με : 0 < 1 - μ + ε := by linarith
  refine pseudoKinf_le_of_forall hμ fun q hq0 hq1 ↦ ?_
  set a := (1 - μ) / (1 - μ + ε) with ha
  have ha0 : 0 < a := div_pos h1μ h1με
  have ha1 : a ≤ 1 := (div_le_one h1με).mpr (by linarith)
  set q' := a * q with hq'
  have hq'0 : 0 ≤ q' := mul_nonneg ha0.le hq0
  have hq'1 : q' * (1 - (μ - ε)) = q * (1 - μ) := by
    rw [hq', ha]
    field_simp
    ring
  have hq'1' : q' * (1 - (μ - ε)) < 1 := by rw [hq'1]; exact hq1
  -- `log α ≥ -ε / (1 - μ)`
  have hloga : -(ε / (1 - μ)) ≤ Real.log a := by
    have h := Real.one_sub_inv_le_log_of_pos ha0
    have : a⁻¹ = 1 + ε / (1 - μ) := by rw [ha, inv_div]; field_simp
    rw [this] at h
    have : 1 - (1 + ε / (1 - μ)) = -(ε / (1 - μ)) := by ring
    linarith
  -- termwise: `log (1 - λ' (y - (μ - ε))) ≥ log α + log (1 - λ (y - μ))`
  have hterm : ∀ y : ℝ, y ∈ Set.Icc (0 : ℝ) 1 →
      Real.log a + Real.log (1 - q * (y - μ)) ≤ Real.log (1 - q' * (y - (μ - ε))) := by
    intro y hy'
    have hp := one_sub_mul_sub_pos hq0 hq1 hy'.2
    rw [← Real.log_mul ha0.ne' hp.ne']
    refine Real.log_le_log (mul_pos ha0 hp) ?_
    -- `1 - λ' (y - μ + ε) - α (1 - λ (y - μ)) = 1 - α - α λ ε ≥ 0`
    have hdiff : 1 - q' * (y - (μ - ε)) - a * (1 - q * (y - μ)) = 1 - a - a * q * ε := by
      rw [hq']; ring
    have hbound : a * q * ε ≤ 1 - a := by
      have : a * q * ε = q * (1 - μ) * (ε / (1 - μ + ε)) := by rw [ha]; field_simp
      have h2 : 1 - a = ε / (1 - μ + ε) := by rw [ha]; field_simp; ring
      rw [this, h2]
      have : 0 ≤ ε / (1 - μ + ε) := div_nonneg hε.le h1με.le
      nlinarith
    linarith
  have hlt := ofReal_pseudoLogMean_le_pseudoKinf (w₀ := w₀) (h := h) (r := r) (c := c)
    (μ := μ - ε) (by linarith) (by linarith) (fun i ↦ (hy i).2) hq'0 hq'1'
  refine le_trans ?_ (add_le_add hlt le_rfl)
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (ENNReal.ofReal_add_le)
  -- `F_μ(λ) ≤ F_(μ-ε)(λ') + ε / (1 - μ)`
  unfold pseudoLogMean
  rw [div_add' _ _ _ hpos.ne', div_le_div_iff_of_pos_right hpos]
  have hsum : ∑ i, ind h r c i * (Real.log a + Real.log (1 - q * ((h i).feedback - μ))) ≤
      ∑ i, ind h r c i * Real.log (1 - q' * ((h i).feedback - (μ - ε))) :=
    Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hterm _ (hy i)) (ind_nonneg i)
  have h0 := hterm 0 ⟨le_rfl, zero_le_one⟩
  rw [show 1 - q * (0 - μ) = 1 + q * μ by ring,
    show 1 - q' * (0 - (μ - ε)) = 1 + q' * (μ - ε) by ring] at h0
  have hlin : ∑ i, ind h r c i * (Real.log a + Real.log (1 - q * ((h i).feedback - μ))) =
      Real.log a * ∑ i, ind h r c i +
        ∑ i, ind h r c i * Real.log (1 - q * ((h i).feedback - μ)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [hlin, ← count_eq_sum_ind] at hsum
  have hw := mul_le_mul_of_nonneg_left h0 hw₀
  have hc0 : (0 : ℝ) ≤ count h r c := Nat.cast_nonneg _
  nlinarith

/-! ### Lemma `lem:pseudo` -/

/-- [INC-P000, Lemma `lem:pseudo`(i)] For rewards in `[0, 1]`, `w₀ ≥ 0`, `N_c ≥ 1` and
`μ ∈ [0, 1)`, `𝒦_inf(ν̂_c, μ) ≤ 𝒦_inf(ν̃_c, μ)` (`ν̂_c` is the pseudo-empirical law with `w₀ = 0`,
the empirical law): `g_λ(0) = log (1 + λ μ) ≥ E_{ν̂_c}[g_λ]`, so adding the atom at `0` raises the
mean of `g_λ`. -/
lemma pseudoKinf_zero_le {w₀ μ : ℝ} (hw₀ : 0 ≤ w₀) (hμ : μ < 1) (hμ0 : 0 ≤ μ)
    (hy : ∀ i, (h i).feedback ∈ Set.Icc (0 : ℝ) 1) (hN : 1 ≤ count h r c) :
    pseudoKinf 0 h r c μ ≤ pseudoKinf w₀ h r c μ := by
  refine pseudoKinf_le_of_forall hμ fun q hq0 hq1 ↦ ?_
  refine le_trans (ENNReal.ofReal_le_ofReal ?_)
    (ofReal_pseudoLogMean_le_pseudoKinf hμ hμ0 (fun i ↦ (hy i).2) hq0 hq1)
  have hN' : (1 : ℝ) ≤ count h r c := by exact_mod_cast hN
  set S := ∑ i, ind h r c i * Real.log (1 - q * ((h i).feedback - μ)) with hS
  have hg0 : S ≤ count h r c * Real.log (1 + q * μ) := by
    rw [count_eq_sum_ind, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left ?_ (ind_nonneg i)
    refine Real.log_le_log (one_sub_mul_sub_pos hq0 hq1 (hy i).2) ?_
    nlinarith [(hy i).1]
  unfold pseudoLogMean
  rw [← hS, zero_mul, add_zero, add_zero, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left hg0 hw₀]

/-- [INC-P000, Lemma `lem:pseudo`(ii)] For rewards in `[0, 1]`, `w₀ ≥ 0`, `N_c ≥ 1` and
`μ ∈ [0, 1)`, `N_c 𝒦_inf(ν̃_c, μ) ≤ N_c 𝒦_inf(ν̂_c, μ) + w₀ κ(μ)`. -/
lemma mul_pseudoKinf_le {w₀ μ : ℝ} (hw₀ : 0 ≤ w₀) (hμ : μ < 1) (hμ0 : 0 ≤ μ)
    (hy : ∀ i, (h i).feedback ∈ Set.Icc (0 : ℝ) 1) (hN : 1 ≤ count h r c) :
    (count h r c : ℝ≥0∞) * pseudoKinf w₀ h r c μ ≤
      (count h r c : ℝ≥0∞) * pseudoKinf 0 h r c μ +
        ENNReal.ofReal (w₀ * Real.log (1 / (1 - μ))) := by
  have hN' : (1 : ℝ) ≤ count h r c := by exact_mod_cast hN
  have h1μ : 0 < 1 - μ := by linarith
  rw [pseudoKinf, ite_eq_left hμ, ENNReal.mul_iSup]
  refine iSup_le fun q ↦ ?_
  split_ifs with hq
  swap
  · rw [mul_zero]
    exact bot_le
  have hq0 := hq.1
  have hq1 := hq.2
  set F := pseudoLogMean w₀ h r c q μ with hF
  set F₀ := pseudoLogMean 0 h r c q μ with hF₀
  have hκ : Real.log (1 + q * μ) ≤ Real.log (1 / (1 - μ)) := by
    refine Real.log_le_log (by nlinarith) ?_
    rw [le_div_iff₀ h1μ]
    nlinarith
  -- `(N + w₀) F = N F₀ + w₀ log (1 + λ μ)`
  have hsplit : ((count h r c : ℝ) + w₀) * F =
      (count h r c : ℝ) * F₀ + w₀ * Real.log (1 + q * μ) := by
    rw [hF, hF₀]
    unfold pseudoLogMean
    rw [zero_mul, add_zero, add_zero]
    field_simp
  have hreal : (count h r c : ℝ) * F ≤ (count h r c : ℝ) * max F₀ 0 +
      w₀ * Real.log (1 / (1 - μ)) := by
    rcases le_total F 0 with hF0 | hF0
    · have : (count h r c : ℝ) * F ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hF0
      have : 0 ≤ (count h r c : ℝ) * max F₀ 0 := mul_nonneg (by linarith) (le_max_right _ _)
      have : 0 ≤ Real.log (1 / (1 - μ)) := Real.log_nonneg (by rw [le_div_iff₀ h1μ]; linarith)
      nlinarith
    · have := le_max_left F₀ 0
      nlinarith [mul_le_mul_of_nonneg_left hκ hw₀]
  have hF₀le : ENNReal.ofReal F₀ ≤ pseudoKinf 0 h r c μ :=
    ofReal_pseudoLogMean_le_pseudoKinf hμ hμ0 (fun i ↦ (hy i).2) hq0 hq1
  calc (count h r c : ℝ≥0∞) * ENNReal.ofReal F
      = ENNReal.ofReal ((count h r c : ℝ) * F) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((count h r c : ℝ) * max F₀ 0 + w₀ * Real.log (1 / (1 - μ))) :=
        ENNReal.ofReal_le_ofReal hreal
    _ ≤ ENNReal.ofReal ((count h r c : ℝ) * max F₀ 0) +
        ENNReal.ofReal (w₀ * Real.log (1 / (1 - μ))) := ENNReal.ofReal_add_le
    _ = (count h r c : ℝ≥0∞) * ENNReal.ofReal F₀ +
        ENNReal.ofReal (w₀ * Real.log (1 / (1 - μ))) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
          ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left zero_le]
    _ ≤ _ := by gcongr

/-- [INC-P000, Lemma `lem:pseudo`(iii), upper inequality] For rewards `≥ 0` and `w₀ ≥ 0`,
`m̃_c ≤ m̂_c` (`m̂_c` is the pseudo-mean with `w₀ = 0`, the empirical mean). -/
lemma pseudoMean_le_pseudoMean_zero {w₀ : ℝ} (hw₀ : 0 ≤ w₀) (hy : ∀ i, 0 ≤ (h i).feedback) :
    pseudoMean w₀ h r c ≤ pseudoMean 0 h r c := by
  unfold pseudoMean
  rw [add_zero]
  rcases Nat.eq_zero_or_pos (count h r c) with h0 | h0
  · have hsum : ∑ i, ind h r c i * (h i).feedback = 0 := by
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      have : ind h r c i = 0 := by
        have h1 := count_eq_sum_ind (h := h) (r := r) (c := c)
        rw [h0, Nat.cast_zero, eq_comm, Finset.sum_eq_zero_iff_of_nonneg
          fun i _ ↦ ind_nonneg i] at h1
        exact h1 i (Finset.mem_univ i)
      rw [this, zero_mul]
    rw [hsum, zero_div, zero_div]
  · have hN : (0 : ℝ) < count h r c := by exact_mod_cast h0
    exact div_le_div_of_nonneg_left
      (Finset.sum_nonneg fun i _ ↦ mul_nonneg (ind_nonneg i) (hy i)) hN (by linarith)

/-- [INC-P000, Lemma `lem:pseudo`(iii), lower inequality] For rewards in `[0, 1]`, `w₀ ≥ 0` and
`N_c ≥ 1`, `m̂_c - w₀ / (N_c + w₀) ≤ m̃_c`. -/
lemma pseudoMean_zero_sub_le_pseudoMean {w₀ : ℝ} (hw₀ : 0 ≤ w₀)
    (hy : ∀ i, (h i).feedback ∈ Set.Icc (0 : ℝ) 1) (hN : 1 ≤ count h r c) :
    pseudoMean 0 h r c - w₀ / ((count h r c : ℝ) + w₀) ≤ pseudoMean w₀ h r c := by
  have hN' : (1 : ℝ) ≤ count h r c := by exact_mod_cast hN
  set S := ∑ i, ind h r c i * (h i).feedback with hS
  have hSN : S ≤ count h r c := by
    rw [count_eq_sum_ind]
    exact Finset.sum_le_sum fun i _ ↦ by
      have := (hy i).2
      have := ind_nonneg (h := h) (r := r) (c := c) i
      nlinarith
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ ↦ mul_nonneg (ind_nonneg i) (hy i).1
  unfold pseudoMean
  rw [← hS, add_zero, sub_le_iff_le_add, ← add_div, div_le_div_iff₀ (by linarith)
    (by linarith)]
  nlinarith

/-- [INC-P000, Lemma `lem:pseudo`, last claim] For rewards in `[0, 1]`, `w₀ ≥ 0`, and an arm
with `N_c ≥ U / 2` and `U ≥ 1`, `m̃_c ≥ m̂_c - 2 w₀ / U`. -/
lemma pseudoMean_zero_sub_le_of_le {w₀ : ℝ} (hw₀ : 0 ≤ w₀)
    (hy : ∀ i, (h i).feedback ∈ Set.Icc (0 : ℝ) 1) {U : ℕ} (hU : 1 ≤ U)
    (hNU : U ≤ 2 * count h r c) :
    pseudoMean 0 h r c - 2 * w₀ / U ≤ pseudoMean w₀ h r c := by
  have hN : 1 ≤ count h r c := by omega
  refine le_trans ?_ (pseudoMean_zero_sub_le_pseudoMean hw₀ hy hN)
  have hU' : (0 : ℝ) < U := by exact_mod_cast hU
  have hNU' : (U : ℝ) ≤ 2 * count h r c := by exact_mod_cast hNU
  have hN' : (1 : ℝ) ≤ count h r c := by exact_mod_cast hN
  refine sub_le_sub_left ?_ _
  rw [div_le_div_iff₀ (by linarith) hU']
  nlinarith

end HY

end Incognita.BatchedBandits
