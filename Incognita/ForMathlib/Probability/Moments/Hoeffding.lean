/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import LMLExplore.Probability.Moments.SubGaussian.Bounded
public import LeanMachineLearning.ForMathlib.Probability.Moments.SubGaussian
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Hoeffding's inequality for bounded independent variables

[INC-P000, Lemma `lem:hoeffding`]: for independent `Z_1, Z_2, …` with values in `[0, 1]` and a
common mean `m`, with `S_n = Z_1 + ⋯ + Z_n` (here `∑ i ∈ range n, Z i`):

* `Incognita.measureReal_add_le_sum_range_le`, `Incognita.measureReal_sum_range_le_sub_le`:
  (a), `P(S_n ≥ n m + y) ≤ e^(-2y²/n)` and `P(S_n ≤ n m - y) ≤ e^(-2y²/n)` for `y ≥ 0`, the case
  `[0, 1]` of `Incognita.measureReal_add_le_sum_range_le_of_mem_Icc` and
  `Incognita.measureReal_sum_range_le_sub_le_of_mem_Icc` (variables in `[a, b]`, bound
  `e^(-2y²/(n (b - a)²))`);
* `Incognita.measure_exists_ge_abs_div_sub_gt_le`: (b), for `ρ > 0` and `u > 0`,
  `P(∃ n ≥ u, |S_n / n - m| > ρ) ≤ 2 e^(-2ρ²u) / (1 - e^(-2ρ²))`.

The variables are only assumed independent with a common mean (the paper's i.i.d. hypothesis is
stronger). The proofs use Mathlib's Hoeffding lemma on `[a, b]` and the sub-Gaussian tail bounds
of Mathlib, LML and LMLExplore, then a union bound over `n ≥ ⌈u⌉` and a geometric series.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open Real (exp)
open scoped NNReal ENNReal

namespace Incognita

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {Z : ℕ → Ω → ℝ} {m : ℝ}

/-- The exponent of Mathlib's Hoeffding bound for variables in `[a, b]`:
`y² / (2 n ((b - a)/2)²) = 2 y² / (n (b - a)²)` (both sides are `0` when `n (b - a)² = 0`). -/
lemma neg_sq_div_two_mul_nnnorm_sub_div_two_sq (n : ℕ) (a b y : ℝ) :
    -y ^ 2 / (2 * n * (((‖b - a‖₊ / 2) ^ 2 : ℝ≥0) : ℝ)) = -2 * y ^ 2 / (n * (b - a) ^ 2) := by
  have h : (2 * n * (((‖b - a‖₊ / 2) ^ 2 : ℝ≥0) : ℝ)) = n * (b - a) ^ 2 / 2 := by
    push_cast
    rw [Real.norm_eq_abs, div_pow, sq_abs]
    ring
  rw [h, div_div_eq_mul_div]
  ring

/-- **Hoeffding's inequality**, upper tail: for independent `Z_i ∈ [a, b]` of common mean `m` and
`y ≥ 0`, `P(S_n ≥ n m + y) ≤ e^(-2y²/(n (b - a)²))` (Mathlib's Hoeffding lemma
`hasSubgaussianMGF_of_mem_Icc` and `HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun`). -/
lemma measureReal_add_le_sum_range_le_of_mem_Icc (hind : iIndepFun Z P)
    (hm : ∀ i, AEMeasurable (Z i) P) {a b : ℝ} (hb : ∀ i, ∀ᵐ ω ∂P, Z i ω ∈ Set.Icc a b)
    (hmean : ∀ i, P[Z i] = m) (n : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    P.real {ω | n * m + y ≤ ∑ i ∈ range n, Z i ω} ≤ exp (-2 * y ^ 2 / (n * (b - a) ^ 2)) := by
  have hsub : ∀ i < n, HasSubgaussianMGF (fun ω ↦ Z i ω - m) ((‖b - a‖₊ / 2) ^ 2) P :=
    fun i _ ↦ by simpa [hmean i] using hasSubgaussianMGF_of_mem_Icc (hm i) (hb i)
  have h := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun
    (hind.comp (g := fun _ (x : ℝ) ↦ x - m) fun _ ↦ measurable_sub_const m) hsub hy
  have hset : {ω | n * m + y ≤ ∑ i ∈ range n, Z i ω} =
      {ω | y ≤ ∑ i ∈ range n, (fun ω ↦ Z i ω - m) ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    constructor <;> intro h <;> linarith
  rw [hset, ← neg_sq_div_two_mul_nnnorm_sub_div_two_sq]
  exact h

/-- **Hoeffding's inequality**, lower tail: for independent `Z_i ∈ [a, b]` of common mean `m` and
`y ≥ 0`, `P(S_n ≤ n m - y) ≤ e^(-2y²/(n (b - a)²))` (Mathlib's Hoeffding lemma and LML's
`HasSubgaussianMGF.measure_sum_range_le_le_of_iIndepFun`). -/
lemma measureReal_sum_range_le_sub_le_of_mem_Icc (hind : iIndepFun Z P)
    (hm : ∀ i, AEMeasurable (Z i) P) {a b : ℝ} (hb : ∀ i, ∀ᵐ ω ∂P, Z i ω ∈ Set.Icc a b)
    (hmean : ∀ i, P[Z i] = m) (n : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    P.real {ω | ∑ i ∈ range n, Z i ω ≤ n * m - y} ≤ exp (-2 * y ^ 2 / (n * (b - a) ^ 2)) := by
  have hsub : ∀ i < n, HasSubgaussianMGF (fun ω ↦ Z i ω - m) ((‖b - a‖₊ / 2) ^ 2) P :=
    fun i _ ↦ by simpa [hmean i] using hasSubgaussianMGF_of_mem_Icc (hm i) (hb i)
  have h := HasSubgaussianMGF.measure_sum_range_le_le_of_iIndepFun
    (hind.comp (g := fun _ (x : ℝ) ↦ x - m) fun _ ↦ measurable_sub_const m) hsub hy
  have hset : {ω | ∑ i ∈ range n, Z i ω ≤ n * m - y} =
      {ω | ∑ i ∈ range n, (fun ω ↦ Z i ω - m) ω ≤ -y} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    constructor <;> intro h <;> linarith
  rw [hset, ← neg_sq_div_two_mul_nnnorm_sub_div_two_sq]
  exact h

/-- [INC-P000, Lemma `lem:hoeffding`(a), upper tail] For independent `Z_i ∈ [0, 1]` of common mean
`m` and `y ≥ 0`, `P(S_n ≥ n m + y) ≤ e^(-2y²/n)`: `measureReal_add_le_sum_range_le_of_mem_Icc`
on `[0, 1]`. -/
lemma measureReal_add_le_sum_range_le (hind : iIndepFun Z P) (hm : ∀ i, AEMeasurable (Z i) P)
    (hb : ∀ i, ∀ᵐ ω ∂P, Z i ω ∈ Set.Icc (0 : ℝ) 1) (hmean : ∀ i, P[Z i] = m) (n : ℕ) {y : ℝ}
    (hy : 0 ≤ y) :
    P.real {ω | n * m + y ≤ ∑ i ∈ range n, Z i ω} ≤ exp (-2 * y ^ 2 / n) := by
  simpa using measureReal_add_le_sum_range_le_of_mem_Icc hind hm hb hmean n hy

/-- [INC-P000, Lemma `lem:hoeffding`(a), lower tail] For independent `Z_i ∈ [0, 1]` of common mean
`m` and `y ≥ 0`, `P(S_n ≤ n m - y) ≤ e^(-2y²/n)`: `measureReal_sum_range_le_sub_le_of_mem_Icc`
on `[0, 1]`. -/
lemma measureReal_sum_range_le_sub_le (hind : iIndepFun Z P) (hm : ∀ i, AEMeasurable (Z i) P)
    (hb : ∀ i, ∀ᵐ ω ∂P, Z i ω ∈ Set.Icc (0 : ℝ) 1) (hmean : ∀ i, P[Z i] = m) (n : ℕ) {y : ℝ}
    (hy : 0 ≤ y) :
    P.real {ω | ∑ i ∈ range n, Z i ω ≤ n * m - y} ≤ exp (-2 * y ^ 2 / n) := by
  simpa using measureReal_sum_range_le_sub_le_of_mem_Icc hind hm hb hmean n hy

/-- The two-sided bound at the deviation `n ρ`:
`P(n ρ ≤ |S_n - n m|) ≤ 2 e^(-2ρ² n)` for `n ≥ 1`, `ρ ≥ 0`. -/
lemma measure_mul_le_abs_sum_range_sub_le (hind : iIndepFun Z P)
    (hm : ∀ i, AEMeasurable (Z i) P) (hb : ∀ i, ∀ᵐ ω ∂P, Z i ω ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ i, P[Z i] = m) {n : ℕ} (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    P {ω | n * ρ ≤ |∑ i ∈ range n, (Z i ω - m)|} ≤
      ENNReal.ofReal (2 * exp (-(2 * ρ ^ 2)) ^ n) := by
  have h := LMLExplore.measureReal_le_abs_sum_sub_integral_le hind (s := range n)
    (fun i _ ↦ hm i) (l := fun _ ↦ 0) (u := fun _ ↦ 1) (fun i _ ↦ hb i)
    (mul_nonneg (Nat.cast_nonneg n) hρ)
  simp only [hmean, sub_zero, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one] at h
  rw [← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal (h.trans_eq ?_)
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [← Real.exp_nat_mul]
  congr 2
  field_simp

/-- [INC-P000, Lemma `lem:hoeffding`(b)] For independent `Z_i ∈ [0, 1]` of common mean `m`,
`ρ > 0` and `u > 0`, `P(∃ n ≥ u, |S_n / n - m| > ρ) ≤ 2 e^(-2ρ²u) / (1 - e^(-2ρ²))` (`n` ranges
over the integers). -/
lemma measure_exists_ge_abs_div_sub_gt_le (hind : iIndepFun Z P)
    (hm : ∀ i, AEMeasurable (Z i) P) (hb : ∀ i, ∀ᵐ ω ∂P, Z i ω ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ i, P[Z i] = m) {ρ u : ℝ} (hρ : 0 < ρ) (hu : 0 < u) :
    P {ω | ∃ n : ℕ, u ≤ n ∧ ρ < |(∑ i ∈ range n, Z i ω) / n - m|} ≤
      ENNReal.ofReal (2 * exp (-(2 * ρ ^ 2 * u)) / (1 - exp (-(2 * ρ ^ 2)))) := by
  set N := ⌈u⌉₊ with hN
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hu).ne'
  set q := exp (-(2 * ρ ^ 2)) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  -- the event is in the union of the events at the deviation `n ρ`, `n ≥ N`
  have hsub : {ω | ∃ n : ℕ, u ≤ n ∧ ρ < |(∑ i ∈ range n, Z i ω) / n - m|} ⊆
      ⋃ k : ℕ, {ω | ((N + k : ℕ) : ℝ) * ρ ≤ |∑ i ∈ range (N + k), (Z i ω - m)|} := by
    rintro ω ⟨n, hun, hρn⟩
    have hNn : N ≤ n := Nat.ceil_le.mpr hun
    refine Set.mem_iUnion.mpr ⟨n - N, ?_⟩
    rw [show N + (n - N) = n by omega]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    simp only [Set.mem_ofPred_eq]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have : (∑ i ∈ range n, Z i ω) / n - m = ((∑ i ∈ range n, Z i ω) - n * m) / n := by
      field_simp
    rw [this, abs_div, abs_of_pos hn0, lt_div_iff₀ hn0] at hρn
    linarith
  refine (measure_mono hsub).trans ((measure_iUnion_le _).trans ?_)
  have hterm : ∀ k : ℕ, P {ω | ((N + k : ℕ) : ℝ) * ρ ≤ |∑ i ∈ range (N + k), (Z i ω - m)|} ≤
      ENNReal.ofReal (2 * q ^ N * q ^ k) := fun k ↦ by
    refine (measure_mul_le_abs_sum_range_sub_le hind hm hb hmean (by omega) hρ.le).trans_eq ?_
    rw [pow_add, mul_assoc]
  have hsum : Summable fun k : ℕ ↦ 2 * q ^ N * q ^ k :=
    (summable_geometric_of_lt_one hq0.le hq1).mul_left _
  refine (tsum_le_tsum hterm).trans ?_
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k ↦ by positivity) hsum, tsum_mul_left,
    tsum_geometric_of_lt_one hq0.le hq1]
  refine ENNReal.ofReal_le_ofReal ?_
  have hqN : q ^ N ≤ exp (-(2 * ρ ^ 2 * u)) := by
    rw [hq, ← Real.exp_nat_mul, Real.exp_le_exp]
    have : u ≤ N := Nat.le_ceil u
    nlinarith
  have h1q : 0 < 1 - q := by linarith
  rw [div_eq_mul_inv]
  have := inv_pos.mpr h1q
  gcongr

end Incognita
