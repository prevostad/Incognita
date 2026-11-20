/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.Grid
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! # Elementary sums and sequences on a grid

The deterministic lemmas of [INC-P000, Subsection `sec:app-sums`], used by the upper bound of
Theorem `thm:upper`. The batch size `B_ℓ` is `(g.t ℓ : ℝ) - g.t (ℓ - 1)` and `log t_ℓ` is
`Real.log (g.t ℓ)`; the sums over `ℓ ≥ 2` of the paper are written over `Finset.Ico 2 L` for
every `L` (their partial sums), which is the form the proofs use.

* `sub_mul_rpow_neg_le`: `(b - a) b^(-(1+θ)) ≤ (a^(-θ) - b^(-θ)) / θ` for `0 < a ≤ b`, `θ > 0`.
* `rpow_mul_exp_neg_mul_le`: `s^p e^(-cs) ≤ (p / (c e))^p` for `s ≥ 0`, `c, p > 0`.
* `Grid.sum_mul_rpow_le`: Lemma `lem:sums`(i), `∑_{ℓ ≥ 2} B_ℓ t_ℓ^(-(1+θ)) ≤ t_1^(-θ) / θ`.
* `Grid.sum_mul_one_add_log_rpow_le`: Lemma `lem:sums`(ii), with the weight `(1 + log t_ℓ)^p`.
* `Grid.sum_mul_log_pow_four_le`, `Grid.sum_mul_rpow_le_one_add`: Lemma `lem:sums`(vi).
* `sum_range_le_add_integral`, `integral_exp_neg_mul_rpow_inv`: Lemma `lem:sums`(iii), for the
  partial sums of the series.
* `sum_Icc_mul_exp_neg_le`: `∑_(n ≥ 1) n e^(-ρn) ≤ 1/ρ²` (Lemma `lem:controlC`(d)).
* `eventually_rpow_mul_exp_neg_le`, `exists_rpow_mul_exp_neg_le`: `y^A e^(-c y^a / (log y)^b)` is
  eventually at most `y^(-2)`, and bounded on `[1, ∞)` (Step 7 of the proof of Lemma `lem:amb`).
-/

@[expose] public section

open Real Finset Filter

open scoped Topology

namespace Incognita.BatchedBandits

/-- **The mean value step of Lemma `lem:sums`(i)** [INC-P000, proof of Lemma `lem:sums`(i)]:
for `0 < a ≤ b` and `θ > 0`, `(b - a) b^(-(1+θ)) ≤ (a^(-θ) - b^(-θ)) / θ` (the integral of
`s^(-(1+θ))` over `[a, b]`). With `u = b / a`, it is `θ (1 - 1/u) ≤ u^θ - 1`, from
`1 - 1/u ≤ log u` and `1 + θ log u ≤ u^θ`. -/
lemma sub_mul_rpow_neg_le {a b θ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hθ : 0 < θ) :
    (b - a) * b ^ (-(1 + θ)) ≤ (a ^ (-θ) - b ^ (-θ)) / θ := by
  have hb : 0 < b := ha.trans_le hab
  have hu : 0 < b / a := div_pos hb ha
  have h1 : 1 - a / b ≤ Real.log (b / a) := by
    have := Real.one_sub_inv_le_log_of_pos hu
    rwa [inv_div] at this
  have h2 : θ * Real.log (b / a) + 1 ≤ (b / a) ^ θ := by
    rw [rpow_def_of_pos hu]
    have := add_one_le_exp (Real.log (b / a) * θ)
    linarith [mul_comm θ (Real.log (b / a))]
  have hB : 0 < b ^ (-θ) := rpow_pos_of_pos hb _
  have hL : b ^ (-(1 + θ)) = b ^ (-θ) / b := by
    rw [show -(1 + θ) = -θ + (-1) by ring, rpow_add hb, rpow_neg_one, div_eq_mul_inv]
  have hR : a ^ (-θ) = (b / a) ^ θ * b ^ (-θ) := by
    rw [div_rpow hb.le ha.le, rpow_neg hb.le, rpow_neg ha.le]
    have : 0 < b ^ θ := rpow_pos_of_pos hb θ
    field_simp
  rw [hL, hR, le_div_iff₀ hθ]
  have : (b - a) * (b ^ (-θ) / b) = (1 - a / b) * b ^ (-θ) := by
    field_simp
  rw [this]
  have key : θ * (1 - a / b) ≤ (b / a) ^ θ - 1 := by
    nlinarith [mul_le_mul_of_nonneg_left h1 hθ.le]
  nlinarith [mul_le_mul_of_nonneg_right key hB.le]

/-- **Maximum of `s^p e^(-cs)`**: for `s ≥ 0`, `c > 0` and `p > 0`,
`s^p e^(-cs) ≤ (p / (c e))^p` (the maximum is at `s = p / c`); it is `log x ≤ x - 1` at
`x = c s / p`. -/
lemma rpow_mul_exp_neg_mul_le {s c p : ℝ} (hs : 0 ≤ s) (hc : 0 < c) (hp : 0 < p) :
    s ^ p * Real.exp (-(c * s)) ≤ (p / (c * Real.exp 1)) ^ p := by
  rcases hs.eq_or_lt with rfl | hs
  · rw [zero_rpow hp.ne', zero_mul]
    exact rpow_nonneg (div_nonneg hp.le (mul_pos hc (exp_pos 1)).le) _
  have hq : 0 < p / (c * Real.exp 1) := div_pos hp (mul_pos hc (exp_pos 1))
  rw [rpow_def_of_pos hs, rpow_def_of_pos hq, ← Real.exp_add, Real.exp_le_exp]
  have hx : Real.log (c * s / p) ≤ c * s / p - 1 :=
    Real.log_le_sub_one_of_pos (div_pos (mul_pos hc hs) hp)
  rw [Real.log_div (mul_pos hc hs).ne' hp.ne', Real.log_mul hc.ne' hs.ne'] at hx
  rw [Real.log_div hp.ne' (mul_pos hc (exp_pos 1)).ne', Real.log_mul hc.ne' (exp_pos 1).ne',
    Real.log_exp]
  have : p * (Real.log c + Real.log s - Real.log p) ≤ p * (c * s / p - 1) :=
    mul_le_mul_of_nonneg_left hx hp.le
  have hcs : p * (c * s / p - 1) = c * s - p := by field_simp
  nlinarith

/-- `(1 + y)^p e^(-θ y / 2) ≤ e^(θ/2) (2p / (e θ))^p` for `y ≥ 0`, `θ, p > 0`
[INC-P000, proof of Lemma `lem:sums`(ii)]. -/
lemma one_add_rpow_mul_exp_neg_le {y θ p : ℝ} (hy : 0 ≤ y) (hθ : 0 < θ) (hp : 0 < p) :
    (1 + y) ^ p * Real.exp (-(θ * y / 2)) ≤
      Real.exp (θ / 2) * (2 * p / (Real.exp 1 * θ)) ^ p := by
  have h := rpow_mul_exp_neg_mul_le (s := 1 + y) (c := θ / 2) (by linarith) (by linarith) hp
  have he : Real.exp (-(θ * y / 2)) = Real.exp (θ / 2) * Real.exp (-(θ / 2 * (1 + y))) := by
    rw [← Real.exp_add]
    ring_nf
  have hc : p / (θ / 2 * Real.exp 1) = 2 * p / (Real.exp 1 * θ) := by
    field_simp
  rw [he, ← hc]
  calc (1 + y) ^ p * (Real.exp (θ / 2) * Real.exp (-(θ / 2 * (1 + y))))
      = Real.exp (θ / 2) * ((1 + y) ^ p * Real.exp (-(θ / 2 * (1 + y)))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (exp_pos _).le

/-- [INC-P000, Lemma `lem:sums`(iii), first claim] If `f ≥ 0` is nonincreasing on `[0, ∞)` and
integrable on `(0, ∞)`, every partial sum of `∑_{n ≥ 0} f(n)` is at most `f(0) + ∫_0^∞ f`. -/
lemma sum_range_le_add_integral {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ x → 0 ≤ f x)
    (hf : AntitoneOn f (Set.Ici 0)) (hfi : MeasureTheory.IntegrableOn f (Set.Ioi 0)) (N : ℕ) :
    ∑ n ∈ Finset.range N, f n ≤ f 0 + ∫ x in Set.Ioi (0 : ℝ), f x := by
  rcases N with _ | N
  · simp only [Finset.range_zero, Finset.sum_empty]
    have : 0 ≤ ∫ x in Set.Ioi (0 : ℝ), f x :=
      MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun x hx ↦ hf0 x (le_of_lt hx)
    linarith [hf0 0 le_rfl]
  rw [Finset.sum_range_succ']
  have h1 := (hf.mono (Set.Icc_subset_Ici_self.trans le_rfl : Set.Icc (0 : ℝ) (0 + N) ⊆
    Set.Ici 0)).sum_le_integral
  simp only [zero_add] at h1
  have h2 : ∫ x in (0 : ℝ)..N, f x ≤ ∫ x in Set.Ioi (0 : ℝ), f x := by
    rw [intervalIntegral.integral_of_le (Nat.cast_nonneg N)]
    exact MeasureTheory.setIntegral_mono_set hfi
      ((MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
        (MeasureTheory.ae_of_all _ fun x hx ↦ hf0 x (le_of_lt hx)))
      (MeasureTheory.ae_of_all _ Set.Ioc_subset_Ioi_self)
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at h1 ⊢
  have : ∑ i ∈ Finset.range N, f (↑i + 1) ≤ ∫ x in (0 : ℝ)..N, f x := by
    convert h1 using 2
  linarith

/-- [INC-P000, Lemma `lem:sums`(iii), second claim] For `c, p > 0`,
`∫_0^∞ e^(-c s^(1/p)) ds = Γ(p + 1) c^(-p)`. -/
lemma integral_exp_neg_mul_rpow_inv {c p : ℝ} (hc : 0 < c) (hp : 0 < p) :
    ∫ s in Set.Ioi (0 : ℝ), Real.exp (-c * s ^ (1 / p)) = Real.Gamma (p + 1) * c ^ (-p) := by
  rw [integral_exp_neg_mul_rpow (by positivity) hc]
  have : 1 / (1 / p) = p := by field_simp
  rw [this, show -1 / (1 / p) = -p by field_simp, mul_comm]

/-- [INC-P000, proof of Lemma `lem:controlC`(d), the series] For `ρ > 0` and every `M`,
`∑_(1 ≤ n ≤ M) n e^(-ρ n) ≤ e^(-ρ) / (1 - e^(-ρ))² ≤ 1 / ρ²`, since
`(1 - e^(-ρ))² ≥ e^(-ρ) ρ²` (`e^(ρ/2) - e^(-ρ/2) = 2 sinh (ρ/2) ≥ ρ`). -/
lemma sum_Icc_mul_exp_neg_le {ρ : ℝ} (hρ : 0 < ρ) (M : ℕ) :
    ∑ n ∈ Finset.Icc 1 M, (n : ℝ) * Real.exp (-(ρ * n)) ≤ 1 / ρ ^ 2 := by
  set q := Real.exp (-ρ) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hpow : ∀ n : ℕ, Real.exp (-(ρ * n)) = q ^ n := fun n ↦ by
    rw [hq, ← Real.exp_nat_mul]
    ring_nf
  simp_rw [hpow]
  have hnorm : ‖q‖ < 1 := by rw [Real.norm_of_nonneg hq0.le]; exact hq1
  have hsum := hasSum_coe_mul_geometric_of_norm_lt_one hnorm
  have h1 : ∑ n ∈ Finset.Icc 1 M, (n : ℝ) * q ^ n ≤ q / (1 - q) ^ 2 :=
    sum_le_hasSum _ (fun n _ ↦ by positivity) hsum
  refine h1.trans ?_
  -- `(1 - q)² ≥ q ρ²`
  set s := Real.exp (-(ρ / 2)) with hs
  have hs0 : 0 < s := Real.exp_pos _
  have hqs : q = s ^ 2 := by
    rw [hq, hs, sq, ← Real.exp_add]
    ring_nf
  have hsinh : ρ ≤ Real.exp (ρ / 2) - s := by
    have h := Real.self_le_sinh_iff.mpr (show 0 ≤ ρ / 2 by linarith)
    rw [Real.sinh_eq] at h
    rw [hs]
    linarith
  have hes : Real.exp (ρ / 2) * s = 1 := by
    rw [hs, ← Real.exp_add]
    simp
  have h1q : 1 - q = s * (Real.exp (ρ / 2) - s) := by
    rw [hqs]
    nlinarith [hes]
  have hpos : 0 < 1 - q := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, h1q]
  have hρs : s * ρ ≤ s * (Real.exp (ρ / 2) - s) := mul_le_mul_of_nonneg_left hsinh hs0.le
  have hρs0 : 0 ≤ s * ρ := by positivity
  calc q * ρ ^ 2 = (s * ρ) ^ 2 := by rw [hqs]; ring
    _ ≤ (s * (Real.exp (ρ / 2) - s)) ^ 2 := by gcongr

open Filter in
/-- [INC-P000, proof of Lemma `lem:amb`, Step 7, the decay] For `c, a > 0` and real `A`, `b`,
eventually `y^A e^(-c y^a / (log y)^b) ≤ y^(-2)`: `(log y)^(b+1) = o(y^a)`. (The terms
`2π`, `p_A`, `p̄_K` of the paper, multiplied by the polynomial cost `c(y)`, are of this form with
`(a, b) = (1, 0)`, `(β - 1/2, 0)` and `(1/2, 2)`.) -/
lemma eventually_rpow_mul_exp_neg_le {A c a b : ℝ} (hc : 0 < c) (ha : 0 < a) :
    ∀ᶠ y in atTop, y ^ A * Real.exp (-(c * y ^ a / Real.log y ^ b)) ≤ y ^ (-2 : ℝ) := by
  have hlo := (isLittleO_log_rpow_rpow_atTop (b + 1) ha).bound
    (show 0 < c / (|A + 2| + 1) by positivity)
  filter_upwards [hlo, eventually_gt_atTop (Real.exp 1)] with y hy hye
  have hy0 : 0 < y := lt_trans (Real.exp_pos 1) hye
  have hlog1 : 1 < Real.log y := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) hye
  have hlog0 : 0 < Real.log y := by linarith
  have hlb : 0 < Real.log y ^ b := Real.rpow_pos_of_pos hlog0 b
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog0.le _),
    Real.norm_of_nonneg (Real.rpow_nonneg hy0.le _)] at hy
  -- `(A + 2) log y ≤ c y^a / (log y)^b`
  have hkey : (A + 2) * Real.log y ≤ c * y ^ a / Real.log y ^ b := by
    rw [le_div_iff₀ hlb]
    have h1 : Real.log y ^ (b + 1) = Real.log y ^ b * Real.log y := by
      rw [Real.rpow_add hlog0, Real.rpow_one]
    have hya : 0 ≤ y ^ a := Real.rpow_nonneg hy0.le a
    have h2 : (|A + 2| + 1) * Real.log y ^ (b + 1) ≤ c * y ^ a := by
      have := mul_le_mul_of_nonneg_left hy (by positivity : (0 : ℝ) ≤ |A + 2| + 1)
      rwa [← mul_assoc, mul_div_cancel₀ _ (by positivity)] at this
    have h3 : (A + 2) * Real.log y * Real.log y ^ b ≤ (|A + 2| + 1) * Real.log y ^ (b + 1) := by
      rw [h1]
      have : (A + 2) ≤ |A + 2| + 1 := by linarith [le_abs_self (A + 2)]
      have hpos : 0 ≤ Real.log y ^ b * Real.log y := by positivity
      nlinarith
    linarith
  rw [Real.rpow_def_of_pos hy0 A, Real.rpow_def_of_pos hy0 (-2), ← Real.exp_add, Real.exp_le_exp]
  linarith

/-- [INC-P000, proof of Lemma `lem:amb`, Step 7] For `A ≥ 0` and `c, a > 0`, the function
`y^A exp(-c y^a / (log y)^b)` is bounded on `[1, ∞)` and at most `y^(-2)` from some `y₀` on
(`eventually_rpow_mul_exp_neg_le`; the exponential is at most `1` on `[1, ∞)`). -/
lemma exists_rpow_mul_exp_neg_le {A c a b : ℝ} (hA : 0 ≤ A) (hc : 0 < c) (ha : 0 < a) :
    ∃ y₀ F : ℝ, (∀ y, y₀ ≤ y →
        y ^ A * Real.exp (-(c * y ^ a / Real.log y ^ b)) ≤ y ^ (-2 : ℝ)) ∧
      ∀ y, 1 ≤ y → y ^ A * Real.exp (-(c * y ^ a / Real.log y ^ b)) ≤ F := by
  obtain ⟨y₁, hy₁⟩ :=
    Filter.eventually_atTop.mp (eventually_rpow_mul_exp_neg_le (A := A) (b := b) hc ha)
  refine ⟨max y₁ 1, max y₁ 1 ^ A + 1, fun y hy ↦ hy₁ y (le_of_max_le_left hy), fun y hy ↦ ?_⟩
  have hy0 : 0 < y := by linarith
  have hM0 : 0 ≤ max y₁ 1 ^ A := Real.rpow_nonneg (zero_le_one.trans (le_max_right _ _)) A
  by_cases h : max y₁ 1 ≤ y
  · have h1 : y ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy (by norm_num)
    have := hy₁ y (le_of_max_le_left h)
    linarith
  · push Not at h
    have he : Real.exp (-(c * y ^ a / Real.log y ^ b)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg
        (mul_nonneg hc.le (Real.rpow_nonneg hy0.le a))
        (Real.rpow_nonneg (Real.log_nonneg hy) b)))
    have hyA : y ^ A ≤ max y₁ 1 ^ A := Real.rpow_le_rpow hy0.le h.le hA
    have hyA0 : 0 ≤ y ^ A := Real.rpow_nonneg hy0.le A
    calc y ^ A * Real.exp (-(c * y ^ a / Real.log y ^ b)) ≤ y ^ A * 1 :=
          mul_le_mul_of_nonneg_left he hyA0
      _ ≤ max y₁ 1 ^ A + 1 := by linarith

variable {K : ℕ}

namespace Grid

variable (g : Grid K)

/-- The telescoping form of Lemma `lem:sums`(i):
`∑_{2 ≤ ℓ < L + 2} B_ℓ t_ℓ^(-(1+θ)) ≤ (t_1^(-θ) - t_(L+1)^(-θ)) / θ`. -/
lemma sum_Ico_mul_rpow_le_sub {θ : ℝ} (hθ : 0 < θ) (L : ℕ) :
    ∑ ℓ ∈ Finset.Ico 2 (L + 2), ((g.t ℓ : ℝ) - g.t (ℓ - 1)) * (g.t ℓ : ℝ) ^ (-(1 + θ)) ≤
      ((g.t 1 : ℝ) ^ (-θ) - (g.t (L + 1) : ℝ) ^ (-θ)) / θ := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [show L + 1 + 2 = L + 2 + 1 by ring, Finset.sum_Ico_succ_top (by omega : 2 ≤ L + 2),
      show L + 2 - 1 = L + 1 by omega, show L + 1 + 1 = L + 2 by ring]
    have hstep := sub_mul_rpow_neg_le (g.t_pos (ℓ := L + 1) (by omega))
      (g.t_le_t (Nat.le_succ (L + 1))) hθ
    calc _ ≤ ((g.t 1 : ℝ) ^ (-θ) - (g.t (L + 1) : ℝ) ^ (-θ)) / θ +
          ((g.t (L + 1) : ℝ) ^ (-θ) - (g.t (L + 2) : ℝ) ^ (-θ)) / θ := add_le_add ih hstep
      _ = _ := by ring

/-- [INC-P000, Lemma `lem:sums`(i)] For `θ > 0`, `∑_{ℓ ≥ 2} B_ℓ t_ℓ^(-(1+θ)) ≤ t_1^(-θ) / θ`:
`B_ℓ t_ℓ^(-(1+θ))` is at most the integral of `s^(-(1+θ))` over `[t_(ℓ-1), t_ℓ]`. -/
lemma sum_mul_rpow_le {θ : ℝ} (hθ : 0 < θ) (L : ℕ) :
    ∑ ℓ ∈ Finset.Ico 2 L, ((g.t ℓ : ℝ) - g.t (ℓ - 1)) * (g.t ℓ : ℝ) ^ (-(1 + θ)) ≤
      (g.t 1 : ℝ) ^ (-θ) / θ := by
  rcases Nat.lt_or_ge L 2 with hL | hL
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    exact div_nonneg (rpow_nonneg (Nat.cast_nonneg _) _) hθ.le
  · obtain ⟨L, rfl⟩ := Nat.exists_eq_add_of_le' hL
    refine (g.sum_Ico_mul_rpow_le_sub hθ L).trans ?_
    gcongr
    exact sub_le_self _ (rpow_nonneg (Nat.cast_nonneg _) _)

/-- [INC-P000, Lemma `lem:sums`(i), second inequality] `t_1^(-θ) / θ ≤ 1 / θ`. -/
lemma rpow_neg_div_le {θ : ℝ} (hθ : 0 < θ) : (g.t 1 : ℝ) ^ (-θ) / θ ≤ 1 / θ := by
  gcongr
  exact rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (show 1 ≤ g.t 1 by
    have := g.two_le_t_one; omega)) (by linarith)

/-- A nonnegative weight `w_ℓ` with `w_ℓ t_ℓ^(-θ/2) ≤ C` gives
`∑_{ℓ ≥ 2} B_ℓ w_ℓ t_ℓ^(-(1+θ)) ≤ 2C / θ` (Lemma `lem:sums`(i) with `θ / 2`). -/
lemma sum_mul_weight_rpow_le {θ C : ℝ} (hθ : 0 < θ) {w : ℕ → ℝ} (hC : 0 ≤ C)
    (hw : ∀ ℓ, 1 ≤ ℓ → w ℓ * (g.t ℓ : ℝ) ^ (-(θ / 2)) ≤ C) (L : ℕ) :
    ∑ ℓ ∈ Finset.Ico 2 L, ((g.t ℓ : ℝ) - g.t (ℓ - 1)) * w ℓ * (g.t ℓ : ℝ) ^ (-(1 + θ)) ≤
      2 / θ * C := by
  have hsum := g.sum_mul_rpow_le (θ := θ / 2) (by linarith) L
  have hone := g.rpow_neg_div_le (θ := θ / 2) (by linarith)
  calc _ ≤ ∑ ℓ ∈ Finset.Ico 2 L, C * (((g.t ℓ : ℝ) - g.t (ℓ - 1)) *
        (g.t ℓ : ℝ) ^ (-(1 + θ / 2))) := by
        refine Finset.sum_le_sum fun ℓ hℓ ↦ ?_
        have hℓ2 : 2 ≤ ℓ := (Finset.mem_Ico.mp hℓ).1
        have ht := g.t_pos (ℓ := ℓ) (by omega)
        have hB : 0 ≤ (g.t ℓ : ℝ) - g.t (ℓ - 1) := sub_nonneg.mpr (g.t_le_t (by omega))
        have hsplit : (g.t ℓ : ℝ) ^ (-(1 + θ)) =
            (g.t ℓ : ℝ) ^ (-(θ / 2)) * (g.t ℓ : ℝ) ^ (-(1 + θ / 2)) := by
          rw [← rpow_add ht]
          ring_nf
        rw [hsplit]
        have hpos : 0 ≤ (g.t ℓ : ℝ) ^ (-(1 + θ / 2)) := (rpow_pos_of_pos ht _).le
        calc ((g.t ℓ : ℝ) - g.t (ℓ - 1)) * w ℓ *
              ((g.t ℓ : ℝ) ^ (-(θ / 2)) * (g.t ℓ : ℝ) ^ (-(1 + θ / 2)))
            = (w ℓ * (g.t ℓ : ℝ) ^ (-(θ / 2))) *
              (((g.t ℓ : ℝ) - g.t (ℓ - 1)) * (g.t ℓ : ℝ) ^ (-(1 + θ / 2))) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (hw ℓ (by omega)) (mul_nonneg hB hpos)
    _ = C * ∑ ℓ ∈ Finset.Ico 2 L, ((g.t ℓ : ℝ) - g.t (ℓ - 1)) *
        (g.t ℓ : ℝ) ^ (-(1 + θ / 2)) := by rw [Finset.mul_sum]
    _ ≤ C * (1 / (θ / 2)) := mul_le_mul_of_nonneg_left (hsum.trans hone) hC
    _ = 2 / θ * C := by field_simp

/-- `t^(-θ/2) = e^(-θ log t / 2)` for `t > 0`. -/
lemma rpow_neg_half_eq_exp {θ : ℝ} {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    (g.t ℓ : ℝ) ^ (-(θ / 2)) = Real.exp (-(θ * Real.log (g.t ℓ) / 2)) := by
  rw [rpow_def_of_pos (g.t_pos hℓ)]
  ring_nf

/-- [INC-P000, Lemma `lem:sums`(ii)] For `p > 0` and `θ > 0`,
`∑_{ℓ ≥ 2} B_ℓ (1 + log t_ℓ)^p t_ℓ^(-(1+θ)) ≤ σ_p(θ) = (2/θ) e^(θ/2) (2p / (e θ))^p`. -/
lemma sum_mul_one_add_log_rpow_le {p θ : ℝ} (hp : 0 < p) (hθ : 0 < θ) (L : ℕ) :
    ∑ ℓ ∈ Finset.Ico 2 L, ((g.t ℓ : ℝ) - g.t (ℓ - 1)) * (1 + Real.log (g.t ℓ)) ^ p *
        (g.t ℓ : ℝ) ^ (-(1 + θ)) ≤
      2 / θ * Real.exp (θ / 2) * (2 * p / (Real.exp 1 * θ)) ^ p := by
  rw [mul_assoc (2 / θ)]
  refine g.sum_mul_weight_rpow_le hθ (by positivity) (fun ℓ hℓ ↦ ?_) L
  rw [g.rpow_neg_half_eq_exp hℓ]
  exact one_add_rpow_mul_exp_neg_le (Real.log_nonneg (by exact_mod_cast
    (show 1 ≤ g.t ℓ by have := g.two_le_t hℓ; omega))) hθ hp

/-- [INC-P000, Lemma `lem:sums`(vi), first sum] For `θ > 0`,
`∑_{ℓ ≥ 2} B_ℓ (log t_ℓ)^4 t_ℓ^(-(1+θ)) ≤ (8 / (e θ))^4 (1 + 2/θ)`; the proof gives the bound
`(2/θ) (8 / (e θ))^4`. -/
lemma sum_mul_log_pow_four_le {θ : ℝ} (hθ : 0 < θ) (L : ℕ) :
    ∑ ℓ ∈ Finset.Ico 2 L, ((g.t ℓ : ℝ) - g.t (ℓ - 1)) * Real.log (g.t ℓ) ^ 4 *
        (g.t ℓ : ℝ) ^ (-(1 + θ)) ≤
      (8 / (Real.exp 1 * θ)) ^ 4 * (1 + 2 / θ) := by
  have hC : 0 ≤ (8 / (Real.exp 1 * θ)) ^ 4 := by positivity
  refine (g.sum_mul_weight_rpow_le hθ hC (fun ℓ hℓ ↦ ?_) L).trans ?_
  · rw [g.rpow_neg_half_eq_exp hℓ]
    have hy : 0 ≤ Real.log (g.t ℓ) := Real.log_nonneg (by exact_mod_cast
      (show 1 ≤ g.t ℓ by have := g.two_le_t hℓ; omega))
    have h := rpow_mul_exp_neg_mul_le hy (c := θ / 2) (p := 4) (by linarith) (by norm_num)
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, rpow_natCast, rpow_natCast] at h
    have hc : (4 : ℕ) / (θ / 2 * Real.exp 1) = 8 / (Real.exp 1 * θ) := by
      field_simp
      norm_num
    rw [hc] at h
    calc Real.log (g.t ℓ) ^ 4 * Real.exp (-(θ * Real.log (g.t ℓ) / 2))
        = Real.log (g.t ℓ) ^ 4 * Real.exp (-(θ / 2 * Real.log (g.t ℓ))) := by ring_nf
      _ ≤ _ := h
  · have h2 : 2 / θ ≤ 1 + 2 / θ := by linarith
    calc 2 / θ * (8 / (Real.exp 1 * θ)) ^ 4 ≤ (1 + 2 / θ) * (8 / (Real.exp 1 * θ)) ^ 4 :=
          mul_le_mul_of_nonneg_right h2 hC
      _ = _ := mul_comm _ _

/-- [INC-P000, Lemma `lem:sums`(vi), second sum] For `θ > 0`,
`∑_{ℓ ≥ 2} B_ℓ t_ℓ^(-(1+θ)) ≤ 1 + 2/θ` (Lemma `lem:sums`(i) gives `1 / θ`). -/
lemma sum_mul_rpow_le_one_add {θ : ℝ} (hθ : 0 < θ) (L : ℕ) :
    ∑ ℓ ∈ Finset.Ico 2 L, ((g.t ℓ : ℝ) - g.t (ℓ - 1)) * (g.t ℓ : ℝ) ^ (-(1 + θ)) ≤
      1 + 2 / θ := by
  refine ((g.sum_mul_rpow_le hθ L).trans (g.rpow_neg_div_le hθ)).trans ?_
  have : 0 < 1 / θ := by positivity
  have : 1 / θ ≤ 2 / θ := by gcongr; norm_num
  linarith

end Grid

end Incognita.BatchedBandits
