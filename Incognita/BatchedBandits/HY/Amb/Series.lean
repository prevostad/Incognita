/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.HY.Amb.Basic

/-! # The failure probabilities of the consistency test, as functions of `L_ℓ`

[INC-P000, proof of Lemma `lem:amb`], Steps 5–6: the bounds on the probabilities of the events
`Acc_ℓ^c` and `KC_ℓ^c` (Definition `def:amb`) depend on `ℓ` only through `y = L_ℓ`, and are at most
explicit functions of `y` whose products with a polynomial cost decay faster than `y^(-2)`
(Step 7, `eventually_rpow_mul_exp_neg_le`).

* `min_div_two_le_one_sub_exp_neg`: `1 - e^(-v) ≥ min(v, 1) / 2` for `v ≥ 0`.
* `one_add_ceil_mul_exp_neg_div_le`: Step 6. With `ζ'_ℓ = (Δ/32) y^(-1/4)`, `R'_ℓ = κ(μ) - log(1 -
  e^(-ζ'_ℓ/4))`,
  `ρ'_ℓ = ζ'_ℓ² / (2 R'_ℓ²)`, `n^g_ℓ = ⌈8 / (ζ'_ℓ (1 - e^(-ζ'_ℓ/4)) (1 - μ))⌉ + 1` and
  `n_ℓ ≥ c₂ y`: for `y ≥ 16`, the bound `p_K = (1 + n^g_ℓ) e^(-ρ'_ℓ n_ℓ) / (1 - e^(-ρ'_ℓ))` of
  `measure_exists_mem_le_pullCount_pseudoKinf_lt_or_lt_le` (at `μ = m⋆`, `ε' = ζ'_ℓ`, `u = n_ℓ`) is
  at most
  `p̄_K(y) = C₂ (1 + 1/c₁) y log² y exp(-c₁ c₂ √y / log² y)`, with the paper's constants
  `a₀ = min(Δ/128, 1)`, `A₁ = 1/4 + (κ(μ) + log(2/a₀)) / log 16`, `c₁ = Δ² / (2048 A₁²)` and
  `C₂ = 3 + 512 / (Δ a₀ (1 - μ))`.
* `mul_exp_neg_div_one_sub_exp_neg_le`: Step 5, the event `Acc_ℓ^c`. With `ζ_ℓ = c_ζ y^(-1/4)` and
  `U_(ℓ-1) ≥ (y/4)^β`, the
  bound `K · 2 e^(-2ζ_ℓ² u) / (1 - e^(-2ζ_ℓ²))` of `measure_exists_mem_le_pullCount_abs_sub_gt_le`
  at `u = U_(ℓ-1)/2` is at most `p_A(y) = 2K (1 + √y / (2c_ζ²)) exp(-c_ζ² 4^(-β) y^(β-1/2))`.
* `exists_rpow_mul_exp_neg_le`, `rpow_add_mul_sum_exp_neg_le`,
  `Grid.exists_sum_activated_rpow_add_mul_exp_neg_le`: Step 7 for the
  paper's function `f(y) = c(y) (2π(y) + p_A(y) + p̄_K(y))` (`y ≥ 16`; `f = 0` below), with the
  cost `c(y) = y^β + k₀ + k₁ y` and `π(y) = (P₀ + P₁ (1 + (P₂ y)⁴)) e^(-q y)` of
  Definition `def:amb`: `f` is bounded on `[1, ∞)` and eventually `O(y^(-2))`, so its sums over
  the activated batches are bounded (`Grid.exists_sum_activated_le`, Lemma `lem:sparse`). With the
  bound `c_ℓ P(E_ℓ^amb(ε)) ≤ f(L_ℓ)` of Step 5, this is `C₄(ε) < ∞`.

* `mul_exp_neg_le_mul_exp_neg_of_le`: condition (f) of Definition `def:amb`, `π(y) = (P₀ + P₁ (1 +
  (P₂ y)⁴)) e^(-q y)`
  is nonincreasing on `[4/q, ∞)`, so `π(L_(ℓ+1)) ≤ π(L_ℓ)` once `L_ℓ ≥ 4/q`.

The probabilistic part of Step 5 (the eight events of `E_ℓ^amb(ε)` as sets of the trajectory
space, and the union bound) is not here: only the bounds of its terms as functions of `L_ℓ`.
-/

@[expose] public section

open Real

namespace Incognita.BatchedBandits

/-- `min(Δ/128, 1) / (2r) ≤ 1 - e^(-Δ/(128 r))` for `Δ > 0` and `r ≥ 1`
(by `min_div_two_le_one_sub_exp_neg`, and `min(Δ/(128 r), 1) ≥ min(Δ/128, 1) / r`). -/
lemma min_div_mul_le_one_sub_exp_neg {Δ r : ℝ} (hΔ : 0 < Δ) (hr : 1 ≤ r) :
    min (Δ / 128) 1 / (2 * r) ≤ 1 - Real.exp (-(Δ / (32 * r) / 4)) := by
  have hr0 : 0 < r := by linarith
  refine le_trans ?_ (min_div_two_le_one_sub_exp_neg (by positivity : 0 ≤ Δ / (32 * r) / 4))
  have hv : Δ / (32 * r) / 4 = Δ / 128 / r := by field_simp; ring
  rw [hv, div_le_div_iff₀ (by positivity) (by norm_num)]
  rcases le_total (Δ / 128 / r) 1 with h | h
  · rw [min_eq_left h]
    have h1 : min (Δ / 128) 1 ≤ Δ / 128 := min_le_left _ _
    have h2 : Δ / 128 / r * (2 * r) = 2 * (Δ / 128) := by field_simp
    rw [h2]
    linarith
  · rw [min_eq_right h]
    have h1 : min (Δ / 128) 1 ≤ 1 := min_le_right _ _
    have h2 : (1 : ℝ) * 2 ≤ 1 * (2 * r) := by linarith
    calc min (Δ / 128) 1 * 2 ≤ 1 * 2 := by linarith
      _ ≤ 1 * (2 * r) := h2

/-- `κ - log E ≤ (1/4 + (κ + log(2/a₀)) / log 16) log y` when `κ ≥ 0`, `0 < a₀ ≤ 1`,
`E ≥ a₀ / (2r)`, `log r = log y / 4` and `log y ≥ log 16` (the bound `R' ≤ A₁ log y` of Step 6). -/
lemma sub_log_le_mul_log {κ a₀ r y E : ℝ} (hκ : 0 ≤ κ) (ha₀ : 0 < a₀) (ha₀1 : a₀ ≤ 1)
    (hr : 0 < r) (hE : a₀ / (2 * r) ≤ E) (hlogr : Real.log r = Real.log y / 4)
    (hy : Real.log 16 ≤ Real.log y) :
    κ - Real.log E ≤ (1 / 4 + (κ + Real.log (2 / a₀)) / Real.log 16) * Real.log y := by
  have hlog16 : 0 < Real.log 16 := Real.log_pos (by norm_num)
  have hlog2a : 0 ≤ Real.log (2 / a₀) := Real.log_nonneg (by rw [le_div_iff₀ ha₀]; linarith)
  have h1 : -Real.log E ≤ Real.log (2 / a₀) + Real.log y / 4 := by
    have h2 : Real.log (a₀ / (2 * r)) ≤ Real.log E := Real.log_le_log (by positivity) hE
    have h3 : Real.log (a₀ / (2 * r)) = -(Real.log (2 / a₀) + Real.log r) := by
      rw [← Real.log_mul (by positivity) hr.ne', ← Real.log_inv]
      congr 1
      field_simp
    rw [h3, hlogr] at h2
    linarith
  have h4 : κ + Real.log (2 / a₀) ≤ (κ + Real.log (2 / a₀)) / Real.log 16 * Real.log y := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog16]
    exact mul_le_mul_of_nonneg_left hy (by positivity)
  have h5 : (1 / 4 + (κ + Real.log (2 / a₀)) / Real.log 16) * Real.log y =
      Real.log y / 4 + (κ + Real.log (2 / a₀)) / Real.log 16 * Real.log y := by ring
  rw [h5]
  linarith

/-- `1 + (⌈8 / (ζE(1 - μ))⌉ + 1) ≤ (3 + 512 / (Δ a₀ (1 - μ))) r²` when `ζE ≥ Δ a₀ / (64 r²)`
and `r ≥ 1` (the bound `1 + n^g ≤ C₂ √y` of Step 6). -/
lemma one_add_ceil_le_mul_sq {Δ a₀ μ ζ E r : ℝ} (hΔ : 0 < Δ) (ha₀ : 0 < a₀) (hμ : μ < 1)
    (hζE : Δ * a₀ / (64 * r ^ 2) ≤ ζ * E) (hr : 1 ≤ r) :
    (1 : ℝ) + ((⌈8 / (ζ * E * (1 - μ))⌉₊ + 1 : ℕ) : ℝ) ≤
      (3 + 512 / (Δ * a₀ * (1 - μ))) * r ^ 2 := by
  have h1μ : 0 < 1 - μ := by linarith
  have hr0 : 0 < r := by linarith
  have hζE0 : 0 < ζ * E := lt_of_lt_of_le (by positivity) hζE
  have hx0 : 0 ≤ 8 / (ζ * E * (1 - μ)) := (div_pos (by norm_num) (by positivity)).le
  have hceil := Nat.ceil_lt_add_one hx0
  have h1 : 8 / (ζ * E * (1 - μ)) ≤ 512 / (Δ * a₀ * (1 - μ)) * r ^ 2 := by
    calc 8 / (ζ * E * (1 - μ)) ≤ 8 / (Δ * a₀ / (64 * r ^ 2) * (1 - μ)) := by
          gcongr
      _ = 512 / (Δ * a₀ * (1 - μ)) * r ^ 2 := by field_simp; ring
  have h3 : (3 : ℝ) ≤ 3 * r ^ 2 := by
    have : (1 : ℝ) ≤ r ^ 2 := one_le_pow₀ hr
    linarith
  push_cast
  rw [add_mul]
  linarith

/-- [INC-P000, proof of Lemma `lem:amb`, Step 6, an explicit bound on `p_K`] Let `Δ > 0`,
`μ ∈ [0, 1)`, `y ≥ 16`, `c₂ > 0` and `u ≥ c₂ y`, and set `ζ' = (Δ/32) y^(-1/4)`,
`R' = κ(μ) - log(1 - e^(-ζ'/4))` (`κ(μ) = log (1/(1 - μ))`), `ρ' = ζ'² / (2R'²)`. With
`a₀ = min(Δ/128, 1)`, `A₁ = 1/4 + (κ(μ) + log(2/a₀)) / log 16`, `c₁ = Δ² / (2048 A₁²)` and
`C₂ = 3 + 512 / (Δ a₀ (1 - μ))`,
`(1 + n^g) e^(-ρ' u) / (1 - e^(-ρ')) ≤ C₂ (1 + 1/c₁) y log² y exp(-c₁ c₂ √y / log² y)`, where
`n^g = ⌈8 / (ζ' (1 - e^(-ζ'/4)) (1 - μ))⌉ + 1`. The left side is the sum of the two bounds of
`measure_exists_mem_le_pullCount_pseudoKinf_lt_or_lt_le` at `ε' = ζ'` (the paper's `p_K(L_ℓ)` with
`u = n_ℓ`, `c₂ = c₂(ε)`). -/
lemma one_add_ceil_mul_exp_neg_div_le {Δ μ y c₂ u ζ R ρ a₀ A₁ c₁ C₂ : ℝ} (hΔ : 0 < Δ) (hμ0 : 0 ≤ μ)
    (hμ : μ < 1)
    (hy : 16 ≤ y) (hc₂ : 0 < c₂) (hu : c₂ * y ≤ u)
    (hζ : ζ = Δ / 32 * y ^ (-(1 / 4 : ℝ)))
    (hR : R = Real.log (1 / (1 - μ)) - Real.log (1 - Real.exp (-(ζ / 4))))
    (hρ : ρ = ζ ^ 2 / (2 * R ^ 2)) (ha₀ : a₀ = min (Δ / 128) 1)
    (hA₁ : A₁ = 1 / 4 + (Real.log (1 / (1 - μ)) + Real.log (2 / a₀)) / Real.log 16)
    (hc₁ : c₁ = Δ ^ 2 / (2048 * A₁ ^ 2)) (hC₂ : C₂ = 3 + 512 / (Δ * a₀ * (1 - μ))) :
    Real.exp (-(ρ * u)) / (1 - Real.exp (-ρ)) +
        ((⌈8 / (ζ * (1 - Real.exp (-(ζ / 4))) * (1 - μ))⌉₊ + 1 : ℕ) : ℝ) *
          Real.exp (-(ρ * u)) / (1 - Real.exp (-ρ)) ≤
      C₂ * (1 + 1 / c₁) * y * Real.log y ^ 2 *
        Real.exp (-(c₁ * c₂ * Real.sqrt y / Real.log y ^ 2)) := by
  have hy0 : 0 < y := by linarith
  -- `r = y^(1/4)`, `y^(-1/4) = 1/r`, `√y = r²`
  set r := y ^ (1 / 4 : ℝ) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hy0 _
  have hr4 : r ^ 4 = y := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hy0.le]
    norm_num
  have hs : y ^ (-(1 / 4 : ℝ)) = 1 / r := by rw [Real.rpow_neg hy0.le, ← hr, one_div]
  have hsq : Real.sqrt y = r ^ 2 := by
    rw [← hr4, show r ^ 4 = (r ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hr2 : 2 ≤ r := by
    by_contra h
    push Not at h
    have : r ^ 4 < 2 ^ 4 := by gcongr
    linarith
  have hlogr : Real.log r = Real.log y / 4 := by
    rw [hr, Real.log_rpow hy0]
    ring
  -- `log y ≥ log 16 > 1`
  have hlog16 : 1 < Real.log 16 := by
    rw [← Real.log_exp 1]
    refine Real.log_lt_log (Real.exp_pos 1) ?_
    have := Real.exp_one_lt_d9
    linarith
  have hlogy : Real.log 16 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  have hlogy1 : 1 < Real.log y := by linarith
  have hlogy0 : 0 < Real.log y := by linarith
  -- the constants
  have ha₀0 : 0 < a₀ := by rw [ha₀]; exact lt_min (by positivity) one_pos
  have ha₀1 : a₀ ≤ 1 := by rw [ha₀]; exact min_le_right _ _
  have hκ0 : 0 ≤ Real.log (1 / (1 - μ)) :=
    Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
  have hlog2a : 0 ≤ Real.log (2 / a₀) :=
    Real.log_nonneg (by rw [le_div_iff₀ ha₀0]; linarith)
  have hA₁0 : 0 < A₁ := by rw [hA₁]; positivity
  have hc₁0 : 0 < c₁ := by rw [hc₁]; positivity
  have h1μ : 0 < 1 - μ := by linarith
  -- `ζ = Δ / (32 r)` and `E = 1 - e^(-ζ/4) ≥ a₀ / (2r)`
  have hζ' : ζ = Δ / (32 * r) := by rw [hζ, hs]; field_simp
  have hζ0 : 0 < ζ := by rw [hζ']; positivity
  set E := 1 - Real.exp (-(ζ / 4)) with hE
  have hE1 : E < 1 := by have := Real.exp_pos (-(ζ / 4)); linarith
  have hEa : a₀ / (2 * r) ≤ E := by
    rw [hE, ha₀, hζ']
    exact min_div_mul_le_one_sub_exp_neg hΔ (by linarith)
  have hE0 : 0 < E := lt_of_lt_of_le (by positivity) hEa
  -- `R ≤ A₁ log y`, `R > 0`
  have hRle : R ≤ A₁ * Real.log y := by
    rw [hR, hA₁]
    exact sub_log_le_mul_log hκ0 ha₀0 ha₀1 hr0 hEa hlogr hlogy
  have hR0 : 0 < R := by
    rw [hR]
    have : Real.log E < 0 := Real.log_neg hE0 hE1
    linarith
  -- `ρ ≥ c₁ / (r² log² y)`
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  have hρge : c₁ / (r ^ 2 * Real.log y ^ 2) ≤ ρ := by
    calc c₁ / (r ^ 2 * Real.log y ^ 2)
        = (Δ / (32 * r)) ^ 2 / (2 * (A₁ * Real.log y) ^ 2) := by
          rw [hc₁]; field_simp; ring
      _ ≤ (Δ / (32 * r)) ^ 2 / (2 * R ^ 2) := by gcongr
      _ = ρ := by rw [hρ, hζ']
  -- `1 / (1 - e^(-ρ)) ≤ (1 + 1/c₁) r² log² y`
  have hgeo : 1 / (1 - Real.exp (-ρ)) ≤ (1 + 1 / c₁) * (r ^ 2 * Real.log y ^ 2) := by
    refine (one_div_one_sub_exp_neg_le hρ0).trans ?_
    have h1 : 1 / ρ ≤ r ^ 2 * Real.log y ^ 2 / c₁ := by
      rw [one_div, inv_le_comm₀ hρ0 (by positivity), inv_div]
      exact hρge
    have h2 : 1 ≤ r ^ 2 * Real.log y ^ 2 :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith)) (one_le_pow₀ hlogy1.le)
    have h3 : r ^ 2 * Real.log y ^ 2 / c₁ = 1 / c₁ * (r ^ 2 * Real.log y ^ 2) := by ring
    calc 1 + 1 / ρ ≤ r ^ 2 * Real.log y ^ 2 + 1 / c₁ * (r ^ 2 * Real.log y ^ 2) :=
          add_le_add h2 (h1.trans_eq h3)
      _ = (1 + 1 / c₁) * (r ^ 2 * Real.log y ^ 2) := by ring
  -- `1 + n^g ≤ C₂ r²`
  have hng : (1 : ℝ) + ((⌈8 / (ζ * E * (1 - μ))⌉₊ + 1 : ℕ) : ℝ) ≤ C₂ * r ^ 2 := by
    have hζE : Δ * a₀ / (64 * r ^ 2) ≤ ζ * E := by
      rw [hζ']
      calc Δ * a₀ / (64 * r ^ 2) = Δ / (32 * r) * (a₀ / (2 * r)) := by field_simp; ring
        _ ≤ Δ / (32 * r) * E := by gcongr
    rw [hC₂]
    exact one_add_ceil_le_mul_sq hΔ ha₀0 hμ hζE (by linarith)
  -- `e^(-ρ u) ≤ exp(-c₁ c₂ r² / log² y)`
  have hexp : Real.exp (-(ρ * u)) ≤ Real.exp (-(c₁ * c₂ * r ^ 2 / Real.log y ^ 2)) := by
    rw [Real.exp_le_exp, neg_le_neg_iff]
    have h1 : c₁ * c₂ * r ^ 2 / Real.log y ^ 2 = c₁ / (r ^ 2 * Real.log y ^ 2) * (c₂ * y) := by
      rw [← hr4]
      field_simp
    rw [h1]
    exact mul_le_mul hρge hu (by positivity) hρ0.le
  -- assembly
  have hsum : Real.exp (-(ρ * u)) / (1 - Real.exp (-ρ)) +
      ((⌈8 / (ζ * E * (1 - μ))⌉₊ + 1 : ℕ) : ℝ) * Real.exp (-(ρ * u)) / (1 - Real.exp (-ρ)) =
      (1 + ((⌈8 / (ζ * E * (1 - μ))⌉₊ + 1 : ℕ) : ℝ)) * Real.exp (-(ρ * u)) *
        (1 / (1 - Real.exp (-ρ))) := by ring
  rw [hsum, hsq]
  have hX0 : 0 ≤ Real.exp (-(ρ * u)) := (Real.exp_pos _).le
  have hgeo0 : 0 ≤ 1 / (1 - Real.exp (-ρ)) := by
    have : Real.exp (-ρ) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    exact (one_div_pos.mpr (by linarith)).le
  calc (1 + ((⌈8 / (ζ * E * (1 - μ))⌉₊ + 1 : ℕ) : ℝ)) * Real.exp (-(ρ * u)) *
        (1 / (1 - Real.exp (-ρ)))
      ≤ C₂ * r ^ 2 * Real.exp (-(c₁ * c₂ * r ^ 2 / Real.log y ^ 2)) *
          ((1 + 1 / c₁) * (r ^ 2 * Real.log y ^ 2)) := by
        have hng0 : (0 : ℝ) ≤ 1 + ((⌈8 / (ζ * E * (1 - μ))⌉₊ + 1 : ℕ) : ℝ) := by positivity
        exact mul_le_mul (mul_le_mul hng hexp hX0 (hng0.trans hng)) hgeo hgeo0
          (mul_nonneg (hng0.trans hng) (Real.exp_pos _).le)
    _ = C₂ * (1 + 1 / c₁) * y * Real.log y ^ 2 *
          Real.exp (-(c₁ * c₂ * r ^ 2 / Real.log y ^ 2)) := by
        rw [← hr4]; ring

/-- [INC-P000, proof of Lemma `lem:amb`, Step 5, the event `Acc_ℓ^c`] Let `K ≥ 0`, `c > 0`,
`y > 0`, `β` real, `ζ = c y^(-1/4)` and `U ≥ (y/4)^β`. The bound
`K · 2 e^(-2ζ² (U/2)) / (1 - e^(-2ζ²))` of `measure_exists_mem_le_pullCount_abs_sub_gt_le` (at the
count `u = U/2`) is at most `p_A(y) = 2K (1 + √y / (2c²)) exp(-c² 4^(-β) y^(β-1/2))`: the paper's
bound with `ζ_ℓ = c_ζ L_ℓ^(-1/4)` (condition (e) of Definition `def:amb`) and
`U_(ℓ-1) ≥ L_(ℓ-2)^β ≥ (L_ℓ/4)^β`. -/
lemma mul_exp_neg_div_one_sub_exp_neg_le {K c y β ζ U : ℝ} (hK : 0 ≤ K) (hc : 0 < c) (hy : 0 < y)
    (hζ : ζ = c * y ^ (-(1 / 4 : ℝ))) (hU : (y / 4) ^ β ≤ U) :
    K * (2 * Real.exp (-(2 * ζ ^ 2 * (U / 2))) / (1 - Real.exp (-(2 * ζ ^ 2)))) ≤
      2 * K * (1 + Real.sqrt y / (2 * c ^ 2)) *
        Real.exp (-(c ^ 2 * (4 : ℝ) ^ (-β) * y ^ (β - 1 / 2))) := by
  have hs2 : (y ^ (-(1 / 4 : ℝ))) ^ 2 = 1 / Real.sqrt y := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hy.le,
      one_div (y ^ (1 / 2 : ℝ)), ← Real.rpow_neg hy.le]
    norm_num
  have hζ2 : ζ ^ 2 = c ^ 2 / Real.sqrt y := by
    rw [hζ, mul_pow, hs2, mul_one_div]
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hζ0 : 0 < ζ ^ 2 := by rw [hζ2]; positivity
  have hgeo := one_div_one_sub_exp_neg_le (by positivity : 0 < 2 * ζ ^ 2)
  have hgeo' : 1 + 1 / (2 * ζ ^ 2) = 1 + Real.sqrt y / (2 * c ^ 2) := by
    rw [hζ2]; field_simp
  have hexp : Real.exp (-(2 * ζ ^ 2 * (U / 2))) ≤
      Real.exp (-(c ^ 2 * (4 : ℝ) ^ (-β) * y ^ (β - 1 / 2))) := by
    rw [Real.exp_le_exp, neg_le_neg_iff]
    have h1 : c ^ 2 * (4 : ℝ) ^ (-β) * y ^ (β - 1 / 2) = ζ ^ 2 * (y / 4) ^ β := by
      rw [hζ2, Real.div_rpow hy.le (by norm_num), Real.rpow_sub hy, Real.rpow_neg (by norm_num),
        Real.sqrt_eq_rpow]
      field_simp
    rw [h1]
    have : ζ ^ 2 * (y / 4) ^ β ≤ ζ ^ 2 * U := mul_le_mul_of_nonneg_left hU hζ0.le
    linarith
  have hX0 : 0 ≤ Real.exp (-(2 * ζ ^ 2 * (U / 2))) := (Real.exp_pos _).le
  have hgeo0 : 0 ≤ 1 / (1 - Real.exp (-(2 * ζ ^ 2))) := by
    have : Real.exp (-(2 * ζ ^ 2)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    exact (one_div_pos.mpr (by linarith)).le
  calc K * (2 * Real.exp (-(2 * ζ ^ 2 * (U / 2))) / (1 - Real.exp (-(2 * ζ ^ 2))))
      = 2 * K * (1 / (1 - Real.exp (-(2 * ζ ^ 2)))) * Real.exp (-(2 * ζ ^ 2 * (U / 2))) := by
        ring
    _ ≤ 2 * K * (1 + Real.sqrt y / (2 * c ^ 2)) *
          Real.exp (-(c ^ 2 * (4 : ℝ) ^ (-β) * y ^ (β - 1 / 2))) := by
        rw [← hgeo']
        gcongr

/-! ### Step 7: the series `C₄(ε)` for the explicit function `f` -/

/-- [INC-P000, proof of Lemma `lem:amb`, Step 7, the terms of `f`] For `y ≥ 1`, with
`m = max(β, 1)`: the cost `c(y) = y^β + k₀ + k₁ y` times
`2π(y) + p_A(y) + p̄_K(y)`, where `π(y) = (P₀ + P₁ (1 + (P₂ y)⁴)) e^(-q y)`,
`p_A(y) = 2K (1 + √y / (2c²)) exp(-c² 4^(-β) y^(β-1/2))` and
`p̄_K(y) = D y log² y exp(-c₃ √y / log² y)`, is at most a combination with nonnegative
coefficients of `y^(m+4) e^(-q y)`, `y^(m+1) exp(-c² 4^(-β) y^(β-1/2))` and
`y^(m+2) exp(-c₃ √y / log² y)` (each written in the form of `exists_rpow_mul_exp_neg_le`). -/
lemma rpow_add_mul_sum_exp_neg_le {β k₀ k₁ P₀ P₁ P₂ q K c D c₃ y : ℝ} (hk₀ : 0 ≤ k₀) (hk₁ : 0 ≤ k₁)
    (hP₀ : 0 ≤ P₀) (hP₁ : 0 ≤ P₁) (hK : 0 ≤ K) (hc : 0 < c) (hD : 0 ≤ D) (hy : 1 ≤ y) :
    (y ^ β + k₀ + k₁ * y) * (2 * ((P₀ + P₁ * (1 + (P₂ * y) ^ 4)) * Real.exp (-(q * y))) +
        2 * K * (1 + Real.sqrt y / (2 * c ^ 2)) *
          Real.exp (-(c ^ 2 * (4 : ℝ) ^ (-β) * y ^ (β - 1 / 2))) +
        D * y * Real.log y ^ 2 * Real.exp (-(c₃ * Real.sqrt y / Real.log y ^ 2))) ≤
      2 * (1 + k₀ + k₁) * (P₀ + P₁ * (1 + P₂ ^ 4)) *
          (y ^ (max β 1 + (4 : ℕ)) * Real.exp (-(q * y ^ (1 : ℝ) / Real.log y ^ (0 : ℝ)))) +
        2 * (1 + k₀ + k₁) * K * (1 + 1 / (2 * c ^ 2)) *
          (y ^ (max β 1 + (1 : ℕ)) * Real.exp (-(c ^ 2 * (4 : ℝ) ^ (-β) * y ^ (β - 1 / 2) /
            Real.log y ^ (0 : ℝ)))) +
        (1 + k₀ + k₁) * D *
          (y ^ (max β 1 + (2 : ℕ)) *
            Real.exp (-(c₃ * y ^ (1 / 2 : ℝ) / Real.log y ^ (2 : ℝ)))) := by
  have hy0 : 0 < y := by linarith
  set m := max β 1 with hm
  have hm0 : 0 ≤ m := zero_le_one.trans (le_max_right _ _)
  rw [Real.rpow_add_natCast hy0.ne', Real.rpow_add_natCast hy0.ne', Real.rpow_add_natCast hy0.ne',
    Real.rpow_one, Real.rpow_zero, div_one, div_one, ← Real.sqrt_eq_rpow, Real.rpow_two]
  set e₁ := Real.exp (-(q * y)) with he₁
  set e₂ := Real.exp (-(c ^ 2 * (4 : ℝ) ^ (-β) * y ^ (β - 1 / 2))) with he₂
  set e₃ := Real.exp (-(c₃ * Real.sqrt y / Real.log y ^ 2)) with he₃
  have he₁0 : 0 ≤ e₁ := (Real.exp_pos _).le
  have he₂0 : 0 ≤ e₂ := (Real.exp_pos _).le
  have he₃0 : 0 ≤ e₃ := (Real.exp_pos _).le
  have hym : 1 ≤ y ^ m := Real.one_le_rpow hy hm0
  -- the cost
  have hcost : y ^ β + k₀ + k₁ * y ≤ (1 + k₀ + k₁) * y ^ m := by
    have h1 : y ^ β ≤ y ^ m := Real.rpow_le_rpow_of_exponent_le hy (le_max_left _ _)
    have h2 : y ≤ y ^ m := by
      calc y = y ^ (1 : ℝ) := (Real.rpow_one y).symm
        _ ≤ y ^ m := Real.rpow_le_rpow_of_exponent_le hy (le_max_right _ _)
    have h3 : k₀ * 1 ≤ k₀ * y ^ m := mul_le_mul_of_nonneg_left hym hk₀
    have h4 : k₁ * y ≤ k₁ * y ^ m := mul_le_mul_of_nonneg_left h2 hk₁
    have h5 : (1 + k₀ + k₁) * y ^ m = y ^ m + k₀ * y ^ m + k₁ * y ^ m := by ring
    rw [h5]
    linarith
  have hcost0 : 0 ≤ y ^ β + k₀ + k₁ * y := by
    have := Real.rpow_nonneg hy0.le β
    positivity
  -- the three prefactors
  have hπ : P₀ + P₁ * (1 + (P₂ * y) ^ 4) ≤ (P₀ + P₁ * (1 + P₂ ^ 4)) * y ^ 4 := by
    have h4 : 1 ≤ y ^ 4 := one_le_pow₀ hy
    have e : (P₀ + P₁ * (1 + P₂ ^ 4)) * y ^ 4 = P₀ * y ^ 4 + P₁ * y ^ 4 + P₁ * (P₂ * y) ^ 4 := by
      ring
    rw [e]
    have := mul_le_mul_of_nonneg_left h4 hP₀
    have := mul_le_mul_of_nonneg_left h4 hP₁
    linarith
  have hA : 1 + Real.sqrt y / (2 * c ^ 2) ≤ (1 + 1 / (2 * c ^ 2)) * y := by
    have hs : Real.sqrt y ≤ y := (Real.sqrt_le_left hy0.le).mpr (by nlinarith)
    have h1 : Real.sqrt y / (2 * c ^ 2) ≤ y / (2 * c ^ 2) :=
      div_le_div_of_nonneg_right hs (by positivity)
    have e : (1 + 1 / (2 * c ^ 2)) * y = y + y / (2 * c ^ 2) := by ring
    rw [e]
    linarith
  have hlog : Real.log y ^ 2 ≤ y := by
    have h1 := pow_le_pow_left₀ (Real.log_nonneg hy) (log_le_sqrt hy0) 2
    rwa [Real.sq_sqrt hy0.le] at h1
  -- the bracket
  have hbr : 2 * ((P₀ + P₁ * (1 + (P₂ * y) ^ 4)) * e₁) +
      2 * K * (1 + Real.sqrt y / (2 * c ^ 2)) * e₂ + D * y * Real.log y ^ 2 * e₃ ≤
      2 * (P₀ + P₁ * (1 + P₂ ^ 4)) * y ^ 4 * e₁ + 2 * K * (1 + 1 / (2 * c ^ 2)) * y * e₂ +
        D * y ^ 2 * e₃ := by
    have h1 : (P₀ + P₁ * (1 + (P₂ * y) ^ 4)) * e₁ ≤ (P₀ + P₁ * (1 + P₂ ^ 4)) * y ^ 4 * e₁ :=
      mul_le_mul_of_nonneg_right hπ he₁0
    have h2 : K * (1 + Real.sqrt y / (2 * c ^ 2)) * e₂ ≤ K * ((1 + 1 / (2 * c ^ 2)) * y) * e₂ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA hK) he₂0
    have h3 : D * y * Real.log y ^ 2 * e₃ ≤ D * y * y * e₃ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog (mul_nonneg hD hy0.le)) he₃0
    have e : 2 * (P₀ + P₁ * (1 + P₂ ^ 4)) * y ^ 4 * e₁ + 2 * K * (1 + 1 / (2 * c ^ 2)) * y * e₂ +
        D * y ^ 2 * e₃ = 2 * ((P₀ + P₁ * (1 + P₂ ^ 4)) * y ^ 4 * e₁) +
          2 * (K * ((1 + 1 / (2 * c ^ 2)) * y) * e₂) + D * y * y * e₃ := by ring
    rw [e]
    linarith
  have hbr0 : 0 ≤ 2 * ((P₀ + P₁ * (1 + (P₂ * y) ^ 4)) * e₁) +
      2 * K * (1 + Real.sqrt y / (2 * c ^ 2)) * e₂ + D * y * Real.log y ^ 2 * e₃ := by
    have : 0 ≤ (P₀ + P₁ * (1 + (P₂ * y) ^ 4)) := by positivity
    have : 0 ≤ Real.log y ^ 2 := sq_nonneg _
    positivity
  calc (y ^ β + k₀ + k₁ * y) * (2 * ((P₀ + P₁ * (1 + (P₂ * y) ^ 4)) * e₁) +
        2 * K * (1 + Real.sqrt y / (2 * c ^ 2)) * e₂ + D * y * Real.log y ^ 2 * e₃)
      ≤ (1 + k₀ + k₁) * y ^ m * (2 * (P₀ + P₁ * (1 + P₂ ^ 4)) * y ^ 4 * e₁ +
          2 * K * (1 + 1 / (2 * c ^ 2)) * y * e₂ + D * y ^ 2 * e₃) :=
        mul_le_mul hcost hbr hbr0 (hcost0.trans hcost)
    _ = _ := by ring

/-- [INC-P000, proof of Lemma `lem:amb`, Step 7, the series `C₄(ε)`] On every grid, with the
default `ϑ`: let `β > 1/2`, `k₀, k₁, P₀, P₁, K, D ≥ 0`, `q, c, c₃ > 0`, and let `f` be the
paper's function: `f(y) = c(y) (2π(y) + p_A(y) + p̄_K(y))` for `y ≥ 16` (the terms of
`rpow_add_mul_sum_exp_neg_le`; `π` of Definition `def:amb`, `p_A` of
`mul_exp_neg_div_one_sub_exp_neg_le`, `p̄_K` of `one_add_ceil_mul_exp_neg_div_le`) and `f(y) = 0`
below `16`. Then the sums `∑_(ℓ ∈ S) f(L_ℓ)` over the finite sets `S` of activated batches with
`t_ℓ ≥ e^e` are bounded uniformly in `S`. With `c_ℓ P(E_ℓ^amb(ε)) ≤ f(L_ℓ)` (Step 5), this is
`C₄(ε) < ∞`. -/
lemma Grid.exists_sum_activated_rpow_add_mul_exp_neg_le {K' : ℕ} (g : Grid K')
    {β k₀ k₁ P₀ P₁ P₂ q K c D c₃ : ℝ} (hβ : 1 / 2 < β) (hk₀ : 0 ≤ k₀) (hk₁ : 0 ≤ k₁)
    (hP₀ : 0 ≤ P₀) (hP₁ : 0 ≤ P₁) (hq : 0 < q) (hK : 0 ≤ K) (hc : 0 < c) (hD : 0 ≤ D)
    (hc₃ : 0 < c₃) {f : ℝ → ℝ}
    (hf : ∀ y, f y = if 16 ≤ y then (y ^ β + k₀ + k₁ * y) *
      (2 * ((P₀ + P₁ * (1 + (P₂ * y) ^ 4)) * Real.exp (-(q * y))) +
        2 * K * (1 + Real.sqrt y / (2 * c ^ 2)) *
          Real.exp (-(c ^ 2 * (4 : ℝ) ^ (-β) * y ^ (β - 1 / 2))) +
        D * y * Real.log y ^ 2 * Real.exp (-(c₃ * Real.sqrt y / Real.log y ^ 2))) else 0) :
    ∃ B, ∀ S : Finset ℕ, (∀ ℓ ∈ S, g.imedEnd g.hyTheta ℓ < g.t (ℓ + 1) ∧
      Real.exp (Real.exp 1) ≤ (g.t ℓ : ℝ)) → ∑ ℓ ∈ S, f (g.logEnd ℓ) ≤ B := by
  have hm0 : 0 ≤ max β 1 := zero_le_one.trans (le_max_right _ _)
  obtain ⟨y₁, F₁, h₁, hF₁⟩ := exists_rpow_mul_exp_neg_le (A := max β 1 + (4 : ℕ)) (b := 0)
    (by positivity) hq one_pos
  obtain ⟨y₂, F₂, h₂, hF₂⟩ := exists_rpow_mul_exp_neg_le (A := max β 1 + (1 : ℕ)) (b := 0)
    (c := c ^ 2 * (4 : ℝ) ^ (-β)) (a := β - 1 / 2) (by positivity) (by positivity)
    (by linarith)
  obtain ⟨y₃, F₃, h₃, hF₃⟩ := exists_rpow_mul_exp_neg_le (A := max β 1 + (2 : ℕ)) (b := 2)
    (a := 1 / 2) (by positivity) hc₃ (by norm_num)
  set k₁' := 2 * (1 + k₀ + k₁) * (P₀ + P₁ * (1 + P₂ ^ 4)) with hk₁'
  set k₂' := 2 * (1 + k₀ + k₁) * K * (1 + 1 / (2 * c ^ 2)) with hk₂'
  set k₃' := (1 + k₀ + k₁) * D with hk₃'
  have hk₁'0 : 0 ≤ k₁' := by positivity
  have hk₂'0 : 0 ≤ k₂' := by positivity
  have hk₃'0 : 0 ≤ k₃' := by positivity
  -- the bounds `F_i` are nonnegative (evaluate at `y = 1`)
  have hF₁0 : 0 ≤ F₁ :=
    (mul_nonneg (Real.rpow_nonneg zero_le_one _) (Real.exp_pos _).le).trans (hF₁ 1 le_rfl)
  have hF₂0 : 0 ≤ F₂ :=
    (mul_nonneg (Real.rpow_nonneg zero_le_one _) (Real.exp_pos _).le).trans (hF₂ 1 le_rfl)
  have hF₃0 : 0 ≤ F₃ :=
    (mul_nonneg (Real.rpow_nonneg zero_le_one _) (Real.exp_pos _).le).trans (hF₃ 1 le_rfl)
  refine g.exists_sum_activated_le (f := f) (F := k₁' * F₁ + k₂' * F₂ + k₃' * F₃)
    (C := k₁' + k₂' + k₃') (y₀ := max (max y₁ y₂) (max y₃ 16)) ?_ ?_ ?_
  · intro y hy
    have hy0 : 0 < y := by linarith
    rw [hf]
    split_ifs
    · have := Real.rpow_nonneg hy0.le β
      have : 0 ≤ (P₀ + P₁ * (1 + (P₂ * y) ^ 4)) := by positivity
      have : 0 ≤ Real.log y ^ 2 := sq_nonneg _
      positivity
    · exact le_rfl
  · intro y hy
    rw [hf]
    split_ifs
    · refine (rpow_add_mul_sum_exp_neg_le hk₀ hk₁ hP₀ hP₁ hK hc hD hy).trans ?_
      have := mul_le_mul_of_nonneg_left (hF₁ y hy) hk₁'0
      have := mul_le_mul_of_nonneg_left (hF₂ y hy) hk₂'0
      have := mul_le_mul_of_nonneg_left (hF₃ y hy) hk₃'0
      linarith
    · positivity
  · intro y hy
    have hy1 : y₁ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
    have hy2 : y₂ ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
    have hy3 : y₃ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hy
    have hy16 : 16 ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hy
    rw [hf, ite_eq_left hy16]
    refine (rpow_add_mul_sum_exp_neg_le hk₀ hk₁ hP₀ hP₁ hK hc hD (by linarith)).trans ?_
    have := mul_le_mul_of_nonneg_left (h₁ y hy1) hk₁'0
    have := mul_le_mul_of_nonneg_left (h₂ y hy2) hk₂'0
    have := mul_le_mul_of_nonneg_left (h₃ y hy3) hk₃'0
    have e : (k₁' + k₂' + k₃') * y ^ (-2 : ℝ) =
        k₁' * y ^ (-2 : ℝ) + k₂' * y ^ (-2 : ℝ) + k₃' * y ^ (-2 : ℝ) := by ring
    rw [e]
    linarith

/-! ### Condition (f) of Definition `def:amb`: `π` is nonincreasing -/

/-- [INC-P000, Definition `def:amb`, condition (f)] For `P₀, P₁ ≥ 0` and `q > 0`, the function
`π(y) = (P₀ + P₁ (1 + (P₂ y)⁴)) e^(-q y)` is nonincreasing on `[4/q, ∞)`. So
`π(L_(ℓ+1)) ≤ π(L_ℓ)` as soon as `L_ℓ ≥ 4/q` (the paper's (f), used in Step 5 of the proof of
Lemma `lem:amb`). -/
lemma mul_exp_neg_le_mul_exp_neg_of_le {P₀ P₁ P₂ q y y' : ℝ} (hP₀ : 0 ≤ P₀) (hP₁ : 0 ≤ P₁)
    (hq : 0 < q)
    (hy : 4 / q ≤ y) (hyy : y ≤ y') :
    (P₀ + P₁ * (1 + (P₂ * y') ^ 4)) * Real.exp (-(q * y')) ≤
      (P₀ + P₁ * (1 + (P₂ * y) ^ 4)) * Real.exp (-(q * y)) := by
  -- For `4/q ≤ y ≤ y'`, the prefactor grows at most by `(y'/y)⁴`, and
  -- `4 log(y'/y) ≤ 4 (y'/y - 1) ≤ q (y' - y)`.
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy
  have hy'0 : 0 < y' := lt_of_lt_of_le hy0 hyy
  set t := y' / y with ht
  have ht1 : 1 ≤ t := by rw [ht, le_div_iff₀ hy0]; linarith
  have hy' : y' = t * y := by rw [ht]; field_simp
  -- the prefactor grows at most by `t⁴`
  have hpre : P₀ + P₁ * (1 + (P₂ * y') ^ 4) ≤ t ^ 4 * (P₀ + P₁ * (1 + (P₂ * y) ^ 4)) := by
    have ht4 : 1 ≤ t ^ 4 := one_le_pow₀ ht1
    have e1 : (P₂ * y') ^ 4 = t ^ 4 * (P₂ * y) ^ 4 := by rw [hy']; ring
    have e2 : t ^ 4 * (P₀ + P₁ * (1 + (P₂ * y) ^ 4)) =
        t ^ 4 * P₀ + t ^ 4 * P₁ + P₁ * (t ^ 4 * (P₂ * y) ^ 4) := by ring
    rw [e1, e2]
    have := mul_le_mul_of_nonneg_right ht4 hP₀
    have := mul_le_mul_of_nonneg_right ht4 hP₁
    linarith
  -- `t⁴ e^(-q y') ≤ e^(-q y)`
  have hexp : t ^ 4 * Real.exp (-(q * y')) ≤ Real.exp (-(q * y)) := by
    have ht0 : 0 < t := by linarith
    have hlog : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos ht0
    have h4 : 4 * (t - 1) ≤ q * y * (t - 1) := by
      have : 4 ≤ q * y := by rw [div_le_iff₀ hq] at hy; linarith
      exact mul_le_mul_of_nonneg_right this (by linarith)
    have hpow : t ^ 4 = Real.exp (4 * Real.log t) := by
      rw [show (4 : ℝ) * Real.log t = ((4 : ℕ) : ℝ) * Real.log t by norm_num, ← Real.log_pow,
        Real.exp_log (by positivity)]
    rw [hpow, ← Real.exp_add, Real.exp_le_exp, hy']
    nlinarith
  have hpre0 : 0 ≤ P₀ + P₁ * (1 + (P₂ * y) ^ 4) := by positivity
  calc (P₀ + P₁ * (1 + (P₂ * y') ^ 4)) * Real.exp (-(q * y'))
      ≤ t ^ 4 * (P₀ + P₁ * (1 + (P₂ * y) ^ 4)) * Real.exp (-(q * y')) :=
        mul_le_mul_of_nonneg_right hpre (Real.exp_pos _).le
    _ = (P₀ + P₁ * (1 + (P₂ * y) ^ 4)) * (t ^ 4 * Real.exp (-(q * y'))) := by ring
    _ ≤ (P₀ + P₁ * (1 + (P₂ * y) ^ 4)) * Real.exp (-(q * y)) :=
        mul_le_mul_of_nonneg_left hexp hpre0

end Incognita.BatchedBandits
