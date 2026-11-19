/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.LogInequalities

/-! # A grid for the dual formula of `𝒦_inf`

[INC-P000, Lemma `lem:grid`]: for reals `y_0, …, y_(n-1) ∈ [0, 1]` (the first `n` rewards of a
stack), a level `r ∈ [0, 1)` and `F(λ) = ∑_{i < n} log (1 - λ (y_i - r))` (so that
`n 𝒦_inf(Ĝ, r) = sup_{λ ∈ [0, 1/(1-r))} F(λ)` for the empirical law `Ĝ`), the supremum is reached
up to `1` on the finite grid `λ^(k) = τ_n^k / (1 - r)`, `1 ≤ k ≤ k_n`, with `τ_n = 1 - 1/(2n)` and
`k_n = ⌈2n log (n / (1 - r))⌉ + 1`. The deviation bounds of [INC-P000] built on this grid are
variants of those of [CGMMS13, Section 5, Theorem 2], [HT15] and [GHMS22, Section 2.3].

* `exists_grid_le_sum_log`: if `F(λ) ≥ z' ≥ 1` for some `λ ∈ [0, 1/(1-r))`, then
  `F(λ^(k)) ≥ z' - 1` for some `k ∈ [1, k_n]`; with `z' = z - 1`, this is Lemma `lem:grid` (if
  `n 𝒦_inf(Ĝ, r) ≥ z ≥ 2`, some `λ` has `F(λ) ≥ z - 1`).
* `grid_mem`: `λ^(k) ∈ [0, 1/(1-r))` for `k ≥ 1`.
* `gridSize_le`: `k_n ≤ (4 + 2 κ(r)) n²`, `κ(r) = log (1/(1-r))`.
-/

@[expose] public section

open Real Finset

namespace Incognita.BatchedBandits

/-- [INC-P000, Lemma `lem:grid`, "moreover"] The grid points `λ^(k) = τ_n^k / (1 - r)`, `k ≥ 1`,
are in `[0, 1/(1-r))`: `λ^(k) (1 - r) = τ_n^k < 1`. -/
lemma grid_mem {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : r < 1) {k : ℕ} (hk : 1 ≤ k) :
    0 ≤ (1 - 1 / (2 * n : ℝ)) ^ k / (1 - r) ∧
      (1 - 1 / (2 * n : ℝ)) ^ k / (1 - r) * (1 - r) < 1 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hτ0 : 0 ≤ 1 - 1 / (2 * n : ℝ) := by
    rw [sub_nonneg, div_le_one (by positivity)]
    linarith
  have hτ1 : 1 - 1 / (2 * n : ℝ) < 1 := by
    have : 0 < 1 / (2 * n : ℝ) := by positivity
    linarith
  have h1r : 0 < 1 - r := by linarith
  refine ⟨div_nonneg (pow_nonneg hτ0 k) h1r.le, ?_⟩
  rw [div_mul_cancel₀ _ h1r.ne']
  exact pow_lt_one₀ hτ0 hτ1 (by omega)

/-- [INC-P000, Lemma `lem:grid`, the size of the grid] `k_n = ⌈2n log (n / (1 - r))⌉ + 1 ≤
(4 + 2 κ(r)) n²` for `n ≥ 1` and `r ∈ [0, 1)`: `k_n ≤ 2n (log n + κ(r)) + 2` and `log n ≤ n`. -/
lemma gridSize_le {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    ((⌈2 * n * Real.log (n / (1 - r))⌉₊ + 1 : ℕ) : ℝ) ≤
      (4 + 2 * Real.log (1 / (1 - r))) * n ^ 2 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1r : 0 < 1 - r := by linarith
  have hκ : 0 ≤ Real.log (1 / (1 - r)) :=
    Real.log_nonneg (by rw [le_div_iff₀ h1r]; linarith)
  have hlogn : Real.log n ≤ n := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn'
  have hsplit : Real.log (n / (1 - r)) = Real.log n + Real.log (1 / (1 - r)) := by
    rw [div_eq_mul_one_div, Real.log_mul (by positivity) (by positivity)]
  have harg : 0 ≤ 2 * n * Real.log (n / (1 - r)) := by rw [hsplit]; positivity
  push_cast
  have hceil := Nat.ceil_lt_add_one harg
  rw [hsplit] at hceil ⊢
  have hnn : (n : ℝ) ≤ n ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hlogn (by positivity : (0 : ℝ) ≤ 2 * n),
    mul_le_mul_of_nonneg_right hnn hκ]

/-- [INC-P000, Lemma `lem:grid`] Let `n ≥ 1`, `y_i ∈ [0, 1]` for `i < n`, `r ∈ [0, 1)` and
`F(λ) = ∑_{i < n} log (1 - λ (y_i - r))`. If `F(λ) ≥ z' ≥ 1` for some `λ ∈ [0, 1/(1-r))`, then
`F(λ^(k)) ≥ z' - 1` for some `k` with `1 ≤ k ≤ ⌈2 n log (n / (1 - r))⌉ + 1`, where
`λ^(k) = (1 - 1/(2n))^k / (1 - r)`. -/
lemma exists_grid_le_sum_log {n : ℕ} (hn : 1 ≤ n) {y : ℕ → ℝ}
    (hy : ∀ i < n, y i ∈ Set.Icc (0 : ℝ) 1) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) {z' lam : ℝ}
    (hz' : 1 ≤ z') (hlam0 : 0 ≤ lam) (hlam1 : lam * (1 - r) < 1)
    (hF : z' ≤ ∑ i ∈ range n, Real.log (1 - lam * (y i - r))) :
    ∃ k, 1 ≤ k ∧ k ≤ ⌈2 * n * Real.log (n / (1 - r))⌉₊ + 1 ∧
      z' - 1 ≤ ∑ i ∈ range n,
        Real.log (1 - (1 - 1 / (2 * n : ℝ)) ^ k / (1 - r) * (y i - r)) := by
  -- With `τ = 1 - 1/(2n)` and `k_n = ⌈2 n log (n / (1 - r))⌉ + 1`: `λ > 1/n ≥ λ^(k_n)` (as
  -- `F(λ) ≤ n λ r`), so `λ ∈ (λ^(k), λ^(k-1)]` for some `k`, and rounding down to
  -- `λ^(k) = ϖ λ`, `ϖ ≥ τ`, costs at most `n log (1/τ) ≤ 1` (Lemma `lem:kinf`(vi)).
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h1r : 0 < 1 - r := by linarith
  set τ : ℝ := 1 - 1 / (2 * n : ℝ) with hτ
  set kn := ⌈2 * n * Real.log (n / (1 - r))⌉₊ + 1 with hkn
  set grid : ℕ → ℝ := fun k ↦ τ ^ k / (1 - r) with hgrid
  have hτ0 : 0 < τ := by
    rw [hτ, sub_pos, div_lt_one (by positivity)]
    linarith
  have hτ1 : τ ≤ 1 := by
    have : 0 ≤ 1 / (2 * n : ℝ) := by positivity
    linarith
  -- Step 2: `λ > 1/n`
  have hFle : ∑ i ∈ range n, Real.log (1 - lam * (y i - r)) ≤ n * lam * r := by
    have : ∀ i ∈ range n, Real.log (1 - lam * (y i - r)) ≤ lam * r := by
      intro i hi
      have hyi := hy i (Finset.mem_range.mp hi)
      have hpos := one_sub_mul_sub_pos hlam0 hlam1 hyi.2
      have := Real.log_le_sub_one_of_pos hpos
      nlinarith [hyi.1]
    calc _ ≤ ∑ _i ∈ range n, lam * r := Finset.sum_le_sum this
      _ = n * lam * r := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have hlamn : 1 / n < lam := by
    rw [div_lt_iff₀ hn0]
    nlinarith
  -- Step 3: `λ^(k_n) ≤ 1/n`
  have hτexp : τ ≤ Real.exp (-(1 / (2 * n))) := by
    have := Real.add_one_le_exp (-(1 / (2 * n : ℝ)))
    rw [hτ]
    linarith
  have hgridkn : grid kn ≤ 1 / n := by
    simp only [hgrid]
    rw [div_le_div_iff₀ h1r hn0, one_mul]
    have hpow : τ ^ kn ≤ Real.exp (-(kn / (2 * n))) := by
      calc τ ^ kn ≤ Real.exp (-(1 / (2 * n))) ^ kn := pow_le_pow_left₀ hτ0.le hτexp kn
        _ = Real.exp (-(kn / (2 * n))) := by
            rw [← Real.exp_nat_mul]
            congr 1
            ring
    have hkn' : Real.log (n / (1 - r)) ≤ kn / (2 * n) := by
      rw [le_div_iff₀ (by positivity)]
      have := Nat.le_ceil (2 * n * Real.log (n / (1 - r)))
      simp only [hkn]
      push_cast
      nlinarith
    have hexp : Real.exp (-(kn / (2 * n))) ≤ (1 - r) / n := by
      rw [show (1 - r) / n = Real.exp (-(Real.log (n / (1 - r)))) by
        rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]]
      exact Real.exp_le_exp.mpr (by linarith)
    calc τ ^ kn * n ≤ (1 - r) / n * n := by
          exact mul_le_mul_of_nonneg_right (hpow.trans hexp) hn0.le
      _ = 1 - r := by field_simp
  -- the first grid point below `λ`
  have hex : ∃ k, grid k < lam := ⟨kn, hgridkn.trans_lt hlamn⟩
  classical
  set k := Nat.find hex with hk
  have hk_lt : grid k < lam := Nat.find_spec hex
  have hk_le : k ≤ kn := Nat.find_min' hex (hgridkn.trans_lt hlamn)
  have hgrid0 : lam < grid 0 := by
    simp only [hgrid, pow_zero]
    rw [lt_div_iff₀ h1r]
    exact hlam1
  have hk1 : 1 ≤ k := by
    by_contra h0
    have : k = 0 := by omega
    rw [this] at hk_lt
    linarith
  have hkprev : lam ≤ grid (k - 1) := by
    have := Nat.find_min hex (show k - 1 < k by omega)
    exact not_lt.mp this
  -- `ϖ = λ^(k) / λ ∈ [τ, 1)`
  have hlam : 0 < lam := lt_of_le_of_lt (by positivity) hlamn
  set ϖ := grid k / lam with hϖ
  have hgridk : grid k = τ * grid (k - 1) := by
    simp only [hgrid]
    rw [show k = k - 1 + 1 by omega, pow_succ]
    simp only [Nat.add_sub_cancel]
    ring
  have hϖτ : τ ≤ ϖ := by
    rw [hϖ, le_div_iff₀ hlam, hgridk]
    exact mul_le_mul_of_nonneg_left hkprev hτ0.le
  have hϖ1 : ϖ ≤ 1 := by
    rw [hϖ, div_le_one hlam]
    exact hk_lt.le
  have hϖ0 : 0 < ϖ := hτ0.trans_le hϖτ
  -- Step 4: rounding down costs at most `1`
  have hround : ∀ i ∈ range n, Real.log ϖ + Real.log (1 - lam * (y i - r)) ≤
      Real.log (1 - grid k * (y i - r)) := by
    intro i hi
    have := log_le_log_one_sub_mul hlam0 hlam1 hϖ0 hϖ1 (hy i (Finset.mem_range.mp hi)).2
    rwa [show ϖ * lam = grid k by rw [hϖ]; field_simp] at this
  have hsum := Finset.sum_le_sum hround
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hlogτ : -1 ≤ n * Real.log τ := by
    have h := Real.one_sub_inv_le_log_of_pos hτ0
    have : 1 - τ⁻¹ = -(1 / (2 * n - 1)) := by
      rw [hτ]
      have : (2 * n : ℝ) - 1 ≠ 0 := by linarith
      field_simp
      ring
    rw [this] at h
    have h2 : (n : ℝ) * (1 / (2 * n - 1)) ≤ 1 := by
      rw [mul_one_div, div_le_one (by linarith)]
      linarith
    nlinarith
  have hlogϖ : Real.log τ ≤ Real.log ϖ := Real.log_le_log hτ0 hϖτ
  refine ⟨k, hk1, hk_le, ?_⟩
  have : (n : ℝ) * Real.log τ ≤ n * Real.log ϖ := mul_le_mul_of_nonneg_left hlogϖ hn0.le
  simp only [hgrid] at hsum
  linarith

end Incognita.BatchedBandits
