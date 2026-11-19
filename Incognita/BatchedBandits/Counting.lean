/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.Sums

/-! # Counting lemmas and sequences for the upper bound of P000

Deterministic lemmas of [INC-P000, Subsection `sec:app-sums`], in general form (sequences indexed
by `ℕ`, with no grid unless one is needed).

* `exists_seq_tendsto_zero_div_tendsto_zero`, `Grid.exists_seq_tendsto_zero_div_log_t`:
  Lemma `lem:diag`, a sequence `ε_L → 0` with `f(ε_L) / log t_L → 0`.
* `tendsto_iSup_Icc_div_of_tendsto`, `Grid.tendsto_iSup_ratio_sq_mul_logEnd_div`: Lemma `lem:H`
  at the batch ends, `H_j / L_j → x²` for the largest level `H_j = max_{1 ≤ k ≤ j} y_(k-1) L_k`.
* `Grid.log_t_le_of_growth`: Lemma `lem:growth`; `Grid.logEnd_add_le_pow_mul`: the last claim of
  Lemma `lem:ranksA`, `L_(k+i) ≤ x₊^i L_k`.
* `exists_le_mul_or_forall_le_mul_of_monotone`: Lemma `lem:chain`.
* `sum_ite_le_sum_Icc_of_monotone`, `sum_ite_sub_le_of_monotone`: Lemma `lem:distinct`(i), (ii),
  for a nondecreasing integer sequence `N_j` (the counts `N_a(t_j)` of a run).
* `le_sum_mul_ite_exists`: Lemma `lem:sums`(v) (layer cake).
* `sum_ceil_sub_mul_le`: Lemma `lem:sums`(iv) (counting), with the finite sum
  `∑_{n < ⌈λ_j⌉} g(n^(1/β))` in place of the series.
* `le_add_sum_of_classes` (with `sum_Ioc_sub_pred`, telescoping): Lemma `lem:decompC`, Steps 1–4,
  in abstract form; `le_add_div_add_mul_of_le_add_div` and `le_mul_of_le_add_div_sq`: the bounds
  of its good class (Step 3) and of its class `𝒪` (Step 4).
-/

@[expose] public section

open Real Finset Filter

open scoped Topology

namespace Incognita.BatchedBandits

/-! ### Lemma `lem:diag` -/

/-- **A sequence `ε_L → 0`** [INC-P000, Lemma `lem:diag`, general form]: for `ε̄ > 0`, every
function `f` and every real sequence `a_L → ∞`, there is a sequence `ε_L ∈ (0, ε̄]` with
`ε_L → 0` and `f(ε_L) / a_L → 0`. With `e_k = ε̄ / 2^k`, `ε_L` is `e_k` for the largest `k ≤ L`
with `k (|f(e_k)| + 1) ≤ a_L`; the hypothesis `f ≥ 0` of the paper is not needed. -/
lemma exists_seq_tendsto_zero_div_tendsto_zero {ε₀ : ℝ} (hε₀ : 0 < ε₀) (f : ℝ → ℝ)
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) :
    ∃ ε : ℕ → ℝ, (∀ L, ε L ∈ Set.Ioc 0 ε₀) ∧ Tendsto ε atTop (𝓝 0) ∧
      Tendsto (fun L ↦ f (ε L) / a L) atTop (𝓝 0) := by
  set e : ℕ → ℝ := fun k ↦ ε₀ / 2 ^ k with he
  set P : ℕ → ℕ → Prop := fun L k ↦ (k : ℝ) * (|f (e k)| + 1) ≤ a L with hP
  set k : ℕ → ℕ := fun L ↦ Nat.findGreatest (P L) L with hk
  have hkt : Tendsto k atTop atTop := by
    refine tendsto_atTop.2 fun K ↦ ?_
    filter_upwards [ha.eventually_ge_atTop ((K : ℝ) * (|f (e K)| + 1)), eventually_ge_atTop K]
      with L hL hKL
    exact Nat.le_findGreatest hKL hL
  refine ⟨fun L ↦ e (k L), fun L ↦ ⟨by positivity, ?_⟩, ?_, ?_⟩
  · exact div_le_self hε₀.le (one_le_pow₀ (by norm_num))
  · have he0 : Tendsto e atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
        (by norm_num)).const_mul ε₀
      rw [mul_zero] at this
      refine this.congr fun n ↦ ?_
      simp [he, div_eq_mul_inv]
    exact he0.comp hkt
  · have hinv : Tendsto (fun L ↦ 1 / (k L : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat.comp hkt
    refine squeeze_zero_norm' ?_ hinv
    filter_upwards [hkt.eventually_ge_atTop 1,
      ha.eventually_ge_atTop (((1 : ℕ) : ℝ) * (|f (e 1)| + 1)),
      eventually_ge_atTop 1] with L hk1 hL1 hL
    have hPk : P L (k L) := Nat.findGreatest_spec (P := P L) hL hL1
    have hk0 : (0 : ℝ) < k L := by exact_mod_cast hk1
    have hpos : 0 < (k L : ℝ) * (|f (e (k L))| + 1) := by positivity
    have haL : 0 < a L := hpos.trans_le hPk
    rw [norm_div, Real.norm_eq_abs, Real.norm_of_nonneg haL.le, div_le_div_iff₀ haL hk0, one_mul]
    calc |f (e (k L))| * k L ≤ (k L : ℝ) * (|f (e (k L))| + 1) := by nlinarith
      _ ≤ a L := hPk

/-- [INC-P000, Lemma `lem:diag`] For `ε̄ > 0`, every function `f` and the grid `(t_L)`, there is a
sequence `ε_L ∈ (0, ε̄]` with `ε_L → 0` and `f(ε_L) / log t_L → 0`. -/
lemma Grid.exists_seq_tendsto_zero_div_log_t {K : ℕ} (g : Grid K) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (f : ℝ → ℝ) :
    ∃ ε : ℕ → ℝ, (∀ L, ε L ∈ Set.Ioc 0 ε₀) ∧ Tendsto ε atTop (𝓝 0) ∧
      Tendsto (fun L ↦ f (ε L) / Real.log (g.t L)) atTop (𝓝 0) :=
  exists_seq_tendsto_zero_div_tendsto_zero hε₀ f
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp g.strictMono.tendsto_atTop))

/-! ### Lemma `lem:H` -/

/-- **Running maxima** [INC-P000, Lemma `lem:H`, general form]: if `a_k / b_k → c ≥ 0`, `b` is
nondecreasing and `b_k → ∞`, then `(max_{1 ≤ k ≤ j} a_k) / b_j → c`; the
maximum is `⨆ k : Icc 1 j, a k`. -/
lemma tendsto_iSup_Icc_div_of_tendsto {a b : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hab : Tendsto (fun k ↦ a k / b k) atTop (𝓝 c)) (hb : Monotone b)
    (hbt : Tendsto b atTop atTop) :
    Tendsto (fun j ↦ (⨆ k : Finset.Icc 1 j, a k) / b j) atTop (𝓝 c) := by
  have hbpos : ∀ᶠ k in atTop, 0 < b k := hbt.eventually_gt_atTop 0
  have hle : ∀ j, 1 ≤ j → a j ≤ ⨆ k : Finset.Icc 1 j, a k := fun j hj ↦
    le_ciSup (f := fun k : Finset.Icc 1 j ↦ a k) (Set.finite_range _).bddAbove
      ⟨j, Finset.mem_Icc.mpr ⟨hj, le_rfl⟩⟩
  refine tendsto_order.2 ⟨fun c' hc' ↦ ?_, fun c' hc' ↦ ?_⟩
  · filter_upwards [(tendsto_order.1 hab).1 c' hc', hbpos, eventually_ge_atTop 1]
      with j hj hbj hj1
    exact hj.trans_le (div_le_div_of_nonneg_right (hle j hj1) hbj.le)
  · obtain ⟨c'', hc'', hc''c'⟩ := exists_between hc'
    obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 (((tendsto_order.1 hab).2 c'' hc'').and hbpos)
    set C₀ : ℝ := ∑ k ∈ Finset.range k₀, |a k| with hC₀
    have hC₀b : Tendsto (fun j ↦ C₀ / b j) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hbt
    filter_upwards [(tendsto_order.1 hC₀b).2 c' ((hc.trans_lt hc'').trans hc''c'),
      hbpos, eventually_ge_atTop (max k₀ 1)] with j hCj hbj hj
    have hbound : (⨆ k : Finset.Icc 1 j, a k) ≤ max C₀ (c'' * b j) := by
      have : Nonempty (Finset.Icc 1 j) := ⟨⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩⟩
      refine ciSup_le fun ⟨k, hk⟩ ↦ ?_
      rcases Nat.lt_or_ge k k₀ with hkk | hkk
      · refine le_max_of_le_left ((le_abs_self (a k)).trans ?_)
        exact Finset.single_le_sum (f := fun k ↦ |a k|) (fun k _ ↦ abs_nonneg (a k))
          (Finset.mem_range.mpr hkk)
      · obtain ⟨h1, h2⟩ := hk₀ k hkk
        rw [div_lt_iff₀ h2] at h1
        refine le_max_of_le_right (h1.le.trans ?_)
        exact mul_le_mul_of_nonneg_left (hb (Finset.mem_Icc.mp hk).2) (hc.trans hc''.le)
    calc (⨆ k : Finset.Icc 1 j, a k) / b j ≤ max C₀ (c'' * b j) / b j :=
          div_le_div_of_nonneg_right hbound hbj.le
      _ = max (C₀ / b j) c'' := by
          rw [← max_div_div_right hbj.le, mul_div_assoc, div_self hbj.ne', mul_one]
      _ < c' := max_lt hCj hc''c'

/-- [INC-P000, Lemma `lem:H`, at the batch ends] On a grid with `x_ℓ → x ≥ 1`, the largest level
`H_j = max_{1 ≤ k ≤ j} y_(k-1) L_k` (`y_k = x_k²`) satisfies `H_j / L_j → x²`. -/
lemma Grid.tendsto_iSup_ratio_sq_mul_logEnd_div {K : ℕ} (g : Grid K) {x : ℝ}
    (hg : Tendsto g.ratio atTop (𝓝 x)) :
    Tendsto (fun j ↦ (⨆ k : Finset.Icc 1 j, g.ratio ((k : ℕ) - 1) ^ 2 * g.logEnd k) /
      g.logEnd j)
      atTop (𝓝 (x ^ 2)) := by
  refine tendsto_iSup_Icc_div_of_tendsto (a := fun k ↦ g.ratio (k - 1) ^ 2 * g.logEnd k)
    (sq_nonneg x) ?_ g.logEnd_monotone g.tendsto_logEnd_atTop
  have hr : Tendsto (fun k ↦ g.ratio (k - 1) ^ 2) atTop (𝓝 (x ^ 2)) :=
    (hg.comp (tendsto_sub_atTop_nat 1)).pow 2
  refine hr.congr' (eventually_atTop.2 ⟨1, fun k hk ↦ ?_⟩)
  simp only
  rw [mul_div_assoc, div_self (g.logEnd_pos hk).ne', mul_one]

/-! ### Lemma `lem:growth` -/

/-- [INC-P000, Lemma `lem:ranksA`, last claim] If `x_j ≤ x₊` for every `j > k`, `k ≥ 1` and
`x₊ ≥ 0`, then `L_(k+i) ≤ x₊^i L_k` for every `i ≥ 0`. -/
lemma Grid.logEnd_add_le_pow_mul {K : ℕ} (g : Grid K) {k : ℕ} (hk : 1 ≤ k) {xp : ℝ}
    (hxp : 0 ≤ xp) (hx : ∀ j, k < j → g.ratio j ≤ xp) (i : ℕ) :
    g.logEnd (k + i) ≤ xp ^ i * g.logEnd k := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [← add_assoc, g.logEnd_succ_eq (j := k + i) (by omega), pow_succ]
    have hL : 0 ≤ g.logEnd (k + i) := (g.logEnd_pos (by omega)).le
    calc g.ratio (k + i + 1) * g.logEnd (k + i) ≤ xp * g.logEnd (k + i) :=
          mul_le_mul_of_nonneg_right (hx _ (by omega)) hL
      _ ≤ xp * (xp ^ i * g.logEnd k) := mul_le_mul_of_nonneg_left ih hxp
      _ = xp ^ i * xp * g.logEnd k := by ring

/-- The induction of the proof of Lemma `lem:growth`. Let `k₀ ≥ 1`, `β₀ ≥ 0` with `x_j ≤ 1 + β₀`
for `j > k₀`, a set `S` of batches, and let `w(m)` be the mass `∑ (t_j - t_(j-1))` of the batches
`j ∈ (k₀, m] ∖ S` and `h(m)` the number of batches of `(k₀, m]` in `S`. If `w(n) ≤ W`, then for
`k₀ ≤ n' ≤ n`, `log (t_(n') + W - w(n')) ≤ (1 + β₀)^h(n') (log (t_(k₀) + W) + h(n') log 2)`. -/
lemma Grid.log_t_add_sub_le {K : ℕ} (g : Grid K) {k₀ : ℕ} (hk₀ : 1 ≤ k₀) {β₀ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hx : ∀ j, k₀ < j → g.ratio j ≤ 1 + β₀) (S : Finset ℕ) {W : ℝ} {n : ℕ}
    (hW : ∑ j ∈ Finset.Ioc k₀ n, (if j ∈ S then 0 else ((g.t j : ℝ) - g.t (j - 1))) ≤ W)
    (n' : ℕ) (hkn' : k₀ ≤ n') (hn' : n' ≤ n) :
    Real.log (g.t n' + (W - ∑ j ∈ Finset.Ioc k₀ n',
        (if j ∈ S then 0 else ((g.t j : ℝ) - g.t (j - 1))))) ≤
      (1 + β₀) ^ (∑ j ∈ Finset.Ioc k₀ n', if j ∈ S then 1 else 0) *
        (Real.log (g.t k₀ + W) +
          (∑ j ∈ Finset.Ioc k₀ n', if j ∈ S then 1 else 0 : ℕ) * Real.log 2) := by
  set w : ℕ → ℝ := fun m ↦ ∑ j ∈ Finset.Ioc k₀ m,
    (if j ∈ S then 0 else ((g.t j : ℝ) - g.t (j - 1))) with hw
  set hc : ℕ → ℕ := fun m ↦ ∑ j ∈ Finset.Ioc k₀ m, if j ∈ S then 1 else 0 with hhc
  have hB : ∀ j, 1 ≤ j → 0 ≤ (g.t j : ℝ) - g.t (j - 1) := fun j _ ↦
    sub_nonneg.mpr (g.t_le_t (by omega))
  -- `w` is nondecreasing on `[k₀, n]`, so `W - w(m) ≥ 0`
  have hwmono : ∀ m, k₀ ≤ m → ∀ m', m ≤ m' → w m ≤ w m' := by
    intro m hm m' hmm'
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc le_rfl hmm') ?_
    intro j hj _
    split_ifs
    · exact le_rfl
    · exact hB j (by have := (Finset.mem_Ioc.mp hj).1; omega)
  have hWw : ∀ m, k₀ ≤ m → m ≤ n → 0 ≤ W - w m := fun m hm hmn ↦
    sub_nonneg.mpr ((hwmono m hm n hmn).trans hW)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h1β : 1 ≤ 1 + β₀ := by linarith
  induction n', hkn' using Nat.le_induction with
  | base =>
    simp only [Finset.Ioc_self, Finset.sum_empty, sub_zero, pow_zero, one_mul,
      Nat.cast_zero, zero_mul, add_zero]
    exact le_rfl
  | succ m hm ih =>
    have ih := ih (by omega)
    have hw1 : w (m + 1) = w m + (if m + 1 ∈ S then 0 else ((g.t (m + 1) : ℝ) - g.t m)) := by
      simp only [hw]
      rw [Finset.sum_Ioc_succ_top hm, Nat.add_sub_cancel]
    have hc1 : hc (m + 1) = hc m + (if m + 1 ∈ S then 1 else 0) := by
      simp only [hhc]
      rw [Finset.sum_Ioc_succ_top hm]
    -- fold back the abbreviations `w` and `hc`, which `induction` unfolded
    change Real.log (g.t (m + 1) + (W - w (m + 1))) ≤
      (1 + β₀) ^ hc (m + 1) * (Real.log (g.t k₀ + W) + (hc (m + 1) : ℝ) * Real.log 2)
    change Real.log (g.t m + (W - w m)) ≤
      (1 + β₀) ^ hc m * (Real.log (g.t k₀ + W) + (hc m : ℝ) * Real.log 2) at ih
    by_cases hS : m + 1 ∈ S
    · -- a batch of `S`: `t_(m+1) ≤ Z^(1+β₀)` and `W - w(m+1) ≤ Z`
      simp only [hS, ite_true] at hw1 hc1
      rw [hw1, hc1, add_zero]
      set Z : ℝ := g.t m + (W - w m) with hZ
      have hWm := hWw m hm (by omega)
      have htm : (1 : ℝ) ≤ g.t m := by
        have := g.two_le_t (ℓ := m) (by omega)
        exact_mod_cast (show 1 ≤ g.t m by omega)
      have hZ1 : 1 ≤ Z := by linarith
      have hlogZ : 0 ≤ Real.log Z := Real.log_nonneg hZ1
      have ha : Real.log (g.t (m + 1)) ≤ (1 + β₀) * Real.log Z := by
        have h := g.logEnd_succ_eq (j := m) (by omega)
        unfold Grid.logEnd at h
        rw [h]
        have hr := hx (m + 1) (by omega)
        have hr0 : 0 ≤ g.ratio (m + 1) := by
          have := g.one_lt_ratio (ℓ := m + 1) (by omega)
          linarith
        have hlt : Real.log (g.t m) ≤ Real.log Z := Real.log_le_log (by linarith) (by linarith)
        have hlt0 : 0 ≤ Real.log (g.t m) := Real.log_nonneg htm
        calc g.ratio (m + 1) * Real.log (g.t m) ≤ (1 + β₀) * Real.log (g.t m) :=
              mul_le_mul_of_nonneg_right hr hlt0
          _ ≤ _ := mul_le_mul_of_nonneg_left hlt (by linarith)
      have htm1 : (0 : ℝ) < g.t (m + 1) := g.t_pos (by omega)
      -- `log (a + b) ≤ log 2 + (1 + β₀) log Z`
      have hsum : Real.log (g.t (m + 1) + (W - w m)) ≤ Real.log 2 + (1 + β₀) * Real.log Z := by
        have hmax : (g.t (m + 1) : ℝ) + (W - w m) ≤ 2 * max (g.t (m + 1) : ℝ) Z := by
          have := le_max_left (g.t (m + 1) : ℝ) Z
          have := le_max_right (g.t (m + 1) : ℝ) Z
          linarith
        have hmaxpos : 0 < max (g.t (m + 1) : ℝ) Z := lt_max_of_lt_left htm1
        calc Real.log (g.t (m + 1) + (W - w m)) ≤ Real.log (2 * max (g.t (m + 1) : ℝ) Z) :=
              Real.log_le_log (by linarith) hmax
          _ = Real.log 2 + Real.log (max (g.t (m + 1) : ℝ) Z) :=
              Real.log_mul (by norm_num) hmaxpos.ne'
          _ ≤ _ := by
              gcongr
              rcases le_total (g.t (m + 1) : ℝ) Z with h | h
              · rw [max_eq_right h]
                nlinarith
              · rw [max_eq_left h]
                exact ha
      have hpow : (1 + β₀) ^ hc m ≤ (1 + β₀) ^ (hc m + 1) :=
        pow_le_pow_right₀ h1β (Nat.le_succ _)
      have hone : 1 ≤ (1 + β₀) ^ (hc m + 1) := one_le_pow₀ h1β
      calc Real.log (g.t (m + 1) + (W - w m)) ≤ Real.log 2 + (1 + β₀) * Real.log Z := hsum
        _ ≤ Real.log 2 + (1 + β₀) * ((1 + β₀) ^ hc m *
            (Real.log (g.t k₀ + W) + (hc m : ℝ) * Real.log 2)) := by gcongr
        _ = Real.log 2 + (1 + β₀) ^ (hc m + 1) *
            (Real.log (g.t k₀ + W) + (hc m : ℝ) * Real.log 2) := by ring
        _ ≤ (1 + β₀) ^ (hc m + 1) * Real.log 2 + (1 + β₀) ^ (hc m + 1) *
            (Real.log (g.t k₀ + W) + (hc m : ℝ) * Real.log 2) := by
            gcongr
            nlinarith
        _ = (1 + β₀) ^ (hc m + 1) *
            (Real.log (g.t k₀ + W) + ((hc m + 1 : ℕ) : ℝ) * Real.log 2) := by
            push_cast
            ring
    · -- a batch outside `S`: the quantity does not change
      simp only [hS, ite_false] at hw1 hc1
      rw [hc1, add_zero]
      have : (g.t (m + 1) : ℝ) + (W - w (m + 1)) = g.t m + (W - w m) := by
        rw [hw1]
        ring
      rw [this]
      exact ih

/-- **Growth of the grid** [INC-P000, Lemma `lem:growth`]: let `k₀ ≥ 1` and `β₀ ≥ 0` with
`x_j ≤ 1 + β₀` for `j > k₀`, `S` a finite set of batches, `n ≥ k₀`, and
`W' ≥ ∑_{k₀ < j ≤ n, j ∉ S} B_j`. If `h'` batches of `(k₀, n]` belong to `S`, then
`log t_n ≤ (1 + β₀)^h' (log (t_(k₀) + W') + h' log 2)`. -/
lemma Grid.log_t_le_of_growth {K : ℕ} (g : Grid K) {k₀ n : ℕ} (hk₀ : 1 ≤ k₀) (hkn : k₀ ≤ n)
    {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) (hx : ∀ j, k₀ < j → g.ratio j ≤ 1 + β₀) (S : Finset ℕ) {W : ℝ}
    (hW : ∑ j ∈ (Finset.Ioc k₀ n).filter (· ∉ S), ((g.t j : ℝ) - g.t (j - 1)) ≤ W) :
    Real.log (g.t n) ≤ (1 + β₀) ^ ((Finset.Ioc k₀ n).filter (· ∈ S)).card *
      (Real.log (g.t k₀ + W) + ((Finset.Ioc k₀ n).filter (· ∈ S)).card * Real.log 2) := by
  have hW' : ∑ j ∈ Finset.Ioc k₀ n, (if j ∈ S then 0 else ((g.t j : ℝ) - g.t (j - 1))) ≤ W := by
    rw [Finset.sum_filter] at hW
    refine le_of_eq_of_le (Finset.sum_congr rfl fun j _ ↦ ?_) hW
    by_cases hj : j ∈ S <;> simp [hj]
  have hcard : ((Finset.Ioc k₀ n).filter (· ∈ S)).card =
      ∑ j ∈ Finset.Ioc k₀ n, if j ∈ S then 1 else 0 := Finset.card_filter _ _
  have h := g.log_t_add_sub_le hk₀ hβ₀ hx S hW' n hkn le_rfl
  rw [hcard]
  refine le_trans ?_ h
  have htn : (0 : ℝ) < g.t n := g.t_pos (by omega)
  refine Real.log_le_log htn ?_
  have : ∑ j ∈ Finset.Ioc k₀ n, (if j ∈ S then 0 else ((g.t j : ℝ) - g.t (j - 1))) ≤ W := hW'
  linarith

/-! ### Lemma `lem:chain` -/

/-- **Chain** [INC-P000, Lemma `lem:chain`]: let `Y ≥ 0`, `δ' < 1`, `D_max > 0`, `(w_j)`
nondecreasing and `S` a finite nonempty set of indices with `0 < D_j ≤ D_max` and
`w_(j+1) D_j ≥ Y` for `j ∈ S`. Then either some `j ∈ S` has `w_j D_j ≥ (1 - δ') Y`, or
`w_(j'+1) ≥ (1 - δ')^(-(|S| - 1)) Y / D_max` for every `j' ≥ max S` (written: every `j'` that
bounds `S`). Induction on `S`, adding a new maximum. -/
lemma exists_le_mul_or_forall_le_mul_of_monotone {Y δ' Dmax : ℝ} (hY : 0 ≤ Y) (hδ' : δ' < 1)
    {w D : ℕ → ℝ} (hw : Monotone w) (S : Finset ℕ) (hS : S.Nonempty)
    (hD : ∀ j ∈ S, 0 < D j ∧ D j ≤ Dmax ∧ Y ≤ w (j + 1) * D j) :
    (∃ j ∈ S, (1 - δ') * Y ≤ w j * D j) ∨
      ∀ j', (∀ j ∈ S, j ≤ j') → ((1 - δ')⁻¹) ^ (S.card - 1) * Y / Dmax ≤ w (j' + 1) := by
  have hδ : 0 < 1 - δ' := by linarith
  induction S using Finset.induction_on_max with
  | empty => exact absurd hS Finset.not_nonempty_empty
  | insert k s hks ih =>
    by_cases hex : ∃ j ∈ insert k s, (1 - δ') * Y ≤ w j * D j
    · exact Or.inl hex
    right
    simp only [not_exists, not_and, not_le] at hex
    have hk := hD k (Finset.mem_insert_self k s)
    have hDmax : 0 < Dmax := hk.1.trans_le hk.2.1
    have hks' : k ∉ s := fun h ↦ (hks k h).false
    rw [Finset.card_insert_of_notMem hks']
    intro j' hj'
    have hkj' : k ≤ j' := hj' k (Finset.mem_insert_self k s)
    have hwk1 : w (k + 1) ≤ w (j' + 1) := hw (by omega)
    rcases s.eq_empty_or_nonempty with rfl | hsne
    · simp only [Finset.card_empty, zero_add, tsub_self, pow_zero, one_mul]
      rw [div_le_iff₀ hDmax]
      have : 0 ≤ w (k + 1) := by
        by_contra h
        have h' := not_le.mp h
        nlinarith [hk.1, hk.2.2]
      nlinarith [hk.2.1, hk.2.2]
    · have hD' : ∀ j ∈ s, 0 < D j ∧ D j ≤ Dmax ∧ Y ≤ w (j + 1) * D j :=
        fun j hj ↦ hD j (Finset.mem_insert_of_mem hj)
      rcases ih hsne hD' with ⟨j, hj, hjY⟩ | hall
      · exact absurd hjY (not_le.mpr (hex j (Finset.mem_insert_of_mem hj)))
      have hk1 : 1 ≤ k := by
        obtain ⟨j, hj⟩ := hsne
        have := hks j hj
        omega
      have hwk := hall (k - 1) fun j hj ↦ by have := hks j hj; omega
      rw [show k - 1 + 1 = k by omega] at hwk
      -- `w_k D_k < (1 - δ') Y ≤ (1 - δ') w_(k+1) D_k`, so `w_k < (1 - δ') w_(k+1)`
      have hlt : w k * D k < (1 - δ') * (w (k + 1) * D k) :=
        (hex k (Finset.mem_insert_self k s)).trans_le (mul_le_mul_of_nonneg_left hk.2.2 hδ.le)
      have hlt' : w k < (1 - δ') * w (k + 1) := by
        have : w k * D k < ((1 - δ') * w (k + 1)) * D k := by linarith
        exact lt_of_mul_lt_mul_right this hk.1.le
      have hcard : 1 ≤ s.card := Finset.card_pos.mpr hsne
      have hpow : ((1 - δ')⁻¹) ^ (s.card + 1 - 1) =
          (1 - δ')⁻¹ * ((1 - δ')⁻¹) ^ (s.card - 1) := by
        rw [← pow_succ', show s.card - 1 + 1 = s.card + 1 - 1 by omega]
      rw [hpow]
      calc _ = (1 - δ')⁻¹ * (((1 - δ')⁻¹) ^ (s.card - 1) * Y / Dmax) := by ring
        _ ≤ (1 - δ')⁻¹ * w k := mul_le_mul_of_nonneg_left hwk (inv_nonneg.mpr hδ.le)
        _ ≤ w (k + 1) := by
            rw [inv_mul_le_iff₀ hδ]
            exact hlt'.le
        _ ≤ w (j' + 1) := hwk1

@[deprecated (since := "2026-11-19")] alias chain := exists_le_mul_or_forall_le_mul_of_monotone

/-! ### Lemma `lem:distinct` -/

/-- [INC-P000, Lemma `lem:distinct`(i), general form] Let `(N_j)` be a nondecreasing sequence of
integers with `N_1 ≥ 1` and `N_L ≤ M`, `g ≥ 0` and `Q` a property of integers. Then
`∑_{j=2}^L g(N_(j-1)) 1(Q(N_(j-1)), N_j > N_(j-1)) ≤ ∑_{n=1}^M g(n) 1(Q(n))`: the batches in which
the count increases start at distinct counts in `[1, M]`. The paper's `M` is `t_L`. -/
lemma sum_ite_le_sum_Icc_of_monotone {N : ℕ → ℕ} (hN : Monotone N) (hN1 : 1 ≤ N 1) {L M : ℕ}
    (hNL : N L ≤ M) {g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n) (Q : ℕ → Prop) [DecidablePred Q] :
    ∑ j ∈ Finset.Ico 2 (L + 1),
        (if Q (N (j - 1)) ∧ N (j - 1) < N j then g (N (j - 1)) else 0) ≤
      ∑ n ∈ Finset.Icc 1 M, if Q n then g n else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  set F := (Finset.Ico 2 (L + 1)).filter fun j ↦ Q (N (j - 1)) ∧ N (j - 1) < N j
  have hinj : Set.InjOn (fun j ↦ N (j - 1)) F := by
    intro j hj j' hj' hjj'
    have h1 := Finset.mem_filter.mp (Finset.mem_coe.mp hj)
    have h2 := Finset.mem_filter.mp (Finset.mem_coe.mp hj')
    have h1' := Finset.mem_Ico.mp h1.1
    have h2' := Finset.mem_Ico.mp h2.1
    have hjj : N (j - 1) = N (j' - 1) := hjj'
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have : N j ≤ N (j' - 1) := hN (by omega)
      omega
    · have : N j' ≤ N (j - 1) := hN (by omega)
      omega
  rw [← Finset.sum_image (f := g) hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ ↦ hg n
  intro n hn
  simp only [Finset.mem_image, F, Finset.mem_filter, Finset.mem_Ico] at hn
  obtain ⟨j, ⟨⟨hj2, hjL⟩, hQ, _⟩, rfl⟩ := hn
  simp only [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨hN1.trans (hN (by omega)), (hN (by omega)).trans hNL⟩, hQ⟩

/-- Telescoping: for a nondecreasing `N` and `1 ≤ L`,
`∑_{j=2}^L 1(P j) (N_j - N_(j-1)) ≤ N_L - N_1`. -/
lemma sum_ite_sub_le_sub_of_monotone {N : ℕ → ℕ} (hN : Monotone N) (P : ℕ → Prop)
    [DecidablePred P] {L : ℕ} (hL : 1 ≤ L) :
    ∑ j ∈ Finset.Ico 2 (L + 1), (if P j then N j - N (j - 1) else 0) ≤ N L - N 1 := by
  induction L, hL using Nat.le_induction with
  | base => simp
  | succ L hL ih =>
    rw [Finset.sum_Ico_succ_top (by omega), show L + 1 - 1 = L by omega]
    have hmono : N L ≤ N (L + 1) := hN (Nat.le_succ L)
    have h1 : N 1 ≤ N L := hN hL
    split_ifs <;> omega

/-- [INC-P000, Lemma `lem:distinct`(ii), general form] Let `(N_j)` be nondecreasing, `n_j =
N_j - N_(j-1)`, and `N_j ≤ M` for every `j ∈ [2, L]` with `P(j)` and `n_j > 0`. Then
`∑_{j=2}^L n_j 1(P(j)) ≤ M`: the sum is at most `N_(j*) - N_1` for the last such `j*`. -/
lemma sum_ite_sub_le_of_monotone {N : ℕ → ℕ} (hN : Monotone N) (P : ℕ → Prop) [DecidablePred P]
    {M : ℕ} (L : ℕ) (hM : ∀ j ∈ Finset.Ico 2 (L + 1), P j → N (j - 1) < N j → N j ≤ M) :
    ∑ j ∈ Finset.Ico 2 (L + 1), (if P j then N j - N (j - 1) else 0) ≤ M := by
  induction L with
  | zero => simp
  | succ L ih =>
    rcases Nat.eq_zero_or_pos L with rfl | hL
    · simp
    by_cases hlast : P (L + 1) ∧ N L < N (L + 1)
    · have hle := sum_ite_sub_le_sub_of_monotone hN P (L := L + 1) (by omega)
      have := hM (L + 1) (by simp; omega) hlast.1 (by simpa using hlast.2)
      omega
    · rw [Finset.sum_Ico_succ_top (by omega), show L + 1 - 1 = L by omega]
      have hz : (if P (L + 1) then N (L + 1) - N L else 0) = 0 := by
        have hmono : N L ≤ N (L + 1) := hN (Nat.le_succ L)
        split_ifs with hP
        · have : ¬ N L < N (L + 1) := fun h ↦ hlast ⟨hP, h⟩
          omega
        · rfl
      rw [hz, add_zero]
      exact ih fun j hj ↦ hM j (by simp only [Finset.mem_Ico] at hj ⊢; omega)

/-! ### Lemma `lem:sums`(iv)–(v) -/

/-- Telescoping over `[i₀, m]`: `∑_{i=i₀}^m (v_i - v_(i-1)) = v_m - v_(i₀-1)`. -/
lemma sum_Icc_sub_pred {v : ℕ → ℝ} {i₀ m : ℕ} (h : i₀ ≤ m) :
    ∑ i ∈ Finset.Icc i₀ m, (v i - v (i - 1)) = v m - v (i₀ - 1) := by
  induction m, h using Nat.le_induction with
  | base =>
    rw [Finset.Icc_self, Finset.sum_singleton]
  | succ m hm ih =>
    rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega), Finset.sum_insert (by simp), ih,
      show m + 1 - 1 = m by omega]
    ring

/-- **Layer cake** [INC-P000, Lemma `lem:sums`(v)]: let `0 = v_(i₀-1) ≤ v_(i₀) ≤ ⋯ ≤ v_j` and
events (here propositions) `E_(i₀), …, E_j`. Then `max_{i₀ ≤ i ≤ j} v_i 1(E_i) ≤
∑_{i=i₀}^j (v_i - v_(i-1)) 1(⋃_{i' = i}^j E_(i'))`, written for each `i` with `E_i` (the right side
is nonnegative). -/
lemma le_sum_mul_ite_exists {v : ℕ → ℝ} {i₀ j : ℕ} (hv0 : v (i₀ - 1) = 0)
    (hv : MonotoneOn v (Set.Icc (i₀ - 1) j)) (E : ℕ → Prop) [DecidablePred E]
    {i : ℕ} (hi : i ∈ Finset.Icc i₀ j) (hE : E i) :
    v i ≤ ∑ i' ∈ Finset.Icc i₀ j,
      (v i' - v (i' - 1)) * (if ∃ i'' ∈ Finset.Icc i' j, E i'' then 1 else 0) := by
  have hi' := Finset.mem_Icc.mp hi
  have hnonneg : ∀ i' ∈ Finset.Icc i₀ j, 0 ≤ v i' - v (i' - 1) := fun i' hi' ↦ by
    have := Finset.mem_Icc.mp hi'
    exact sub_nonneg.mpr (hv ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega))
  calc v i = ∑ i' ∈ Finset.Icc i₀ i, (v i' - v (i' - 1)) := by
        rw [sum_Icc_sub_pred hi'.1, hv0, sub_zero]
    _ = ∑ i' ∈ Finset.Icc i₀ i,
        (v i' - v (i' - 1)) * (if ∃ i'' ∈ Finset.Icc i' j, E i'' then 1 else 0) := by
        refine Finset.sum_congr rfl fun i' hi'' ↦ ?_
        have := Finset.mem_Icc.mp hi''
        split_ifs with hex
        · rw [mul_one]
        · exact absurd ⟨i, Finset.mem_Icc.mpr ⟨this.2, hi'.2⟩, hE⟩ hex
    _ ≤ _ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl hi'.2)
          fun i' hi'' _ ↦ mul_nonneg (hnonneg i' hi'') (by split_ifs <;> norm_num)

/-- **Counting** [INC-P000, Lemma `lem:sums`(iv)]: let `i₀ ≤ j`, `0 = λ_(i₀-1) ≤ λ_(i₀) ≤ ⋯ ≤
λ_j`, `v_i = ⌈λ_i⌉`, `β > 0` and `g ≥ 0` nonincreasing on `[0, ∞)`. Then
`∑_{i=i₀}^j (v_i - v_(i-1)) g(λ_i^(1/β)) ≤ ∑_{n < v_j} g(n^(1/β))` (the paper bounds the right
side by the series `∑_{n ≥ 0} g(n^(1/β))`): `v_i - v_(i-1)` counts the integers `n` with
`λ_(i-1) ≤ n < λ_i`, and for them `g(λ_i^(1/β)) ≤ g(n^(1/β))`. -/
lemma sum_ceil_sub_mul_le {lam : ℕ → ℝ} {i₀ j : ℕ} (hij : i₀ ≤ j) (hl0 : lam (i₀ - 1) = 0)
    (hl : MonotoneOn lam (Set.Icc (i₀ - 1) j)) {β : ℝ} (hβ : 0 < β) {g : ℝ → ℝ}
    (hg : AntitoneOn g (Set.Ici 0)) :
    ∑ i ∈ Finset.Icc i₀ j, (((⌈lam i⌉₊ : ℕ) : ℝ) - ⌈lam (i - 1)⌉₊) * g (lam i ^ (1 / β)) ≤
      ∑ n ∈ Finset.range ⌈lam j⌉₊, g ((n : ℝ) ^ (1 / β)) := by
  have hlam0 : ∀ i ∈ Set.Icc (i₀ - 1) j, 0 ≤ lam i := fun i hi ↦
    hl0 ▸ hl ⟨le_rfl, by omega⟩ hi hi.1
  -- each term is at most the sum over `n ∈ [⌈λ_(i-1)⌉, ⌈λ_i⌉)`
  have hterm : ∀ i ∈ Finset.Icc i₀ j, (((⌈lam i⌉₊ : ℕ) : ℝ) - ⌈lam (i - 1)⌉₊) *
      g (lam i ^ (1 / β)) ≤
      ∑ n ∈ Finset.Ico ⌈lam (i - 1)⌉₊ ⌈lam i⌉₊, g ((n : ℝ) ^ (1 / β)) := by
    intro i hi
    have hi' := Finset.mem_Icc.mp hi
    have hle : ⌈lam (i - 1)⌉₊ ≤ ⌈lam i⌉₊ :=
      Nat.ceil_le_ceil (hl ⟨by omega, by omega⟩ ⟨by omega, hi'.2⟩ (by omega))
    have hli : 0 ≤ lam i := hlam0 i ⟨by omega, hi'.2⟩
    calc (((⌈lam i⌉₊ : ℕ) : ℝ) - ⌈lam (i - 1)⌉₊) * g (lam i ^ (1 / β))
        = ∑ _n ∈ Finset.Ico ⌈lam (i - 1)⌉₊ ⌈lam i⌉₊, g (lam i ^ (1 / β)) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hle]
      _ ≤ _ := by
          refine Finset.sum_le_sum fun n hn ↦ ?_
          have hn' : (n : ℝ) < lam i := by
            have := (Finset.mem_Ico.mp hn).2
            exact (Nat.lt_ceil).mp this
          have h1 : 0 ≤ (n : ℝ) ^ (1 / β) := rpow_nonneg (Nat.cast_nonneg n) _
          refine hg (Set.mem_Ici.mpr h1) (Set.mem_Ici.mpr (rpow_nonneg hli _)) ?_
          exact rpow_le_rpow (Nat.cast_nonneg n) hn'.le (by positivity)
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  -- the intervals `[⌈λ_(i-1)⌉, ⌈λ_i⌉)` tile `[0, ⌈λ_j⌉)`
  have htile : ∀ m, i₀ ≤ m → m ≤ j → ∑ i ∈ Finset.Icc i₀ m,
      ∑ n ∈ Finset.Ico ⌈lam (i - 1)⌉₊ ⌈lam i⌉₊, g ((n : ℝ) ^ (1 / β)) =
      ∑ n ∈ Finset.range ⌈lam m⌉₊, g ((n : ℝ) ^ (1 / β)) := by
    intro m hm hmj
    induction m, hm using Nat.le_induction with
    | base =>
      rw [Finset.Icc_self, Finset.sum_singleton, hl0, Nat.ceil_zero, Finset.range_eq_Ico]
    | succ m hm ih =>
      rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega), Finset.sum_insert (by simp),
        ih (by omega),
        show m + 1 - 1 = m by omega, Finset.range_eq_Ico, Finset.range_eq_Ico, add_comm]
      refine Finset.sum_Ico_consecutive _ (Nat.zero_le _) ?_
      exact Nat.ceil_le_ceil (hl ⟨by omega, by omega⟩ ⟨by omega, hmj⟩ (by omega))
  exact htile j hij le_rfl

/-- Telescoping over `(j₀, L]` in an additive commutative group:
`∑_(j₀ < j ≤ L) (f_j - f_(j-1)) = f_L - f_(j₀)`. -/
lemma sum_Ioc_sub_pred {M : Type*} [AddCommGroup M] {f : ℕ → M} {j₀ L : ℕ} (h : j₀ ≤ L) :
    ∑ j ∈ Finset.Ioc j₀ L, (f j - f (j - 1)) = f L - f j₀ := by
  induction L, h using Nat.le_induction with
  | base => simp
  | succ L hL ih =>
    rw [Finset.sum_Ioc_succ_top hL, ih, Nat.add_sub_cancel]
    abel

/-- [INC-P000, proof of Lemma `lem:decompC`, Steps 1–4, abstract form] Let `(N_j)` be a
nondecreasing sequence of integers (the counts `N_a(t_j)`), `1 ≤ j₀ ≤ L`, and let every batch
`j ∈ (j₀, L]` be in one of four classes, with increments `n_j = N_j - N_(j-1)`:
* *bad* (the deviations `𝒟_j ∪ 𝒱⋆_j ∪ 𝒱_(a,j)`): `n_j ≤ B_j`;
* *good* (`𝒢_j` with `a` rejected, Lemma `lem:pullsC`(ii)): if `a` is pulled, `N_j ≤ M`;
* *other* (`𝒪_j` with `a` rejected, Lemmas `lem:pullsC`(ii), `lem:logcountC`): if `a` is pulled,
  `N_j ≤ C N_(j-1)` and `Q(N_(j-1))` (the empirical divergence of `a` at `N_(j-1)` is low);
* *ambiguous* (`a` ambiguous in an activated batch, Lemma `lem:pullsC`(iii)): `n_j ≤ c_j`.
Then, for `M, C ≥ 0`, `B, c ≥ 0`,
`N_L ≤ N_(j₀) + M + ∑_(j₀ < j ≤ L) B_j 1(bad_j) + C ∑_(2 ≤ j ≤ L) N_(j-1) 1(Q(N_(j-1)), n_j > 0)
  + ∑_(j₀ < j ≤ L) c_j 1(amb_j)`:
the good increments sum to at most `M` (Lemma `lem:distinct`(ii)), and the last sum of the other
class is the one of Lemma `lem:controlC`(d) (`lintegral_sum_ite_pseudoKinf_lt_le`), at most
`∑_n n 1(Q(n))` by Lemma `lem:distinct`(i). -/
lemma le_add_sum_of_classes {N : ℕ → ℕ} (hN : Monotone N) {j₀ L : ℕ} (hj₀ : 1 ≤ j₀)
    (hjL : j₀ ≤ L) (bad G O A Q : ℕ → Prop) [DecidablePred bad] [DecidablePred A]
    [DecidablePred Q] {B c : ℕ → ℝ} {M C : ℝ} (hB0 : ∀ j, 0 ≤ B j)
    (hc0 : ∀ j, 0 ≤ c j) (hM0 : 0 ≤ M) (hC0 : 0 ≤ C)
    (hcover : ∀ j, j₀ < j → j ≤ L → bad j ∨ G j ∨ O j ∨ A j)
    (hbad : ∀ j, j₀ < j → j ≤ L → bad j → (N j : ℝ) - N (j - 1) ≤ B j)
    (hG : ∀ j, j₀ < j → j ≤ L → G j → N (j - 1) < N j → (N j : ℝ) ≤ M)
    (hO : ∀ j, j₀ < j → j ≤ L → O j → N (j - 1) < N j → (N j : ℝ) ≤ C * N (j - 1) ∧ Q (N (j - 1)))
    (hA : ∀ j, j₀ < j → j ≤ L → A j → (N j : ℝ) - N (j - 1) ≤ c j) :
    (N L : ℝ) ≤ N j₀ + M + ∑ j ∈ Finset.Ioc j₀ L, (if bad j then B j else 0) +
      C * ∑ j ∈ Finset.Ico 2 (L + 1),
        (if Q (N (j - 1)) ∧ N (j - 1) < N j then (N (j - 1) : ℝ) else 0) +
      ∑ j ∈ Finset.Ioc j₀ L, (if A j then c j else 0) := by
  classical
  set PG : ℕ → Prop := fun j ↦ j₀ < j ∧ ¬ bad j ∧ G j with hPG
  set Ot : ℕ → ℝ := fun j ↦
    if Q (N (j - 1)) ∧ N (j - 1) < N j then (N (j - 1) : ℝ) else 0 with hOt
  have hOt0 : ∀ j, 0 ≤ Ot j := fun j ↦ by simp only [hOt]; split_ifs <;> positivity
  have hmono : ∀ j, (N (j - 1) : ℝ) ≤ N j := fun j ↦ by exact_mod_cast hN (Nat.sub_le j 1)
  -- the bound of one increment
  have hterm : ∀ j ∈ Finset.Ioc j₀ L, (N j : ℝ) - N (j - 1) ≤
      (if bad j then B j else 0) + (if PG j then ((N j - N (j - 1) : ℕ) : ℝ) else 0) +
        C * Ot j + (if A j then c j else 0) := by
    intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Ioc.mp hj
    have hsub : ((N j - N (j - 1) : ℕ) : ℝ) = (N j : ℝ) - N (j - 1) :=
      Nat.cast_sub (hN (Nat.sub_le j 1))
    have hA0 : 0 ≤ (if A j then c j else 0) := by split_ifs <;> simp [hc0]
    have hB0' : 0 ≤ (if bad j then B j else 0) := by split_ifs <;> simp [hB0]
    have hPG0 : 0 ≤ (if PG j then ((N j - N (j - 1) : ℕ) : ℝ) else 0) := by
      split_ifs <;> positivity
    have hCO : 0 ≤ C * Ot j := mul_nonneg hC0 (hOt0 j)
    by_cases hb : bad j
    · rw [ite_eq_left hb]
      linarith [hbad j hj1 hj2 hb]
    by_cases hg : G j
    · rw [ite_eq_left (show PG j from ⟨hj1, hb, hg⟩), hsub]
      linarith
    rcases (hcover j hj1 hj2).resolve_left hb |>.resolve_left hg with ho | ha
    · by_cases hpull : N (j - 1) < N j
      · obtain ⟨hle, hq⟩ := hO j hj1 hj2 ho hpull
        have : Ot j = N (j - 1) := by simp only [hOt]; rw [ite_eq_left ⟨hq, hpull⟩]
        rw [this]
        have : (0 : ℝ) ≤ N (j - 1) := Nat.cast_nonneg _
        linarith
      · have : (N j : ℝ) = N (j - 1) := by
          exact_mod_cast le_antisymm (not_lt.mp hpull) (hN (Nat.sub_le j 1))
        linarith
    · rw [ite_eq_left ha]
      linarith [hA j hj1 hj2 ha]
  -- sum over the batches
  have htel := sum_Ioc_sub_pred (f := fun j ↦ (N j : ℝ)) hjL
  have hsum := Finset.sum_le_sum hterm
  rw [htel, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  -- the good increments: Lemma `lem:distinct`(ii)
  have hgood : ∑ j ∈ Finset.Ioc j₀ L, (if PG j then ((N j - N (j - 1) : ℕ) : ℝ) else 0) ≤ M := by
    have hsub : ∑ j ∈ Finset.Ioc j₀ L, (if PG j then ((N j - N (j - 1) : ℕ) : ℝ) else 0) =
        ((∑ j ∈ Finset.Ico 2 (L + 1), (if PG j then N j - N (j - 1) else 0) : ℕ) : ℝ) := by
      rw [Nat.cast_sum]
      have hss : Finset.Ioc j₀ L ⊆ Finset.Ico 2 (L + 1) := fun j hj ↦
        Finset.mem_Ico.mpr ⟨by have := (Finset.mem_Ioc.mp hj).1; omega,
          by have := (Finset.mem_Ioc.mp hj).2; omega⟩
      have h1 := Finset.sum_subset hss (f := fun j ↦
        ((if PG j then N j - N (j - 1) else 0 : ℕ) : ℝ)) (fun j hj hjn ↦ by
          have : ¬ PG j := fun hP ↦ hjn (Finset.mem_Ioc.mpr ⟨hP.1, by
            have := (Finset.mem_Ico.mp hj).2; omega⟩)
          simp only [this, ite_false, Nat.cast_zero])
      rw [← h1]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      split_ifs <;> simp
    rw [hsub]
    have hle := sum_ite_sub_le_of_monotone hN PG (M := ⌊M⌋₊) L (fun j hj hP hpull ↦ by
      obtain ⟨hj1, hb, hg⟩ := hP
      exact Nat.le_floor (hG j hj1 (by have := (Finset.mem_Ico.mp hj).2; omega) hg hpull))
    exact (Nat.cast_le.mpr hle).trans (Nat.floor_le hM0)
  -- the other class: the sum over `(j₀, L]` is at most the sum over `[2, L]`
  have hother : ∑ j ∈ Finset.Ioc j₀ L, C * Ot j ≤ C * ∑ j ∈ Finset.Ico 2 (L + 1), Ot j := by
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg (fun j hj ↦ ?_)
      fun j _ _ ↦ hOt0 j) hC0
    exact Finset.mem_Ico.mpr ⟨by have := (Finset.mem_Ioc.mp hj).1; omega,
      by have := (Finset.mem_Ioc.mp hj).2; omega⟩
  simp only [hOt] at hother hsum ⊢
  linarith

/-- [INC-P000, proof of Lemma `lem:decompC`, Step 3, the main term] If `N ≤ K + (1 + ω) y L_j / D`
(Lemma `lem:pullsC`(ii)) with `D ≥ D' > 0`, `(1 + ω) y ≤ 1 + ε`, `0 ≤ L_j ≤ L_L` and
`(1 + ε)/D' ≤ 1/Δ + C₁ε` (Lemma `lem:constC`(b), `dInf_sub_shift_bounds_of_gap_pos`), then `N ≤ K +
L_L/Δ + C₁ ε L_L`. -/
lemma le_add_div_add_mul_of_le_add_div {N K ω y Lj LL D D' ε Δ C₁ : ℝ} (hN : N ≤ K +
    (1 + ω) * y * Lj / D)
    (hD' : 0 < D') (hDD : D' ≤ D) (hωy0 : 0 ≤ (1 + ω) * y) (hωy : (1 + ω) * y ≤ 1 + ε)
    (hLj : 0 ≤ Lj) (hLL : Lj ≤ LL) (hC : (1 + ε) / D' ≤ 1 / Δ + C₁ * ε) :
    N ≤ K + LL / Δ + C₁ * ε * LL := by
  have hD : 0 < D := hD'.trans_le hDD
  have hLL0 : 0 ≤ LL := hLj.trans hLL
  have h1 : (1 + ω) * y * Lj / D ≤ (1 + ε) * LL / D' := by
    rw [div_le_div_iff₀ hD hD']
    have h2 : (1 + ω) * y * Lj ≤ (1 + ε) * LL := by
      calc (1 + ω) * y * Lj ≤ (1 + ε) * Lj := mul_le_mul_of_nonneg_right hωy hLj
        _ ≤ (1 + ε) * LL := mul_le_mul_of_nonneg_left hLL (by nlinarith)
    have h3 : 0 ≤ (1 + ε) * LL := le_trans (mul_nonneg hωy0 hLj) h2
    calc (1 + ω) * y * Lj * D' ≤ (1 + ε) * LL * D' := mul_le_mul_of_nonneg_right h2 hD'.le
      _ ≤ (1 + ε) * LL * D := mul_le_mul_of_nonneg_left hDD h3
  have h4 : (1 + ε) * LL / D' = (1 + ε) / D' * LL := by ring
  have h5 : (1 + ε) / D' * LL ≤ (1 / Δ + C₁ * ε) * LL := mul_le_mul_of_nonneg_right hC hLL0
  have h6 : (1 / Δ + C₁ * ε) * LL = LL / Δ + C₁ * ε * LL := by ring
  linarith

/-- [INC-P000, proof of Lemma `lem:decompC`, Step 4, the class `𝒪`] If `N ≤ K + 16 ȳ L_j / ε²`
(Lemma `lem:pullsC`(ii) with `D ≥ ε²/8`, `1 + ω ≤ 2`, `y ≤ ȳ`), `N' ≥ 1` and
`(1 - δ) L_j ≤ (κ + 1) N'` (Lemma `lem:logcountC`, `N' = N_a(t_(j-1))`), with `K, ȳ ≥ 0`,
`κ ≥ 0`, `δ < 1` and `ε > 0`, then `N ≤ C_ε N'`, `C_ε = K + 16 ȳ (κ + 1)/((1 - δ) ε²)`. -/
lemma le_mul_of_le_add_div_sq {N K yb Lj ε N' δ κ : ℝ} (hN : N ≤ K + 16 * yb * Lj / ε ^ 2)
    (hK : 0 ≤ K) (hyb : 0 ≤ yb) (hε : 0 < ε) (hN' : 1 ≤ N') (hδ : δ < 1) (hκ : 0 ≤ κ)
    (hlog : (1 - δ) * Lj ≤ (κ + 1) * N') :
    N ≤ (K + 16 * yb * (κ + 1) / ((1 - δ) * ε ^ 2)) * N' := by
  have h1δ : 0 < 1 - δ := by linarith
  have hLj : Lj ≤ (κ + 1) * N' / (1 - δ) := by rw [le_div_iff₀ h1δ]; linarith
  have h1 : 16 * yb * Lj / ε ^ 2 ≤ 16 * yb * (κ + 1) / ((1 - δ) * ε ^ 2) * N' := by
    have h2 : 16 * yb * (κ + 1) / ((1 - δ) * ε ^ 2) * N' = 16 * yb * ((κ + 1) * N' / (1 - δ)) /
        ε ^ 2 := by
      field_simp
    rw [h2]
    gcongr
  have h3 : K ≤ K * N' := le_mul_of_one_le_right hK hN'
  calc N ≤ K + 16 * yb * Lj / ε ^ 2 := hN
    _ ≤ K * N' + 16 * yb * (κ + 1) / ((1 - δ) * ε ^ 2) * N' := add_le_add h3 h1
    _ = (K + 16 * yb * (κ + 1) / ((1 - δ) * ε ^ 2)) * N' := by ring

end Incognita.BatchedBandits
