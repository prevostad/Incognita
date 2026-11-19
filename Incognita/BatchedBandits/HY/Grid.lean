/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.HY
public import Incognita.BatchedBandits.Counting
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # The grid quantities of HY: activated batches

[INC-P000, Lemma `lem:sparse`]. Batch `ℓ + 1` is **activated** (it has paced rounds) if
`t_(ℓ+1) > s_ℓ = ⌊t_ℓ^(1+ϑ_ℓ)⌋`, i.e. `g.imedEnd θ ℓ < g.t (ℓ + 1)` [INC-P000,
Definition `def:hy-vocab`]; activation is a property of the grid alone.

* `Grid.mul_logEnd_lt_logEnd_succ`: Step 1 of the proof of Lemma `lem:sparse`, an activated batch
  makes `L` jump: `L_(ℓ+1) > (1 + ϑ_ℓ) L_ℓ`.
* `Grid.card_activated_le`: Lemma `lem:sparse`, with the default `ϑ`: at most `k + 1` activated
  batches `ℓ` with `t_ℓ ≥ e^e` have `L_ℓ ∈ [2^k, 2^(k+1))`.
* `Grid.sum_activated_le`: the sum of Lemma `lem:sparse`,
  `∑_{ℓ activated, t_ℓ ≥ e^e} f(L_ℓ) ≤ ∑_{k ≥ 1} (k + 1) sup_{[2^k, 2^(k+1))} f`.
-/

@[expose] public section

open Real Finset Filter

namespace Incognita.BatchedBandits

variable {K : ℕ}

namespace Grid

variable (g : Grid K)

/-- [INC-P000, proof of Lemma `lem:sparse`, Step 1] If batch `ℓ + 1` is activated
(`s_ℓ < t_(ℓ+1)`), then `L_(ℓ+1) > (1 + ϑ_ℓ) L_ℓ`, since `t_(ℓ+1) ≥ s_ℓ + 1 > t_ℓ^(1+ϑ_ℓ)`. -/
lemma mul_logEnd_lt_logEnd_succ {θ : ℕ → ℝ} {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (hact : g.imedEnd θ ℓ < g.t (ℓ + 1)) : (1 + θ ℓ) * g.logEnd ℓ < g.logEnd (ℓ + 1) := by
  have ht := g.t_pos hℓ
  have hlt : (g.t ℓ : ℝ) ^ (1 + θ ℓ) < g.t (ℓ + 1) := by
    have h1 := Nat.lt_floor_add_one ((g.t ℓ : ℝ) ^ (1 + θ ℓ))
    have h2 : (⌊(g.t ℓ : ℝ) ^ (1 + θ ℓ)⌋₊ : ℝ) + 1 ≤ g.t (ℓ + 1) := by
      exact_mod_cast hact
    linarith
  unfold logEnd
  rw [← Real.log_rpow ht]
  exact Real.log_lt_log (rpow_pos_of_pos ht _) hlt

/-- With the default `ϑ`, `ϑ_ℓ = 1 / log L_ℓ` when `t_ℓ ≥ e^e`. -/
lemma hyTheta_eq {ℓ : ℕ} (h : Real.exp (Real.exp 1) ≤ (g.t ℓ : ℝ)) :
    g.hyTheta ℓ = 1 / Real.log (g.logEnd ℓ) := by
  simp [hyTheta, h, logEnd]

/-- `L_ℓ ≥ e` when `t_ℓ ≥ e^e`. -/
lemma exp_one_le_logEnd {ℓ : ℕ} (h : Real.exp (Real.exp 1) ≤ (g.t ℓ : ℝ)) :
    Real.exp 1 ≤ g.logEnd ℓ := by
  unfold logEnd
  rw [← Real.log_exp (Real.exp 1)]
  exact Real.log_le_log (exp_pos _) h

/-- `log L_ℓ ≥ 1` when `t_ℓ ≥ e^e`. -/
lemma one_le_log_logEnd {ℓ : ℕ} (h : Real.exp (Real.exp 1) ≤ (g.t ℓ : ℝ)) :
    1 ≤ Real.log (g.logEnd ℓ) := by
  have he := g.exp_one_le_logEnd h
  rw [← Real.log_exp 1]
  exact Real.log_le_log (exp_pos 1) he

/-- [INC-P000, Lemma `lem:sparse`] With the default `ϑ`, for every `k`, the number of activated
batches `ℓ` (`s_ℓ < t_(ℓ+1)`) with `t_ℓ ≥ e^e` and `L_ℓ ∈ [2^k, 2^(k+1))` is at most `k + 1`:
written for every finite set `S` of such batches. The paper's `k ≥ 1` is not assumed: for `k = 0`
the set is empty (`L_ℓ ≥ e`). -/
lemma card_activated_le {k : ℕ} (S : Finset ℕ)
    (hS : ∀ ℓ ∈ S, g.imedEnd g.hyTheta ℓ < g.t (ℓ + 1) ∧
      Real.exp (Real.exp 1) ≤ (g.t ℓ : ℝ) ∧ (2 : ℝ) ^ k ≤ g.logEnd ℓ ∧
      g.logEnd ℓ < 2 ^ (k + 1)) :
    S.card ≤ k + 1 := by
  -- Each jump is by a factor at least `1 + u`, `u = 1 / ((k + 1) log 2)`, the block has ratio `2`,
  -- so `(|S| - 1) u / 2 < log 2`, and `2 (log 2)² < 1`.
  set u : ℝ := 1 / ((k + 1) * Real.log 2) with hu
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hu0 : 0 < u := by positivity
  -- every element of `S` has `ℓ ≥ 1` (since `t_ℓ ≥ e^e > 0 = t_0`)
  have hpos : ∀ ℓ ∈ S, 1 ≤ ℓ := by
    intro ℓ hℓ
    rcases Nat.eq_zero_or_pos ℓ with rfl | h
    · have := (hS 0 hℓ).2.1
      rw [g.t_zero, Nat.cast_zero] at this
      exact absurd this (not_le.mpr (exp_pos _))
    · exact h
  -- the jump of a batch of `S`
  have hjump : ∀ ℓ ∈ S, (1 + u) * g.logEnd ℓ < g.logEnd (ℓ + 1) := by
    intro ℓ hℓ
    obtain ⟨hact, he, -, hlt⟩ := hS ℓ hℓ
    have hL := g.logEnd_pos (hpos ℓ hℓ)
    have hθ : u < g.hyTheta ℓ := by
      rw [g.hyTheta_eq he, hu]
      have h1 := g.one_le_log_logEnd he
      have h2 : Real.log (g.logEnd ℓ) < (k + 1) * Real.log 2 := by
        have := Real.log_lt_log hL hlt
        rwa [Real.log_pow, Nat.cast_add, Nat.cast_one] at this
      exact one_div_lt_one_div_of_lt (by linarith) h2
    calc (1 + u) * g.logEnd ℓ < (1 + g.hyTheta ℓ) * g.logEnd ℓ :=
          mul_lt_mul_of_pos_right (by linarith) hL
      _ < _ := g.mul_logEnd_lt_logEnd_succ (hpos ℓ hℓ) hact
  -- the chain of jumps
  have hchain : ∀ T ⊆ S, T.Nonempty → ∃ m ∈ T, (∀ x ∈ T, x ≤ m) ∧
      (1 + u) ^ (T.card - 1) * 2 ^ k ≤ g.logEnd m := by
    intro T
    induction T using Finset.induction_on_max with
    | empty => intro _ h; exact absurd h Finset.not_nonempty_empty
    | insert a s has ih =>
      intro hT _
      have haS : a ∈ S := hT (Finset.mem_insert_self a s)
      have has' : a ∉ s := fun h ↦ (has a h).false
      rcases s.eq_empty_or_nonempty with rfl | hs
      · refine ⟨a, Finset.mem_insert_self a ∅, fun x hx ↦ ?_, ?_⟩
        · simp only [Finset.insert_empty, Finset.mem_singleton] at hx
          exact hx.le
        · simpa using (hS a haS).2.2.1
      · obtain ⟨m, hm, hmax, hbound⟩ :=
          ih (fun x hx ↦ hT (Finset.mem_insert_of_mem hx)) hs
        refine ⟨a, Finset.mem_insert_self a s, fun x hx ↦ ?_, ?_⟩
        · rcases Finset.mem_insert.mp hx with rfl | hx
          · exact le_rfl
          · exact (has x hx).le
        · rw [Finset.card_insert_of_notMem has']
          have hma : m < a := has m hm
          have hcard : 1 ≤ s.card := Finset.card_pos.mpr hs
          have hmS : m ∈ S := hT (Finset.mem_insert_of_mem hm)
          calc (1 + u) ^ (s.card + 1 - 1) * 2 ^ k
              = (1 + u) * ((1 + u) ^ (s.card - 1) * 2 ^ k) := by
                rw [show s.card + 1 - 1 = s.card - 1 + 1 by omega, pow_succ]
                ring
            _ ≤ (1 + u) * g.logEnd m := mul_le_mul_of_nonneg_left hbound (by linarith)
            _ ≤ g.logEnd (m + 1) := (hjump m hmS).le
            _ ≤ g.logEnd a := g.monotone_logEnd (by omega)
  rcases S.eq_empty_or_nonempty with rfl | hSne
  · simp
  obtain ⟨m, hm, -, hbound⟩ := hchain S subset_rfl hSne
  have hlt := (hS m hm).2.2.2
  -- `(1 + u)^(|S| - 1) < 2`
  have h2 : (1 + u) ^ (S.card - 1) < 2 := by
    have h2k : (0 : ℝ) < 2 ^ k := by positivity
    have : (1 + u) ^ (S.card - 1) * 2 ^ k < 2 * 2 ^ k := by
      calc _ ≤ g.logEnd m := hbound
        _ < 2 ^ (k + 1) := hlt
        _ = 2 * 2 ^ k := by ring
    exact lt_of_mul_lt_mul_right this h2k.le
  have hlog : ((S.card - 1 : ℕ) : ℝ) * Real.log (1 + u) < Real.log 2 := by
    rw [← Real.log_pow]
    exact Real.log_lt_log (by positivity) h2
  -- `k ≥ 1`, since `L_m ≥ e > 2`
  have hk1 : 1 ≤ k := by
    by_contra hk
    have hk0 : k = 0 := by omega
    have he := g.exp_one_le_logEnd (hS m hm).2.1
    have := Real.exp_one_gt_d9
    rw [hk0] at hlt
    norm_num at hlt
    linarith
  -- `log (1 + u) ≥ u / 2`, as `u ≤ 1`
  have hu1 : u ≤ 1 := by
    rw [hu, div_le_one (by positivity)]
    have : (1 : ℝ) / 2 < Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    nlinarith
  have hlogu : u / 2 ≤ Real.log (1 + u) := by
    have h := Real.one_sub_inv_le_log_of_pos (x := 1 + u) (by linarith)
    have : u / 2 ≤ 1 - (1 + u)⁻¹ := by
      rw [show 1 - (1 + u)⁻¹ = u / (1 + u) by field_simp; ring]
      exact div_le_div_of_nonneg_left hu0.le (by linarith) (by linarith)
    linarith
  have hm1 : ((S.card - 1 : ℕ) : ℝ) * (u / 2) < Real.log 2 :=
    (mul_le_mul_of_nonneg_left hlogu (Nat.cast_nonneg _)).trans_lt hlog
  -- so `|S| - 1 < 2 (k + 1) (log 2)² < k + 1`
  have hsq : Real.log 2 ^ 2 < 1 / 2 := by
    have := Real.log_two_lt_d9
    nlinarith
  have hfin : ((S.card - 1 : ℕ) : ℝ) < k + 1 := by
    have hk1 : (0 : ℝ) < k + 1 := by positivity
    have e : ((S.card - 1 : ℕ) : ℝ) * (u / 2) =
        ((S.card - 1 : ℕ) : ℝ) / (2 * ((k + 1) * Real.log 2)) := by
      rw [hu]
      field_simp
    rw [e, div_lt_iff₀ (by positivity)] at hm1
    nlinarith
  have : S.card - 1 < k + 1 := by exact_mod_cast hfin
  omega

/-- [INC-P000, Lemma `lem:sparse`, the sum] With the default `ϑ`, let `S` be a finite set of
activated batches `ℓ` with `t_ℓ ≥ e^e` and `L_ℓ < 2^κ`, `f ≥ 0` on `[1, ∞)` and `M_k` a bound of
`f` on `[2^k, 2^(k+1))`. Then `∑_{ℓ ∈ S} f(L_ℓ) ≤ ∑_{1 ≤ k < κ} (k + 1) M_k` (the paper writes
`M_k = sup_{[2^k, 2^(k+1))} f` and the series over `k ≥ 1`). The dyadic block of `L_ℓ` is
`k = Nat.log 2 ⌊L_ℓ⌋`. -/
lemma sum_activated_le {κ : ℕ} (S : Finset ℕ)
    (hS : ∀ ℓ ∈ S, g.imedEnd g.hyTheta ℓ < g.t (ℓ + 1) ∧
      Real.exp (Real.exp 1) ≤ (g.t ℓ : ℝ) ∧ g.logEnd ℓ < 2 ^ κ)
    {f : ℝ → ℝ} (hf : ∀ y, 1 ≤ y → 0 ≤ f y) {M : ℕ → ℝ}
    (hM : ∀ k, ∀ y, (2 : ℝ) ^ k ≤ y → y < 2 ^ (k + 1) → f y ≤ M k) :
    ∑ ℓ ∈ S, f (g.logEnd ℓ) ≤ ∑ k ∈ Finset.Ico 1 κ, ((k : ℝ) + 1) * M k := by
  set blk : ℕ → ℕ := fun ℓ ↦ Nat.log 2 ⌊g.logEnd ℓ⌋₊ with hblk
  -- the block of `L_ℓ`
  have hblock : ∀ ℓ ∈ S, (2 : ℝ) ^ blk ℓ ≤ g.logEnd ℓ ∧ g.logEnd ℓ < 2 ^ (blk ℓ + 1) ∧
      1 ≤ blk ℓ := by
    intro ℓ hℓ
    have he := g.exp_one_le_logEnd (hS ℓ hℓ).2.1
    have he2 : (2 : ℝ) < Real.exp 1 := by
      have := Real.exp_one_gt_d9
      linarith
    have hL0 : 0 ≤ g.logEnd ℓ := by linarith [exp_pos 1]
    have hfl : 2 ≤ ⌊g.logEnd ℓ⌋₊ := Nat.le_floor (by norm_num; linarith)
    refine ⟨?_, ?_, Nat.log_pos (by norm_num) hfl⟩
    · have h1 : 2 ^ blk ℓ ≤ ⌊g.logEnd ℓ⌋₊ := Nat.pow_log_le_self 2 (by omega)
      calc (2 : ℝ) ^ blk ℓ = ((2 ^ blk ℓ : ℕ) : ℝ) := by norm_cast
        _ ≤ (⌊g.logEnd ℓ⌋₊ : ℝ) := by exact_mod_cast h1
        _ ≤ g.logEnd ℓ := Nat.floor_le hL0
    · have h1 : ⌊g.logEnd ℓ⌋₊ < 2 ^ (blk ℓ + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
      have h2 : ⌊g.logEnd ℓ⌋₊ + 1 ≤ 2 ^ (blk ℓ + 1) := h1
      calc g.logEnd ℓ < (⌊g.logEnd ℓ⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
        _ ≤ ((2 ^ (blk ℓ + 1) : ℕ) : ℝ) := by exact_mod_cast h2
        _ = 2 ^ (blk ℓ + 1) := by norm_cast
  have hmaps : ∀ ℓ ∈ S, blk ℓ ∈ Finset.Ico 1 κ := by
    intro ℓ hℓ
    obtain ⟨h1, -, h3⟩ := hblock ℓ hℓ
    have : (2 : ℝ) ^ blk ℓ < 2 ^ κ := h1.trans_lt (hS ℓ hℓ).2.2
    have : blk ℓ < κ := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp this
    exact Finset.mem_Ico.mpr ⟨h3, this⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_le_sum fun k _ ↦ ?_
  have hMk : 0 ≤ M k := (hf _ (one_le_pow₀ (by norm_num))).trans
    (hM k _ le_rfl (pow_lt_pow_right₀ (by norm_num) (Nat.lt_succ_self k)))
  have hcard : (S.filter fun ℓ ↦ blk ℓ = k).card ≤ k + 1 := by
    refine g.card_activated_le _ fun ℓ hℓ ↦ ?_
    obtain ⟨hℓS, rfl⟩ := Finset.mem_filter.mp hℓ
    obtain ⟨h1, h2, -⟩ := hblock ℓ hℓS
    exact ⟨(hS ℓ hℓS).1, (hS ℓ hℓS).2.1, h1, h2⟩
  calc ∑ ℓ ∈ S with blk ℓ = k, f (g.logEnd ℓ) ≤ ∑ ℓ ∈ S with blk ℓ = k, M k := by
        refine Finset.sum_le_sum fun ℓ hℓ ↦ ?_
        obtain ⟨hℓS, rfl⟩ := Finset.mem_filter.mp hℓ
        obtain ⟨h1, h2, -⟩ := hblock ℓ hℓS
        exact hM _ _ h1 h2
    _ = (S.filter fun ℓ ↦ blk ℓ = k).card * M k := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((k : ℝ) + 1) * M k := by
        refine mul_le_mul_of_nonneg_right ?_ hMk
        exact_mod_cast hcard

end Grid

end Incognita.BatchedBandits
