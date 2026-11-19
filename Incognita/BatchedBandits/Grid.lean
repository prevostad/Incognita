/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Imposed grids of batches

An imposed grid for `K` arms is a strictly increasing sequence of batch ends
`0 = t 0 < t 1 < t 2 < ⋯` with `max 2 K ≤ t 1` [INC-P006, Definition `def:grid`].

**Rounds are numbered from `0`**, as in LML: the round `t ≥ 1` of the paper is the round `t - 1`
here. Batch `ℓ ≥ 1` is the set of rounds `t (ℓ - 1), …, t ℓ - 1`, the batch of a round `n` is
`min {ℓ ≥ 1 | n < t ℓ}` (`Grid.batchOf`), and the rewards available during batch `ℓ + 1` are those
of the rounds `< t ℓ`. A quantity evaluated at a batch end `t ℓ` (a count `pullCount A a (t ℓ)`,
the regret) is the same in both numberings.

## Main definitions

* `Incognita.BatchedBandits.Grid K`: a grid for `K` arms.
* `Incognita.BatchedBandits.Grid.batchOf g n`: the batch of the round `n`.
* `Incognita.BatchedBandits.Grid.logEnd g ℓ`: `L_ℓ = log t_ℓ`.
* `Incognita.BatchedBandits.Grid.ratio g ℓ`: `x_ℓ = L_ℓ / L_{ℓ-1}` for `ℓ ≥ 2`, and `x_1 = 1`.
* `Incognita.BatchedBandits.Grid.IsFiner g g'`: every batch end of `g'` is a batch end of `g`.
* `Incognita.BatchedBandits.Grid.sequential`, `Grid.geometric`, `Grid.doublyExp`: the grids
  `t ℓ = s + ℓ - 1`, `t ℓ = s 2 ^ (ℓ - 1)` and `t ℓ = s ^ 2 ^ (ℓ - 1)` (for `ℓ ≥ 1`)
  [INC-P006, Definition `def:exgrids`].

## Main statements

* `Grid.batchOf_eq_iff`: `batchOf n = ℓ + 1` if and only if `t ℓ ≤ n < t (ℓ + 1)`.
* `Grid.sequential_batchOf`: on the sequential grid every round `n ≥ s` is a batch on its own.
* `Grid.not_exists_t_eq_id`: the sequence `t ℓ = ℓ` is not a grid.
* `Grid.ratio_doublyExp`: the ratios of the doubly exponential grid are all `2`;
  `Grid.tendsto_ratio_sequential`, `Grid.tendsto_ratio_geometric`: those of the sequential and
  geometric grids tend to `1`.
* The basic API of `t`, `logEnd` and `ratio`: `Grid.t_pos`, `Grid.t_le_t`, `Grid.logEnd_zero`,
  `Grid.logEnd_nonneg`, `Grid.ratio_one`, `Grid.ratio_of_two_le`, `Grid.one_le_ratio`,
  `Grid.isFiner_refl`, `Grid.IsFiner.trans`, `Grid.monotone_logEnd`,
  `Grid.tendsto_logEnd_atTop`, `Grid.exp_logEnd`, `Grid.logEnd_succ_eq`,
  `Grid.tendsto_log_t_add_two_div_log_t` (`L_(ℓ+2) / L_ℓ → x²` when `x_ℓ → x`),
  `Grid.eq_of_forall_one_le_t_eq`, `Grid.logEnd_eq_of_t_eq`, `Grid.ratio_eq_of_t_eq` and
  `Grid.t_batchOf_sub_one_le_of_isFiner`.
-/

@[expose] public section

open Real

namespace Incognita.BatchedBandits

/-- An **imposed grid** for `K` arms [INC-P006, Definition `def:grid`]: batch ends
`0 = t 0 < t 1 < t 2 < ⋯`, strictly increasing, with `max 2 K ≤ t 1`. In 0-based rounds, batch
`ℓ ≥ 1` is the set of rounds `t (ℓ - 1), …, t ℓ - 1`, of size `t ℓ - t (ℓ - 1) ≥ 1`; `t ℓ` is its
end. The number of arms is a parameter because the condition `K ≤ t 1` is part of a grid. -/
@[ext]
structure Grid (K : ℕ) where
  /-- The batch ends: `t 0 = 0`, and `t ℓ` is the end of batch `ℓ ≥ 1`. -/
  t : ℕ → ℕ
  /-- The sequence of ends starts at `0`. -/
  t_zero : t 0 = 0
  /-- The ends are strictly increasing. -/
  strictMono : StrictMono t
  /-- The first batch has at least `max 2 K` rounds. -/
  le_t_one : max 2 K ≤ t 1

namespace Grid

attribute [simp] t_zero

variable {K : ℕ} (g : Grid K)

lemma le_t (ℓ : ℕ) : ℓ ≤ g.t ℓ := g.strictMono.id_le ℓ

lemma two_le_t_one : 2 ≤ g.t 1 := (le_max_left 2 K).trans g.le_t_one

lemma card_le_t_one : K ≤ g.t 1 := (le_max_right 2 K).trans g.le_t_one

lemma two_le_t {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : 2 ≤ g.t ℓ :=
  g.two_le_t_one.trans (g.strictMono.monotone hℓ)

lemma exists_lt_t (n : ℕ) : ∃ ℓ, 1 ≤ ℓ ∧ n < g.t ℓ :=
  ⟨n + 1, by omega, Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (g.le_t (n + 1))⟩

/-- The **batch of a round** `n` (rounds from `0`): `min {ℓ ≥ 1 | n < t ℓ}`, the paper's `b(n + 1)`
[INC-P006, Definition `def:grid` and paragraph "Rounds numbered from zero"]. -/
noncomputable def batchOf (n : ℕ) : ℕ := Nat.find (g.exists_lt_t n)

lemma one_le_batchOf (n : ℕ) : 1 ≤ g.batchOf n := (Nat.find_spec (g.exists_lt_t n)).1

lemma lt_t_batchOf (n : ℕ) : n < g.t (g.batchOf n) := (Nat.find_spec (g.exists_lt_t n)).2

lemma t_batchOf_sub_one_le (n : ℕ) : g.t (g.batchOf n - 1) ≤ n := by
  rcases Nat.lt_or_ge (g.batchOf n - 1) 1 with h | h
  · simp [show g.batchOf n - 1 = 0 by omega]
  · have hlt : g.batchOf n - 1 < g.batchOf n := by have := g.one_le_batchOf n; omega
    have := Nat.find_min (g.exists_lt_t n) hlt
    rw [not_and, not_lt] at this
    exact this h

/-- The round `n` is in batch `ℓ + 1` if and only if `t ℓ ≤ n < t (ℓ + 1)`. -/
lemma batchOf_eq_iff {n ℓ : ℕ} : g.batchOf n = ℓ + 1 ↔ g.t ℓ ≤ n ∧ n < g.t (ℓ + 1) := by
  constructor
  · intro h
    have h1 := g.t_batchOf_sub_one_le n
    have h2 := g.lt_t_batchOf n
    rw [h] at h1 h2
    exact ⟨by simpa using h1, h2⟩
  · rintro ⟨h1, h2⟩
    rw [batchOf, Nat.find_eq_iff]
    refine ⟨⟨by omega, h2⟩, fun m hm ⟨_, hm2⟩ ↦ ?_⟩
    have := g.strictMono.monotone (show m ≤ ℓ by omega)
    omega

/-- `L_ℓ = log t_ℓ` [INC-P006, Definition `def:logratio`]. The paper uses it for `ℓ ≥ 1` only; at
`ℓ = 0` it takes the junk value `log 0 = 0`. -/
noncomputable def logEnd (ℓ : ℕ) : ℝ := Real.log (g.t ℓ)

/-- The **growth ratio** `x_ℓ = L_ℓ / L_{ℓ-1}` for `ℓ ≥ 2`, and `x_1 = 1`
[INC-P006, Definition `def:logratio`]; at `ℓ = 0`, which the paper does not use, it is `1`. -/
noncomputable def ratio (ℓ : ℕ) : ℝ := if ℓ ≤ 1 then 1 else g.logEnd ℓ / g.logEnd (ℓ - 1)

/-- A grid `g` is **finer** than a grid `g'` if every batch end of `g'` is a batch end of `g`
[INC-P006, Definition `def:grid`]. (Both have `t 0 = 0`, so the index `0` changes nothing.) -/
def IsFiner (g g' : Grid K) : Prop := Set.range g'.t ⊆ Set.range g.t

@[simp]
lemma ratio_one : g.ratio 1 = 1 := by simp [ratio]

/-- `x_ℓ = L_ℓ / L_{ℓ-1}` for `ℓ ≥ 2` [INC-P006, Definition `def:logratio`]. -/
lemma ratio_of_two_le {ℓ : ℕ} (hℓ : 2 ≤ ℓ) : g.ratio ℓ = g.logEnd ℓ / g.logEnd (ℓ - 1) := by
  simp [ratio, show ¬ ℓ ≤ 1 by omega]

/-- `L_0 = log 0 = 0` (the junk value). -/
@[simp]
lemma logEnd_zero : g.logEnd 0 = 0 := by simp [logEnd]

/-- `L_ℓ = log t_ℓ ≥ 0`, `t_ℓ` being a natural number. -/
lemma logEnd_nonneg (ℓ : ℕ) : 0 ≤ g.logEnd ℓ := Real.log_natCast_nonneg _

lemma log_two_le_logEnd {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : Real.log 2 ≤ g.logEnd ℓ := by
  unfold logEnd
  gcongr
  exact_mod_cast g.two_le_t hℓ

lemma logEnd_pos {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : 0 < g.logEnd ℓ :=
  (Real.log_pos one_lt_two).trans_le (g.log_two_le_logEnd hℓ)

/-- The ratios after the first are larger than `1`. -/
lemma one_lt_ratio {ℓ : ℕ} (hℓ : 2 ≤ ℓ) : 1 < g.ratio ℓ := by
  rw [g.ratio_of_two_le hℓ, one_lt_div (g.logEnd_pos (by omega))]
  unfold logEnd
  gcongr
  · exact_mod_cast (show 0 < g.t (ℓ - 1) by have := g.two_le_t (ℓ := ℓ - 1) (by omega); omega)
  · exact_mod_cast g.strictMono (show ℓ - 1 < ℓ by omega)

/-- All the ratios are at least `1` (`x_0 = x_1 = 1`). -/
lemma one_le_ratio (ℓ : ℕ) : 1 ≤ g.ratio ℓ := by
  rcases Nat.lt_or_ge ℓ 2 with h | h
  · simp [ratio, show ℓ ≤ 1 by omega]
  · exact (g.one_lt_ratio h).le

/-- No grid is the sequence `t ℓ = ℓ`: its first batch has one round [INC-P006,
Proposition `prop:witnesses`(b)]. -/
lemma not_exists_t_eq_id : ¬ ∃ g : Grid K, g.t = id := by
  rintro ⟨g, hg⟩
  have := g.two_le_t_one
  rw [hg] at this
  simp at this

/-! ### Example grids -/

variable {s : ℕ}

/-- The **sequential grid** `𝖲_s`: `t ℓ = s + ℓ - 1` for `ℓ ≥ 1`; its batches after the first have
size one [INC-P006, Definition `def:exgrids`]. -/
def sequential (s : ℕ) (hs : max 2 K ≤ s) : Grid K where
  t ℓ := if ℓ = 0 then 0 else s + ℓ - 1
  t_zero := rfl
  strictMono := strictMono_nat_of_lt_succ fun ℓ ↦ by
    have : 2 ≤ s := (le_max_left 2 K).trans hs
    change (if ℓ = 0 then 0 else s + ℓ - 1) < (if ℓ + 1 = 0 then 0 else s + (ℓ + 1) - 1)
    split_ifs <;> first | contradiction | omega
  le_t_one := by simpa using hs

/-- The **geometric grid** `𝖦_s`: `t ℓ = s 2 ^ (ℓ - 1)` for `ℓ ≥ 1` [INC-P006,
Definition `def:exgrids`]. -/
def geometric (s : ℕ) (hs : max 2 K ≤ s) : Grid K where
  t ℓ := if ℓ = 0 then 0 else s * 2 ^ (ℓ - 1)
  t_zero := rfl
  strictMono := strictMono_nat_of_lt_succ fun ℓ ↦ by
    have : 2 ≤ s := (le_max_left 2 K).trans hs
    rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
    · simp; omega
    · change (if ℓ = 0 then 0 else s * 2 ^ (ℓ - 1)) < (if ℓ + 1 = 0 then 0 else s * 2 ^ (ℓ + 1 - 1))
      rw [ite_eq_right (show ℓ ≠ 0 by omega), ite_eq_right (show ℓ + 1 ≠ 0 by omega),
        show ℓ + 1 - 1 = (ℓ - 1) + 1 by omega, pow_succ,
        show s * (2 ^ (ℓ - 1) * 2) = 2 * (s * 2 ^ (ℓ - 1)) by ring]
      have : 0 < s * 2 ^ (ℓ - 1) := by positivity
      omega
  le_t_one := by simpa using hs

/-- The **doubly exponential grid** `𝖣_s`: `t ℓ = s ^ 2 ^ (ℓ - 1)` for `ℓ ≥ 1` [INC-P006,
Definition `def:exgrids`]. -/
def doublyExp (s : ℕ) (hs : max 2 K ≤ s) : Grid K where
  t ℓ := if ℓ = 0 then 0 else s ^ 2 ^ (ℓ - 1)
  t_zero := rfl
  strictMono := strictMono_nat_of_lt_succ fun ℓ ↦ by
    have : 2 ≤ s := (le_max_left 2 K).trans hs
    rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
    · simp; omega
    · change (if ℓ = 0 then 0 else s ^ 2 ^ (ℓ - 1)) < (if ℓ + 1 = 0 then 0 else s ^ 2 ^ (ℓ + 1 - 1))
      rw [ite_eq_right (show ℓ ≠ 0 by omega), ite_eq_right (show ℓ + 1 ≠ 0 by omega)]
      exact Nat.pow_lt_pow_right (by omega) (Nat.pow_lt_pow_right (by norm_num) (by omega))
  le_t_one := by simpa using hs

@[simp]
lemma sequential_t {hs : max 2 K ≤ s} {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    (sequential s hs).t ℓ = s + ℓ - 1 := by
  simp [sequential, show ℓ ≠ 0 by omega]

@[simp]
lemma doublyExp_t {hs : max 2 K ≤ s} {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    (doublyExp s hs).t ℓ = s ^ 2 ^ (ℓ - 1) := by
  simp [doublyExp, show ℓ ≠ 0 by omega]

/-- On the sequential grid `𝖲_s`, every round `n ≥ s` is a batch on its own, the batch
`n - s + 2`: the batched constraint is the sequential one after the first batch. -/
lemma sequential_batchOf {hs : max 2 K ≤ s} {n : ℕ} (hn : s ≤ n) :
    (sequential s hs).batchOf n = n - s + 2 := by
  rw [show n - s + 2 = (n - s + 1) + 1 by omega, batchOf_eq_iff, sequential_t (by omega),
    sequential_t (by omega)]
  omega

/-- On the sequential grid `𝖲_s`, the first batch is the set of rounds `0, …, s - 1`. -/
lemma sequential_batchOf_of_lt {hs : max 2 K ≤ s} {n : ℕ} (hn : n < s) :
    (sequential s hs).batchOf n = 1 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, batchOf_eq_iff, (sequential s hs).t_zero,
    sequential_t le_rfl]
  omega

@[simp]
lemma geometric_t {hs : max 2 K ≤ s} {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    (geometric s hs).t ℓ = s * 2 ^ (ℓ - 1) := by
  simp [geometric, show ℓ ≠ 0 by omega]

/-- **Known case**: on the doubly exponential grid `𝖣_s`, `L_ℓ = 2 ^ (ℓ - 1) log s`. -/
lemma logEnd_doublyExp {hs : max 2 K ≤ s} {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    (doublyExp s hs).logEnd ℓ = 2 ^ (ℓ - 1) * Real.log s := by
  rw [logEnd, doublyExp_t hℓ, Nat.cast_pow, Real.log_pow]
  push_cast
  ring

/-- **Known case**: on the geometric grid `𝖦_s`, for `ℓ ≥ 2`,
`x_ℓ = (log s + (ℓ - 1) log 2) / (log s + (ℓ - 2) log 2)` [INC-P006, proof of
Proposition `prop:witnesses`(b)]. -/
lemma ratio_geometric {hs : max 2 K ≤ s} {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    (geometric s hs).ratio ℓ = (Real.log s + ((ℓ - 1 : ℕ) : ℝ) * Real.log 2) /
      (Real.log s + ((ℓ - 2 : ℕ) : ℝ) * Real.log 2) := by
  have hs0 : (s : ℝ) ≠ 0 := by
    have : 2 ≤ s := (le_max_left 2 K).trans hs
    exact_mod_cast (show s ≠ 0 by omega)
  rw [ratio_of_two_le _ hℓ, logEnd, logEnd, geometric_t (by omega),
    geometric_t (by omega), Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow,
    Real.log_mul hs0 (by positivity), Real.log_mul hs0 (by positivity), Real.log_pow,
    Real.log_pow, show ℓ - 1 - 1 = ℓ - 2 by omega]
  push_cast
  ring

/-- **Known case** [INC-P006, Proposition `prop:witnesses`(b)]: on the geometric grid `𝖦_s`,
`x_ℓ → 1`. -/
lemma tendsto_ratio_geometric (hs : max 2 K ≤ s) :
    Filter.Tendsto (geometric s hs).ratio Filter.atTop (nhds 1) := by
  have h2 : 2 ≤ s := (le_max_left 2 K).trans hs
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogs : 0 < Real.log s := Real.log_pos (by exact_mod_cast (show 1 < s by omega))
  have hden : Filter.Tendsto (fun ℓ : ℕ ↦ Real.log s + ((ℓ - 2 : ℕ) : ℝ) * Real.log 2)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_left _ _ (Filter.Tendsto.atTop_mul_const hlog2
      (tendsto_natCast_atTop_atTop.comp (Filter.tendsto_sub_atTop_nat 2)))
  have h1 := ((tendsto_const_nhds (x := Real.log 2)).div_atTop hden).const_add 1
  rw [add_zero] at h1
  refine h1.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with ℓ hℓ
  rw [ratio_geometric hℓ]
  have hpos : 0 < Real.log s + ((ℓ - 2 : ℕ) : ℝ) * Real.log 2 := by positivity
  have hcast : ((ℓ - 1 : ℕ) : ℝ) = ((ℓ - 2 : ℕ) : ℝ) + 1 := by
    rw [show ℓ - 1 = (ℓ - 2) + 1 by omega]
    push_cast
    ring
  rw [hcast]
  field_simp
  ring

/-- **Known case** [INC-P006, Proposition `prop:witnesses`(b)]: on the sequential grid `𝖲_s`,
`x_ℓ → 1`. -/
lemma tendsto_ratio_sequential (hs : max 2 K ≤ s) :
    Filter.Tendsto (sequential s hs).ratio Filter.atTop (nhds 1) := by
  have h2 : 2 ≤ s := (le_max_left 2 K).trans hs
  set x : ℕ → ℝ := fun ℓ ↦ ((s + ℓ - 2 : ℕ) : ℝ) with hx
  have hxtop : Filter.Tendsto x Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono
      (fun ℓ ↦ by simp only [hx]; exact_mod_cast (show ℓ ≤ s + ℓ - 2 by omega))
      tendsto_natCast_atTop_atTop
  have hnum := (Real.tendsto_log_comp_add_sub_log 1).comp hxtop
  have hden := Real.tendsto_log_atTop.comp hxtop
  have h1 := (hnum.div_atTop hden).const_add 1
  rw [add_zero] at h1
  refine h1.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with ℓ hℓ
  have hx2 : (2 : ℝ) ≤ x ℓ := by
    simp only [hx]
    exact_mod_cast (show 2 ≤ s + ℓ - 2 by omega)
  have hlogpos : 0 < Real.log (x ℓ) := Real.log_pos (by linarith)
  rw [ratio_of_two_le _ hℓ, logEnd, logEnd, sequential_t (by omega),
    sequential_t (by omega), show s + (ℓ - 1) - 1 = s + ℓ - 2 by omega,
    show s + ℓ - 1 = (s + ℓ - 2) + 1 by omega]
  simp only [Function.comp_apply, hx, Nat.cast_add, Nat.cast_one] at hlogpos ⊢
  have hne : Real.log ((s + ℓ - 2 : ℕ) : ℝ) ≠ 0 := hlogpos.ne'
  field_simp
  ring

/-- Every grid is finer than itself. -/
lemma isFiner_refl (g : Grid K) : g.IsFiner g := subset_rfl

/-- Being finer is transitive: `IsFiner` is a preorder on the grids. -/
lemma IsFiner.trans {g₁ g₂ g₃ : Grid K} (h₁₂ : g₁.IsFiner g₂) (h₂₃ : g₂.IsFiner g₃) :
    g₁.IsFiner g₃ :=
  Set.Subset.trans h₂₃ h₁₂

/-- **Witness and known case**: the sequential grid `𝖲_s`, whose ends are `0` and every
`n ≥ s`, is finer than every grid whose first end is at least `s`; observing after every round
(the sequential setting) is the finest way to observe. -/
lemma sequential_isFiner {hs : max 2 K ≤ s} {g' : Grid K} (h : s ≤ g'.t 1) :
    (sequential s hs).IsFiner g' := by
  rintro _ ⟨ℓ, rfl⟩
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · exact ⟨0, by simp⟩
  · have := g'.strictMono.monotone (show 1 ≤ ℓ by omega)
    refine ⟨g'.t ℓ - s + 1, ?_⟩
    rw [sequential_t (by omega)]
    omega

/-- **Exclusion**: `𝖲_{s+1}` is not finer than `𝖲_s`, whose end `s` is not an end of `𝖲_{s+1}`. -/
lemma not_sequential_succ_isFiner {hs : max 2 K ≤ s} {hs' : max 2 K ≤ s + 1} :
    ¬ (sequential (s + 1) hs').IsFiner (sequential s hs) := by
  intro h
  have h2 : 2 ≤ s := (le_max_left 2 K).trans hs
  obtain ⟨j, hj⟩ := h ⟨1, rfl⟩
  rw [sequential_t (hs := hs) le_rfl] at hj
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rw [(sequential (s + 1) hs').t_zero] at hj
    omega
  · rw [sequential_t hj0] at hj
    omega

/-- The ratios of the doubly exponential grid `𝖣_s` are `x_ℓ = 2` for `ℓ ≥ 2` [INC-P006,
Proposition `prop:witnesses`(b)]. -/
lemma ratio_doublyExp {hs : max 2 K ≤ s} {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    (doublyExp s hs).ratio ℓ = 2 := by
  have hs1 : (1 : ℝ) < s := by
    have : 2 ≤ s := (le_max_left 2 K).trans hs
    exact_mod_cast (show 1 < s by omega)
  have hlog : 0 < Real.log s := Real.log_pos hs1
  rw [ratio_of_two_le _ hℓ, logEnd, logEnd, doublyExp_t (by omega),
    doublyExp_t (by omega),
    Nat.cast_pow, Nat.cast_pow, Real.log_pow, Real.log_pow,
    show ℓ - 1 = (ℓ - 1 - 1) + 1 by omega, pow_succ]
  field_simp
  push_cast
  ring

/-! ### Batch ends, `L_ℓ` and `x_ℓ` -/

section API

open Filter Topology

/-- The batch ends after the first are positive. -/
lemma t_pos {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : (0 : ℝ) < g.t ℓ := by
  have := g.two_le_t hℓ
  exact_mod_cast (show 0 < g.t ℓ by omega)

/-- The batch ends are nondecreasing, as reals. -/
lemma t_le_t {ℓ ℓ' : ℕ} (h : ℓ ≤ ℓ') : (g.t ℓ : ℝ) ≤ g.t ℓ' := by
  exact_mod_cast g.strictMono.monotone h

/-- `L_ℓ = log t_ℓ` is nondecreasing in `ℓ` (`L_0 = log 0 = 0`). -/
lemma monotone_logEnd : Monotone g.logEnd := by
  intro ℓ ℓ' h
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · rw [logEnd_zero]
    exact g.logEnd_nonneg ℓ'
  · exact Real.log_le_log (g.t_pos hℓ) (g.t_le_t h)

/-- `L_ℓ → ∞`. -/
lemma tendsto_logEnd_atTop : Tendsto g.logEnd atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp g.strictMono.tendsto_atTop)

/-- `t_ℓ = exp(L_ℓ)` for `ℓ ≥ 1`. -/
lemma exp_logEnd {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : Real.exp (g.logEnd ℓ) = g.t ℓ := by
  unfold logEnd
  exact Real.exp_log (g.t_pos hℓ)

/-- `L_(j+1) = x_(j+1) L_j` for `j ≥ 1`. -/
lemma logEnd_succ_eq {j : ℕ} (hj : 1 ≤ j) :
    g.logEnd (j + 1) = g.ratio (j + 1) * g.logEnd j := by
  simp only [Grid.ratio, show ¬ (j + 1 ≤ 1) by omega, ite_false, Nat.add_sub_cancel]
  rw [div_mul_cancel₀ _ (g.logEnd_pos hj).ne']

/-- On a grid with `x_ℓ → x`, `log t_(ℓ+2) / log t_ℓ = x_(ℓ+1) x_(ℓ+2) → x²`. -/
lemma tendsto_log_t_add_two_div_log_t {x : ℝ} (hg : Tendsto g.ratio atTop (𝓝 x)) :
    Tendsto (fun ℓ ↦ Real.log (g.t (ℓ + 2)) / Real.log (g.t ℓ)) atTop (𝓝 (x ^ 2)) := by
  have h2 : Tendsto (fun ℓ ↦ g.ratio (ℓ + 2) * g.ratio (ℓ + 1)) atTop (𝓝 (x * x)) :=
    (hg.comp (tendsto_add_atTop_nat 2)).mul (hg.comp (tendsto_add_atTop_nat 1))
  rw [sq]
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with ℓ hℓ
  have hpos1 := g.logEnd_pos (ℓ := ℓ + 1) (by omega)
  have hpos0 := g.logEnd_pos hℓ
  simp only [Grid.ratio, show ¬ (ℓ + 2 ≤ 1) by omega, show ¬ (ℓ + 1 ≤ 1) by omega,
    ↓reduceIte, show ℓ + 2 - 1 = ℓ + 1 by omega, Nat.add_sub_cancel]
  unfold Grid.logEnd at hpos0 hpos1 ⊢
  field_simp

/-- Two grids with the same ends `t j` for every `j ≥ 1` are equal (both have `t 0 = 0`). -/
lemma eq_of_forall_one_le_t_eq {g g' : Grid K} (h : ∀ j, 1 ≤ j → g.t j = g'.t j) :
    g = g' := by
  refine Grid.ext (funext fun j ↦ ?_)
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · exact h j hj

/-- Two grids with the same ends `t 0, …, t ℓ` have the same `logEnd j` for `j ≤ ℓ`. -/
lemma logEnd_eq_of_t_eq {g g' : Grid K} {ℓ : ℕ} (ht : ∀ j ≤ ℓ, g.t j = g'.t j) {j : ℕ}
    (hj : j ≤ ℓ) :
    g.logEnd j = g'.logEnd j := by
  simp [logEnd, ht j hj]

/-- Two grids with the same ends `t 0, …, t ℓ` have the same ratio `x_j` for `j ≤ ℓ`. -/
lemma ratio_eq_of_t_eq {g g' : Grid K} {ℓ : ℕ} (ht : ∀ j ≤ ℓ, g.t j = g'.t j) {j : ℕ}
    (hj : j ≤ ℓ) :
    g.ratio j = g'.ratio j := by
  simp only [ratio, logEnd_eq_of_t_eq ht hj, logEnd_eq_of_t_eq ht ((Nat.sub_le j 1).trans hj)]

/-- If `g` is finer than `g'`, the end of the batch before the batch of a round `n` in `g'` is at
most the end of the batch before the batch of `n` in `g`: the batches of `g` start later. -/
lemma t_batchOf_sub_one_le_of_isFiner {g g' : Grid K} (hgg' : g.IsFiner g') (n : ℕ) :
    g'.t (g'.batchOf n - 1) ≤ g.t (g.batchOf n - 1) := by
  obtain ⟨m, hm⟩ := hgg' (Set.mem_range_self (g'.batchOf n - 1))
  rw [← hm]
  have hlt : g.t m < g.t (g.batchOf n) :=
    (hm ▸ g'.t_batchOf_sub_one_le n).trans_lt (g.lt_t_batchOf n)
  exact g.strictMono.monotone (by have := g.strictMono.lt_iff_lt.mp hlt; omega)

end API

end Grid

end Incognita.BatchedBandits
