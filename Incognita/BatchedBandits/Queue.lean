/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import LeanMachineLearning.SequentialLearning.FiniteActions

/-! # The queue lemma of the paced phase

[INC-P000, Lemma `lem:service`], in an abstract form. A sequence of actions `A` (LML's
`A : ℕ → Ω → β` at a fixed `ω`; the paper's round `t ≥ 1` pulls `A (t - 1) ω`, and its count
`N_c(t)` is `pullCount A c t ω`) runs a paced phase on the rounds `t ∈ (σ, T]`: a finite set `C`
of arms (the non-leaders `𝒞_ℓ`) has integer targets `n_c(t)` (the paper's `n_{ℓ,c}(t)`),
nondecreasing on `[σ, T]` and at most `B` (the paper's `U_(ℓ+1) + K - 1`), and

* (rule) an arm `c ∈ C` pulled at a round `t` has a demand, `N_c(t - 1) < n_c(t)`;
* (idle) if the arm pulled at `t` is not in `C`, no arm of `C` has a demand.

HY's paced rule (pull the first demanding non-leader, the leader if there is none) satisfies both;
the order is not used. The backlog after the round `t` is
`Q(t) = ∑_{c ∈ C} (n_c(t) - N_c(t))⁺` (natural subtraction).

* `pullCount_le_max_target`: (a), `N_c(t) ≤ max(N_c(σ), n_c(t))`; `pullCount_sub_le_target`: so
  `c` is pulled at most `B` times in `(σ, t]`.
* `backlog_le`: (b), if the arrivals are slow (`∑_{c ∈ C} (n_c(t) - n_c(u)) ≤ |C| + (t - u)/2`
  for `σ ≤ u ≤ t ≤ T`, Step (b2) of the paper), then `Q(t) ≤ max(|C| B - (t - σ), |C|)`;
  `target_sub_le_pullCount`: in particular `N_c(t) ≥ n_c(t) - |C|` once `t - σ ≥ |C| B`.
* `card_le_card_filter_not_mem`: (c), the arms outside `C` (the leader) are pulled at least
  `(t - σ) - |C| B` times in `(σ, t]`.
* `two_mul_min_ceil_sub_le`: Step (b2) for one paced target `min(U, ⌈f log t⌉)`, under the
  paper's `s_ℓ log s_ℓ ≥ 2(K - 1) U_(ℓ+1)`.
-/

@[expose] public section

open Learning Finset

namespace Incognita.BatchedBandits

variable {β Ω : Type*} [DecidableEq β] {A : ℕ → Ω → β} {ω : Ω}

/-- [INC-P000, Lemma `lem:service`(a), no overshoot] If every pull of `c` at a round
`t ∈ (σ, T]` has a demand `N_c(t - 1) < n_c(t)` and `n_c` is nondecreasing on `[σ, T]`, then
`N_c(t) ≤ max(N_c(σ), n_c(t))` for `t ∈ [σ, T]`. -/
lemma pullCount_le_max_target {c : β} {n : ℕ → ℕ} {σ T : ℕ}
    (hmono : MonotoneOn n (Set.Icc σ T))
    (hrule : ∀ t, σ < t → t ≤ T → A (t - 1) ω = c → pullCount A c (t - 1) ω < n t)
    {t : ℕ} (hσt : σ ≤ t) (htT : t ≤ T) :
    pullCount A c t ω ≤ max (pullCount A c σ ω) (n t) := by
  induction t, hσt using Nat.le_induction with
  | base => exact le_max_left _ _
  | succ t ht ih =>
    have ih := ih (by omega)
    rw [pullCount_add_one]
    split_ifs with hA
    · have := hrule (t + 1) (by omega) htT (by simpa using hA)
      simp only [Nat.add_sub_cancel] at this
      exact le_max_of_le_right (by omega)
    · have : n t ≤ n (t + 1) := hmono ⟨ht, by omega⟩ ⟨by omega, htT⟩ (by omega)
      omega

/-- [INC-P000, Lemma `lem:service`(a), the number of pulls] Under the hypotheses of
`pullCount_le_max_target` and `n_c ≤ B` on `[σ, T]`, `c` is pulled at most `B` times in
`(σ, t]`. -/
lemma pullCount_sub_le_target {c : β} {n : ℕ → ℕ} {σ T B : ℕ}
    (hmono : MonotoneOn n (Set.Icc σ T)) (hB : ∀ t, σ ≤ t → t ≤ T → n t ≤ B)
    (hrule : ∀ t, σ < t → t ≤ T → A (t - 1) ω = c → pullCount A c (t - 1) ω < n t)
    {t : ℕ} (hσt : σ ≤ t) (htT : t ≤ T) :
    pullCount A c t ω - pullCount A c σ ω ≤ B := by
  have := pullCount_le_max_target hmono hrule hσt htT
  have := hB t hσt htT
  omega

/-- The pulls in the rounds `(σ, t]` of the arms of `C`: their number is the sum of the increments
of the counts. -/
lemma card_filter_mem_eq_sum (C : Finset β) {σ t : ℕ} (hσt : σ ≤ t) :
    ((Finset.Ico σ t).filter fun u ↦ A u ω ∈ C).card =
      ∑ c ∈ C, (pullCount A c t ω - pullCount A c σ ω) := by
  have hpc : ∀ c, pullCount A c t ω - pullCount A c σ ω =
      ∑ u ∈ Finset.Ico σ t, if A u ω = c then 1 else 0 := by
    intro c
    rw [pullCount_eq_sum, pullCount_eq_sum, ← Finset.sum_range_add_sum_Ico _ hσt,
      Nat.add_sub_cancel_left]
  simp_rw [hpc]
  rw [Finset.card_filter, Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [Finset.sum_ite_eq]

/-- [INC-P000, Lemma `lem:service`(c), the leader] If every `c ∈ C` is pulled at most `B` times in
`(σ, t]`, the arms outside `C` are pulled at least `(t - σ) - |C| B` times there. -/
lemma card_le_card_filter_not_mem (C : Finset β) {σ t B : ℕ} (hσt : σ ≤ t)
    (hB : ∀ c ∈ C, pullCount A c t ω - pullCount A c σ ω ≤ B) :
    (t - σ) - C.card * B ≤ ((Finset.Ico σ t).filter fun u ↦ A u ω ∉ C).card := by
  have hsum := Finset.card_filter_add_card_filter_not (s := Finset.Ico σ t)
    (fun u ↦ A u ω ∈ C)
  rw [card_filter_mem_eq_sum C hσt, Nat.card_Ico] at hsum
  have : ∑ c ∈ C, (pullCount A c t ω - pullCount A c σ ω) ≤ C.card * B := by
    calc _ ≤ ∑ _c ∈ C, B := Finset.sum_le_sum hB
      _ = C.card * B := by rw [Finset.sum_const, smul_eq_mul]
  omega

/-- [INC-P000, proof of Lemma `lem:service`, Step (b1)] One round of the queue: at a round
`t ∈ (σ, T]`, either the backlog is `0`, or `Q(t) + 1 ≤ Q(t - 1) + δ(t)` with the arrivals
`δ(t) = ∑_{c ∈ C} (n_c(t) - n_c(t - 1))`. -/
lemma backlog_step (C : Finset β) {n : β → ℕ → ℕ} {σ T : ℕ}
    (hmono : ∀ c ∈ C, MonotoneOn (n c) (Set.Icc σ T))
    (hrule : ∀ t, σ < t → t ≤ T → A (t - 1) ω ∈ C →
      pullCount A (A (t - 1) ω) (t - 1) ω < n (A (t - 1) ω) t)
    (hidle : ∀ t, σ < t → t ≤ T → A (t - 1) ω ∉ C → ∀ c ∈ C, n c t ≤ pullCount A c (t - 1) ω)
    {t : ℕ} (hσt : σ < t) (htT : t ≤ T) :
    ∑ c ∈ C, (n c t - pullCount A c t ω) = 0 ∨
      ∑ c ∈ C, (n c t - pullCount A c t ω) + 1 ≤
        ∑ c ∈ C, (n c (t - 1) - pullCount A c (t - 1) ω) +
          ∑ c ∈ C, (n c t - n c (t - 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hrule hidle ⊢
  have hcount : ∀ c, pullCount A c (k + 1) ω =
      pullCount A c k ω + if A k ω = c then 1 else 0 := fun c ↦ pullCount_add_one
  have hmono' : ∀ c ∈ C, n c k ≤ n c (k + 1) := fun c hc ↦
    hmono c hc ⟨by omega, by omega⟩ ⟨by omega, htT⟩ (by omega)
  by_cases hA : A k ω ∈ C
  · right
    have hd := hrule (k + 1) hσt htT (by simpa using hA)
    simp only [Nat.add_sub_cancel] at hd
    rw [← Finset.sum_add_distrib, ← Finset.add_sum_erase C _ hA,
      ← Finset.add_sum_erase C _ hA]
    have hrest : ∑ c ∈ C.erase (A k ω), (n c (k + 1) - pullCount A c (k + 1) ω) ≤
        ∑ c ∈ C.erase (A k ω), (n c k - pullCount A c k ω + (n c (k + 1) - n c k)) := by
      refine Finset.sum_le_sum fun c hc ↦ ?_
      have hne : A k ω ≠ c := (Finset.ne_of_mem_erase hc).symm
      rw [hcount c, ite_eq_right hne, add_zero]
      have := hmono' c (Finset.mem_of_mem_erase hc)
      omega
    have hfirst : n (A k ω) (k + 1) - pullCount A (A k ω) (k + 1) ω + 1 ≤
        n (A k ω) k - pullCount A (A k ω) k ω + (n (A k ω) (k + 1) - n (A k ω) k) := by
      rw [hcount, ite_eq_left rfl]
      have := hmono' _ hA
      omega
    omega
  · left
    refine Finset.sum_eq_zero fun c hc ↦ ?_
    have hne : A k ω ≠ c := fun h ↦ hA (h ▸ hc)
    have := hidle (k + 1) hσt htT (by simpa using hA) c hc
    simp only [Nat.add_sub_cancel] at this
    rw [hcount c, ite_eq_right hne, add_zero]
    omega

omit [DecidableEq β] in
/-- The arrivals telescope: `∑_c (n_c(t + 1) - n_c(u)) = ∑_c (n_c(t) - n_c(u)) + δ(t + 1)` for
`u ≤ t` and nondecreasing targets. -/
lemma arrivals_succ (C : Finset β) {n : β → ℕ → ℕ} {σ T : ℕ}
    (hmono : ∀ c ∈ C, MonotoneOn (n c) (Set.Icc σ T)) {u t : ℕ} (hσu : σ ≤ u) (hut : u ≤ t)
    (htT : t + 1 ≤ T) :
    ∑ c ∈ C, (n c (t + 1) - n c u) =
      ∑ c ∈ C, (n c t - n c u) + ∑ c ∈ C, (n c (t + 1) - n c t) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c hc ↦ ?_
  have h1 : n c u ≤ n c t := hmono c hc ⟨hσu, by omega⟩ ⟨by omega, by omega⟩ hut
  have h2 : n c t ≤ n c (t + 1) := hmono c hc ⟨by omega, by omega⟩ ⟨by omega, htT⟩ (by omega)
  omega

/-- [INC-P000, proof of Lemma `lem:service`, Step (b3)] Lindley's recursion, unrolled: for
`t ∈ [σ, T]`, either `Q(t) + (t - σ) ≤ Q(σ) + ∑_c (n_c(t) - n_c(σ))`, or some `u ∈ (σ, t]` has
`Q(t) + (t - u) ≤ ∑_c (n_c(t) - n_c(u))`. -/
lemma backlog_lindley (C : Finset β) {n : β → ℕ → ℕ} {σ T : ℕ}
    (hmono : ∀ c ∈ C, MonotoneOn (n c) (Set.Icc σ T))
    (hrule : ∀ t, σ < t → t ≤ T → A (t - 1) ω ∈ C →
      pullCount A (A (t - 1) ω) (t - 1) ω < n (A (t - 1) ω) t)
    (hidle : ∀ t, σ < t → t ≤ T → A (t - 1) ω ∉ C → ∀ c ∈ C, n c t ≤ pullCount A c (t - 1) ω)
    {t : ℕ} (hσt : σ ≤ t) (htT : t ≤ T) :
    ∑ c ∈ C, (n c t - pullCount A c t ω) + (t - σ) ≤
        ∑ c ∈ C, (n c σ - pullCount A c σ ω) + ∑ c ∈ C, (n c t - n c σ) ∨
      ∃ u, σ < u ∧ u ≤ t ∧
        ∑ c ∈ C, (n c t - pullCount A c t ω) + (t - u) ≤ ∑ c ∈ C, (n c t - n c u) := by
  induction t, hσt using Nat.le_induction with
  | base => left; simp
  | succ t ht ih =>
    have ih := ih (by omega)
    have hstep := backlog_step C hmono hrule hidle (t := t + 1) (by omega) htT
    simp only [Nat.add_sub_cancel] at hstep
    rcases hstep with h0 | hlt
    · right
      refine ⟨t + 1, by omega, le_rfl, ?_⟩
      rw [h0]
      simp
    · have hδσ := arrivals_succ C hmono le_rfl ht htT
      rcases ih with h1 | ⟨u, hu1, hu2, hu3⟩
      · left
        rw [hδσ]
        omega
      · right
        refine ⟨u, hu1, by omega, ?_⟩
        rw [arrivals_succ C hmono (by omega) hu2 htT]
        omega

/-- [INC-P000, Lemma `lem:service`(b)] If the targets are at most `B` on `[σ, T]` and the
arrivals are slow, `2 ∑_{c ∈ C} (n_c(t) - n_c(u)) ≤ 2|C| + (t - u)` for `σ ≤ u ≤ t ≤ T`
(Step (b2), which the paper derives from `s_ℓ log s_ℓ ≥ 2(K - 1) U_(ℓ+1)`), then the backlog after
every round `t ∈ [σ, T]` is `Q(t) ≤ max(|C| B - (t - σ), |C|)`. -/
lemma backlog_le (C : Finset β) {n : β → ℕ → ℕ} {σ T B : ℕ}
    (hmono : ∀ c ∈ C, MonotoneOn (n c) (Set.Icc σ T))
    (hB : ∀ c ∈ C, ∀ t, σ ≤ t → t ≤ T → n c t ≤ B)
    (hrule : ∀ t, σ < t → t ≤ T → A (t - 1) ω ∈ C →
      pullCount A (A (t - 1) ω) (t - 1) ω < n (A (t - 1) ω) t)
    (hidle : ∀ t, σ < t → t ≤ T → A (t - 1) ω ∉ C → ∀ c ∈ C, n c t ≤ pullCount A c (t - 1) ω)
    (harr : ∀ u t, σ ≤ u → u ≤ t → t ≤ T → 2 * ∑ c ∈ C, (n c t - n c u) ≤ 2 * C.card + (t - u))
    {t : ℕ} (hσt : σ ≤ t) (htT : t ≤ T) :
    ∑ c ∈ C, (n c t - pullCount A c t ω) ≤ max (C.card * B - (t - σ)) C.card := by
  rcases backlog_lindley C hmono hrule hidle hσt htT with h1 | ⟨u, hu1, hu2, hu3⟩
  · -- the first term: each bracket is at most `n_c(t) ≤ B`
    have hbr : ∑ c ∈ C, (n c σ - pullCount A c σ ω) + ∑ c ∈ C, (n c t - n c σ) ≤
        C.card * B := by
      rw [← Finset.sum_add_distrib]
      calc _ ≤ ∑ _c ∈ C, B := Finset.sum_le_sum fun c hc ↦ by
            have h1 := hmono c hc ⟨le_rfl, hσt.trans htT⟩ ⟨hσt, htT⟩ hσt
            have h2 := hB c hc t hσt htT
            omega
        _ = C.card * B := by rw [Finset.sum_const, smul_eq_mul]
    refine le_max_of_le_left ?_
    omega
  · -- the second term: `Q(t) ≤ |C| + (t - u)/2 - (t - u) ≤ |C|`
    have := harr u t (by omega) hu2 htT
    refine le_max_of_le_right ?_
    omega

/-- [INC-P000, Lemma `lem:service`(b), "in particular"] Under the hypotheses of `backlog_le`, if
`t - σ ≥ |C| B`, then every `c ∈ C` has `N_c(t) ≥ n_c(t) - |C|`. -/
lemma target_sub_le_pullCount (C : Finset β) {n : β → ℕ → ℕ} {σ T B : ℕ}
    (hmono : ∀ c ∈ C, MonotoneOn (n c) (Set.Icc σ T))
    (hB : ∀ c ∈ C, ∀ t, σ ≤ t → t ≤ T → n c t ≤ B)
    (hrule : ∀ t, σ < t → t ≤ T → A (t - 1) ω ∈ C →
      pullCount A (A (t - 1) ω) (t - 1) ω < n (A (t - 1) ω) t)
    (hidle : ∀ t, σ < t → t ≤ T → A (t - 1) ω ∉ C → ∀ c ∈ C, n c t ≤ pullCount A c (t - 1) ω)
    (harr : ∀ u t, σ ≤ u → u ≤ t → t ≤ T → 2 * ∑ c ∈ C, (n c t - n c u) ≤ 2 * C.card + (t - u))
    {t : ℕ} (hσt : σ ≤ t) (htT : t ≤ T) (hlong : C.card * B ≤ t - σ) {c : β} (hc : c ∈ C) :
    n c t - C.card ≤ pullCount A c t ω := by
  have hQ := backlog_le C hmono hB hrule hidle harr hσt htT
  have hmax : max (C.card * B - (t - σ)) C.card = C.card := by
    rw [max_eq_right]
    omega
  rw [hmax] at hQ
  have := Finset.single_le_sum (f := fun c ↦ n c t - pullCount A c t ω)
    (fun _ _ ↦ Nat.zero_le _) hc
  omega

omit [DecidableEq β] in
/-- [INC-P000, proof of Lemma `lem:service`, Step (b2), one arm] A paced target
`m(t) = min(U, ⌈f log t⌉)` (`f ≥ 0`, the paper's `(1 + ω_ℓ) y_ℓ / K̂_ℓ(c)`) grows slowly after
`σ ≥ 2` with `σ log σ ≥ 2k U`, `k ≥ 1`: for `σ ≤ u ≤ t`,
`2k (m(t) - m(u)) ≤ 2k + (t - u)`, i.e. `m(t) - m(u) ≤ 1 + (t - u) / (2k)`. If `m(t) > m(u)` the cap
is not reached at `u`, so `f log u < U`, and
`m(t) - m(u) < f log (t/u) + 1 ≤ U (t - u) / (u log u) + 1 ≤ (t - u) / (2k) + 1`. -/
lemma two_mul_min_ceil_sub_le {f : ℝ} (hf : 0 ≤ f) {U k σ : ℕ} (hk : 1 ≤ k) (hσ : 2 ≤ σ)
    (hσU : 2 * k * U ≤ σ * Real.log σ) {u t : ℕ} (hσu : σ ≤ u) (hut : u ≤ t) :
    2 * k * (min U ⌈f * Real.log t⌉₊ - min U ⌈f * Real.log u⌉₊) ≤ 2 * k + (t - u) := by
  set mt := min U ⌈f * Real.log t⌉₊ with hmt
  set mu := min U ⌈f * Real.log u⌉₊ with hmu
  rcases le_or_gt mt mu with hle | hlt
  · rw [Nat.sub_eq_zero_of_le hle, mul_zero]
    exact Nat.zero_le _
  -- the cap is not reached at `u`
  have hmuU : mu < U := lt_of_lt_of_le hlt (min_le_left _ _)
  have hmu' : mu = ⌈f * Real.log u⌉₊ := by
    rcases le_total U ⌈f * Real.log u⌉₊ with h | h
    · rw [hmu, min_eq_left h] at hmuU
      exact absurd hmuU (lt_irrefl _)
    · rw [hmu, min_eq_right h]
  have hu2 : (2 : ℝ) ≤ u := by exact_mod_cast hσ.trans hσu
  have hlogu : 0 < Real.log u := Real.log_pos (by linarith)
  have hσ2 : (2 : ℝ) ≤ σ := by exact_mod_cast hσ
  have hlogσ : 0 < Real.log σ := Real.log_pos (by linarith)
  have hfu : f * Real.log u < U := by
    have h1 : f * Real.log u ≤ ⌈f * Real.log u⌉₊ := Nat.le_ceil _
    have h2 : (⌈f * Real.log u⌉₊ : ℝ) < U := by rw [← hmu']; exact_mod_cast hmuU
    linarith
  -- `m(t) - m(u) < f log (t / u) + 1`
  have hut' : (u : ℝ) ≤ t := by exact_mod_cast hut
  have hdiff : ((mt - mu : ℕ) : ℝ) < f * (Real.log t - Real.log u) + 1 := by
    have h1 : (mt : ℝ) ≤ ⌈f * Real.log t⌉₊ := by exact_mod_cast min_le_right _ _
    have h2 : (⌈f * Real.log t⌉₊ : ℝ) < f * Real.log t + 1 :=
      Nat.ceil_lt_add_one (mul_nonneg hf (Real.log_nonneg (by linarith)))
    have h3 : f * Real.log u ≤ (mu : ℝ) := by rw [hmu']; exact Nat.le_ceil _
    push_cast [hlt.le]
    linarith
  -- `f log (t / u) ≤ U (t - u) / (u log u) ≤ (t - u) / (2k)`
  have hlogtu : Real.log t - Real.log u ≤ (t - u) / u := by
    rw [← Real.log_div (by linarith) (by linarith)]
    have := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < t / u from div_pos (by linarith) (by linarith))
    have e : (t : ℝ) / u - 1 = (t - u) / u := by field_simp
    linarith
  have hσu' : (σ : ℝ) * Real.log σ ≤ u * Real.log u :=
    mul_le_mul (by exact_mod_cast hσu) (Real.log_le_log (by linarith) (by exact_mod_cast hσu))
      hlogσ.le (by linarith)
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have htu0 : (0 : ℝ) ≤ t - u := by linarith
  have hbound : f * (Real.log t - Real.log u) ≤ (t - u) / (2 * k) := by
    have hf' : f ≤ U / Real.log u := by rw [le_div_iff₀ hlogu]; exact hfu.le
    calc f * (Real.log t - Real.log u) ≤ (U / Real.log u) * ((t - u) / u) :=
          mul_le_mul hf' hlogtu (by
            rw [sub_nonneg]; exact Real.log_le_log (by linarith) hut') (by positivity)
      _ = U * (t - u) / (u * Real.log u) := by field_simp
      _ ≤ U * (t - u) / (σ * Real.log σ) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity) hσu'
      _ ≤ (t - u) / (2 * k) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have : (2 * k * U : ℝ) ≤ σ * Real.log σ := by exact_mod_cast hσU
          nlinarith
  have hfin : (2 * k : ℝ) * ((mt - mu : ℕ) : ℝ) < 2 * k + (t - u) := by
    have := hdiff.trans_le (by linarith : f * (Real.log t - Real.log u) + 1 ≤
      (t - u) / (2 * k) + 1)
    have h2k : (0 : ℝ) < 2 * k := by positivity
    calc (2 * k : ℝ) * ((mt - mu : ℕ) : ℝ) < 2 * k * ((t - u) / (2 * k) + 1) :=
          mul_lt_mul_of_pos_left this h2k
      _ = 2 * k + (t - u) := by field_simp; ring
  have : ((2 * k * (mt - mu) : ℕ) : ℝ) < ((2 * k + (t - u) : ℕ) : ℝ) := by
    push_cast [hut]
    exact hfin
  exact_mod_cast this.le

end Incognita.BatchedBandits
