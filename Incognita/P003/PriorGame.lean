/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.Checks

/-! # P003: prior games give size rules

Proofs of [INC-P003, lem:prior-game (b)] and [INC-P003, prop:stopped-games (a)].

## Main statements

* `measurable_state`: the state of the prior game after `r` rounds is measurable.
* `sum_state_fst`: after `r` rounds the counts add up to `r`.
* `state_eq_of_eqOn_box`: two source points that agree on the randomisation and on the box of `n`
  give the same first `r` rounds as long as the counts after `r` rounds are at most `n`.
* `stoppedCounts_isSizeRule`, `priorCounts_isSizeRule`.

The proof that `{N' = n} ∈ 𝒢_n` maps a source point `ω` to the point `ω̂` with the same
randomisation and box of `n`, and `0` outside it: `ω̂` is `𝒢_n`-measurable, and `N'(ω) = n` iff
`N'(ω̂) = n`, since on `{N' = n}` the stopped game reads only values of the box of `n`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Incognita.TransferBandits

open scoped unitInterval

namespace Incognita.P003

section Lemmas

variable {α : Type*} [DecidableEq α] [MeasurableSpace α]

/-- The state of the prior game after `r` rounds (counts and history) is measurable. -/
lemma measurable_state [Finite α] [MeasurableSingletonClass α] (g : PriorStrategy α) :
    ∀ r, Measurable fun ω : SourceSpace α ↦ g.state ω r
  | 0 => measurable_const
  | r + 1 => by
    have ih := measurable_state g r
    have ha : Measurable fun ω : SourceSpace α ↦ g.act r (ω.1, (g.state ω r).2) :=
      (g.measurable_act r).comp (measurable_fst.prodMk ih.snd)
    have hc : Measurable fun ω : SourceSpace α ↦
        (g.act r (ω.1, (g.state ω r).2), (g.state ω r).1) :=
      ha.prodMk ih.fst
    have hy : Measurable fun ω : SourceSpace α ↦
        ω.2 (g.act r (ω.1, (g.state ω r).2))
          ((g.state ω r).1 (g.act r (ω.1, (g.state ω r).2))) := by
      have : Measurable fun q : (α → ℕ → ℝ) × (α × (α → ℕ)) ↦ q.1 q.2.1 (q.2.2 q.2.1) :=
        measurable_from_prod_countable_left fun y ↦ by
          dsimp only
          exact (measurable_pi_apply y.1).eval
      exact this.comp (measurable_snd.prodMk hc)
    simp only [PriorStrategy.state]
    refine Measurable.prodMk ?_ ?_
    · exact (measurable_of_countable
        (fun p : α × (α → ℕ) ↦ Function.update p.2 p.1 (p.2 p.1 + 1))).comp hc
    · exact (MeasurableEquiv.finSuccProd (α × ℝ) r).symm.measurable.comp
        (ih.snd.prodMk (ha.prodMk hy))

/-- After `r` rounds of the prior game the counts add up to `r`. -/
lemma sum_state_fst [Fintype α] (g : PriorStrategy α) (ω : SourceSpace α) :
    ∀ r, ∑ a, (g.state ω r).1 a = r
  | 0 => by simp [PriorStrategy.state]
  | r + 1 => by
    have ih := sum_state_fst g ω r
    simp only [PriorStrategy.state]
    rw [Finset.sum_update_of_mem (Finset.mem_univ _), Finset.sdiff_singleton_eq_erase]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (g.act r (ω.1, (g.state ω r).2)))] at ih
    omega

/-- The counts of the prior game do not decrease from one round to the next. -/
lemma state_fst_le_succ (g : PriorStrategy α) (ω : SourceSpace α) (r : ℕ) (a : α) :
    (g.state ω r).1 a ≤ (g.state ω (r + 1)).1 a := by
  simp only [PriorStrategy.state]
  by_cases ha : a = g.act r (ω.1, (g.state ω r).2)
  · rw [ha, Function.update_self]
    omega
  · rw [Function.update_of_ne ha]

/-- Two source points with the same randomisation and the same values in the box of `n` give
the same first `r` rounds of the prior game when the counts after `r` rounds are at most `n`:
the game has only read values of the box. -/
lemma state_eq_of_eqOn_box (g : PriorStrategy α) {n : α → ℕ} {ω ω' : SourceSpace α}
    (h1 : ω.1 = ω'.1) (h2 : ∀ a, ∀ j < n a, ω.2 a j = ω'.2 a j) :
    ∀ r, (∀ a, (g.state ω r).1 a ≤ n a) → g.state ω r = g.state ω' r
  | 0 => fun _ ↦ rfl
  | r + 1 => fun hle ↦ by
    have ih := state_eq_of_eqOn_box g h1 h2 r
      (fun a ↦ (state_fst_le_succ g ω r a).trans (hle a))
    have hread : ω.2 (g.act r (ω.1, (g.state ω r).2))
          ((g.state ω r).1 (g.act r (ω.1, (g.state ω r).2))) =
        ω'.2 (g.act r (ω.1, (g.state ω r).2))
          ((g.state ω r).1 (g.act r (ω.1, (g.state ω r).2))) := by
      refine h2 _ _ ?_
      have := hle (g.act r (ω.1, (g.state ω r).2))
      simp only [PriorStrategy.state, Function.update_self] at this
      omega
    simp only [PriorStrategy.state]
    rw [← ih, ← h1, ← hread]

/-- On `{N' = n}`, the stopped counts only depend on the randomisation and the box of `n`. -/
lemma stoppedCounts_eq_of_eqOn_box (g : PriorStrategy α) {T' : ℕ} {τ : SourceSpace α → ℕ}
    (hτ : g.IsStoppingTime T' τ) {n : α → ℕ} {ω ω' : SourceSpace α}
    (h1 : ω.1 = ω'.1) (h2 : ∀ a, ∀ j < n a, ω.2 a j = ω'.2 a j)
    (h : g.stoppedCounts τ ω = n) : g.stoppedCounts τ ω' = n := by
  have hst : g.state ω (τ ω) = g.state ω' (τ ω) :=
    state_eq_of_eqOn_box g h1 h2 (τ ω) fun a ↦ (congrFun h a).le
  obtain ⟨t, -, ht⟩ := hτ.measurableSet_eq (τ ω)
  have hω : (ω.1, (g.state ω (τ ω)).2) ∈ t := by
    have : ω ∈ {x | τ x = τ ω} := rfl
    rw [← ht] at this
    exact this
  have hω' : (ω'.1, (g.state ω' (τ ω)).2) ∈ t := by
    rw [← h1, ← hst]
    exact hω
  have hτω : τ ω' = τ ω := by
    have : ω' ∈ (fun x ↦ (x.1, (g.state x (τ ω)).2)) ⁻¹' t := hω'
    rw [ht] at this
    exact this
  change (g.state ω' (τ ω')).1 = n
  rw [hτω, ← hst]
  exact h

/-- A stopping time of the prior game is measurable. -/
lemma measurable_of_isStoppingTime [Finite α] [MeasurableSingletonClass α] (g : PriorStrategy α)
    {T' : ℕ} {τ : SourceSpace α → ℕ}
    (hτ : g.IsStoppingTime T' τ) : Measurable τ :=
  measurable_to_countable' fun r ↦
    (measurable_fst.prodMk (measurable_state g r).snd).comap_le _ (hτ.measurableSet_eq r)

end Lemmas

/-- [INC-P003, prop:stopped-games (a)] The stopped counts of a prior game over `T'` rounds form a
size rule whose total is at most `T'`. -/
theorem stoppedCounts_isSizeRule {α : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (_hK : 2 ≤ Fintype.card α) (g : PriorStrategy α) {T' : ℕ}
    {τ : SourceSpace α → ℕ} (hτ : g.IsStoppingTime T' τ) :
    IsSizeRule (g.stoppedCounts τ) ∧ ∀ ω, ∑ a, g.stoppedCounts τ ω a ≤ T' := by
  have hmeas : Measurable (g.stoppedCounts τ) := by
    have hF : Measurable fun p : ℕ × SourceSpace α ↦ (g.state p.2 p.1).1 :=
      measurable_from_prod_countable_right fun r ↦ (measurable_state g r).fst
    exact hF.comp ((measurable_of_isStoppingTime g hτ).prodMk measurable_id)
  refine ⟨⟨hmeas, fun n ↦ ?_⟩, fun ω ↦ ?_⟩
  · let ext : (ℕ → I) × ((a : α) → Fin (n a) → ℝ) → SourceSpace α :=
      fun x ↦ (x.1, fun a j ↦ if h : j < n a then x.2 a ⟨j, h⟩ else 0)
    have hext : Measurable ext := by
      refine measurable_fst.prodMk (measurable_pi_iff.mpr fun a ↦ measurable_pi_iff.mpr fun j ↦ ?_)
      by_cases h : j < n a
      · simp only [h, ↓reduceDIte]
        exact (measurable_pi_apply _).comp ((measurable_pi_apply a).comp measurable_snd)
      · simp only [h, ↓reduceDIte]
        exact measurable_const
    have hhat : Measurable[boxSigma n] (ext ∘ boxRestrict n) :=
      hext.comp (comap_measurable (boxRestrict n))
    have hagree : ∀ ω : SourceSpace α, ∀ a, ∀ j < n a, ω.2 a j = (ext (boxRestrict n ω)).2 a j :=
      fun ω a j hj ↦ by simp [ext, boxRestrict, hj]
    have hE : {ω | g.stoppedCounts τ ω = n} =
        (ext ∘ boxRestrict n) ⁻¹' {ω | g.stoppedCounts τ ω = n} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Function.comp_apply]
      exact ⟨stoppedCounts_eq_of_eqOn_box g hτ rfl (hagree ω),
        stoppedCounts_eq_of_eqOn_box g hτ rfl fun a j hj ↦ (hagree ω a j hj).symm⟩
    rw [hE]
    exact hhat (hmeas (measurableSet_singleton n))
  · exact (sum_state_fst g ω (τ ω)).le.trans (hτ.le ω)

/-- [INC-P003, lem:prior-game (b)] The counts of a prior bandit game over `T'` rounds form a size
rule, and each count is at most `T'`. -/
theorem priorCounts_isSizeRule {α : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (hK : 2 ≤ Fintype.card α) (g : PriorStrategy α) (T' : ℕ) :
    IsSizeRule (g.counts T') ∧ ∀ ω a, g.counts T' ω a ≤ T' := by
  have h := stoppedCounts_isSizeRule hK g (PriorStrategy.isStoppingTime_const g T')
  refine ⟨h.1, fun ω a ↦ ?_⟩
  calc g.counts T' ω a ≤ ∑ b, g.counts T' ω b :=
        Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)
    _ ≤ T' := h.2 ω

end Incognita.P003
