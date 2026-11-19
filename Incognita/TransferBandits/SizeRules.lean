/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.PriorGame

/-! # Size rules that read only their box; the prior game round by round

General facts about `IsSizeRule` and `PriorStrategy` [INC-P003, def:size-rule, def:prior-game and
def:stopped-game].

## Main statements

* `isSizeRule_of_eqOn_box`: a measurable size map such that `N'(ω) = n` implies `N'(ω') = n`
  whenever `ω'` has the randomisation and the values of the box of `n` of `ω` is a size rule.
* `eq_of_boxRestrict_eq`: conversely, a size rule that equals `n` at `ω` equals `n` at every point
  with the same randomisation and the same values in the box of `n`.
* `PriorStrategy.measurable_state`: the state of the prior game after `r` rounds is measurable.
* `PriorStrategy.sum_state_fst`: after `r` rounds the counts add up to `r`.
* `PriorStrategy.state_eq_of_eqOn_box`: two source points that agree on the randomisation and on
  the box of `n` give the same first `r` rounds as long as the counts after `r` rounds are at
  most `n`; `PriorStrategy.stoppedCounts_eq_of_eqOn_box`: the same for the stopped counts.
* `PriorStrategy.measurable_of_isStoppingTime`: a stopping time of the prior game is measurable;
  `PriorStrategy.measurable_stoppedCounts`, `PriorStrategy.sum_stoppedCounts`: the stopped counts
  are measurable and add up to `τ`.
-/

@[expose] public section

open MeasureTheory

open scoped unitInterval

namespace Incognita.TransferBandits

/-- A measurable size map whose event `{N' = n}` only depends on the randomisation and on the box
of `n` is a size rule: `{N' = n}` is its own preimage under the `𝒢_n`-measurable map that keeps
the box of `n` and puts `0` outside it. -/
lemma isSizeRule_of_eqOn_box {α : Type*} [Finite α] {N : SourceSpace α → α → ℕ}
    (hN : Measurable N)
    (h : ∀ (n : α → ℕ) (ω ω' : SourceSpace α), ω.1 = ω'.1 → (∀ a, ∀ j < n a, ω.2 a j = ω'.2 a j) →
      N ω = n → N ω' = n) :
    IsSizeRule N := by
  refine ⟨hN, fun n ↦ ?_⟩
  let ext : (ℕ → I) × ((a : α) → Fin (n a) → ℝ) → SourceSpace α :=
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
  have hE : {ω | N ω = n} = (ext ∘ boxRestrict n) ⁻¹' {ω | N ω = n} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Function.comp_apply]
    exact ⟨h n ω _ rfl (hagree ω), h n _ ω rfl fun a j hj ↦ (hagree ω a j hj).symm⟩
  rw [hE]
  exact hhat (hN (measurableSet_singleton n))

/-- A size rule that equals `n` at `ω` equals `n` at every point with the same randomisation and
the same values in the box of `n`. -/
lemma eq_of_boxRestrict_eq {α : Type*} {N : SourceSpace α → α → ℕ} (hN : IsSizeRule N) {n : α → ℕ}
    {ω ω' : SourceSpace α} (h : N ω = n) (hbox : boxRestrict n ω = boxRestrict n ω') :
    N ω' = n := by
  obtain ⟨G, -, hG⟩ := hN.measurableSet_eq n
  have h1 : ω ∈ boxRestrict n ⁻¹' G := by rw [hG]; exact h
  have h2 : ω' ∈ boxRestrict n ⁻¹' G := by
    simp only [Set.mem_preimage] at h1 ⊢
    rwa [← hbox]
  rw [hG] at h2
  exact h2

section Snoc

variable {α : Type*} [DecidableEq α]

/-- Removing the last round of a history does not change the counts before an earlier round. -/
lemma card_filter_castSucc {r : ℕ} (h : Fin r → α × ℝ) (y : α × ℝ) (a : α) (i : Fin r) :
    (Finset.univ.filter fun i' : Fin (r + 1) ↦
        i' < i.castSucc ∧ (Fin.snoc (α := fun _ ↦ α × ℝ) h y i').1 = a).card =
      (Finset.univ.filter fun i' : Fin r ↦ i' < i ∧ (h i').1 = a).card := by
  rw [← Finset.card_map (Fin.castSuccEmb : Fin r ↪ Fin (r + 1))
    (s := Finset.univ.filter fun i' : Fin r ↦ i' < i ∧ (h i').1 = a)]
  refine congrArg Finset.card ?_
  ext i'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Fin.castSuccEmb_apply]
  refine Fin.lastCases ?_ (fun k ↦ ?_) i'
  · constructor
    · rintro ⟨h1, -⟩
      exact absurd h1 (not_lt.mpr (Fin.castSucc_lt_last i).le)
    · rintro ⟨k, -, hk⟩
      exact absurd hk (Fin.castSucc_ne_last k)
  · simp only [Fin.snoc_castSucc,
      Fin.castSucc_lt_castSucc_iff]
    constructor
    · rintro h1
      exact ⟨k, h1, rfl⟩
    · rintro ⟨k', hk', hkk'⟩
      rw [← Fin.castSucc_inj.mp hkk']
      exact hk'

/-- The count of `a` before the last round of a history is the count of `a` in the history
without it. -/
lemma card_filter_last {r : ℕ} (h : Fin r → α × ℝ) (y : α × ℝ) (a : α) :
    (Finset.univ.filter fun i' : Fin (r + 1) ↦
        i' < Fin.last r ∧ (Fin.snoc (α := fun _ ↦ α × ℝ) h y i').1 = a).card =
      (Finset.univ.filter fun i' : Fin r ↦ (h i').1 = a).card := by
  rw [← Finset.card_map (Fin.castSuccEmb : Fin r ↪ Fin (r + 1))
    (s := Finset.univ.filter fun i' : Fin r ↦ (h i').1 = a)]
  refine congrArg Finset.card ?_
  ext i'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Fin.castSuccEmb_apply]
  refine Fin.lastCases ?_ (fun k ↦ ?_) i'
  · simp only [lt_self_iff_false, false_and, false_iff, not_exists, not_and]
    exact fun k _ hk ↦ Fin.castSucc_ne_last k hk
  · simp only [Fin.snoc_castSucc,
      Fin.castSucc_lt_last, true_and]
    constructor
    · rintro h1
      exact ⟨k, h1, rfl⟩
    · rintro ⟨k', hk', hkk'⟩
      rw [← Fin.castSucc_inj.mp hkk']
      exact hk'

end Snoc

namespace PriorStrategy

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
  -- `stoppedCounts τ ω' = (g.state ω' (τ ω')).1`, by definition
  change (g.state ω' (τ ω')).1 = n
  rw [hτω, ← hst]
  exact h

/-- A stopping time of the prior game is measurable. -/
lemma measurable_of_isStoppingTime [Finite α] [MeasurableSingletonClass α] (g : PriorStrategy α)
    {T' : ℕ} {τ : SourceSpace α → ℕ}
    (hτ : g.IsStoppingTime T' τ) : Measurable τ :=
  measurable_to_countable' fun r ↦
    (measurable_fst.prodMk (measurable_state g r).snd).comap_le _ (hτ.measurableSet_eq r)

/-- The stopped counts of the prior game are measurable. -/
lemma measurable_stoppedCounts [Finite α] [MeasurableSingletonClass α] (g : PriorStrategy α)
    {T' : ℕ} {τ : SourceSpace α → ℕ} (hτ : g.IsStoppingTime T' τ) :
    Measurable (g.stoppedCounts τ) := by
  have hF : Measurable fun p : ℕ × SourceSpace α ↦ (g.state p.2 p.1).1 :=
    measurable_from_prod_countable_right fun r ↦ (measurable_state g r).fst
  exact hF.comp ((measurable_of_isStoppingTime g hτ).prodMk measurable_id)

/-- The stopped counts of the prior game add up to `τ`. -/
lemma sum_stoppedCounts [Fintype α] (g : PriorStrategy α) (τ : SourceSpace α → ℕ)
    (ω : SourceSpace α) : ∑ a, g.stoppedCounts τ ω a = τ ω :=
  sum_state_fst g ω (τ ω)

/-- The counts of a prior game do not decrease. -/
lemma state_fst_mono (g : PriorStrategy α)
    (ω : SourceSpace α) {r r' : ℕ} (h : r ≤ r') (a : α) :
    (g.state ω r).1 a ≤ (g.state ω r').1 a := by
  induction r', h using Nat.le_induction with
  | base => exact le_rfl
  | succ r' _ ih => exact ih.trans (state_fst_le_succ g ω r' a)

/-- After one round, the arm pulled first has count `1`. -/
lemma state_one_fst_act (g : PriorStrategy α) (ω : SourceSpace α) :
    (g.state ω 1).1 (g.act 0 (ω.1, fun i ↦ i.elim0)) = 1 := by
  simp only [PriorStrategy.state]
  rw [Function.update_self]
  rfl

/-- The counts of a prior game are the counts of its history. -/
lemma state_fst_eq_card (g : PriorStrategy α) (ω : SourceSpace α) :
    ∀ r a, (g.state ω r).1 a = (Finset.univ.filter fun i ↦ ((g.state ω r).2 i).1 = a).card
  | 0, a => by simp [PriorStrategy.state]
  | r + 1, a => by
    have ih := state_fst_eq_card g ω r a
    have hst : g.state ω (r + 1) = (Function.update (g.state ω r).1
        (g.act r (ω.1, (g.state ω r).2)) ((g.state ω r).1 (g.act r (ω.1, (g.state ω r).2)) + 1),
        Fin.snoc (α := fun _ ↦ α × ℝ) (g.state ω r).2 (g.act r (ω.1, (g.state ω r).2),
          ω.2 (g.act r (ω.1, (g.state ω r).2))
            ((g.state ω r).1 (g.act r (ω.1, (g.state ω r).2))))) := by
      simp only [PriorStrategy.state, MeasurableEquiv.finSuccProd_symm_apply]
    rw [hst, Finset.card_filter, Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [← Finset.card_filter, ← ih]
    by_cases ha : g.act r (ω.1, (g.state ω r).2) = a
    · rw [← ha, Function.update_self]
      simp
    · rw [Function.update_of_ne (Ne.symm ha)]
      simp [ha]

end PriorStrategy

end Incognita.TransferBandits
