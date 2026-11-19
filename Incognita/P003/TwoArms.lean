/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.Checks
public import Incognita.TransferBandits.SizeRules
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! # P003, prop:stopped-games (b): with two arms, bounded size rules are stopped games

Proof of [INC-P003, prop:stopped-games (b)], following the paper's proof. The result is a
pointwise version of [MV81, Theorem 4] (on `ℕ²`, under a conditional independence condition, every
stopping point is predictable, that is, reached by a policy), and its proof follows that of MV81:
the events where the size of one arm is reached and that of the other is not are separated, here
by Lusin's separation theorem.

## Main statements

* `two_arms_sizeRule_eq_stoppedCounts`: the frozen statement: with two arms, every bounded size rule
  is, at every point, the stopped counts of a prior game over `sup |N'|` rounds.
* `exists_separating`: the separation step: with two arms `a₁, a₂` and counts `m`, a Borel set of
  the data seen at `m` contains the data of the points where the size of `a₁` is reached and that
  of `a₂` is not, and none of the data of the points where the converse holds.
* `exists_stack_of_history`: the values of the stacks read by a prior game are measurable
  functions of its history: the `(j+1)`-th value observed on arm `a` is `X'_{a,j}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Incognita.TransferBandits

open scoped unitInterval

namespace Incognita.P003

section Helpers

@[deprecated (since := "2026-11-19")]
alias card_filter_castSucc := TransferBandits.card_filter_castSucc

@[deprecated (since := "2026-11-19")] alias card_filter_last := TransferBandits.card_filter_last

@[deprecated (since := "2026-11-19")] alias state_fst_eq_card := PriorStrategy.state_fst_eq_card

variable {α : Type*} [MeasurableSpace α] [DecidableEq α]

variable [Finite α] [MeasurableSingletonClass α]

/-- **The values read by a prior game are functions of its history**: there is a measurable map
`V r` from the histories of `r` rounds such that, along the game, `V r H_r a j = X'_{a,j}` for the
values already observed (`j < C_a(r)`) and `0` otherwise. -/
lemma exists_stack_of_history :
    ∃ V : (r : ℕ) → (Fin r → α × ℝ) → α → ℕ → ℝ, (∀ r a j, Measurable fun h ↦ V r h a j) ∧
      ∀ (g : PriorStrategy α) (ω : SourceSpace α) r a j,
        V r (g.state ω r).2 a j = if j < (g.state ω r).1 a then ω.2 a j else 0 := by
  refine ⟨fun r h a j ↦ ∑ i : Fin r, if (h i).1 = a ∧
      (Finset.univ.filter fun i' : Fin r ↦ i' < i ∧ (h i').1 = a).card = j then (h i).2 else 0,
    fun r a j ↦ ?_, fun g ω r ↦ ?_⟩
  · refine Finset.measurable_sum _ fun i _ ↦ Measurable.ite ?_ (by fun_prop) measurable_const
    have hp : Measurable fun h : Fin r → α × ℝ ↦ fun i ↦ (h i).1 := by fun_prop
    exact hp (MeasurableSet.of_discrete (s := {p : Fin r → α | p i = a ∧
      (Finset.univ.filter fun i' : Fin r ↦ i' < i ∧ p i' = a).card = j}))
  induction r with
  | zero => intro a j; simp [PriorStrategy.state]
  | succ r ih =>
    intro a j
    have hcount := g.state_fst_eq_card ω r a
    have hst : g.state ω (r + 1) = (Function.update (g.state ω r).1
        (g.act r (ω.1, (g.state ω r).2)) ((g.state ω r).1 (g.act r (ω.1, (g.state ω r).2)) + 1),
        Fin.snoc (α := fun _ ↦ α × ℝ) (g.state ω r).2 (g.act r (ω.1, (g.state ω r).2),
          ω.2 (g.act r (ω.1, (g.state ω r).2))
            ((g.state ω r).1 (g.act r (ω.1, (g.state ω r).2))))) := by
      simp only [PriorStrategy.state, MeasurableEquiv.finSuccProd_symm_apply]
    rw [hst]
    beta_reduce
    rw [Fin.sum_univ_castSucc]
    simp only [TransferBandits.card_filter_castSucc, TransferBandits.card_filter_last,
      Fin.snoc_castSucc, Fin.snoc_last]
    have ih' := ih a j
    simp only at ih'
    rw [ih', ← hcount]
    set a' := g.act r (ω.1, (g.state ω r).2)
    by_cases ha : a' = a
    · rw [← ha]
      simp only [Function.update_self]
      rcases lt_trichotomy j ((g.state ω r).1 a') with hj | hj | hj
      · simp [hj, hj.ne', Nat.lt_succ_of_lt hj]
      · simp [hj]
      · have h1 : ¬ j < (g.state ω r).1 a' := by omega
        have h2 : ¬ j < (g.state ω r).1 a' + 1 := by omega
        simp [h1, h2, hj.ne]
    · simp only [Function.update_of_ne (Ne.symm ha)]
      simp [ha]

omit [MeasurableSpace α] [DecidableEq α] [MeasurableSingletonClass α] in
/-- **Step 1 of the paper's proof**: with two arms `a₁, a₂` and counts `m`, a Borel set of the
data seen at `m` contains the data of the points where the size of `a₁` is reached and that of `a₂`
is not, and none of the data of the points where the converse holds (Lusin's separation theorem,
the two projections being disjoint analytic sets). -/
lemma exists_separating {N : SourceSpace α → α → ℕ} (hN : IsSizeRule N) {a₁ a₂ : α}
    (hall : ∀ a, a = a₁ ∨ a = a₂) (m : α → ℕ) :
    ∃ S : Set ((ℕ → I) × ((a : α) → Fin (m a) → ℝ)), MeasurableSet S ∧
      (∀ ω, N ω a₁ = m a₁ → m a₂ < N ω a₂ → boxRestrict m ω ∈ S) ∧
      (∀ ω, m a₁ < N ω a₁ → N ω a₂ = m a₂ → boxRestrict m ω ∉ S) := by
  classical
  have hNa : ∀ a, Measurable fun ω : SourceSpace α ↦ N ω a := fun a ↦
    (measurable_pi_apply a).comp hN.measurable
  set A : Set (SourceSpace α) := {ω | N ω a₁ = m a₁ ∧ m a₂ < N ω a₂}
  set B : Set (SourceSpace α) := {ω | m a₁ < N ω a₁ ∧ N ω a₂ = m a₂}
  have hAm : MeasurableSet A :=
    (measurableSet_eq_fun (hNa a₁) measurable_const).inter
      (measurableSet_lt measurable_const (hNa a₂))
  have hBm : MeasurableSet B :=
    (measurableSet_lt measurable_const (hNa a₁)).inter
      (measurableSet_eq_fun (hNa a₂) measurable_const)
  have hbox : Measurable (boxRestrict (α := α) m) := measurable_boxRestrict m
  have hdisj : Disjoint (boxRestrict m '' A) (boxRestrict m '' B) := by
    refine Set.disjoint_left.mpr ?_
    rintro y ⟨ω, hω, rfl⟩ ⟨ω', hω', hy⟩
    have hy1 : ω'.1 = ω.1 := by
      have := congrArg Prod.fst hy
      exact this
    have hy2 : ∀ a (j : ℕ), j < m a → ω'.2 a j = ω.2 a j := fun a j hj ↦
      congrFun (congrFun (congrArg Prod.snd hy) a) ⟨j, hj⟩
    set ω'' : SourceSpace α := (ω.1, fun a j ↦ if a = a₁ then ω'.2 a₁ j else ω.2 a j)
    have h1 : N ω'' = N ω := by
      refine eq_of_boxRestrict_eq hN rfl ?_
      refine Prod.ext rfl (funext fun a ↦ funext fun j ↦ ?_)
      simp only [boxRestrict, ω'']
      by_cases ha : a = a₁
      · subst ha
        rw [ite_eq_left rfl, hy2 a j (by have := j.2; have := hω.1; omega)]
      · rw [ite_eq_right ha]
    have h2 : N ω'' = N ω' := by
      refine eq_of_boxRestrict_eq hN rfl ?_
      refine Prod.ext (by exact hy1) (funext fun a ↦ funext fun j ↦ ?_)
      simp only [boxRestrict, ω'']
      by_cases ha : a = a₁
      · subst ha
        rw [ite_eq_left rfl]
      · rw [ite_eq_right ha]
        have ha2 : a = a₂ := (hall a).resolve_left ha
        subst ha2
        exact hy2 a j (by have := j.2; have := hω'.2; omega)
    have := congrFun (h1.symm.trans h2) a₂
    have h3 := hω.2
    have h4 := hω'.2
    omega
  obtain ⟨u, hAu, hBu, hu⟩ := (hAm.analyticSet_image hbox).measurablySeparable
    (hBm.analyticSet_image hbox) hdisj
  refine ⟨u, hu, fun ω h1 h2 ↦ hAu ⟨ω, ⟨h1, h2⟩, rfl⟩, fun ω h1 h2 hω ↦ ?_⟩
  exact Set.disjoint_left.mp hBu ⟨ω, ⟨h1, h2⟩, rfl⟩ hω

end Helpers

/-- [INC-P003, prop:stopped-games (b)] With two arms, every bounded size rule is, at every point,
the stopped counts of a prior game over `sup |N'|` rounds: a pointwise version of
[MV81, Theorem 4] (on `ℕ²`, stopping points are predictable). -/
theorem two_arms_sizeRule_eq_stoppedCounts {α : Type*} [Fintype α] [DecidableEq α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (hK : Fintype.card α = 2)
    {N : SourceSpace α → α → ℕ} (hN : IsSizeRule N) (hbdd : ∃ M : ℕ, ∀ ω, ∑ a, N ω a ≤ M) :
    ∃ (g : PriorStrategy α) (τ : SourceSpace α → ℕ),
      g.IsStoppingTime (sSup (Set.range fun ω ↦ ∑ a, N ω a)) τ ∧
        ∀ ω, g.stoppedCounts τ ω = N ω := by
  classical
  -- The two arms.
  obtain ⟨a₁⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card α)
  obtain ⟨a₂, h21⟩ := Fintype.exists_ne_of_one_lt_card (by omega) a₁
  have hall : ∀ a, a = a₁ ∨ a = a₂ := by
    intro a
    by_contra h
    push Not at h
    have h3 : ({a, a₁, a₂} : Finset α).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [h.1, h.2]), Finset.card_pair (Ne.symm h21)]
    have := Finset.card_le_univ ({a, a₁, a₂} : Finset α)
    omega
  choose S hSm hSA hSB using fun m ↦ exists_separating hN hall m
  obtain ⟨V, hVm, hV⟩ := exists_stack_of_history (α := α)
  -- Measurability of the events of a history.
  have hacts : ∀ r, Measurable fun x : (ℕ → I) × (Fin r → α × ℝ) ↦ fun i ↦ (x.2 i).1 :=
    fun r ↦ by fun_prop
  have hdat : ∀ r (m : α → ℕ), Measurable fun x : (ℕ → I) × (Fin r → α × ℝ) ↦
      ((x.1, fun a (i : Fin (m a)) ↦ V r x.2 a i) : (ℕ → I) × ((a : α) → Fin (m a) → ℝ)) :=
    fun r m ↦ measurable_fst.prodMk (measurable_pi_iff.mpr fun a ↦ measurable_pi_iff.mpr
      fun i ↦ (hVm r a i).comp measurable_snd)
  have hcntm : ∀ r (m : α → ℕ), MeasurableSet {x : (ℕ → I) × (Fin r → α × ℝ) |
      (fun a ↦ (Finset.univ.filter fun i ↦ (x.2 i).1 = a).card) = m} := fun r m ↦
    hacts r (MeasurableSet.of_discrete (s := {p : Fin r → α |
      (fun a ↦ (Finset.univ.filter fun i ↦ p i = a).card) = m}))
  -- The decision sets and the strategy.
  set T : (r : ℕ) → Set ((ℕ → I) × (Fin r → α × ℝ)) := fun r ↦ ⋃ m : α → ℕ,
    {x | (fun a ↦ (Finset.univ.filter fun i ↦ (x.2 i).1 = a).card) = m} ∩
      {x | ((x.1, fun a (i : Fin (m a)) ↦ V r x.2 a i) :
        (ℕ → I) × ((a : α) → Fin (m a) → ℝ)) ∈ S m}
  have hT : ∀ r, MeasurableSet (T r) := fun r ↦
    MeasurableSet.iUnion fun m ↦ (hcntm r m).inter (hdat r m (hSm m))
  let g : PriorStrategy α := ⟨fun r x ↦ if x ∈ T r then a₂ else a₁,
    fun r ↦ Measurable.ite (hT r) measurable_const measurable_const⟩
  -- Along the game, the history gives the counts and the values of the box.
  have hdata : ∀ ω r, ((ω.1, fun a (i : Fin ((g.state ω r).1 a)) ↦ V r (g.state ω r).2 a i) :
      (ℕ → I) × ((a : α) → Fin ((g.state ω r).1 a) → ℝ)) = boxRestrict (g.state ω r).1 ω := by
    intro ω r
    refine Prod.ext rfl (funext fun a ↦ funext fun i ↦ ?_)
    -- `(boxRestrict n ω).2 a i = ω.2 a i`, by definition of `boxRestrict`
    change V r (g.state ω r).2 a i = ω.2 a i
    rw [hV g ω r a i, ite_eq_left i.2]
  have hcnt : ∀ ω r, (fun a ↦ (Finset.univ.filter fun i ↦ ((g.state ω r).2 i).1 = a).card) =
      (g.state ω r).1 := fun ω r ↦ funext fun a ↦ (g.state_fst_eq_card ω r a).symm
  have hmemT : ∀ ω r, ((ω.1, (g.state ω r).2) ∈ T r ↔
      boxRestrict (g.state ω r).1 ω ∈ S (g.state ω r).1) := by
    intro ω r
    simp only [T, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨m, hm, hS⟩
      rw [hcnt] at hm
      subst hm
      rwa [← hdata]
    · intro h
      exact ⟨_, hcnt ω r, by rw [hdata]; exact h⟩
  -- The game follows the size rule.
  have hfollow : ∀ ω r, r ≤ ∑ a, N ω a → ∀ a, (g.state ω r).1 a ≤ N ω a := by
    intro ω r
    induction r with
    | zero => intro _ a; simp [PriorStrategy.state]
    | succ r ih =>
      intro hr a
      have hle := ih (by omega)
      have hsum := PriorStrategy.sum_state_fst g ω r
      have hne : ∃ b, (g.state ω r).1 b < N ω b := by
        by_contra h
        push Not at h
        have : ∑ a, N ω a ≤ ∑ a, (g.state ω r).1 a := Finset.sum_le_sum fun b _ ↦ h b
        omega
      have hstep : (g.state ω (r + 1)).1 = Function.update (g.state ω r).1
          (g.act r (ω.1, (g.state ω r).2))
          ((g.state ω r).1 (g.act r (ω.1, (g.state ω r).2)) + 1) := rfl
      have hlt : (g.state ω r).1 (g.act r (ω.1, (g.state ω r).2)) <
          N ω (g.act r (ω.1, (g.state ω r).2)) := by
        by_cases h1 : N ω a₁ = (g.state ω r).1 a₁
        · have h2 : (g.state ω r).1 a₂ < N ω a₂ := by
            obtain ⟨b, hb⟩ := hne
            rcases hall b with rfl | rfl
            · omega
            · exact hb
          have hin : (ω.1, (g.state ω r).2) ∈ T r :=
            (hmemT ω r).mpr (hSA (g.state ω r).1 ω h1 h2)
          have ha' : g.act r (ω.1, (g.state ω r).2) = a₂ := ite_eq_left hin
          rw [ha']
          exact h2
        · by_cases h2 : N ω a₂ = (g.state ω r).1 a₂
          · have h1' : (g.state ω r).1 a₁ < N ω a₁ := lt_of_le_of_ne (hle a₁) (Ne.symm h1)
            have hin : (ω.1, (g.state ω r).2) ∉ T r := fun h ↦
              hSB (g.state ω r).1 ω h1' h2 ((hmemT ω r).mp h)
            have ha' : g.act r (ω.1, (g.state ω r).2) = a₁ := ite_eq_right hin
            rw [ha']
            exact h1'
          · rcases hall (g.act r (ω.1, (g.state ω r).2)) with h | h <;> rw [h]
            · exact lt_of_le_of_ne (hle a₁) (Ne.symm h1)
            · exact lt_of_le_of_ne (hle a₂) (Ne.symm h2)
      rw [hstep]
      by_cases ha : a = g.act r (ω.1, (g.state ω r).2)
      · rw [ha, Function.update_self]
        omega
      · rw [Function.update_of_ne ha]
        exact hle a
  have hreach : ∀ ω, (g.state ω (∑ a, N ω a)).1 = N ω := by
    intro ω
    have hle := hfollow ω _ le_rfl
    have hsum := PriorStrategy.sum_state_fst g ω (∑ a, N ω a)
    funext a
    by_contra h
    have hlt : ∑ b, (g.state ω (∑ a, N ω a)).1 b < ∑ b, N ω b :=
      Finset.sum_lt_sum (fun b _ ↦ hle b) ⟨a, Finset.mem_univ a, lt_of_le_of_ne (hle a) h⟩
    omega
  refine ⟨g, fun ω ↦ ∑ a, N ω a, ⟨fun ω ↦ ?_, fun r ↦ ?_⟩, fun ω ↦ hreach ω⟩
  · obtain ⟨M, hM⟩ := hbdd
    exact le_csSup ⟨M, by rintro _ ⟨ω', rfl⟩; exact hM ω'⟩ ⟨ω, rfl⟩
  · have hset : {ω : SourceSpace α | ∑ a, N ω a = r} = {ω | N ω = (g.state ω r).1} := by
      ext ω
      simp only [Set.mem_ofPred_eq]
      constructor
      · intro h
        rw [← h, hreach]
      · intro h
        rw [h]
        exact PriorStrategy.sum_state_fst g ω r
    rw [hset]
    choose G hG hGeq using fun m : α → ℕ ↦ hN.measurableSet_eq m
    refine ⟨⋃ m : α → ℕ, {x | (fun a ↦ (Finset.univ.filter fun i ↦ (x.2 i).1 = a).card) = m} ∩
      {x | ((x.1, fun a (i : Fin (m a)) ↦ V r x.2 a i) :
        (ℕ → I) × ((a : α) → Fin (m a) → ℝ)) ∈ G m},
      MeasurableSet.iUnion fun m ↦ (hcntm r m).inter (hdat r m (hG m)), ?_⟩
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    have hmemG : ∀ m, boxRestrict m ω ∈ G m ↔ N ω = m := fun m ↦ by
      rw [← Set.mem_preimage, hGeq m]
      rfl
    constructor
    · rintro ⟨m, hm, hGm⟩
      rw [hcnt] at hm
      subst hm
      rw [hdata] at hGm
      exact (hmemG _).mp hGm
    · intro h
      refine ⟨_, hcnt ω r, ?_⟩
      rw [hdata]
      exact (hmemG _).mpr h

end Incognita.P003
