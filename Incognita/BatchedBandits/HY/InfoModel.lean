/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.HY

/-! # HY is a learner of the information model `𝓜_0`

The algorithm `HY(w₀, β, ω, ϑ, γ)` of [INC-P000, Definition `def:hy`] (`hyAlg`) is batched on its
grid: at a round of batch `ℓ + 1`, its action is a function of the statistics of the history at the
cutoffs `t ℓ` and `t (ℓ - 1)` (counts, pseudo-means, divergences of the pseudo-empirical laws) and
of the current counts, which use the actions only. With the default parameters (`hy`), it depends
on the grid only through `t 1, …, t ℓ`; hence the family `g ↦ hy w₀ β g` is in `𝓜_0`
[INC-P006, Definition `def:infomodel`].

## Main statements

* `HY.next_congr`: two histories with the same actions and the same rewards before `R` give the
  same action at a round `n` with `t (batchOf n - 1) ≤ R`.
* `isBatched_hyAlg`: `HY(w₀, β, ω, ϑ, γ)` is batched on its grid, for all parameters.
* `HY.next_hy_eq_of_t_eq`: with the default parameters, the action at a round of batch `ℓ + 1` of
  two grids depends on the grid only through `t 0, …, t ℓ`.
* `infoModel_zero_hy`: the family `g ↦ hy w₀ β g` is in `𝓜_0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning

namespace Incognita.BatchedBandits

variable {K : ℕ}

namespace HY

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} {h h' : Hist Unit α ℝ n} {R : ℕ}

omit [Fintype α] in
/-- `HY.ind` reads only the actions. -/
lemma ind_congr (ha : ∀ i, (h i).action = (h' i).action) (r : ℕ) (c : α) (i : Fin n) :
    ind h r c i = ind h' r c i := by
  simp [ind, ha i]

omit [Fintype α] in
/-- `HY.count` reads only the actions. -/
lemma count_congr (ha : ∀ i, (h i).action = (h' i).action) (r : ℕ) (c : α) :
    count h r c = count h' r c := by
  simp [count, ha]

omit [Fintype α] in
/-- A reward of the rounds `< r` weighted by `HY.ind` reads only the actions and the rewards
before `R ≥ r`. -/
lemma ind_mul_congr (ha : ∀ i, (h i).action = (h' i).action)
    (hy : ∀ i : Fin n, (i : ℕ) < R → (h i).feedback = (h' i).feedback) {r : ℕ} (hr : r ≤ R)
    (c : α) (i : Fin n) (f : ℝ → ℝ) :
    ind h r c i * f (h i).feedback = ind h' r c i * f (h' i).feedback := by
  by_cases hi : (i : ℕ) < r
  · rw [hy i (hi.trans_le hr), ind_congr ha]
  · simp [ind, hi]

omit [Fintype α] in
/-- `HY.pseudoMean` at the cutoff `r ≤ R` reads only the actions and the rewards before `R`. -/
lemma pseudoMean_congr (ha : ∀ i, (h i).action = (h' i).action)
    (hy : ∀ i : Fin n, (i : ℕ) < R → (h i).feedback = (h' i).feedback) {r : ℕ} (hr : r ≤ R)
    (w₀ : ℝ) (c : α) : pseudoMean w₀ h r c = pseudoMean w₀ h' r c := by
  unfold pseudoMean
  rw [count_congr ha]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ ind_mul_congr ha hy hr c i (fun y ↦ y)

omit [Fintype α] in
/-- `HY.pseudoLogMean` at the cutoff `r ≤ R` reads only the actions and the rewards before
`R`. -/
lemma pseudoLogMean_congr (ha : ∀ i, (h i).action = (h' i).action)
    (hy : ∀ i : Fin n, (i : ℕ) < R → (h i).feedback = (h' i).feedback) {r : ℕ} (hr : r ≤ R)
    (w₀ : ℝ) (c : α) (q μ : ℝ) : pseudoLogMean w₀ h r c q μ = pseudoLogMean w₀ h' r c q μ := by
  unfold pseudoLogMean
  rw [count_congr ha]
  congr 2
  exact Finset.sum_congr rfl fun i _ ↦
    ind_mul_congr ha hy hr c i (fun y ↦ Real.log (1 - q * (y - μ)))

omit [Fintype α] in
/-- `HY.pseudoKinf` at the cutoff `r ≤ R` reads only the actions and the rewards before `R`. -/
lemma pseudoKinf_congr (ha : ∀ i, (h i).action = (h' i).action)
    (hy : ∀ i : Fin n, (i : ℕ) < R → (h i).feedback = (h' i).feedback) {r : ℕ} (hr : r ≤ R)
    (w₀ : ℝ) (c : α) (μ : ℝ) : pseudoKinf w₀ h r c μ = pseudoKinf w₀ h' r c μ := by
  simp only [pseudoKinf, pseudoLogMean_congr ha hy hr, pseudoMean_congr ha hy hr]

omit [Fintype α] in
/-- The current count `pullCount'` reads only the actions. -/
lemma pullCount'_congr (ha : ∀ i, (h i).action = (h' i).action) (c : α) :
    pullCount' n h c = pullCount' n h' c := by
  simp [pullCount', ha]

variable [Nonempty α]

/-- `HY.leader` at the cutoff `r ≤ R` reads only the actions and the rewards before `R`. -/
lemma leader_congr (ha : ∀ i, (h i).action = (h' i).action)
    (hy : ∀ i : Fin n, (i : ℕ) < R → (h i).feedback = (h' i).feedback) {r : ℕ} (hr : r ≤ R)
    (w₀ : ℝ) : leader w₀ h r = leader w₀ h' r := by
  simp only [leader, pseudoMean_congr ha hy hr]

/-- `HY.reference` at the cutoff `r ≤ R` reads only the actions and the rewards before `R`. -/
lemma reference_congr (ha : ∀ i, (h i).action = (h' i).action)
    (hy : ∀ i : Fin n, (i : ℕ) < R → (h i).feedback = (h' i).feedback) {r : ℕ} (hr : r ≤ R)
    (w₀ : ℝ) (U : ℕ) : reference w₀ h r U = reference w₀ h' r U := by
  have hc : ∀ c, IsWellSampled h r U c ↔ IsWellSampled h' r U c := fun c ↦ by
    simp only [IsWellSampled, count_congr ha]
  unfold reference
  by_cases h1 : ∃ c, IsWellSampled h r U c
  · have h1' : ∃ c, IsWellSampled h' r U c := h1.imp fun c ↦ (hc c).mp
    simp only [h1, h1', ↓reduceIte]
    congr 1
    funext c
    by_cases h2 : IsWellSampled h r U c
    · have h2' := (hc c).mp h2
      simp only [h2, h2', ↓reduceIte, pseudoMean_congr ha hy hr]
    · have h2' : ¬ IsWellSampled h' r U c := fun h3 ↦ h2 ((hc c).mpr h3)
      simp only [h2, h2', ↓reduceIte]
  · have h1' : ¬ ∃ c, IsWellSampled h' r U c := fun h3 ↦ h1 (h3.imp fun c ↦ (hc c).mpr)
    simp only [h1, h1', ↓reduceIte, leader_congr ha hy hr]

/-- `HY.imedKinf` at the cutoff `r ≤ R` reads only the actions and the rewards before `R`. -/
lemma imedKinf_congr (ha : ∀ i, (h i).action = (h' i).action)
    (hy : ∀ i : Fin n, (i : ℕ) < R → (h i).feedback = (h' i).feedback) {r : ℕ} (hr : r ≤ R)
    (w₀ : ℝ) (c : α) : imedKinf w₀ h r c = imedKinf w₀ h' r c := by
  simp only [imedKinf, pseudoKinf_congr ha hy hr, pseudoMean_congr ha hy hr,
    leader_congr ha hy hr]

/-- `HY.testKinf` at the cutoff `r ≤ R` reads only the actions and the rewards before `R`. -/
lemma testKinf_congr (ha : ∀ i, (h i).action = (h' i).action)
    (hy : ∀ i : Fin n, (i : ℕ) < R → (h i).feedback = (h' i).feedback) {r : ℕ} (hr : r ≤ R)
    (w₀ : ℝ) (U : ℕ) (c : α) : testKinf w₀ h r U c = testKinf w₀ h' r U c := by
  simp only [testKinf, pseudoKinf_congr ha hy hr, pseudoMean_congr ha hy hr,
    reference_congr ha hy hr]

/-- `HY.imedIndex` at the cutoff `r ≤ R` reads only the actions and the rewards before `R`. -/
lemma imedIndex_congr (ha : ∀ i, (h i).action = (h' i).action)
    (hy : ∀ i : Fin n, (i : ℕ) < R → (h i).feedback = (h' i).feedback) {r : ℕ} (hr : r ≤ R)
    (w₀ y : ℝ) (c : α) : imedIndex w₀ y h r c = imedIndex w₀ y h' r c := by
  simp only [imedIndex, imedKinf_congr ha hy hr, pullCount'_congr ha]

/-- `HY.imedArm` at the cutoff `r ≤ R` reads only the actions and the rewards before `R`. -/
lemma imedArm_congr (ha : ∀ i, (h i).action = (h' i).action)
    (hy : ∀ i : Fin n, (i : ℕ) < R → (h i).feedback = (h' i).feedback) {r : ℕ} (hr : r ≤ R)
    (w₀ y : ℝ) : imedArm w₀ y h r = imedArm w₀ y h' r := by
  simp only [imedArm, imedIndex_congr ha hy hr, leader_congr ha hy hr]

/-- `HY.threshold` with the leader's cutoff `r' ≤ R` reads only the actions and the rewards
before `R`. -/
lemma threshold_congr (ha : ∀ i, (h i).action = (h' i).action)
    (hy : ∀ i : Fin n, (i : ℕ) < R → (h i).feedback = (h' i).feedback) {r r' : ℕ}
    (hr' : r' ≤ R) (w₀ L y' : ℝ) (U U' : ℕ) :
    threshold w₀ L y' h r r' U U' = threshold w₀ L y' h' r r' U U' := by
  unfold threshold
  congr 2
  refine iInf_congr fun c ↦ ?_
  have hc : (¬ IsWellSampled h r U c ∧ c ≠ leader w₀ h r') ↔
      (¬ IsWellSampled h' r U c ∧ c ≠ leader w₀ h' r') := by
    simp only [IsWellSampled, count_congr ha, leader_congr ha hy hr']
  by_cases h1 : ¬ IsWellSampled h r U c ∧ c ≠ leader w₀ h r'
  · have h1' := hc.mp h1
    rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_left_of_eq_true _ _ (eq_true h1'),
      count_congr ha, testKinf_congr ha hy hr']
  · have h1' : ¬ (¬ IsWellSampled h' r U c ∧ c ≠ leader w₀ h' r') := fun h3 ↦ h1 (hc.mpr h3)
    rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h1')]

/-- `HY.target` at the cutoff `r ≤ R` reads only the actions and the rewards before `R`. -/
lemma target_congr (ha : ∀ i, (h i).action = (h' i).action)
    (hy : ∀ i : Fin n, (i : ℕ) < R → (h i).feedback = (h' i).feedback) {r : ℕ} (hr : r ≤ R)
    (w₀ thr ω y logt : ℝ) (U Unext : ℕ) (c : α) :
    target w₀ thr ω y logt h r U Unext c = target w₀ thr ω y logt h' r U Unext c := by
  simp only [target, count_congr ha, testKinf_congr ha hy hr]

/-- `HY.pacedArm` at the cutoff `r ≤ R` reads only the actions and the rewards before `R`. -/
lemma pacedArm_congr (ha : ∀ i, (h i).action = (h' i).action)
    (hy : ∀ i : Fin n, (i : ℕ) < R → (h i).feedback = (h' i).feedback) {r : ℕ} (hr : r ≤ R)
    (w₀ thr ω y logt : ℝ) (U Unext : ℕ) :
    pacedArm w₀ thr ω y logt h r U Unext = pacedArm w₀ thr ω y logt h' r U Unext := by
  simp only [pacedArm, target_congr ha hy hr, pullCount'_congr ha, leader_congr ha hy hr]

/-- **HY only sees the rewards of the previous batches.** At a round `n` of batch `ℓ + 1`
(`ℓ = batchOf n - 1`), two histories with the same actions and the same rewards at the rounds
`< R`, for some `R ≥ t ℓ`, give the same action of `HY(w₀, β, ω, ϑ, γ)`. -/
lemma next_congr (ha : ∀ i, (h i).action = (h' i).action)
    (hy : ∀ i : Fin n, (i : ℕ) < R → (h i).feedback = (h' i).feedback) (w₀ β : ℝ)
    (ω θ γ : ℕ → ℝ) (g : Grid K) (hR : g.t (g.batchOf n - 1) ≤ R) :
    next w₀ β ω θ γ g n h = next w₀ β ω θ γ g n h' := by
  have hR' : g.t (g.batchOf n - 1 - 1) ≤ R :=
    (g.strictMono.monotone (Nat.sub_le _ 1)).trans hR
  unfold next
  split_ifs
  · rfl
  · exact imedArm_congr ha hy hR _ _
  · exact pacedArm_congr ha hy hR _ _ _ _ _ _ _
  · rw [threshold_congr ha hy hR']
    exact pacedArm_congr ha hy hR _ _ _ _ _ _ _

end HY

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α]

/-- **HY is batched** [INC-P000, Definition `def:hy`; Theorem `thm:main`(b)]: for all parameters,
`HY(w₀, β, ω, ϑ, γ)` on the grid `g` is batched on `g`: during batch `ℓ + 1` it uses the rewards of
the rounds `< t ℓ` only. -/
lemma isBatched_hyAlg (w₀ β : ℝ) (ω θ γ : ℕ → ℝ) (g : Grid K) :
    IsBatched (hyAlg w₀ β ω θ γ g : Algorithm Unit α ℝ) g := by
  intro n h h' ha hy
  simp only [hyAlg, Algorithm.deterministic_policy, Kernel.deterministic_apply]
  rw [HY.next_congr ha hy w₀ β ω θ γ g le_rfl]

namespace Grid

variable {g g' : Grid K} {ℓ : ℕ}

omit [Fintype α] in
/-- Two grids with the same ends `t 0, …, t ℓ` have the same `netSize β j` (`U_j`) for
`j ≤ ℓ + 1`. -/
lemma netSize_eq_of_t_eq (ht : ∀ j ≤ ℓ, g.t j = g'.t j) (β : ℝ) {j : ℕ} (hj : j ≤ ℓ + 1) :
    g.netSize β j = g'.netSize β j := by
  unfold netSize
  split_ifs with h1
  · rfl
  · rw [logEnd_eq_of_t_eq ht (by omega)]

end Grid

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **HY does not know the grid ahead** [INC-P000, Definition `def:M0`]: with the default
parameters, at a round `n` of batch `ℓ + 1` of two grids `g`, `g'` with the same ends
`t 0, …, t ℓ`, HY takes the same action. -/
lemma HY.next_hy_eq_of_t_eq (w₀ β : ℝ) {g g' : Grid K} {ℓ n : ℕ} (hb : g.batchOf n = ℓ + 1)
    (hb' : g'.batchOf n = ℓ + 1) (ht : ∀ j ≤ ℓ, g.t j = g'.t j) :
    (HY.next w₀ β g.hyOmega g.hyTheta g.hyGamma g n : Hist Unit α ℝ n → α) =
      HY.next w₀ β g'.hyOmega g'.hyTheta g'.hyGamma g' n := by
  funext h
  unfold HY.next
  rw [hb, hb']
  simp only [Nat.add_sub_cancel]
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · simp
  have hne : ℓ ≠ 0 := hℓ.ne'
  have e1 : g.t ℓ = g'.t ℓ := ht ℓ le_rfl
  have e2 : g.t (ℓ - 1) = g'.t (ℓ - 1) := ht _ (Nat.sub_le ℓ 1)
  have e3 : g.ratio ℓ = g'.ratio ℓ := Grid.ratio_eq_of_t_eq ht le_rfl
  have e4 : g.ratio (ℓ - 1) = g'.ratio (ℓ - 1) := Grid.ratio_eq_of_t_eq ht (Nat.sub_le ℓ 1)
  have e5 : g.logEnd ℓ = g'.logEnd ℓ := Grid.logEnd_eq_of_t_eq ht le_rfl
  have e6 : g.logEnd 1 = g'.logEnd 1 := Grid.logEnd_eq_of_t_eq ht hℓ
  have e7 : g.netSize β ℓ = g'.netSize β ℓ := Grid.netSize_eq_of_t_eq ht β (by omega)
  have e8 : g.netSize β (ℓ - 1) = g'.netSize β (ℓ - 1) := Grid.netSize_eq_of_t_eq ht β (by omega)
  have e9 : g.netSize β (ℓ + 1) = g'.netSize β (ℓ + 1) := Grid.netSize_eq_of_t_eq ht β le_rfl
  have e10 : g.imedEnd g.hyTheta ℓ = g'.imedEnd g'.hyTheta ℓ := by
    simp only [Grid.imedEnd, Grid.hyTheta, e1]
  have e11 : g.hyOmega ℓ = g'.hyOmega ℓ := by simp only [Grid.hyOmega, e5]
  have e12 : g.hyGamma ℓ = g'.hyGamma ℓ := by simp only [Grid.hyGamma, e5]
  simp only [hne, ↓reduceIte, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12]

/-- **HY is a learner of `𝓜_0`** [INC-P000, Theorem `thm:main`(b)]: the family `g ↦ hy w₀ β g` of
HY with the default parameters is in the information model `𝓜_0` [INC-P006, Definition
`def:infomodel`], for all `w₀`, `β`. -/
lemma infoModel_zero_hy (w₀ β : ℝ) :
    InfoModel (0 : ℕ∞) (fun g : Grid K ↦ (hy w₀ β g : Algorithm Unit α ℝ)) := by
  refine ⟨fun g ↦ isBatched_hyAlg _ _ _ _ _ g, fun g g' ℓ n hb hb' ht ↦ ?_⟩
  have ht' : ∀ j ≤ ℓ, g.t j = g'.t j := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [g.t_zero, g'.t_zero]
    · exact ht j hj0 (by simpa using hj)
  have hnext := HY.next_hy_eq_of_t_eq (α := α) w₀ β hb hb' ht'
  ext x : 1
  simp only [hy, hyAlg, Algorithm.deterministic_policy, Kernel.deterministic_apply, hnext]

end Incognita.BatchedBandits
