/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.Consistency
public import LeanMachineLearning.ForMathlib.MeasureTheory.Group.Arithmetic

/-! # Examples of size maps and transfer learners

Objects of [INC-P003] used by its statements (paper `P003-transfer-setting`).

## Main definitions

* `constSize n`: the constant size map `N' ≡ n` (lem:prior-game (a)).
* `lookahead a₁`: the look-ahead map `N^la` of thm:main (b) and lem:lookahead: `N^la_{a₁} = 1` if
  the second value of the stack of `a₁` exceeds `1/2`, and `2` otherwise; `0` on the other arms.
* `TransferAlgorithm.constArm a`: the learner that pulls `a` at every round.
* `cyclicSize a₁ a₂ a₃`: the cyclic map `N^cyc` of prop:stopped-games (c), on three arms.
* `sourceMean s k`: the source empirical mean `m̂'_k(s)` of arm `k` (def:source-data).
* `bestSourceArm s`: the smallest arm maximising the source empirical mean.
* `followSourceArm s`, `TransferAlgorithm.followSource`: the learner `π^tr` of prop:exclusion, which
  pulls `bestSourceArm s` at every round when every arm has a source value, and the smallest arm
  otherwise.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Incognita.TransferBandits

variable {α : Type*} [MeasurableSpace α]

/-- The constant size map `N' ≡ n` (deterministic sizes) [INC-P003, lem:prior-game (a)]. -/
def constSize (n : α → ℕ) (_ : SourceSpace α) : α → ℕ := n

/-- The **look-ahead map** `N^la` of [INC-P003, thm:main (b) and lem:lookahead]: on the arm `a₁`
(the paper's arm `1`), the size is `1` if the second value `X'_{a₁,2}` (0-based index `1`) of the
stack of `a₁` exceeds `1/2`, and `2` otherwise; the other arms get size `0`. -/
noncomputable def lookahead [DecidableEq α] (a₁ : α) (ω : SourceSpace α) : α → ℕ :=
  fun a ↦ if a = a₁ then (if (1 / 2 : ℝ) < ω.2 a₁ 1 then 1 else 2) else 0

/-- The learner that pulls the arm `a` at every round, whatever the source data and the history. -/
noncomputable def TransferAlgorithm.constArm (a : α) : TransferAlgorithm α where
  policy _ := Kernel.const _ (Measure.dirac a)

/-- The **cyclic map** `N^cyc` of [INC-P003, prop:stopped-games (c)], on three arms `a₁, a₂, a₃`
(the paper's arms `1, 2, 3`), with `b_k = 1{X'_{k,1} > 1/2}` read on the first value (0-based index
`0`) of each stack: `e₁ + e₂` on `{b₁ = 1, b₂ = 0}`, `e₂ + e₃` on `{b₂ = 1, b₃ = 0}`, `e₃ + e₁` on
`{b₃ = 1, b₁ = 0}`, and `e₁ + e₂ + e₃` elsewhere (the three events are disjoint). -/
noncomputable def cyclicSize [DecidableEq α] (a₁ a₂ a₃ : α) (ω : SourceSpace α) : α → ℕ :=
  let b : α → Prop := fun k ↦ (1 / 2 : ℝ) < ω.2 k 0
  if b a₁ ∧ ¬ b a₂ then Pi.single a₁ 1 + Pi.single a₂ 1
  else if b a₂ ∧ ¬ b a₃ then Pi.single a₂ 1 + Pi.single a₃ 1
  else if b a₃ ∧ ¬ b a₁ then Pi.single a₃ 1 + Pi.single a₁ 1
  else Pi.single a₁ 1 + Pi.single a₂ 1 + Pi.single a₃ 1

/-- The source empirical mean `m̂'_k(s) = n_k(s)⁻¹ ∑_{j < n_k(s)} x_{k,j}` of arm `k`
[INC-P003, def:source-data] (it is `0` when `n_k(s) = 0`, a case where it is not used). -/
noncomputable def sourceMean (s : Source α) (k : α) : ℝ :=
  (∑ j ∈ Finset.range (s.1 k), s.2 k j) / s.1 k

omit [MeasurableSpace α] in
/-- The source empirical mean of an arm is measurable (LML's `measurable_sum_range`). -/
lemma measurable_sourceMean (k : α) : Measurable fun s : Source α ↦ sourceMean s k := by
  have hn : Measurable fun s : Source α ↦ s.1 k := (measurable_pi_apply k).comp measurable_fst
  exact (measurable_sum_range (fun j ↦ (measurable_pi_apply j).comp
    ((measurable_pi_apply k).comp measurable_snd)) hn).div (measurable_from_nat.comp hn)

section FollowSource

variable [Fintype α] [LinearOrder α] [Nonempty α]

/-- The smallest arm `k̂(s)` maximising the source empirical mean. -/
noncomputable def bestSourceArm (s : Source α) : α :=
  (Finset.univ.filter fun k ↦ ∀ j, sourceMean s j ≤ sourceMean s k).min'
    (by
      obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ (sourceMean s) Finset.univ_nonempty
      exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, fun j ↦ hk j (Finset.mem_univ j)⟩⟩)

/-- The arm pulled at every round by `π^tr` [INC-P003, prop:exclusion]: `k̂(s)` when `n_k(s) ≥ 1`
for every arm `k`, and otherwise the smallest arm (the paper's arm `1`). -/
noncomputable def followSourceArm (s : Source α) : α :=
  by classical exact
    if ∀ k, 1 ≤ s.1 k then bestSourceArm s else Finset.univ.min' Finset.univ_nonempty

omit [MeasurableSpace α] in
lemma bestSourceArm_eq_iff (s : Source α) (k : α) :
    bestSourceArm s = k ↔ (∀ j, sourceMean s j ≤ sourceMean s k) ∧
      ∀ i, (∀ j, sourceMean s j ≤ sourceMean s i) → k ≤ i := by
  unfold bestSourceArm
  rw [Finset.min'_eq_iff]
  simp

lemma measurable_bestSourceArm : Measurable (bestSourceArm (α := α)) := by
  refine measurable_to_countable' fun k ↦ ?_
  have : bestSourceArm ⁻¹' {k} = {s : Source α | (∀ j, sourceMean s j ≤ sourceMean s k) ∧
      ∀ i, (∀ j, sourceMean s j ≤ sourceMean s i) → k ≤ i} := by
    ext s
    simp [bestSourceArm_eq_iff]
  rw [this, Set.ofPred_and]
  refine MeasurableSet.inter ?_ ?_
  · simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j ↦
      measurableSet_le (measurable_sourceMean j) (measurable_sourceMean k)
  · simp only [Set.ofPred_forall]
    refine MeasurableSet.iInter fun i ↦ ?_
    by_cases hki : k ≤ i
    · simp [hki]
    · simp only [hki, imp_false]
      refine MeasurableSet.compl (s := {x : Source α | ∀ j, sourceMean x j ≤ sourceMean x i}) ?_
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun j ↦
        measurableSet_le (measurable_sourceMean j) (measurable_sourceMean i)

lemma measurable_followSourceArm : Measurable (followSourceArm (α := α)) := by
  classical
  unfold followSourceArm
  refine Measurable.ite ?_ measurable_bestSourceArm measurable_const
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun k ↦ measurableSet_le measurable_const (by fun_prop)

/-- The learner `π^tr` that **follows the source** [INC-P003, prop:exclusion]: at every round it
pulls `followSourceArm s`, the smallest arm maximising the source empirical mean when every arm
has at least one source value, and the smallest arm otherwise. -/
noncomputable def TransferAlgorithm.followSource : TransferAlgorithm α where
  policy _ := Kernel.deterministic (fun p ↦ followSourceArm p.1)
    (measurable_followSourceArm.comp measurable_fst)

end FollowSource

end Incognita.TransferBandits
