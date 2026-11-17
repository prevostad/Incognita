/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.Consistency
public import Incognita.BatchedBandits.Instances

/-! # Joint satisfiability of the hypotheses of the frozen statements of P006

For each frozen statement `Incognita.Statements.P006.<name>`, the lemma
`Incognita.P006.<name>_satisfiable` exhibits an explicit instance that satisfies all its
hypotheses at once (and, where the statement is about a class or a learner, a non-trivial one).
The arms are `Bool` (two arms, `K = 2`); the instance is the Bernoulli instance
`(Ber(0.7), Ber(0.5))` of [INC-P006, Section `sec:examples`] (arm `true` has mean `7/10`, arm
`false` has mean `1/2`); the grids are `𝖲_2` and `𝖣_2`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Bandits LMLExplore.Bandits

open scoped unitInterval

namespace Incognita.P006

open Incognita.BatchedBandits

lemma two_le_card_bool : 2 ≤ Fintype.card Bool := by simp

lemma max_two_card_bool_le : max 2 (Fintype.card Bool) ≤ 2 := by simp

/-- The largest mean of the two-armed Bernoulli instance with means `p` (arm `true`) and `q ≤ p`
(arm `false`) is `p`. -/
lemma iSup_bernoulliBandit_bool {p q : I} (hqp : (q : ℝ) ≤ p) :
    (⨆ b, (bernoulliBandit (fun b : Bool ↦ if b then p else q) b)[id]) = (p : ℝ) := by
  simp_rw [integral_id_bernoulliBandit]
  refine le_antisymm (ciSup_le fun b ↦ ?_) (le_ciSup_of_le (Finite.bddAbove_range _) true ?_)
  · cases b
    · simpa using hqp
    · simp
  · simp

lemma gap_bernoulliBandit_bool_false {p q : I} (hqp : (q : ℝ) ≤ p) :
    gap (bernoulliBandit (fun b : Bool ↦ if b then p else q)) false = p - q := by
  rw [gap, iSup_bernoulliBandit_bool hqp]
  simp

lemma gap_bernoulliBandit_bool_true {p q : I} (hqp : (q : ℝ) ≤ p) :
    gap (bernoulliBandit (fun b : Bool ↦ if b then p else q)) true = 0 := by
  rw [gap, iSup_bernoulliBandit_bool hqp]
  simp

/-- The means `7/10` and `1/2` of the example instance. -/
lemma example_means :
    ((⟨1 / 2, by norm_num, by norm_num⟩ : I) : ℝ) ≤ ((⟨7 / 10, by norm_num, by norm_num⟩ : I) : ℝ) ∧
      ((⟨7 / 10, by norm_num, by norm_num⟩ : I) : ℝ) < 1 := by
  norm_num

/-- The Bernoulli instance `(Ber(0.7), Ber(0.5))` is in `𝒫`, arm `true` is optimal and arm `false`
is suboptimal. -/
lemma example_instance :
    bernoulliBandit (fun b : Bool ↦ if b then (⟨7 / 10, by norm_num, by norm_num⟩ : I)
        else ⟨1 / 2, by norm_num, by norm_num⟩) ∈ unitBandits Bool ∧
      gap (bernoulliBandit (fun b : Bool ↦ if b then (⟨7 / 10, by norm_num, by norm_num⟩ : I)
        else ⟨1 / 2, by norm_num, by norm_num⟩)) true = 0 ∧
      0 < gap (bernoulliBandit (fun b : Bool ↦ if b then (⟨7 / 10, by norm_num, by norm_num⟩ : I)
        else ⟨1 / 2, by norm_num, by norm_num⟩)) false := by
  refine ⟨bernoulliBandit_mem_unitBandits _ fun b ↦ ?_, gap_bernoulliBandit_bool_true
    example_means.1, ?_⟩
  · cases b <;> norm_num
  · rw [gap_bernoulliBandit_bool_false example_means.1]
    norm_num

/-! ### `thm:main`(i) -/

/-- `Incognita.Statements.P006.infoModel_mono`: two arms, `k = 1 ≤ k' = ∞`, and the parity
learner `Par^{(0)}`, which depends on the grid and is in `𝓜_1`. -/
lemma infoModel_mono_satisfiable :
    ∃ (k k' : ℕ∞) (π : Grid (Fintype.card Bool) → Algorithm Unit Bool ℝ),
      2 ≤ Fintype.card Bool ∧ k ≤ k' ∧ InfoModel k π :=
  ⟨((0 + 1 : ℕ) : ℕ∞), ⊤, fun g ↦ parityAlg 0 true false g, two_le_card_bool, le_top,
    infoModel_parityAlg 0 true false⟩

/-- `Incognita.Statements.P006.infoModel_strict`: two arms and `k = 0 < k' = 1`. -/
lemma infoModel_strict_satisfiable :
    ∃ k k' : ℕ∞, 2 ≤ Fintype.card Bool ∧ k < k' :=
  ⟨0, 1, two_le_card_bool, zero_lt_one⟩

/-- `Incognita.Statements.P006.isBatched_iff_exists_infoModel_top`: two arms, the grid `𝖣_2` and a
learner batched on it that uses the rewards (`firstRewardAlg true false`), so that both sides of
the equivalence can hold. -/
lemma isBatched_iff_exists_infoModel_top_satisfiable :
    ∃ (alg : Algorithm Unit Bool ℝ) (g : Grid (Fintype.card Bool)),
      2 ≤ Fintype.card Bool ∧ IsBatched alg g ∧ ¬ SeesRewardsUpTo alg (g.t 1) 0 :=
  ⟨_, Grid.doublyExp 2 max_two_card_bool_le, two_le_card_bool,
    isBatched_firstRewardAlg true false _, not_seesRewardsUpTo_zero_firstRewardAlg (by decide) _⟩

/-! ### `thm:main`(ii) -/

/-- `𝖲_2` is finer than `𝖣_2`. -/
lemma sequential_two_isFiner_doublyExp_two :
    (Grid.sequential (K := Fintype.card Bool) 2 max_two_card_bool_le).IsFiner
      (Grid.doublyExp 2 max_two_card_bool_le) :=
  Grid.sequential_isFiner (by rw [Grid.doublyExp_t le_rfl]; norm_num)

/-- `Incognita.Statements.P006.isBatched_of_isFiner`: two arms, `g = 𝖲_2` finer than `g' = 𝖣_2`,
and `firstRewardAlg true false 𝖣_2`, batched on `𝖣_2` and using the rewards. -/
lemma isBatched_of_isFiner_satisfiable :
    ∃ (g g' : Grid (Fintype.card Bool)) (alg : Algorithm Unit Bool ℝ),
      2 ≤ Fintype.card Bool ∧ g.IsFiner g' ∧ IsBatched alg g' :=
  ⟨_, _, firstRewardAlg true false (Grid.doublyExp 2 max_two_card_bool_le), two_le_card_bool,
    sequential_two_isFiner_doublyExp_two, isBatched_firstRewardAlg true false _⟩

/-- `Incognita.Statements.P006.isConsistentAtBatchEnds_of_isFiner`: two arms, `g = 𝖲_2` finer
than `g' = 𝖣_2`, the class `E = 𝒫_true ⊆ 𝒫` of the instances of `𝒫` where arm `true` is optimal
(it contains the Bernoulli instance `(Ber(0.7), Ber(0.5))`, which has a suboptimal arm), and
`Const_true`, consistent at the batch ends of `𝖲_2` on `E`. -/
lemma isConsistentAtBatchEnds_of_isFiner_satisfiable :
    ∃ (g g' : Grid (Fintype.card Bool)) (E : Set (Kernel Bool ℝ)) (alg : Algorithm Unit Bool ℝ),
      2 ≤ Fintype.card Bool ∧ g.IsFiner g' ∧ E ⊆ unitBandits Bool ∧
        IsConsistentAtBatchEnds alg g E ∧
        ∃ ν ∈ E, ∃ c, 0 < gap ν c := by
  refine ⟨_, _, {ν | ν ∈ unitBandits Bool ∧ gap ν true = 0}, Algorithm.const (Measure.dirac true),
    two_le_card_bool, sequential_two_isFiner_doublyExp_two, fun ν hν ↦ hν.1,
    (isConsistentAtBatchEnds_const true _).mono fun ν hν ↦ hν.2, ?_⟩
  exact ⟨_, ⟨example_instance.1, example_instance.2.1⟩, false, example_instance.2.2⟩

/-! ### `thm:main`(iii) -/

/-- `Incognita.Statements.P006.isBatched_sequential_iff`: two arms, `s = 2`, and a learner batched
on `𝖲_2` that uses the rewards. -/
lemma isBatched_sequential_iff_satisfiable :
    ∃ (s : ℕ) (hs : max 2 (Fintype.card Bool) ≤ s) (alg : Algorithm Unit Bool ℝ),
      2 ≤ Fintype.card Bool ∧ IsBatched alg (Grid.sequential s hs) :=
  ⟨2, max_two_card_bool_le, _, two_le_card_bool, isBatched_firstRewardAlg true false _⟩

/-- `Incognita.Statements.P006.isConsistentAtBatchEnds_sequential_iff`: two arms, `s = 2` and
`E = 𝒫`, which contains an instance with a suboptimal arm. -/
lemma isConsistentAtBatchEnds_sequential_iff_satisfiable :
    ∃ (s : ℕ) (_ : max 2 (Fintype.card Bool) ≤ s) (E : Set (Kernel Bool ℝ)),
      2 ≤ Fintype.card Bool ∧ E ⊆ unitBandits Bool ∧ ∃ ν ∈ E, ∃ c, 0 < gap ν c :=
  ⟨2, max_two_card_bool_le, unitBandits Bool, two_le_card_bool, subset_rfl, _,
    example_instance.1, false, example_instance.2.2⟩

/-! ### `prop:kinf` -/

/-- `Incognita.Statements.P006.kinf_eq_top_of_one_le`: `P = δ_0` and `μ = 1`. -/
lemma kinf_eq_top_of_one_le_satisfiable :
    ∃ (P : Measure ℝ) (μ : ℝ), P ∈ unitLaws ∧ 1 ≤ μ :=
  ⟨Measure.dirac 0, 1, dirac_mem_unitLaws (by norm_num), le_rfl⟩

/-- `Incognita.Statements.P006.kinf_eq_zero_of_lt_mean`: `P = δ_1` and `μ = 0`. -/
lemma kinf_eq_zero_of_lt_mean_satisfiable :
    ∃ (P : Measure ℝ) (μ : ℝ), P ∈ unitLaws ∧ μ < ∫ x, id x ∂P :=
  ⟨Measure.dirac 1, 0, dirac_mem_unitLaws (by norm_num), by simp⟩

/-- `Incognita.Statements.P006.kinf_bounds`: `P = Ber(1/2)` and `μ = 7/10`. -/
lemma kinf_bounds_satisfiable :
    ∃ (P : Measure ℝ) (μ : ℝ), P ∈ unitLaws ∧ ∫ x, id x ∂P ≤ μ ∧ μ < 1 := by
  refine ⟨bernoulliMeasure (1 : ℝ) 0 ⟨1 / 2, by norm_num, by norm_num⟩, 7 / 10,
    bernoulliMeasure_mem_unitLaws _, ?_, by norm_num⟩
  have := integral_id_bernoulliBandit (α := Unit) (fun _ ↦ (⟨1 / 2, by norm_num, by norm_num⟩ : I))
    ()
  simp only [bernoulliBandit_apply] at this
  rw [show (fun x : ℝ ↦ id x) = id from rfl, this]
  norm_num

/-- `Incognita.Statements.P006.kinf_bernoulli`: `p = 1/2` and `μ = 7/10`. -/
lemma kinf_bernoulli_satisfiable :
    ∃ (p : I) (μ : ℝ), (p : ℝ) ≤ μ ∧ μ < 1 :=
  ⟨⟨1 / 2, by norm_num, by norm_num⟩, 7 / 10, by norm_num, by norm_num⟩

/-- `Incognita.Statements.P006.kinf_bounds_of_gap_pos`: the Bernoulli instance
`(Ber(0.7), Ber(0.5))` and its suboptimal arm `false`. -/
lemma kinf_bounds_of_gap_pos_satisfiable :
    ∃ (ν : Kernel Bool ℝ) (a : Bool), ν ∈ unitBandits Bool ∧ 0 < gap ν a :=
  ⟨_, false, example_instance.1, example_instance.2.2⟩

end Incognita.P006
