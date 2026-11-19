/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.P006.Witnesses
public import LMLExplore.Bandits.AsymptoticOptimality

/-! # Joint satisfiability of the hypotheses of the frozen statements of P000

For each frozen statement `Incognita.Statements.P000.<name>`, the lemma
`Incognita.P000.<name>_satisfiable` exhibits an explicit instance that satisfies all its
hypotheses at once. The arms are `Bool` (two arms, `K = 2`); the instance is the Bernoulli instance
`(Ber(0.7), Ber(0.5))` of `Incognita.P006.example_instance` (arm `false` is sub-optimal); the grid
is the sequential grid `𝖲_2`, whose ratios tend to `x = 1`.

The lower bounds assume a batched learner consistent on `𝒫`. The witness is LMLExplore's KL-UCB
`klucb`, consistent on the bandits with rewards in `[0, 1]` (`KLUCB.isConsistent`), hence at the
batch ends of every grid; on `𝖲_2` it is batched (`klucb_isBatched_sequential_two`): its first
batch is the rounds `0` and `1`, and at the round `1` the only arm of index `⊤` is the arm not
pulled at the round `0`, so KL-UCB ignores the reward of the round `0` there.

No witness is given with a limit `x > 1`: it would need a batched learner consistent on `𝒫` on a
grid with `x > 1`, which is what Theorem `thm:upper` provides (HY). Theorem `thm:lower`(ii) is
contained in the statements of Theorem `thm:main`(a), which hold for every `x ≥ 1`
(`lower_limsup`, `lower_liminf`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Bandits LMLExplore.Bandits

open scoped unitInterval

namespace Incognita.P000

open Incognita.BatchedBandits Incognita.P006

/-- The sequential grid `𝖲_2` for two arms. -/
noncomputable abbrev seqTwo : Grid (Fintype.card Bool) := Grid.sequential 2 max_two_card_bool_le

/-- The ratios of `𝖲_2` tend to `1`. -/
lemma tendsto_ratio_seqTwo : Filter.Tendsto seqTwo.ratio Filter.atTop (nhds 1) :=
  Grid.tendsto_ratio_sequential _

/-- The Bernoulli family generating KL-UCB has finite upper confidence levels, so the KL-UCB index
of an arm is `⊤` exactly when the arm has not been pulled. -/
lemma klucbIndex_eq_top_iff {n : ℕ} (h : Hist Unit Bool ℝ n) (a : Bool) :
    klucbFamIndex (fun _ ↦ Ber((1 : ℝ), 0, unitInterval.sigmoid 0)) n h a = ⊤ ↔
      pullCount' n h a = 0 :=
  klucbFamIndex_eq_top_iff fun _ _ _ _ ↦ Measure.expFamilyUpper_ne_top_of_bddAbove
    (by rw [LMLExplore.expFamilyMeans_bernoulliMeasure_sigmoid]; exact bddAbove_Ioo)

lemma pullCount'_one_eq_zero_iff (h : Hist Unit Bool ℝ 1) (a : Bool) :
    pullCount' 1 h a = 0 ↔ (h 0).action ≠ a := by
  simp [pullCount', Finset.filter_eq_empty_iff]

/-- At the round `1`, KL-UCB pulls the arm not pulled at the round `0`. -/
lemma klucb_argmax_one (h : Hist Unit Bool ℝ 1) :
    argmax (fun a ↦ klucbFamIndex (fun _ ↦ Ber((1 : ℝ), 0, unitInterval.sigmoid 0)) 1 h a) =
      !(h 0).action := by
  set f := fun a ↦ klucbFamIndex (fun _ ↦ Ber((1 : ℝ), 0, unitInterval.sigmoid 0)) 1 h a
  have htop : f (!(h 0).action) = ⊤ :=
    (klucbIndex_eq_top_iff h _).mpr
      ((pullCount'_one_eq_zero_iff h _).mpr (by cases (h 0).action <;> simp))
  have hmax : f (argmax f) = ⊤ := by
    rw [argmax_spec f]
    exact top_le_iff.mp (htop ▸ Function.le_max f _)
  have hne := (pullCount'_one_eq_zero_iff h _).mp ((klucbIndex_eq_top_iff h _).mp hmax)
  revert hne
  cases (h 0).action <;> cases argmax f <;> simp

/-- KL-UCB ignores the rewards at the round `1`. -/
lemma klucb_seesRewardsUpTo_one :
    SeesRewardsUpTo (klucb : Algorithm Unit Bool ℝ) 1 0 := by
  intro h h' ha _
  simp only [klucb_def, klucbFam_def, indexAlgorithm_policy, Kernel.deterministic_apply]
  rw [klucb_argmax_one h, klucb_argmax_one h', ha 0]

/-- KL-UCB ignores the rewards at the round `0` (there is no history). -/
lemma klucb_seesRewardsUpTo_zero :
    SeesRewardsUpTo (klucb : Algorithm Unit Bool ℝ) 0 0 := by
  intro h h' _ _
  rw [show h = h' from funext fun i ↦ Fin.elim0 i]

/-- **KL-UCB is batched on `𝖲_2`** (two arms): in the first batch (the rounds `0` and `1`) it
ignores the rewards, and afterwards every round is a batch on its own. -/
lemma klucb_isBatched_sequential_two : IsBatched (klucb : Algorithm Unit Bool ℝ) seqTwo := by
  intro n
  rcases Nat.lt_or_ge n 2 with hn | hn
  · rw [Grid.sequential_batchOf_of_lt hn, show 1 - 1 = 0 from rfl, seqTwo, Grid.t_zero]
    interval_cases n
    · exact klucb_seesRewardsUpTo_zero
    · exact klucb_seesRewardsUpTo_one
  · rw [Grid.sequential_batchOf hn, Grid.sequential_t (by omega),
      show 2 + (n - 2 + 2 - 1) - 1 = n by omega]
    exact seesRewardsUpTo_self _ n

/-- KL-UCB is consistent at the batch ends of every grid on `𝒫`. -/
lemma klucb_isConsistentAtBatchEnds {K : ℕ} (g : Grid K) :
    IsConsistentAtBatchEnds (klucb : Algorithm Unit Bool ℝ) g (unitBandits Bool) :=
  (KLUCB.isConsistent.mono fun _ hν a ↦ (hν.1 a).2).isConsistentAtBatchEnds g

/-- The example Bernoulli instance `(Ber(0.7), Ber(0.5))`. -/
noncomputable abbrev exampleBandit : Kernel Bool ℝ :=
  bernoulliBandit (fun b : Bool ↦ if b then (⟨7 / 10, by norm_num, by norm_num⟩ : I)
    else ⟨1 / 2, by norm_num, by norm_num⟩)

/-! ### The lower bounds -/

/-- The hypotheses shared by the lower bounds: two arms, the grid `𝖲_2` with limit `x = 1`,
KL-UCB (batched on `𝖲_2` and consistent on `𝒫`), the Bernoulli instance `(Ber(0.7), Ber(0.5))` in
`𝒫` and its sub-optimal arm `false`. -/
lemma lower_hypotheses :
    2 ≤ Fintype.card Bool ∧ (1 : ℝ) ≤ 1 ∧ Filter.Tendsto seqTwo.ratio Filter.atTop (nhds 1) ∧
      IsBatched (klucb : Algorithm Unit Bool ℝ) seqTwo ∧
      IsConsistentAtBatchEnds (klucb : Algorithm Unit Bool ℝ) seqTwo (unitBandits Bool) ∧
      exampleBandit ∈ unitBandits Bool ∧ 0 < gap exampleBandit false :=
  ⟨two_le_card_bool, le_rfl, tendsto_ratio_seqTwo, klucb_isBatched_sequential_two,
    klucb_isConsistentAtBatchEnds _, example_instance.1, example_instance.2.2⟩

/-- `Incognita.Statements.P000.one_batch_ahead`: the grid `𝖲_2`, KL-UCB, the example instance and
its sub-optimal arm. -/
lemma one_batch_ahead_satisfiable :
    ∃ (g : Grid (Fintype.card Bool)) (alg : Algorithm Unit Bool ℝ) (ν : Kernel Bool ℝ)
      (_ : IsMarkovKernel ν) (a : Bool), 2 ≤ Fintype.card Bool ∧ IsBatched alg g ∧
      IsConsistentAtBatchEnds alg g (unitBandits Bool) ∧ ν ∈ unitBandits Bool ∧ 0 < gap ν a :=
  ⟨seqTwo, klucb, exampleBandit, inferInstance, false, two_le_card_bool,
    klucb_isBatched_sequential_two, klucb_isConsistentAtBatchEnds _, example_instance.1,
    example_instance.2.2⟩

/-- `Incognita.Statements.P000.lower_liminf_of_tendsto_ratio_one`: the grid `𝖲_2` (ratios
`→ 1`), KL-UCB, the example instance and its sub-optimal arm. -/
lemma lower_liminf_of_tendsto_ratio_one_satisfiable :
    ∃ (g : Grid (Fintype.card Bool)) (alg : Algorithm Unit Bool ℝ) (ν : Kernel Bool ℝ)
      (_ : IsMarkovKernel ν) (a : Bool), 2 ≤ Fintype.card Bool ∧
      Filter.Tendsto g.ratio Filter.atTop (nhds 1) ∧ IsBatched alg g ∧
      IsConsistentAtBatchEnds alg g (unitBandits Bool) ∧ ν ∈ unitBandits Bool ∧ 0 < gap ν a :=
  ⟨seqTwo, klucb, exampleBandit, inferInstance, false, two_le_card_bool,
    tendsto_ratio_seqTwo, klucb_isBatched_sequential_two, klucb_isConsistentAtBatchEnds _,
    example_instance.1, example_instance.2.2⟩

/-- `Incognita.Statements.P000.lower_limsup`: `x = 1`, the grid `𝖲_2`, KL-UCB, the example instance
and its sub-optimal arm. -/
lemma lower_limsup_satisfiable :
    ∃ (g : Grid (Fintype.card Bool)) (x : ℝ) (alg : Algorithm Unit Bool ℝ) (ν : Kernel Bool ℝ)
      (_ : IsMarkovKernel ν) (a : Bool), 2 ≤ Fintype.card Bool ∧ 1 ≤ x ∧
      Filter.Tendsto g.ratio Filter.atTop (nhds x) ∧ IsBatched alg g ∧
      IsConsistentAtBatchEnds alg g (unitBandits Bool) ∧ ν ∈ unitBandits Bool ∧ 0 < gap ν a :=
  ⟨seqTwo, 1, klucb, exampleBandit, inferInstance, false, lower_hypotheses⟩

/-- `Incognita.Statements.P000.lower_liminf`: as for `lower_limsup`, with `x = 1` for the
alternative `x = 1 ∨ E[N_a(t_ℓ)] = O(log t_ℓ)`. -/
lemma lower_liminf_satisfiable :
    ∃ (g : Grid (Fintype.card Bool)) (x : ℝ) (alg : Algorithm Unit Bool ℝ) (ν : Kernel Bool ℝ)
      (_ : IsMarkovKernel ν) (a : Bool), 2 ≤ Fintype.card Bool ∧ 1 ≤ x ∧
      Filter.Tendsto g.ratio Filter.atTop (nhds x) ∧ IsBatched alg g ∧
      IsConsistentAtBatchEnds alg g (unitBandits Bool) ∧ ν ∈ unitBandits Bool ∧
      0 < gap ν a ∧ (x = 1 ∨ Asymptotics.IsBigO Filter.atTop
        (fun ℓ ↦ ∫ ω, (pullCount IT.action a (g.t ℓ) ω : ℝ)
          ∂(trajMeasure alg (Environment.bandit ν)))
        (fun ℓ ↦ Real.log (g.t ℓ))) :=
  ⟨seqTwo, 1, klucb, exampleBandit, inferInstance, false, two_le_card_bool,
    le_rfl, tendsto_ratio_seqTwo, klucb_isBatched_sequential_two,
    klucb_isConsistentAtBatchEnds _, example_instance.1, example_instance.2.2,
    Or.inl rfl⟩

/-- `Incognita.Statements.P000.lower_regret_liminf`: `x = 1` (for the alternative of `hlog`), the
grid `𝖲_2`, KL-UCB and the example instance. -/
lemma lower_regret_liminf_satisfiable :
    ∃ (g : Grid (Fintype.card Bool)) (x : ℝ) (alg : Algorithm Unit Bool ℝ) (ν : Kernel Bool ℝ)
      (_ : IsMarkovKernel ν), 2 ≤ Fintype.card Bool ∧ 1 ≤ x ∧
      Filter.Tendsto g.ratio Filter.atTop (nhds x) ∧ IsBatched alg g ∧
      IsConsistentAtBatchEnds alg g (unitBandits Bool) ∧ ν ∈ unitBandits Bool ∧
      (x = 1 ∨ ∀ c, 0 < gap ν c → Asymptotics.IsBigO Filter.atTop
        (fun ℓ ↦ ∫ ω, (pullCount IT.action c (g.t ℓ) ω : ℝ)
          ∂(trajMeasure alg (Environment.bandit ν)))
        (fun ℓ ↦ Real.log (g.t ℓ))) :=
  ⟨seqTwo, 1, klucb, exampleBandit, inferInstance, two_le_card_bool, le_rfl,
    tendsto_ratio_seqTwo, klucb_isBatched_sequential_two, klucb_isConsistentAtBatchEnds _,
    example_instance.1, Or.inl rfl⟩

/-- `Incognita.Statements.P000.lower_regret_limsup`: `x = 1`, the grid `𝖲_2`, KL-UCB and the
example instance (which has a sub-optimal arm, so the constant `C_1` is a non-empty sum). -/
lemma lower_regret_limsup_satisfiable :
    ∃ (g : Grid (Fintype.card Bool)) (x : ℝ) (alg : Algorithm Unit Bool ℝ) (ν : Kernel Bool ℝ)
      (_ : IsMarkovKernel ν), 2 ≤ Fintype.card Bool ∧ 1 ≤ x ∧
      Filter.Tendsto g.ratio Filter.atTop (nhds x) ∧ IsBatched alg g ∧
      IsConsistentAtBatchEnds alg g (unitBandits Bool) ∧ ν ∈ unitBandits Bool ∧
      ∃ a, 0 < gap ν a :=
  ⟨seqTwo, 1, klucb, exampleBandit, inferInstance, two_le_card_bool, le_rfl,
    tendsto_ratio_seqTwo, klucb_isBatched_sequential_two, klucb_isConsistentAtBatchEnds _,
    example_instance.1, false, example_instance.2.2⟩

/-! ### HY -/

/-- `Incognita.Statements.P000.hy_infoModel_zero`: two arms and the default parameters `w₀ = 1`,
`β = 2`. -/
lemma hy_infoModel_zero_satisfiable :
    ∃ w₀ β : ℝ, 2 ≤ Fintype.card Bool ∧ Nonempty Bool ∧ 0 ≤ w₀ ∧ 2 ≤ β :=
  ⟨1, 2, two_le_card_bool, inferInstance, zero_le_one, le_rfl⟩

/-- `Incognita.Statements.P000.hy_isConsistent`: the grid `𝖲_2` with `x = 1` and the default
parameters `w₀ = 1`, `β = 2`. -/
lemma hy_isConsistent_satisfiable :
    ∃ (g : Grid (Fintype.card Bool)) (x w₀ β : ℝ), 2 ≤ Fintype.card Bool ∧ Nonempty Bool ∧
      1 ≤ x ∧ Filter.Tendsto g.ratio Filter.atTop (nhds x) ∧ 0 ≤ w₀ ∧ 2 ≤ β :=
  ⟨seqTwo, 1, 1, 2, two_le_card_bool, inferInstance, le_rfl, tendsto_ratio_seqTwo, zero_le_one,
    le_rfl⟩

/-- `Incognita.Statements.P000.hy_tendsto_count`: the grid `𝖲_2` with `x = 1`, the default
parameters, the example instance and its sub-optimal arm. -/
lemma hy_tendsto_count_satisfiable :
    ∃ (g : Grid (Fintype.card Bool)) (x w₀ β : ℝ) (ν : Kernel Bool ℝ) (_ : IsMarkovKernel ν)
      (a : Bool), 2 ≤ Fintype.card Bool ∧ Nonempty Bool ∧ 1 ≤ x ∧
      Filter.Tendsto g.ratio Filter.atTop (nhds x) ∧ 0 ≤ w₀ ∧ 2 ≤ β ∧ ν ∈ unitBandits Bool ∧
      0 < gap ν a :=
  ⟨seqTwo, 1, 1, 2, exampleBandit, inferInstance, false, two_le_card_bool, inferInstance, le_rfl,
    tendsto_ratio_seqTwo, zero_le_one, le_rfl, example_instance.1, example_instance.2.2⟩

/-- `Incognita.Statements.P000.hy_tendsto_regret`: the grid `𝖲_2` with `x = 1`, the default
parameters and the example instance (which has a sub-optimal arm). -/
lemma hy_tendsto_regret_satisfiable :
    ∃ (g : Grid (Fintype.card Bool)) (x w₀ β : ℝ) (ν : Kernel Bool ℝ) (_ : IsMarkovKernel ν),
      2 ≤ Fintype.card Bool ∧ Nonempty Bool ∧ 1 ≤ x ∧
      Filter.Tendsto g.ratio Filter.atTop (nhds x) ∧ 0 ≤ w₀ ∧ 2 ≤ β ∧ ν ∈ unitBandits Bool ∧
      ∃ a, 0 < gap ν a :=
  ⟨seqTwo, 1, 1, 2, exampleBandit, inferInstance, two_le_card_bool, inferInstance, le_rfl,
    tendsto_ratio_seqTwo, zero_le_one, le_rfl, example_instance.1, false, example_instance.2.2⟩

end Incognita.P000
