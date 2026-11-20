/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.Consistency
public import LMLExplore.Bandits.IndexAlgorithm
public import LMLExplore.Bandits.LaiRobbins
public import LeanMachineLearning.Online.Bandit.Algorithms.UCB
public import LeanMachineLearning.SequentialLearning.SumRewards

/-! # Uniform fast and super-fast convergence, and UCB with a Hoeffding bonus

The classes of learners of [INC-P007, Definition `def:ufc`] ([GMS19, Definitions 1 and 6]) and
the learner `UCB` of [INC-P007, Definition `def:ucb`], with the conventions of the roadmap
StochasticBandits: a learner is an LML `Algorithm Unit α ℝ`, its run on `ν` is
`trajMeasure alg (Environment.bandit ν)`, rounds are numbered from `0`, and `N_a(T)` is LML's
`pullCount IT.action a T` (pulls of `a` in the rounds `0, …, T - 1`).

## Main definitions

* `IsUniformlyFastConvergent alg E`: for every Markov `ν ∈ E`, every suboptimal arm `a` and every
  `p ∈ (0, 1]`, `E[N_a(T)] / T^p → 0`.
* `IsUniformlySuperFastConvergent alg E C`: for every Markov `ν ∈ E`, every suboptimal arm `a`
  and every `T ≥ 2`, `E[N_a(T)] ≤ C log T / Δ_a²`.
* `hoeffdingIndex n h a`: the index `μ̂_a + √(2 log (n + 1) / N_a)` at round `n` after the history
  `h`, and `⊤` if `a` has not been pulled.
* `IsHoeffdingUCB alg`: at every round and after every history, the policy of `alg` is concentrated
  on the arms of maximal `hoeffdingIndex` (the learner `UCB` with some tie rule).
* `hoeffdingUCB`: LMLExplore's index policy with `hoeffdingIndex` (ties broken by LML's `argmax`).

## Main statements (the checks of AGENTS.md §6.4)

* `isUniformlySuperFastConvergent_const`, `isUniformlyFastConvergent_const` (witnesses: the
  learner that always pulls `c`, on the instances where `c` is optimal);
  `IsUniformlySuperFastConvergent.isUniformlyFastConvergent` (known case: the inclusion of the
  classes of [GMS19, Section 2]); `not_isUniformlyFastConvergent_const`,
  `not_isUniformlySuperFastConvergent_const` (exclusions: the learner that always pulls `b`, on a
  class with an instance where `b` is suboptimal).
* `isHoeffdingUCB_hoeffdingUCB` (witness); `hoeffdingIndex_eq_empMean'_add_ucbWidth'` and
  `hoeffdingIndex_le_hoeffdingIndex_nextArm` (known cases: on `Fin K`, the index of an arm already
  pulled is LML's UCB1 index `empMean' + ucbWidth' 1`, and after `K` rounds in which every arm has
  been pulled the arm of LML's `ucbAlgorithm K 1` maximises it); `hoeffdingIndex_eq_top_iff` (an
  arm never pulled has index `+∞`, so that every arm is pulled once before any is pulled twice);
  `not_isHoeffdingUCB_const` (exclusion: the learner that always pulls `b` is not `UCB`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Learning Bandits

open scoped Topology

namespace Incognita.StochasticBandits

variable {α : Type*} [DecidableEq α] [MeasurableSpace α]

/-! ### Uniform fast and super-fast convergence -/

/-- A learner is **uniformly fast convergent** on a class `E` [INC-P007, Definition `def:ufc`;
GMS19, Definition 1] if, for every Markov kernel `ν ∈ E`, every suboptimal arm `a` of `ν` and every
`p ∈ (0, 1]`, `E[N_a(T)] / T^p → 0` as `T → ∞`. -/
def IsUniformlyFastConvergent (alg : Algorithm Unit α ℝ) (E : Set (Kernel α ℝ)) : Prop :=
  ∀ ν ∈ E, ∀ [IsMarkovKernel ν], ∀ a, 0 < gap ν a → ∀ p : ℝ, 0 < p → p ≤ 1 →
    Tendsto (fun T : ℕ ↦ (∫ ω, (pullCount IT.action a T ω : ℝ)
      ∂(trajMeasure alg (Environment.bandit ν))) / (T : ℝ) ^ p) atTop (𝓝 0)

/-- A learner is **uniformly super-fast convergent** on a class `E` with the constant `C`
[INC-P007, Definition `def:ufc`; GMS19, Definition 6] if, for every Markov kernel `ν ∈ E`, every
suboptimal arm `a` of `ν` and every horizon `T ≥ 2`, `E[N_a(T)] ≤ C log T / Δ_a²`. -/
def IsUniformlySuperFastConvergent (alg : Algorithm Unit α ℝ) (E : Set (Kernel α ℝ)) (C : ℝ) :
    Prop :=
  ∀ ν ∈ E, ∀ [IsMarkovKernel ν], ∀ a, 0 < gap ν a → ∀ T : ℕ, 2 ≤ T →
    ∫ ω, (pullCount IT.action a T ω : ℝ) ∂(trajMeasure alg (Environment.bandit ν)) ≤
      C * Real.log T / gap ν a ^ 2

section Const

variable [MeasurableSingletonClass α]

lemma integral_pullCount_const_of_ne {c a : α} (hac : a ≠ c) (ν : Kernel α ℝ) [IsMarkovKernel ν]
    (T : ℕ) :
    ∫ ω, (pullCount IT.action a T ω : ℝ)
      ∂(trajMeasure (Algorithm.const (Measure.dirac c)) (Environment.bandit ν)) = 0 := by
  refine integral_eq_zero_of_ae ?_
  filter_upwards [BatchedBandits.ae_forall_action_eq_const c ν] with ω hω
  simp [pullCount, hω, Ne.symm hac]

lemma integral_pullCount_const_self (c : α) (ν : Kernel α ℝ) [IsMarkovKernel ν] (T : ℕ) :
    ∫ ω, (pullCount IT.action c T ω : ℝ)
      ∂(trajMeasure (Algorithm.const (Measure.dirac c)) (Environment.bandit ν)) = T := by
  have : ∀ᵐ ω ∂(trajMeasure (Algorithm.const (Measure.dirac c)) (Environment.bandit ν)),
      (pullCount IT.action c T ω : ℝ) = T := by
    filter_upwards [BatchedBandits.ae_forall_action_eq_const c ν] with ω hω
    simp [pullCount, hω]
  rw [integral_congr_ae this]
  simp

/-- **Witness**: the learner that always pulls `c` is uniformly super-fast convergent, with every
constant `C ≥ 0`, on the instances where `c` is optimal. -/
lemma isUniformlySuperFastConvergent_const (c : α) {C : ℝ} (hC : 0 ≤ C) :
    IsUniformlySuperFastConvergent (Algorithm.const (Measure.dirac c)) {ν | gap ν c = 0} C := by
  intro ν hν _ a ha T hT
  have hac : a ≠ c := by rintro rfl; exact ha.ne' hν
  rw [integral_pullCount_const_of_ne hac]
  have : 0 ≤ Real.log T := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ T))
  positivity

/-- **Witness**: the learner that always pulls `c` is uniformly fast convergent on the instances
where `c` is optimal. -/
lemma isUniformlyFastConvergent_const (c : α) :
    IsUniformlyFastConvergent (Algorithm.const (Measure.dirac c)) {ν | gap ν c = 0} := by
  intro ν hν _ a ha p _ _
  have hac : a ≠ c := by rintro rfl; exact ha.ne' hν
  simp_rw [integral_pullCount_const_of_ne hac, zero_div]
  exact tendsto_const_nhds

/-- **Exclusion**: on a class that contains an instance where `b` is suboptimal, the learner that
always pulls `b` is not uniformly fast convergent (its count of `b` is `T`). -/
lemma not_isUniformlyFastConvergent_const {E : Set (Kernel α ℝ)} {ν : Kernel α ℝ}
    [IsMarkovKernel ν] (hν : ν ∈ E) {b : α} (hb : 0 < gap ν b) :
    ¬ IsUniformlyFastConvergent (Algorithm.const (Measure.dirac b)) E := by
  intro h
  have hlim := h ν hν b hb 1 one_pos le_rfl
  simp_rw [integral_pullCount_const_self, Real.rpow_one] at hlim
  have h1 : Tendsto (fun T : ℕ ↦ (T : ℝ) / T) atTop (𝓝 1) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop 1] with T hT
      rw [div_self (by exact_mod_cast (by omega : T ≠ 0))])
  exact one_ne_zero (tendsto_nhds_unique h1 hlim)

omit [DecidableEq α] in
/-- **Exclusion** for consistency [INC-P007, Lemma `lem:constant`]: on a class that contains an
instance where `b` is suboptimal, the learner that always pulls `b` is not consistent (its expected
regret is `T Δ_b`, which is not `o(T)`). -/
lemma not_isConsistent_const [Finite α] {E : Set (Kernel α ℝ)} {ν : Kernel α ℝ}
    [IsMarkovKernel ν] (hν : ν ∈ E) {b : α} (hb : 0 < gap ν b) :
    ¬ LMLExplore.Bandits.IsConsistent (Algorithm.const (Measure.dirac b)) E := by
  classical
  intro h
  have hlim := (LMLExplore.Bandits.isConsistent_def _ _).mp h ν hν 1 one_pos
  simp_rw [Real.rpow_one] at hlim
  have hge : ∀ᶠ T : ℕ in atTop, gap ν b ≤ (∫ ω, regret ν IT.action T ω
      ∂(trajMeasure (Algorithm.const (Measure.dirac b)) (Environment.bandit ν))) / T := by
    filter_upwards [eventually_ge_atTop 1] with T hT
    rw [le_div_iff₀ (by exact_mod_cast hT)]
    have := BatchedBandits.gap_mul_integral_pullCount_le_integral_regret
      (Algorithm.const (Measure.dirac b)) ν b T
    rwa [integral_pullCount_const_self] at this
  exact absurd (ge_of_tendsto hlim hge) (not_le.mpr hb)

end Const

/-- **Known case**: a uniformly super-fast convergent learner is uniformly fast convergent, the
inclusion of the classes of [GMS19, Section 2]. -/
lemma IsUniformlySuperFastConvergent.isUniformlyFastConvergent
    {alg : Algorithm Unit α ℝ} {E : Set (Kernel α ℝ)} {C : ℝ}
    (h : IsUniformlySuperFastConvergent alg E C) : IsUniformlyFastConvergent alg E := by
  intro ν hν _ a ha p hp _
  have hlog : Tendsto (fun T : ℕ ↦ Real.log T / (T : ℝ) ^ p) atTop (𝓝 0) :=
    ((isLittleO_log_rpow_atTop hp).tendsto_div_nhds_zero).comp
      tendsto_natCast_atTop_atTop
  have hup : Tendsto (fun T : ℕ ↦ C / gap ν a ^ 2 * (Real.log T / (T : ℝ) ^ p)) atTop (𝓝 0) := by
    simpa using hlog.const_mul (C / gap ν a ^ 2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards with T
    exact div_nonneg (integral_nonneg fun _ ↦ by positivity) (by positivity)
  · filter_upwards [eventually_ge_atTop 2] with T hT
    have hTp : 0 < (T : ℝ) ^ p := Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < T)) p
    calc (∫ ω, (pullCount IT.action a T ω : ℝ) ∂(trajMeasure alg (Environment.bandit ν))) /
          (T : ℝ) ^ p ≤ C * Real.log T / gap ν a ^ 2 / (T : ℝ) ^ p :=
          div_le_div_of_nonneg_right (h ν hν a ha T hT) hTp.le
      _ = C / gap ν a ^ 2 * (Real.log T / (T : ℝ) ^ p) := by ring

/-- **Exclusion**: on a class that contains an instance where `b` is suboptimal, the learner that
always pulls `b` is not uniformly super-fast convergent, with any constant. -/
lemma not_isUniformlySuperFastConvergent_const [MeasurableSingletonClass α]
    {E : Set (Kernel α ℝ)} {ν : Kernel α ℝ} [IsMarkovKernel ν] (hν : ν ∈ E) {b : α}
    (hb : 0 < gap ν b) (C : ℝ) :
    ¬ IsUniformlySuperFastConvergent (Algorithm.const (Measure.dirac b)) E C :=
  fun h ↦ not_isUniformlyFastConvergent_const hν hb h.isUniformlyFastConvergent

/-! ### UCB with a Hoeffding bonus -/

/-- The **index of `UCB`** [INC-P007, (`eq:ucb`)] at the round `n`, after the history `h` of the
rounds `0, …, n - 1`: `⊤` if the arm `a` has not been pulled, and otherwise
`μ̂_a + √(2 log (n + 1) / N_a)`, where `N_a = pullCount' n h a` is the number of pulls of `a` and
`μ̂_a = empMean' n h a` its empirical mean. -/
noncomputable def hoeffdingIndex (n : ℕ) (h : Hist Unit α ℝ n) (a : α) : EReal :=
  if pullCount' n h a = 0 then ⊤ else
    ((empMean' n h a + √(2 * Real.log (n + 1) / pullCount' n h a) : ℝ) : EReal)

omit [MeasurableSpace α] in
/-- An arm has the index `+∞` if and only if it has not been pulled. -/
lemma hoeffdingIndex_eq_top_iff {n : ℕ} {h : Hist Unit α ℝ n} {a : α} :
    hoeffdingIndex n h a = ⊤ ↔ pullCount' n h a = 0 := by
  by_cases h0 : pullCount' n h a = 0
  · simp [hoeffdingIndex, h0]
  · simp [hoeffdingIndex, h0]

/-- **Known case**: on the arms `Fin K`, the index of an arm already pulled is the index of LML's
UCB1 with the exploration parameter `c = 1` [ACF02, Theorem 1]: its empirical mean plus
`UCB.ucbWidth' 1 n h a = √(2 log (n + 1) / N_a)`. -/
lemma hoeffdingIndex_eq_empMean'_add_ucbWidth' {K n : ℕ} {h : Hist Unit (Fin K) ℝ n} {a : Fin K}
    (ha : pullCount' n h a ≠ 0) :
    hoeffdingIndex n h a = ((empMean' n h a + UCB.ucbWidth' 1 n h a : ℝ) : EReal) := by
  simp [hoeffdingIndex, ha, UCB.ucbWidth']

/-- **Known case**: on the arms `Fin K`, at a round `n ≥ K`, after a history in which every arm has
been pulled, the arm chosen by LML's UCB1 with `c = 1` (`ucbAlgorithm K 1`) has the maximal
`hoeffdingIndex`, so it is an arm that `UCB` may pull under some tie rule. -/
lemma hoeffdingIndex_le_hoeffdingIndex_nextArm {K n : ℕ} [NeZero K] (hn : K ≤ n)
    {h : Hist Unit (Fin K) ℝ n} (hpull : ∀ a, pullCount' n h a ≠ 0) (b : Fin K) :
    hoeffdingIndex n h b ≤ hoeffdingIndex n h (UCB.nextArm K 1 n h) := by
  rw [hoeffdingIndex_eq_empMean'_add_ucbWidth' (hpull b),
    hoeffdingIndex_eq_empMean'_add_ucbWidth' (hpull _), EReal.coe_le_coe_iff, UCB.nextArm]
  simp only [not_lt.mpr hn, ↓reduceIte]
  exact isMaxOn_iff.mp (isMaxOn_argmax fun a ↦ empMean' n h a + UCB.ucbWidth' 1 n h a) b
    (Set.mem_univ b)

lemma measurable_hoeffdingIndex [MeasurableSingletonClass α] (n : ℕ) :
    Measurable (hoeffdingIndex (α := α) n) := by
  refine Measurable.of_eval fun a ↦ ?_
  simp_rw [hoeffdingIndex]
  refine Measurable.ite ?_ measurable_const (by fun_prop)
  exact (measurableSet_singleton 0).preimage (measurable_pullCount' n a)

/-- The learner **`UCB` with a Hoeffding bonus and some tie rule** [INC-P007, Definition
`def:ucb`]: at every round `n`, after every history `h`, its policy gives mass `1` to the set of
the arms of maximal index `hoeffdingIndex n h`. The tie rule is the policy itself.

As in `def:ucb`, the condition is imposed after every history, including histories that the learner
cannot produce. So LML's `ucbAlgorithm K 1`, which pulls the arms in turn in the rounds `n < K`
whatever the history, is not an `IsHoeffdingUCB` learner (for `K ≥ 2`). After `K` rounds in which
every arm has been pulled, it pulls an arm of maximal index
(`hoeffdingIndex_le_hoeffdingIndex_nextArm`). -/
def IsHoeffdingUCB (alg : Algorithm Unit α ℝ) : Prop :=
  ∀ (n : ℕ) (x : Hist Unit α ℝ n × Unit),
    alg.policy n x {a | ∀ b, hoeffdingIndex n x.1 b ≤ hoeffdingIndex n x.1 a} = 1

/-- `UCB` with a Hoeffding bonus and the tie rule of LML's `argmax`: LMLExplore's index policy with
the index `hoeffdingIndex`. -/
noncomputable def hoeffdingUCB [Fintype α] [Nonempty α] [MeasurableSingletonClass α] :
    Algorithm Unit α ℝ :=
  LMLExplore.Bandits.indexAlgorithm (fun n x ↦ hoeffdingIndex n x.1)
    fun n ↦ (measurable_hoeffdingIndex n).comp measurable_fst

/-- **Witness**: `hoeffdingUCB` is `UCB` with a Hoeffding bonus. -/
lemma isHoeffdingUCB_hoeffdingUCB [Fintype α] [Nonempty α] [MeasurableSingletonClass α] :
    IsHoeffdingUCB (hoeffdingUCB (α := α)) := by
  intro n x
  rw [hoeffdingUCB, LMLExplore.Bandits.indexAlgorithm_policy, Kernel.deterministic_apply]
  refine Measure.dirac_apply_of_mem fun b ↦ ?_
  exact isMaxOn_iff.mp (isMaxOn_argmax _) b (Set.mem_univ b)

/-- **Exclusion**: with at least two arms, the learner that always pulls `b` is not `UCB`: after
one pull of `b`, another arm has the index `+∞`, larger than that of `b`. -/
lemma not_isHoeffdingUCB_const [Nontrivial α] [MeasurableSingletonClass α] (b : α) :
    ¬ IsHoeffdingUCB (Algorithm.const (Measure.dirac b) : Algorithm Unit α ℝ) := by
  intro h
  obtain ⟨c, hcb⟩ := exists_ne b
  let hist : Hist Unit α ℝ 1 := fun _ ↦ ((), b, 0)
  have hb1 : pullCount' 1 hist b = 1 := by simp [pullCount', hist]
  have hc0 : pullCount' 1 hist c = 0 := by simp [pullCount', hist, Ne.symm hcb]
  have hnot : b ∉ {a | ∀ b', hoeffdingIndex 1 hist b' ≤ hoeffdingIndex 1 hist a} := by
    intro hmem
    have hle := hmem c
    rw [hoeffdingIndex_eq_top_iff.mpr hc0, top_le_iff, hoeffdingIndex_eq_top_iff, hb1] at hle
    exact one_ne_zero hle
  have := h 1 (hist, ())
  simp only [Algorithm.const, Kernel.const_apply] at this
  rw [Measure.dirac_apply, Set.indicator_of_notMem hnot] at this
  exact zero_ne_one this

end Incognita.StochasticBandits
