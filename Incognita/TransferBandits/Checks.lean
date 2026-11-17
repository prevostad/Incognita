/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.Examples
public import Incognita.TransferBandits.PriorGame
public import LMLExplore.Bandits.Instances
public import LMLExplore.SequentialLearning.Algorithms.OfSeq

/-! # Checks of the definitions of the TransferBandits setting

Witnesses, known cases and exclusions (AGENTS.md §6.4) for the definitions of
`Incognita.TransferBandits.Setting`, `Consistency`, `Examples` and `PriorGame`
([INC-P003, sec:setting]).

## Main statements

* `isProbabilityMeasure_sourceMeasure`: `P'_{ν'}` is a probability measure.
* `isSizeRule_constSize` (witness), `isSizeRule_of_randomisation` (known case: sizes drawn from the
  randomisation alone), `not_isSizeRule_peek` (exclusion: a size that reads a value outside its
  box).
* `sourceData_constSize_zero` (witness), `sourceData_constSize` (known case),
  `sourceData_eq_of_eqOn_box` (exclusion: the source data do not see the values outside the box);
  `measurable_sourceData`.
* `isMarkovKernel_onlineKernel`, `isProbabilityMeasure_gameMeasure` (witness),
  `map_fst_gameMeasure_zero` (known case: at horizon `0` the game is the source phase).
* `const_dirac_mem_unitBandits`, `bernoulliBandit_mem_unitBandits` (witness, known case),
  `const_dirac_two_not_mem_unitBandits` (exclusion).
* `driftBound_self`, `driftBound_const_dirac_iff`, `not_driftBound_dirac_one_zero`;
  `twoSidedDriftBound_self`, `twoSidedDriftBound_const_dirac_iff`,
  `not_twoSidedDriftBound_dirac_one_zero`; `mem_meanBand_self`, `mem_meanBand_const_dirac_iff`,
  `not_mem_meanBand_dirac_one_zero` (witness, known case, exclusion of each condition).
* `TransferAlgorithm.constArm_policy`, `TransferAlgorithm.ofAlgorithm_policy`.
* `ae_onlineKernel_constArm`, `integral_onlineCount_constArm`: the learner `constArm a` pulls `a`
  at every round, so `E[N_a(T)] = T`.
* `not_isConsistent_constArm` (exclusion for `IsConsistent`: `constArm a` is in no `𝒞_L`, `L ≥ 0`),
  `not_isConsistentOnUnit_ofSeq_const` (exclusion for `IsConsistentOnUnit`: LML's algorithm that
  always pulls `a` is not consistent on `𝒫^K`).
* `PriorStrategy.constArm`, `PriorStrategy.counts_zero`, `PriorStrategy.counts_constArm`,
  `PriorStrategy.isStoppingTime_const`, `PriorStrategy.not_isStoppingTime_peek`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace Incognita.TransferBandits

variable {α : Type*} [MeasurableSpace α]

/-! ### The source space -/

instance isProbabilityMeasure_sourceMeasure (ν' : Kernel α ℝ) [IsMarkovKernel ν'] :
    IsProbabilityMeasure (sourceMeasure ν') := by
  unfold sourceMeasure
  infer_instance

/-! ### Size rules -/

omit [MeasurableSpace α] in
/-- Witness: a constant size map is a size rule. -/
lemma isSizeRule_constSize (n : α → ℕ) : IsSizeRule (constSize n : SourceSpace α → α → ℕ) where
  measurable := measurable_const
  measurableSet_eq m := by
    by_cases h : n = m
    · simp [constSize, h]
    · simp [constSize, h]

omit [MeasurableSpace α] in
/-- Known case: sizes chosen from the randomisation alone, `N' = f(U')` with `f` measurable
(sizes independent of the source values, as deterministic sizes are), form a size rule. -/
lemma isSizeRule_of_randomisation [Finite α] {f : (ℕ → unitInterval) → α → ℕ}
    (hf : Measurable f) : IsSizeRule (fun ω : SourceSpace α ↦ f ω.1) where
  measurable := hf.comp measurable_fst
  measurableSet_eq m := by
    have hm : MeasurableSet {u : ℕ → unitInterval | f u = m} := hf (measurableSet_singleton m)
    refine ⟨Prod.fst ⁻¹' {u | f u = m}, measurable_fst hm, ?_⟩
    ext ω
    simp [boxRestrict]

omit [MeasurableSpace α] in
/-- A size map that reads the first value of the stack of `a₁` and keeps none of it, when that
value is at most `1/2`. -/
noncomputable def peekSize [DecidableEq α] (a₁ : α) (ω : SourceSpace α) : α → ℕ :=
  fun a ↦ if a = a₁ ∧ (1 / 2 : ℝ) < ω.2 a₁ 0 then 1 else 0

omit [MeasurableSpace α] in
/-- Exclusion: `peekSize a₁` is not a size rule: the event `{N' = 0}` reads the first value of the
stack of `a₁`, outside the empty box. -/
lemma not_isSizeRule_peek [DecidableEq α] (a₁ : α) : ¬ IsSizeRule (peekSize a₁) := by
  intro h
  obtain ⟨t, -, ht⟩ := h.measurableSet_eq 0
  let ω₀ : SourceSpace α := (fun _ ↦ 0, fun _ _ ↦ 0)
  let ω₁ : SourceSpace α := (fun _ ↦ 0, fun _ _ ↦ 1)
  have h₀ : ω₀ ∈ {ω : SourceSpace α | peekSize a₁ ω = 0} := by
    ext a
    simp [peekSize, ω₀]
  have h₁ : ω₁ ∉ {ω : SourceSpace α | peekSize a₁ ω = 0} := by
    intro hω
    have := congrFun (Set.mem_ofPred_eq ▸ hω) a₁
    norm_num [peekSize, ω₁] at this
  have hbox : boxRestrict 0 ω₀ = boxRestrict 0 ω₁ := by
    simp only [boxRestrict, ω₀, ω₁, Prod.mk.injEq, true_and]
    funext a j
    exact j.elim0
  rw [← ht] at h₀ h₁
  exact h₁ (by simpa [Set.mem_preimage, hbox] using h₀)

/-! ### Source data and the law of the game -/

omit [MeasurableSpace α] in
/-- Witness: with no source sample, the source data are the zero sizes and no value. -/
lemma sourceData_constSize_zero (ω : SourceSpace α) :
    sourceData (constSize (0 : α → ℕ)) ω = (0, 0) := by
  simp only [sourceData, constSize, Prod.mk.injEq, true_and]
  funext a j
  simp

omit [MeasurableSpace α] in
lemma measurable_sourceData {N : SourceSpace α → α → ℕ} (hN : Measurable N) :
    Measurable (sourceData N) := by
  refine hN.prodMk (measurable_pi_iff.mpr fun a ↦ measurable_pi_iff.mpr fun j ↦ ?_)
  refine Measurable.ite ?_ ((measurable_pi_apply j).comp ((measurable_pi_apply a).comp
    measurable_snd)) measurable_const
  exact measurableSet_lt measurable_const ((measurable_pi_apply a).comp hN)

instance isProbabilityMeasure_sourceLaw (ν' : Kernel α ℝ) [IsMarkovKernel ν']
    (N : SourceSpace α → α → ℕ) : IsProbabilityMeasure (sourceLaw ν' N) := by
  unfold sourceLaw
  infer_instance

instance isMarkovKernel_stepKernel (π : TransferAlgorithm α) (ν : Kernel α ℝ) [IsMarkovKernel ν]
    (n : ℕ) : IsMarkovKernel (stepKernel π ν n) := by
  unfold stepKernel
  infer_instance

instance isMarkovKernel_onlineKernel (π : TransferAlgorithm α) (ν : Kernel α ℝ)
    [IsMarkovKernel ν] : ∀ T, IsMarkovKernel (onlineKernel π ν T)
  | 0 => by
    unfold onlineKernel
    infer_instance
  | T + 1 => by
    have := isMarkovKernel_onlineKernel π ν T
    unfold onlineKernel
    exact Kernel.IsMarkovKernel.map _ (MeasurableEquiv.measurable _)

/-- Witness: for instances that are Markov kernels, the law of the game is a probability
measure. -/
instance isProbabilityMeasure_gameMeasure (N : SourceSpace α → α → ℕ) (ν' ν : Kernel α ℝ)
    [IsMarkovKernel ν'] [IsMarkovKernel ν] (π : TransferAlgorithm α) (T : ℕ) :
    IsProbabilityMeasure (gameMeasure ν' N ν π T) := by
  unfold gameMeasure
  infer_instance

/-- Known case: at horizon `0`, the law of the game is the law of the source data (with the empty
history). -/
lemma map_fst_gameMeasure_zero {N : SourceSpace α → α → ℕ} (ν' ν : Kernel α ℝ)
    [IsMarkovKernel ν'] (π : TransferAlgorithm α) :
    (gameMeasure ν' N ν π 0).map Prod.fst = sourceLaw ν' N := by
  have : IsMarkovKernel (onlineKernel π ν 0) := by
    unfold onlineKernel
    infer_instance
  change (gameMeasure ν' N ν π 0).fst = _
  rw [gameMeasure, Measure.fst_compProd]

omit [MeasurableSpace α] in
/-- Known case: for deterministic sizes `n`, the source data are `n` and the first `n_k` values of
each stack. -/
lemma sourceData_constSize (n : α → ℕ) (ω : SourceSpace α) :
    sourceData (constSize n) ω = (n, fun a j ↦ if j < n a then ω.2 a j else 0) := rfl

omit [MeasurableSpace α] in
/-- Exclusion: the source data do not see the values outside the box of the sizes. -/
lemma sourceData_eq_of_eqOn_box (N : SourceSpace α → α → ℕ) {ω ω' : SourceSpace α}
    (hN : N ω = N ω') (hx : ∀ a, ∀ j < N ω a, ω.2 a j = ω'.2 a j) :
    sourceData N ω = sourceData N ω' := by
  simp only [sourceData, hN, Prod.mk.injEq, true_and]
  funext a j
  split_ifs with hj
  · exact hx a j (hN ▸ hj)
  · rfl

/-! ### Instances on `[0,1]` -/

/-- Witness: the constant kernel at a Dirac mass of `[0,1]` is an instance of `𝒫^K`. -/
lemma const_dirac_mem_unitBandits {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    Kernel.const α (Measure.dirac x) ∈ unitBandits α := by
  refine ⟨inferInstance, fun a ↦ ?_⟩
  rw [Kernel.const_apply]
  exact (ae_dirac_iff measurableSet_Icc).mpr hx

/-- Known case: Bernoulli bandits are instances of `𝒫^K`. -/
lemma bernoulliBandit_mem_unitBandits [Countable α] [MeasurableSingletonClass α]
    (p : α → unitInterval) : LMLExplore.Bandits.bernoulliBandit p ∈ unitBandits α :=
  ⟨inferInstance, LMLExplore.Bandits.ae_mem_Icc_bernoulliBandit p⟩

/-- Exclusion: a law with mass outside `[0,1]` is not allowed. -/
lemma const_dirac_two_not_mem_unitBandits [Nonempty α] :
    Kernel.const α (Measure.dirac (2 : ℝ)) ∉ unitBandits α := by
  rintro ⟨-, h⟩
  have := h (Classical.arbitrary α)
  rw [Kernel.const_apply] at this
  have h2 := (ae_dirac_iff (a := (2 : ℝ)) measurableSet_Icc).mp this
  norm_num at h2

/-! ### Drift conditions -/

/-- Witness: a pair with `ν' = ν` satisfies `Drift_L` for every positive `L`. -/
lemma driftBound_self {L : α → ℝ} (hL : ∀ a, 0 < L a) (ν : Kernel α ℝ) : DriftBound L ν ν :=
  fun a ↦ by simpa using hL a

/-- Witness: a pair with `ν' = ν` satisfies the two-sided strict condition for positive `L`. -/
lemma twoSidedDriftBound_self {L : α → ℝ} (hL : ∀ a, 0 < L a) (ν : Kernel α ℝ) :
    TwoSidedDriftBound L ν ν :=
  fun a ↦ by simpa using hL a

/-- Witness: a pair `(ν, ν)` of `𝒫^K` is in `𝒫_L` for every nonnegative `L`. -/
lemma mem_meanBand_self {L : α → ℝ} (hL : ∀ a, 0 ≤ L a) {ν : Kernel α ℝ}
    (hν : ν ∈ unitBandits α) : (ν, ν) ∈ meanBand L :=
  ⟨hν, hν, fun a ↦ by simpa using hL a⟩

/-- Exclusion: the pair `(δ_1, δ_0)` does not satisfy `Drift_𝟏`. -/
lemma not_driftBound_dirac_one_zero [Nonempty α] :
    ¬ DriftBound (fun _ ↦ 1) (Kernel.const α (Measure.dirac (1 : ℝ)))
      (Kernel.const α (Measure.dirac (0 : ℝ))) := by
  intro h
  have := h (Classical.arbitrary α)
  simp at this

/-- Exclusion: the pair `(δ_1, δ_0)` is not in `𝒫_L` when `L < 1`. -/
lemma not_mem_meanBand_dirac_one_zero [Nonempty α] {L : α → ℝ} (hL : ∀ a, L a < 1) :
    (Kernel.const α (Measure.dirac (1 : ℝ)), Kernel.const α (Measure.dirac (0 : ℝ))) ∉
      meanBand L := by
  rintro ⟨-, -, h⟩
  have h1 := h (Classical.arbitrary α)
  have h2 := hL (Classical.arbitrary α)
  simp only [Kernel.const_apply, integral_dirac, id_eq, sub_zero, abs_one] at h1
  linarith

/-- Exclusion: the pair `(δ_1, δ_0)` does not satisfy the two-sided strict condition with
`L = 𝟏`. -/
lemma not_twoSidedDriftBound_dirac_one_zero [Nonempty α] :
    ¬ TwoSidedDriftBound (fun _ ↦ 1) (Kernel.const α (Measure.dirac (1 : ℝ)))
      (Kernel.const α (Measure.dirac (0 : ℝ))) := by
  intro h
  have := h (Classical.arbitrary α)
  simp at this

/-- Known case: for Dirac masses, the two-sided strict condition compares the atoms. -/
lemma twoSidedDriftBound_const_dirac_iff {L : α → ℝ} {x y : ℝ} :
    TwoSidedDriftBound L (Kernel.const α (Measure.dirac x)) (Kernel.const α (Measure.dirac y)) ↔
      ∀ a, |x - y| < L a := by
  simp [TwoSidedDriftBound]

/-- Known case: for Dirac masses of `[0,1]`, membership in `𝒫_L` compares the atoms. -/
lemma mem_meanBand_const_dirac_iff {L : α → ℝ} {x y : ℝ} (hx : x ∈ Set.Icc 0 1)
    (hy : y ∈ Set.Icc 0 1) :
    (Kernel.const α (Measure.dirac x), Kernel.const α (Measure.dirac y)) ∈ meanBand L ↔
      ∀ a, |x - y| ≤ L a := by
  simp [meanBand, const_dirac_mem_unitBandits hx, const_dirac_mem_unitBandits hy]

/-- Known case: the drift conditions only depend on the means; for Dirac masses they compare the
atoms. -/
lemma driftBound_const_dirac_iff {L : α → ℝ} {x y : ℝ} :
    DriftBound L (Kernel.const α (Measure.dirac x)) (Kernel.const α (Measure.dirac y)) ↔
      ∀ a, x - y < L a := by
  simp [DriftBound]

/-! ### Learners -/

/-- Known case: the source-ignoring learner of an LML algorithm plays, at every round, the policy
of that algorithm on the online history. -/
lemma TransferAlgorithm.ofAlgorithm_policy (alg : Learning.Algorithm Unit α ℝ) (n : ℕ)
    (s : Source α) (h : Fin n → α × ℝ) :
    (TransferAlgorithm.ofAlgorithm alg).policy n (s, h) = alg.policy n (pairsHist h, ()) := rfl

/-- Witness: the learner that pulls a fixed arm. -/
lemma TransferAlgorithm.constArm_policy (a : α) (n : ℕ) (x : Source α × (Fin n → α × ℝ)) :
    (TransferAlgorithm.constArm a).policy n x = Measure.dirac a := rfl

/-! ### The consistency class -/

/-- Under the learner `constArm a`, almost every online history pulls `a` at every round. -/
lemma ae_onlineKernel_constArm [MeasurableSingletonClass α] (a : α) (ν : Kernel α ℝ) :
    ∀ (T : ℕ) (s : Source α),
      ∀ᵐ h ∂(onlineKernel (TransferAlgorithm.constArm a) ν T s), ∀ i, (h i).1 = a
  | 0, _ => ae_of_all _ fun _ i ↦ i.elim0
  | T + 1, s => by
    have hmeas : MeasurableSet {h : Fin (T + 1) → α × ℝ | ∀ i, (h i).1 = a} := by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun i ↦
        (by fun_prop : Measurable fun h : Fin (T + 1) → α × ℝ ↦ (h i).1)
          (measurableSet_singleton a)
    rw [onlineKernel, Kernel.map_apply _ (MeasurableEquiv.measurable _),
      (MeasurableEquiv.measurableEmbedding _).ae_map_iff]
    refine Kernel.ae_compProd_of_ae_ae ((MeasurableEquiv.measurable _) hmeas) ?_
    filter_upwards [ae_onlineKernel_constArm a ν T s] with h hh
    have hstep : ∀ᵐ x ∂(stepKernel (TransferAlgorithm.constArm a) ν T (s, h)), x.1 = a := by
      rw [stepKernel]
      refine Kernel.ae_compProd_of_ae_ae (measurable_fst (measurableSet_singleton a)) ?_
      change ∀ᵐ b ∂(Measure.dirac a), _
      rw [ae_dirac_eq]
      exact Filter.eventually_pure.mpr (ae_of_all _ fun _ ↦ rfl)
    filter_upwards [hstep] with x hx i
    rw [MeasurableEquiv.finSuccProd_symm_apply]
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa using hx
    · simpa using hh j

/-- Under the learner `constArm a`, the expected number of pulls of `a` over `T` rounds is `T`,
whatever the source phase. -/
lemma integral_onlineCount_constArm [MeasurableSingletonClass α] (a : α) (ν' ν : Kernel α ℝ)
    [IsMarkovKernel ν'] [IsMarkovKernel ν] (N : SourceSpace α → α → ℕ) (T : ℕ) :
    ∫ p, (onlineCount a p.2 : ℝ) ∂(gameMeasure ν' N ν (TransferAlgorithm.constArm a) T) = T := by
  have hmeas : MeasurableSet {p : Source α × (Fin T → α × ℝ) | ∀ i, (p.2 i).1 = a} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i ↦
      (by fun_prop : Measurable fun p : Source α × (Fin T → α × ℝ) ↦ (p.2 i).1)
        (measurableSet_singleton a)
  have hall : ∀ᵐ p ∂(gameMeasure ν' N ν (TransferAlgorithm.constArm a) T), ∀ i, (p.2 i).1 = a :=
    Measure.ae_compProd_of_ae_ae hmeas (ae_of_all _ fun s ↦ ae_onlineKernel_constArm a ν T s)
  have h : ∀ᵐ p ∂(gameMeasure ν' N ν (TransferAlgorithm.constArm a) T),
      (onlineCount a p.2 : ℝ) = T := by
    filter_upwards [hall] with p hp
    simp [onlineCount, hp]
  rw [integral_congr_ae h]
  simp

/-- Exclusion: the learner `constArm a`, which pulls the arm `a` at every round, is in no class
`𝒞_L` (`L ≥ 0`) as soon as there is a second arm `b`. On the pair `(ν, ν)`, with `ν a = δ_0` and
`ν k = δ_1` for `k ≠ a`, the arm `a` is suboptimal and `E[N_a(T)] = T`, so with `c = 1` the ratio
`E[N_a(T)] / T` tends to `1`, not to `0`. -/
theorem not_isConsistent_constArm [MeasurableSingletonClass α] {L : α → ℝ} (hL : ∀ k, 0 ≤ L k)
    {a b : α} (hab : a ≠ b) : ¬ IsConsistent L (TransferAlgorithm.constArm a) := by
  classical
  intro h
  let f : α → ℝ := fun k ↦ if k = a then 0 else 1
  have hf : Measurable f :=
    Measurable.ite (measurableSet_singleton a) measurable_const measurable_const
  let ν : Kernel α ℝ := Kernel.deterministic f hf
  have hν : ν ∈ unitBandits α := by
    refine ⟨inferInstance, fun k ↦ ?_⟩
    refine (ae_dirac_iff measurableSet_Icc).mpr ?_
    by_cases hk : k = a <;> simp [f, hk]
  have : IsMarkovKernel ν := hν.1
  have hsub : ∃ c, (ν a)[id] < (ν c)[id] :=
    ⟨b, by simp [ν, f, Kernel.deterministic_apply, Ne.symm hab]⟩
  have ht := h ν ν (mem_meanBand_self hL hν) (fun _ ↦ constSize 0)
    (fun _ ↦ isSizeRule_constSize 0) a hsub 1 one_pos
  simp only [integral_onlineCount_constArm, Real.rpow_one] at ht
  have h1 : Filter.Tendsto (fun T : ℕ ↦ (T : ℝ) / T) Filter.atTop (nhds 1) :=
    tendsto_const_nhds.congr' ((Filter.eventually_ne_atTop 0).mono fun T hT ↦
      (div_self (Nat.cast_ne_zero.mpr hT)).symm)
  exact one_ne_zero (tendsto_nhds_unique h1 ht)

/-- Exclusion: LML's algorithm that pulls the arm `a` at every round (`Algorithm.ofSeq`, the fixed
design of the constant sequence `a`) is not consistent on `𝒫^K` as soon as there is a second arm
`b`: on the instance `ν a = δ_0`, `ν k = δ_1` for `k ≠ a`, it pulls the suboptimal arm `a` at all
`T` rounds, so `E[N_a(T)] / T` tends to `1`, not to `0`. -/
theorem not_isConsistentOnUnit_ofSeq_const [Countable α] [MeasurableSingletonClass α]
    [DecidableEq α] {a b : α} (hab : a ≠ b) :
    ¬ IsConsistentOnUnit (Learning.Algorithm.ofSeq (fun _ ↦ a) : Learning.Algorithm Unit α ℝ) := by
  intro h
  let f : α → ℝ := fun k ↦ if k = a then 0 else 1
  have hf : Measurable f :=
    Measurable.ite (measurableSet_singleton a) measurable_const measurable_const
  let ν : Kernel α ℝ := Kernel.deterministic f hf
  have hν : ∀ k, ∀ᵐ x ∂(ν k), x ∈ Set.Icc 0 1 := fun k ↦ by
    refine (ae_dirac_iff measurableSet_Icc).mpr ?_
    by_cases hk : k = a <;> simp [f, hk]
  have hsub : ∃ c, (ν a)[id] < (ν c)[id] :=
    ⟨b, by simp [ν, f, Kernel.deterministic_apply, Ne.symm hab]⟩
  have ht := h ν hν a hsub 1 one_pos
  have hall : ∀ᵐ ω ∂(Learning.trajMeasure (Learning.Algorithm.ofSeq (fun _ ↦ a))
      (Learning.Environment.bandit ν)), ∀ n, Learning.IT.action n ω = a :=
    (Learning.IT.isAlgEnvSeq_trajMeasure _ _).action_ofSeq_ae_all_eq
  have hT : ∀ T : ℕ, ∫ ω, (Learning.pullCount Learning.IT.action a T ω : ℝ)
      ∂(Learning.trajMeasure (Learning.Algorithm.ofSeq (fun _ ↦ a))
        (Learning.Environment.bandit ν)) = T := fun T ↦ by
    rw [integral_congr_ae (g := fun _ ↦ (T : ℝ)) (by
      filter_upwards [hall] with ω hω
      simp [Learning.pullCount, hω])]
    simp
  simp only [hT, Real.rpow_one] at ht
  have h1 : Filter.Tendsto (fun T : ℕ ↦ (T : ℝ) / T) Filter.atTop (nhds 1) :=
    tendsto_const_nhds.congr' ((Filter.eventually_ne_atTop 0).mono fun T hT ↦
      (div_self (Nat.cast_ne_zero.mpr hT)).symm)
  exact one_ne_zero (tendsto_nhds_unique h1 ht)

/-! ### Prior games -/

namespace PriorStrategy

variable [DecidableEq α]

/-- Witness: the strategy that pulls the arm `a` at every round. -/
def constArm (a : α) : PriorStrategy α where
  act _ _ := a
  measurable_act _ := measurable_const

/-- Known case: a game of `0` rounds has zero counts. -/
lemma counts_zero (g : PriorStrategy α) (ω : SourceSpace α) : g.counts 0 ω = 0 := rfl

/-- Known case: the strategy that always pulls `a` has counts `T'` on `a` and `0` elsewhere. -/
lemma counts_constArm (a : α) (T' : ℕ) (ω : SourceSpace α) :
    (constArm a).counts T' ω = Function.update (0 : α → ℕ) a T' := by
  induction T' with
  | zero => simp [counts, state]
  | succ T' ih =>
    simp only [counts, state] at ih ⊢
    rw [ih]
    simp [constArm]

/-- Witness: a constant time `T'` is a stopping time of the game over `T'` rounds. -/
lemma isStoppingTime_const (g : PriorStrategy α) (T' : ℕ) :
    g.IsStoppingTime T' (fun _ ↦ T') where
  le _ := le_rfl
  measurableSet_eq r := by
    by_cases h : T' = r
    · simp [h]
    · simp [h]

/-- Exclusion: a time that reads the first value of the stack of `a₁` before any round is not a
stopping time. -/
lemma not_isStoppingTime_peek (g : PriorStrategy α) (a₁ : α) :
    ¬ g.IsStoppingTime 1 (fun ω ↦ if (1 / 2 : ℝ) < ω.2 a₁ 0 then 1 else 0) := by
  intro h
  obtain ⟨t, -, ht⟩ := h.measurableSet_eq 0
  let ω₀ : SourceSpace α := (fun _ ↦ 0, fun _ _ ↦ 0)
  let ω₁ : SourceSpace α := (fun _ ↦ 0, fun _ _ ↦ 1)
  have h₀ : ω₀ ∈ {ω : SourceSpace α | (if (1 / 2 : ℝ) < ω.2 a₁ 0 then 1 else 0) = 0} := by
    simp [ω₀]
  have h₁ : ω₁ ∉ {ω : SourceSpace α | (if (1 / 2 : ℝ) < ω.2 a₁ 0 then 1 else 0) = 0} := by
    norm_num [ω₁]
  have hst : (ω₀.1, (g.state ω₀ 0).2) = (ω₁.1, (g.state ω₁ 0).2) := by
    simp only [state, ω₀, ω₁]
  rw [← ht] at h₀ h₁
  exact h₁ (by simpa [Set.mem_preimage, hst] using h₀)

end PriorStrategy

end Incognita.TransferBandits
