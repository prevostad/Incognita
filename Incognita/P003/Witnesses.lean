/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.Checks
public import LMLExplore.Bandits.AsymptoticOptimality

/-! # Joint satisfiability of the hypotheses of the frozen statements of P003

For each frozen statement `Incognita.Statements.P003.<name>`, the lemma
`Incognita.P003.<name>_satisfiable` gives an explicit instance satisfying all its hypotheses at
once (AGENTS.md §6.4). The instances use the arms `Bool` (two arms) or `Fin 3` (three arms),
Dirac and Bernoulli laws, constant size rules, and constant learners. The hypothesis "`σ` is
consistent on `𝒫^K`" of `ofAlgorithm_isConsistent` is satisfied by LMLExplore's KL-UCB
(`isConsistentOnUnit_klucb`, proved here from `LMLExplore.Bandits.KLUCB.isConsistent`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Filter Incognita.TransferBandits

open scoped ENNReal Topology unitInterval

namespace Incognita.P003

/-- The instance `δ_0` on every arm. -/
noncomputable abbrev diracZero (α : Type*) [MeasurableSpace α] : Kernel α ℝ :=
  Kernel.const α (Measure.dirac 0)

lemma diracZero_mem (α : Type*) [MeasurableSpace α] : diracZero α ∈ unitBandits α :=
  const_dirac_mem_unitBandits ⟨le_rfl, zero_le_one⟩

lemma lintegral_constSize_lt_top {α : Type*} [MeasurableSpace α] (n : α → ℕ) (ν' : Kernel α ℝ)
    [IsMarkovKernel ν'] (a : α) :
    ∫⁻ ω, ((constSize n : SourceSpace α → α → ℕ) ω a : ℝ≥0∞) ∂(sourceMeasure ν') < ∞ := by
  simp [constSize, lintegral_const]

/-- Hypotheses of `divergence_decomposition` (thm:main (a)). -/
lemma divergence_decomposition_satisfiable :
    ∃ (N : SourceSpace Bool → Bool → ℕ) (_π : TransferAlgorithm Bool) (ν ν' ν₂ ν₂' : Kernel Bool ℝ),
      2 ≤ Fintype.card Bool ∧ IsSizeRule N ∧ ν ∈ unitBandits Bool ∧ ν' ∈ unitBandits Bool ∧
        ν₂ ∈ unitBandits Bool ∧ ν₂' ∈ unitBandits Bool ∧
        ∀ a, ∫⁻ ω, (N ω a : ℝ≥0∞) ∂(sourceMeasure ν') < ∞ :=
  ⟨constSize fun _ ↦ 1, TransferAlgorithm.constArm true, diracZero Bool, diracZero Bool,
    diracZero Bool, diracZero Bool, by simp, isSizeRule_constSize _, diracZero_mem _,
    diracZero_mem _, diracZero_mem _, diracZero_mem _,
    fun a ↦ lintegral_constSize_lt_top _ _ a⟩

/-- Hypotheses of `fundamental_inequality` (cor:fundamental). -/
lemma fundamental_inequality_satisfiable :
    ∃ (N : SourceSpace Bool → Bool → ℕ) (_π : TransferAlgorithm Bool) (T : ℕ)
      (ν ν' ν₂ ν₂' : Kernel Bool ℝ) (Z : Source Bool × (Fin T → Bool × ℝ) → ℝ),
      2 ≤ Fintype.card Bool ∧ IsSizeRule N ∧ ν ∈ unitBandits Bool ∧ ν' ∈ unitBandits Bool ∧
        ν₂ ∈ unitBandits Bool ∧ ν₂' ∈ unitBandits Bool ∧
        (∀ a, ∫⁻ ω, (N ω a : ℝ≥0∞) ∂(sourceMeasure ν') < ∞) ∧
        Measurable Z ∧ ∀ x, Z x ∈ Set.Icc 0 1 :=
  ⟨constSize fun _ ↦ 1, TransferAlgorithm.constArm true, 1, diracZero Bool, diracZero Bool,
    diracZero Bool, diracZero Bool, fun _ ↦ 0, by simp, isSizeRule_constSize _, diracZero_mem _,
    diracZero_mem _, diracZero_mem _, diracZero_mem _, fun a ↦ lintegral_constSize_lt_top _ _ a,
    measurable_const, fun _ ↦ ⟨le_rfl, zero_le_one⟩⟩

/-- The point `1/4` of `[0,1]`. -/
noncomputable def quarter : I := ⟨1 / 4, by norm_num, by norm_num⟩

/-- The point `1/2` of `[0,1]`. -/
noncomputable def half : I := ⟨1 / 2, by norm_num, by norm_num⟩

/-- Hypotheses of `lookahead_divergence` (thm:main (b)). -/
lemma lookahead_divergence_satisfiable :
    ∃ (a₁ : Bool) (p q : I) (_π : TransferAlgorithm Bool) (_T : ℕ) (ν ν' ν₂' : Kernel Bool ℝ),
      2 ≤ Fintype.card Bool ∧ (p : ℝ) ∈ Set.Ioo 0 1 ∧ (q : ℝ) ∈ Set.Ioo 0 1 ∧ p ≠ q ∧
        ν ∈ unitBandits Bool ∧ ν' ∈ unitBandits Bool ∧ ν' a₁ = Ber((1 : ℝ), 0, p) ∧
        ν₂' a₁ = Ber((1 : ℝ), 0, q) ∧ ∀ a, a ≠ a₁ → ν₂' a = ν' a := by
  refine ⟨true, quarter, half, TransferAlgorithm.constArm true, 1, diracZero Bool,
    LMLExplore.Bandits.bernoulliBandit fun _ ↦ quarter,
    LMLExplore.Bandits.bernoulliBandit fun a ↦ if a = true then half else quarter, by simp,
    ?_, ?_, ?_, diracZero_mem _, bernoulliBandit_mem_unitBandits _, by simp, by simp, ?_⟩
  · simp only [quarter, Set.mem_Ioo]
    norm_num
  · simp only [half, Set.mem_Ioo]
    norm_num
  · intro h
    have := congrArg Subtype.val h
    simp only [quarter, half] at this
    norm_num at this
  · intro a ha
    simp [ha]

/-- Hypotheses of `lookahead_not_isSizeRule` (lem:lookahead). -/
lemma lookahead_not_isSizeRule_satisfiable : ∃ _a₁ : Bool, 2 ≤ Fintype.card Bool :=
  ⟨true, by simp⟩

/-- Hypotheses of `constSize_isSizeRule` (lem:prior-game (a)). -/
lemma constSize_isSizeRule_satisfiable : ∃ _n : Bool → ℕ, 2 ≤ Fintype.card Bool :=
  ⟨fun _ ↦ 1, by simp⟩

/-- Hypotheses of `priorCounts_isSizeRule` (lem:prior-game (b)). -/
lemma priorCounts_isSizeRule_satisfiable :
    ∃ (_g : PriorStrategy Bool) (_T' : ℕ), 2 ≤ Fintype.card Bool :=
  ⟨PriorStrategy.constArm true, 3, by simp⟩

/-- Hypotheses of `stoppedCounts_isSizeRule` (prop:stopped-games (a)). -/
lemma stoppedCounts_isSizeRule_satisfiable :
    ∃ (g : PriorStrategy Bool) (T' : ℕ) (τ : SourceSpace Bool → ℕ),
      2 ≤ Fintype.card Bool ∧ g.IsStoppingTime T' τ :=
  ⟨PriorStrategy.constArm true, 3, fun _ ↦ 3, by simp,
    PriorStrategy.isStoppingTime_const _ _⟩

/-- Hypotheses of `two_arms_sizeRule_eq_stoppedCounts` (prop:stopped-games (b)). -/
lemma two_arms_sizeRule_eq_stoppedCounts_satisfiable :
    ∃ N : SourceSpace Bool → Bool → ℕ, Fintype.card Bool = 2 ∧ IsSizeRule N ∧
      ∃ M : ℕ, ∀ ω, ∑ a, N ω a ≤ M :=
  ⟨constSize fun _ ↦ 1, by simp, isSizeRule_constSize _, 2, fun _ ↦ by simp [constSize]⟩

/-- Hypotheses of `cyclicSize_not_stoppedCounts` (prop:stopped-games (c)). -/
lemma cyclicSize_not_stoppedCounts_satisfiable :
    ∃ a₁ a₂ a₃ : Fin 3, 3 ≤ Fintype.card (Fin 3) ∧ a₁ ≠ a₂ ∧ a₂ ≠ a₃ ∧ a₁ ≠ a₃ :=
  ⟨0, 1, 2, by simp, by decide, by decide, by decide⟩

/-- Hypotheses of `learner_exclusion` (lem:learner-exclusion). -/
lemma learner_exclusion_satisfiable : ∃ a₁ a₂ : Bool, 2 ≤ Fintype.card Bool ∧ a₁ ≠ a₂ :=
  ⟨true, false, by simp, by decide⟩

/-- Hypotheses of `drift_of_twoSided` (prop:drift (a)). -/
lemma drift_of_twoSided_satisfiable :
    ∃ (L : Bool → ℝ) (ν ν' : Kernel Bool ℝ), 2 ≤ Fintype.card Bool ∧ (∀ a, 0 < L a) ∧
      ν ∈ unitBandits Bool ∧ ν' ∈ unitBandits Bool ∧ TwoSidedDriftBound L ν ν' :=
  ⟨fun _ ↦ 1, diracZero Bool, diracZero Bool, by simp, fun _ ↦ one_pos, diracZero_mem _,
    diracZero_mem _, twoSidedDriftBound_self (fun _ ↦ one_pos) _⟩

/-- Hypotheses of `drift_of_mem_meanBand` (prop:drift (b)). -/
lemma drift_of_mem_meanBand_satisfiable :
    ∃ (L L' : Bool → ℝ) (ν ν' : Kernel Bool ℝ), 2 ≤ Fintype.card Bool ∧ (∀ a, 0 < L a) ∧
      (∀ a, L a < L' a) ∧ (ν, ν') ∈ meanBand L :=
  ⟨fun _ ↦ 1, fun _ ↦ 2, diracZero Bool, diracZero Bool, by simp, fun _ ↦ one_pos,
    fun _ ↦ one_lt_two, mem_meanBand_self (fun _ ↦ zero_le_one) (diracZero_mem _)⟩

/-- Hypotheses of `drift_meanBand_inclusions` (prop:drift (c)). -/
lemma drift_meanBand_inclusions_satisfiable :
    ∃ L : Bool → ℝ, 2 ≤ Fintype.card Bool ∧ ∀ a, 0 < L a :=
  ⟨fun _ ↦ 1, by simp, fun _ ↦ one_pos⟩

/-- Hypotheses of `drift_all_pairs` (prop:drift (d)). -/
lemma drift_all_pairs_satisfiable : ∃ L : Bool → ℝ, 2 ≤ Fintype.card Bool ∧ ∀ a, 0 < L a :=
  ⟨fun _ ↦ 1, by simp, fun _ ↦ one_pos⟩

/-- Hypotheses of `drift_witness_exclusion` (prop:drift (e)). -/
lemma drift_witness_exclusion_satisfiable :
    ∃ L : Bool → ℝ, 2 ≤ Fintype.card Bool ∧ ∀ a, 0 < L a :=
  ⟨fun _ ↦ 1, by simp, fun _ ↦ one_pos⟩

/-- Hypotheses of `isConsistent_anti` (prop:classes (a)). -/
lemma isConsistent_anti_satisfiable :
    ∃ L L' : Bool → ℝ, 2 ≤ Fintype.card Bool ∧ (∀ a, 0 < L a) ∧ (∀ a, 0 < L' a) ∧
      ∀ a, L a ≤ L' a :=
  ⟨fun _ ↦ 1, fun _ ↦ 2, by simp, fun _ ↦ one_pos, fun _ ↦ two_pos, fun _ ↦ one_le_two⟩

/-- Hypotheses of `isConsistent_one` (prop:classes (b)). -/
lemma isConsistent_one_satisfiable : ∃ _π : TransferAlgorithm Bool, 2 ≤ Fintype.card Bool :=
  ⟨TransferAlgorithm.constArm true, by simp⟩

/-- Hypotheses of `exists_isConsistent` (prop:witness, last claim). -/
lemma exists_isConsistent_satisfiable : ∃ L : Bool → ℝ, 2 ≤ Fintype.card Bool ∧ ∀ a, 0 < L a :=
  ⟨fun _ ↦ 1, by simp, fun _ ↦ one_pos⟩

/-- Hypotheses of `ucb_isConsistentOnUnit` (prop:witness, second claim). -/
lemma ucb_isConsistentOnUnit_satisfiable : ∃ (K : ℕ) (c : ℝ), NeZero K ∧ 2 ≤ K ∧ 1 / 2 < c :=
  ⟨2, 1, inferInstance, le_rfl, by norm_num⟩

/-- Hypotheses of `followSource_not_isConsistent` (prop:exclusion). -/
lemma followSource_not_isConsistent_satisfiable :
    2 ≤ Fintype.card Bool ∧ Nonempty Bool :=
  ⟨by simp, ⟨true⟩⟩

/-- Pull-count consistency on `𝒫^K` follows from LMLExplore's regret-based consistency over the
bandits with rewards in `[0, 1]`: `Δ_a E[N_a(T)] ≤ E[R_T]`. -/
lemma isConsistentOnUnit_of_isConsistent {α : Type*} [Finite α] [DecidableEq α]
    [MeasurableSpace α] [MeasurableSingletonClass α] {alg : Algorithm Unit α ℝ}
    (h : LMLExplore.Bandits.IsConsistent alg {ν : Kernel α ℝ | ∀ a, ∀ᵐ x ∂(ν a), x ∈ Set.Icc 0 1}) :
    IsConsistentOnUnit alg := by
  have := Fintype.ofFinite α
  intro ν _ hν a ⟨b, hab⟩ c hc
  have hreg := (LMLExplore.Bandits.isConsistent_def alg _).mp h ν hν c hc
  set P := trajMeasure alg (Environment.bandit ν)
  have hgap : 0 < Bandits.gap ν a := by
    have : (ν b)[id] ≤ ⨆ i, (ν i)[id] :=
      le_ciSup (f := fun i ↦ (ν i)[id]) (Set.finite_range _).bddAbove b
    rw [Bandits.gap]
    linarith
  have hA : ∀ n, Measurable (IT.action (𝓞 := Unit) (𝓐 := α) (𝓨 := ℝ) n) := IT.measurable_action
  have hle : ∀ T : ℕ, (∫ ω, (pullCount IT.action a T ω : ℝ) ∂P) ≤
      (∫ ω, Bandits.regret ν IT.action T ω ∂P) / Bandits.gap ν a := by
    intro T
    rw [le_div_iff₀ hgap, Bandits.integral_regret_eq_sum_gap_mul_integral_pullCount hA, mul_comm]
    exact Finset.single_le_sum
      (f := fun i ↦ Bandits.gap ν i * ∫ ω, (pullCount IT.action i T ω : ℝ) ∂P)
      (fun i _ ↦ mul_nonneg Bandits.gap_nonneg (integral_nonneg fun _ ↦ by positivity))
      (Finset.mem_univ a)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hreg.div_const (Bandits.gap ν a)) (fun T ↦ ?_) (fun T ↦ ?_)
  · exact div_nonneg (integral_nonneg fun _ ↦ by positivity) (by positivity)
  · simp only
    rw [div_right_comm]
    exact div_le_div_of_nonneg_right (hle T) (by positivity)

/-- LMLExplore's KL-UCB is consistent on `𝒫^K` in the sense of pull counts. -/
lemma isConsistentOnUnit_klucb {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]
    [MeasurableSpace α] [StandardBorelSpace α] [MeasurableSingletonClass α] :
    IsConsistentOnUnit (LMLExplore.Bandits.klucb (α := α)) :=
  isConsistentOnUnit_of_isConsistent LMLExplore.Bandits.KLUCB.isConsistent

/-- Hypotheses of `ofAlgorithm_isConsistent` (prop:witness, first claim). -/
lemma ofAlgorithm_isConsistent_satisfiable :
    ∃ alg : Algorithm Unit Bool ℝ, 2 ≤ Fintype.card Bool ∧ IsConsistentOnUnit alg :=
  ⟨LMLExplore.Bandits.klucb, by simp, isConsistentOnUnit_klucb⟩

end Incognita.P003
