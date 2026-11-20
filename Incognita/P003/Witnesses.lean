/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.Checks
public import Incognita.TransferBandits.Relations
public import LMLExplore.Bandits.AsymptoticOptimality

/-! # Joint satisfiability of the hypotheses of the frozen statements of P003

For each frozen statement `Incognita.Statements.P003.<name>`, the lemma
`Incognita.P003.<name>_satisfiable` gives an explicit instance satisfying all its hypotheses at
once. The instances use the arms `Bool` (two arms) or `Fin 3` (three arms),
Dirac and Bernoulli laws, constant size rules, and constant learners. The hypothesis "`σ` is
consistent on `𝒫^K`" of `ofAlgorithm_isConsistent` is satisfied by LMLExplore's KL-UCB
(`Incognita.TransferBandits.Relations.isConsistentOnUnit_klucb`, from
`LMLExplore.Bandits.KLUCB.isConsistent`).
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

/-- Hypotheses of `followSource_not_isConsistent_v2` (prop:exclusion, correction SC1): the arms
`Bool`, a finite linear order with two elements and measurable singletons. -/
lemma followSource_not_isConsistent_v2_satisfiable :
    2 ≤ Fintype.card Bool ∧ Nonempty Bool ∧ MeasurableSingletonClass Bool :=
  ⟨by simp, ⟨true⟩, inferInstance⟩

@[deprecated (since := "2026-11-19")]
alias isConsistentOnUnit_of_isConsistent := LMLExplore.Bandits.IsConsistent.isConsistentOnUnit

@[deprecated (since := "2026-11-19")]
alias isConsistentOnUnit_klucb := Relations.isConsistentOnUnit_klucb

/-- Hypotheses of `ofAlgorithm_isConsistent` (prop:witness, first claim). -/
lemma ofAlgorithm_isConsistent_satisfiable :
    ∃ alg : Algorithm Unit Bool ℝ, 2 ≤ Fintype.card Bool ∧ IsConsistentOnUnit alg :=
  ⟨LMLExplore.Bandits.klucb, by simp, Relations.isConsistentOnUnit_klucb⟩

end Incognita.P003
