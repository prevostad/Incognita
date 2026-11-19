/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.Batched
public import Incognita.BatchedBandits.Instances
public import LMLExplore.Bandits.LaiRobbins

/-! # Consistency at the batch ends

A learner is consistent at the batch ends of a grid `g` on a class `E` of instances if
`E_ν[N_c(t_ℓ)] = o(t_ℓ ^ p)` for every `ν ∈ E`, every suboptimal arm `c` of `ν` and every `p > 0`
[INC-P006, Definition `def:consistent`]. The count `N_c(t)` of the paper (pulls in the rounds
`1, …, t`) is LML's `pullCount IT.action c t` (pulls in the rounds `0, …, t - 1`): no shift.
The classical (sequential) consistency [LS, Definition 16.1] is LMLExplore's
`LMLExplore.Bandits.IsConsistent`.

## Main definitions

* `Incognita.BatchedBandits.IsConsistentAtBatchEnds alg g E`.

## Main statements

* `isConsistentAtBatchEnds_const`: `Const_c` is consistent at the batch ends of every grid on the
  instances where `c` is optimal [INC-P006, Proposition `prop:witnesses`(e)].
* `not_isConsistentAtBatchEnds_const`: on every grid, `Const_c` is not consistent at the batch
  ends on a class containing an instance where `c` is suboptimal.
* `gap_mul_integral_pullCount_le_integral_regret`: `Δ_a E[N_a(T)] ≤ E[R_T]`;
  `tendsto_integral_pullCount_div_rpow_of_isConsistent`: a consistent learner has
  `E[N_a(T)] = o(T^p)` for every suboptimal arm `a` and every `p > 0`.
* `LMLExplore.Bandits.IsConsistent.isConsistentAtBatchEnds`: a (sequentially) consistent learner is
  consistent at the batch ends of every grid.
* `ae_feedback_mem_Icc`: on an instance of `𝒫`, the rewards of almost every run of every learner
  are in `[0, 1]`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Bandits Filter Real

open scoped Topology

namespace Incognita.BatchedBandits

variable {α : Type*} [MeasurableSpace α] [DecidableEq α] {K : ℕ}

/-- A learner `alg` is **consistent at the batch ends** of a grid `g` on a class `E` of instances
[INC-P006, Definition `def:consistent`]: for every Markov kernel `ν ∈ E`, every arm `c` with
`gap ν c > 0` and every `p > 0`, `E_ν[N_c(t ℓ)] / (t ℓ) ^ p → 0` as `ℓ → ∞`, where
`N_c(t) = pullCount IT.action c t` is the number of pulls of `c` in the rounds `0, …, t - 1`, under
the law `trajMeasure alg (Environment.bandit ν)` of the interaction. -/
def IsConsistentAtBatchEnds (alg : Algorithm Unit α ℝ) (g : Grid K) (E : Set (Kernel α ℝ)) :
    Prop :=
  ∀ ν ∈ E, ∀ [IsMarkovKernel ν], ∀ c, 0 < gap ν c → ∀ p : ℝ, 0 < p →
    Tendsto (fun ℓ : ℕ ↦ (∫ ω, (pullCount IT.action c (g.t ℓ) ω : ℝ)
      ∂(trajMeasure alg (Environment.bandit ν))) / (g.t ℓ : ℝ) ^ p) atTop (𝓝 0)

lemma IsConsistentAtBatchEnds.mono {alg : Algorithm Unit α ℝ} {g : Grid K}
    {E E' : Set (Kernel α ℝ)} (h : IsConsistentAtBatchEnds alg g E) (hE : E' ⊆ E) :
    IsConsistentAtBatchEnds alg g E' :=
  fun ν hν ↦ h ν (hE hν)

variable [MeasurableSingletonClass α]

omit [DecidableEq α] in
/-- Under `Const_c`, every action is `c`, almost surely. -/
lemma ae_forall_action_eq_const (c : α) (ν : Kernel α ℝ) [IsMarkovKernel ν] :
    ∀ᵐ ω ∂(trajMeasure (Algorithm.const (Measure.dirac c)) (Environment.bandit ν)),
      ∀ n, IT.action n ω = c := by
  refine ae_all_iff.mpr fun n ↦ ?_
  have hlaw := (IT.isAlgEnvSeq_trajMeasure (Algorithm.const (Measure.dirac c))
    (Environment.bandit ν)).hasLaw_action_const n
  have : ∀ᵐ x ∂((trajMeasure (Algorithm.const (Measure.dirac c)) (Environment.bandit ν)).map
      (IT.action n)), x = c := by
    rw [hlaw.map_eq]
    exact (ae_dirac_iff (measurableSet_singleton c)).mpr rfl
  exact ae_of_ae_map (IT.measurable_action n).aemeasurable this

/-- **Witness** [INC-P006, Proposition `prop:witnesses`(e)]: on every grid, `Const_c` is consistent
at the batch ends on the instances where `c` is optimal (it never pulls a suboptimal arm). -/
lemma isConsistentAtBatchEnds_const (c : α) (g : Grid K) :
    IsConsistentAtBatchEnds (Algorithm.const (Measure.dirac c)) g {ν | gap ν c = 0} := by
  intro ν hν _ c' hc' p _
  have hne : c' ≠ c := by
    rintro rfl
    exact hc'.ne' hν
  have h0 : ∀ m, ∫ ω, (pullCount IT.action c' m ω : ℝ)
      ∂(trajMeasure (Algorithm.const (Measure.dirac c)) (Environment.bandit ν)) = 0 := by
    intro m
    refine integral_eq_zero_of_ae ?_
    filter_upwards [ae_forall_action_eq_const c ν] with ω hω
    simp [pullCount, hω, Ne.symm hne]
  simp only [h0, zero_div]
  exact tendsto_const_nhds

/-- **Exclusion** [INC-P006, Proposition `prop:witnesses`(e)]: on every grid, `Const_c` is not
consistent at the batch ends on a class that contains an instance where `c` is suboptimal: there
`E[N_c(t ℓ)] = t ℓ`, which is not `o((t ℓ) ^ (1 / 2))`. -/
lemma not_isConsistentAtBatchEnds_const {E : Set (Kernel α ℝ)} {ν : Kernel α ℝ}
    [IsMarkovKernel ν] (hν : ν ∈ E) {c : α} (hc : 0 < gap ν c) (g : Grid K) :
    ¬ IsConsistentAtBatchEnds (Algorithm.const (Measure.dirac c)) g E := by
  intro h
  have hlim := h ν hν c hc (1 / 2) (by norm_num)
  have hN : ∀ m, ∫ ω, (pullCount IT.action c m ω : ℝ)
      ∂(trajMeasure (Algorithm.const (Measure.dirac c)) (Environment.bandit ν)) = m := by
    intro m
    have : (fun ω ↦ (pullCount IT.action c m ω : ℝ)) =ᵐ[trajMeasure
        (Algorithm.const (Measure.dirac c)) (Environment.bandit ν)] fun _ ↦ (m : ℝ) := by
      filter_upwards [ae_forall_action_eq_const c ν] with ω hω
      simp [pullCount, hω]
    rw [integral_congr_ae this]
    simp
  simp only [hN] at hlim
  have hge : ∀ᶠ ℓ in atTop, (1 : ℝ) ≤ (g.t ℓ : ℝ) / (g.t ℓ : ℝ) ^ (1 / 2 : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with ℓ hℓ
    have hx : (1 : ℝ) ≤ g.t ℓ := by
      exact_mod_cast (show 1 ≤ g.t ℓ by have := g.two_le_t hℓ; omega)
    have hpos : 0 < (g.t ℓ : ℝ) ^ (1 / 2 : ℝ) := rpow_pos_of_pos (by linarith) _
    rw [le_div_iff₀ hpos, one_mul]
    calc (g.t ℓ : ℝ) ^ (1 / 2 : ℝ) ≤ (g.t ℓ : ℝ) ^ (1 : ℝ) :=
          rpow_le_rpow_of_exponent_le hx (by norm_num)
      _ = g.t ℓ := rpow_one _
  exact absurd (ge_of_tendsto hlim hge) (by norm_num)

/-- The expected regret bounds each expected pull count: `Δ_a E[N_a(T)] ≤ E[R_T]`, since
`E[R_T] = ∑_c Δ_c E[N_c(T)]` (LML's `integral_regret_eq_sum_gap_mul_integral_pullCount`) is a sum
of nonnegative terms. -/
lemma gap_mul_integral_pullCount_le_integral_regret [Finite α] (alg : Algorithm Unit α ℝ)
    (ν : Kernel α ℝ) [IsMarkovKernel ν] (a : α) (T : ℕ) :
    gap ν a * ∫ ω, (pullCount IT.action a T ω : ℝ) ∂(trajMeasure alg (Environment.bandit ν)) ≤
      ∫ ω, regret ν IT.action T ω ∂(trajMeasure alg (Environment.bandit ν)) := by
  have := Fintype.ofFinite α
  rw [integral_regret_eq_sum_gap_mul_integral_pullCount (fun n ↦ IT.measurable_action n)]
  exact Finset.single_le_sum (f := fun c ↦ gap ν c * ∫ ω, (pullCount IT.action c T ω : ℝ)
      ∂(trajMeasure alg (Environment.bandit ν)))
    (fun c _ ↦ mul_nonneg gap_nonneg (integral_nonneg fun ω ↦ Nat.cast_nonneg _))
    (Finset.mem_univ a)

/-- A learner consistent on `E` [LS, Definition 16.1] (expected regret `o(T^p)` for every
`p > 0`) has `E[N_a(T)] = o(T^p)` for every arm `a` with a positive gap, on every instance of
`E`: `Δ_a E[N_a(T)] ≤ E[R_T]` (`gap_mul_integral_pullCount_le_integral_regret`). -/
lemma tendsto_integral_pullCount_div_rpow_of_isConsistent [Finite α] {alg : Algorithm Unit α ℝ}
    {E : Set (Kernel α ℝ)} (h : LMLExplore.Bandits.IsConsistent alg E) {ν : Kernel α ℝ}
    [IsMarkovKernel ν] (hν : ν ∈ E) {a : α} (ha : 0 < gap ν a) {p : ℝ} (hp : 0 < p) :
    Tendsto (fun T : ℕ ↦ (∫ ω, (pullCount IT.action a T ω : ℝ)
      ∂(trajMeasure alg (Environment.bandit ν))) / (T : ℝ) ^ p) atTop (𝓝 0) := by
  have := Fintype.ofFinite α
  have hreg := ((LMLExplore.Bandits.isConsistent_def _ _).mp h ν hν p hp).div_const (gap ν a)
  rw [zero_div] at hreg
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hreg (fun T ↦ ?_)
    (fun T ↦ ?_)
  · exact div_nonneg (integral_nonneg fun ω ↦ Nat.cast_nonneg _)
      (rpow_nonneg (Nat.cast_nonneg _) _)
  · rw [div_right_comm]
    gcongr
    rw [le_div_iff₀ ha, mul_comm]
    exact gap_mul_integral_pullCount_le_integral_regret alg ν a T

/-- **Known case**: a (sequentially) consistent learner [LS, Definition 16.1] is consistent at the
batch ends of every grid (`tendsto_integral_pullCount_div_rpow_of_isConsistent` along the batch
ends). -/
lemma _root_.LMLExplore.Bandits.IsConsistent.isConsistentAtBatchEnds [Finite α]
    {alg : Algorithm Unit α ℝ} {E : Set (Kernel α ℝ)} (h : LMLExplore.Bandits.IsConsistent alg E)
    (g : Grid K) : IsConsistentAtBatchEnds alg g E := fun _ hν _ _ hc _ hp ↦
  (tendsto_integral_pullCount_div_rpow_of_isConsistent h hν hc hp).comp g.strictMono.tendsto_atTop

omit [DecidableEq α] [MeasurableSingletonClass α] in
/-- For an instance of `𝒫` (rewards in `[0, 1]`), the rewards of almost every run of every learner
are in `[0, 1]`: the reward of round `n` has the conditional law `ν_(A_n)`. -/
lemma ae_feedback_mem_Icc {alg : Algorithm Unit α ℝ} {ν : ProbabilityTheory.Kernel α ℝ}
    [ProbabilityTheory.IsMarkovKernel ν] (hν : ν ∈ unitBandits α) :
    ∀ᵐ ω ∂(trajMeasure alg (Environment.bandit ν)), ∀ n,
      IT.feedback n ω ∈ Set.Icc (0 : ℝ) 1 := by
  rw [MeasureTheory.ae_all_iff]
  intro n
  have hlaw := ((IT.isAlgEnvSeq_trajMeasure alg (Environment.bandit ν)).hasCondDistrib_feedback
    n).hasLaw_comp
  have hmem : ∀ᵐ y ∂((Environment.bandit ν).feedback n ∘ₘ
      (trajMeasure alg (Environment.bandit ν)).map
        (fun ω ↦ ((history IT.obs IT.action IT.feedback n ω, IT.obs n ω), IT.action n ω))),
      y ∈ Set.Icc (0 : ℝ) 1 := by
    refine MeasureTheory.Measure.ae_comp_of_ae_ae measurableSet_Icc
      (MeasureTheory.ae_of_all _ fun x ↦ ?_)
    rw [feedback_bandit, ProbabilityTheory.Kernel.prodMkLeft_apply]
    exact (hν.1 x.2).2
  rw [← hlaw.map_eq] at hmem
  exact MeasureTheory.ae_of_ae_map hlaw.aemeasurable hmem

end Incognita.BatchedBandits
