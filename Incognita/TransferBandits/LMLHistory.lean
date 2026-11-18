/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.Checks

/-! # The online law of a source-ignoring learner as an LML history

[INC-P003, lem:lml-history and lem:mixture], for the source-ignoring learner `π^σ` of an LML
bandit algorithm `σ`: whatever the source data `s`, the kernel `κ^T_{π^σ,ν}(s)` of the game is the
law of the first `T` (action, reward) pairs of any LML algorithm-environment sequence of `σ`
against the bandit `ν`, in particular of LML's `trajMeasure σ (Environment.bandit ν)`.

## Main statements

* `onlineKernel_ofAlgorithm_apply`: `κ^T_{π^σ,ν}(s)` is the law of `histPairs (history O A Y T)`
  for every algorithm-environment sequence `(O, A, Y)` of `σ` and `Environment.bandit ν`.
* `onlineKernel_ofAlgorithm`: the kernel is constant, equal to the law of the first `T` pairs
  under `trajMeasure σ (Environment.bandit ν)`.
* `integral_onlineCount_gameMeasure_ofAlgorithm`: under the law of the game, the expected number
  of pulls of an arm by `π^σ` is LML's expected `pullCount` of that arm by `σ`, whatever the source
  law and the size map.

LML's rewards are real; the paper's lem:lml-history extends kernels on `[0,1]`-valued histories to
real histories by clamping. In the Lean setting both the transfer learners and LML's algorithms
are already kernels on real histories (blueprint.md, decision 7), so no clamping is needed here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning

namespace Incognita.TransferBandits

variable {α : Type*} [MeasurableSpace α]

omit [MeasurableSpace α] in
/-- Forgetting the trivial observations of an LML history and putting them back is the
identity. -/
lemma pairsHist_histPairs {n : ℕ} (h : Hist Unit α ℝ n) : pairsHist (histPairs h) = h := rfl

/-- Forgetting the observations of an LML history is measurable. -/
@[fun_prop]
lemma measurable_histPairs (n : ℕ) : Measurable (histPairs (α := α) (n := n)) := by
  unfold histPairs
  fun_prop

/-- The (action, reward) part of LML's step kernel of `σ` against the bandit `ν`, at the LML
history `h`, is the step kernel `π^σ_n ⊗ ν` of the source-ignoring learner at `(s, histPairs h)`,
for every source data `s`. -/
lemma map_snd_stepKernel_bandit (alg : Algorithm Unit α ℝ) (ν : Kernel α ℝ) [IsMarkovKernel ν]
    (n : ℕ) (s : Source α) (h : Hist Unit α ℝ n) :
    (Learning.stepKernel alg (Environment.bandit ν) n h).map Prod.snd =
      stepKernel (TransferAlgorithm.ofAlgorithm alg) ν n (s, histPairs h) := by
  ext S hS
  rw [Measure.map_apply measurable_snd hS, stepKernel_bandit,
    Kernel.compProd_apply (measurable_snd hS), stepKernel, Kernel.compProd_apply hS]
  simp only [Kernel.const_apply, lintegral_dirac]
  rw [Kernel.compProd_apply (by exact hS)]
  rfl

/-- The joint law of an LML history and of the next (action, reward) pair, read as pairs, is the
law of the pairs composed with the step kernel of the source-ignoring learner (with the source
data `s` fixed). -/
lemma map_compProd_stepKernel_bandit (alg : Algorithm Unit α ℝ) (ν : Kernel α ℝ)
    [IsMarkovKernel ν] (n : ℕ) (s : Source α) (μ : Measure (Hist Unit α ℝ n)) [SFinite μ] :
    (μ ⊗ₘ Learning.stepKernel alg (Environment.bandit ν) n).map (Prod.map histPairs Prod.snd) =
      μ.map histPairs ⊗ₘ Kernel.sectR (stepKernel (TransferAlgorithm.ofAlgorithm alg) ν n) s := by
  have hF : Measurable
      (Prod.map (histPairs (α := α) (n := n)) (Prod.snd : Round Unit α ℝ → α × ℝ)) :=
    (measurable_histPairs n).prodMap measurable_snd
  ext S hS
  rw [Measure.map_apply hF hS, Measure.compProd_apply (hF hS), Measure.compProd_apply hS,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hS) (measurable_histPairs n)]
  refine lintegral_congr fun h ↦ ?_
  rw [Kernel.sectR_apply, ← map_snd_stepKernel_bandit alg ν n s h,
    Measure.map_apply measurable_snd (measurable_prodMk_left hS)]
  rfl

/-- **The online law as an LML history** [INC-P003, lem:lml-history], for the source-ignoring
learner `π^σ` of an LML algorithm `σ`: for every algorithm-environment sequence `(O, A, Y)` of `σ`
against the bandit `ν` and every source data `s`, `κ^T_{π^σ,ν}(s)` is the law of the first `T`
(action, reward) pairs. -/
lemma onlineKernel_ofAlgorithm_apply {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {Y : ℕ → Ω → ℝ}
    {alg : Algorithm Unit α ℝ} {ν : Kernel α ℝ} [IsMarkovKernel ν]
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) (T : ℕ) (s : Source α) :
    onlineKernel (TransferAlgorithm.ofAlgorithm alg) ν T s =
      P.map (fun ω ↦ histPairs (history O A Y T ω)) := by
  induction T with
  | zero =>
    rw [onlineKernel, Kernel.deterministic_apply]
    have : (fun ω ↦ histPairs (history O A Y 0 ω)) = fun _ ↦ (Fin.elim0 : Fin 0 → α × ℝ) :=
      funext fun _ ↦ Subsingleton.elim _ _
    rw [this, Measure.map_const, measure_univ, one_smul]
  | succ T ih =>
    have hH := h.measurable_history T
    have hS := h.measurable_step T
    have hsucc : (fun ω ↦ histPairs (history O A Y (T + 1) ω)) =
        (MeasurableEquiv.finSuccProd (α × ℝ) T).symm ∘
          (Prod.map histPairs Prod.snd ∘ fun ω ↦ (history O A Y T ω, step O A Y T ω)) := by
      funext ω i
      simp only [Function.comp_apply, Prod.map_apply, MeasurableEquiv.finSuccProd_symm_apply]
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simp [histPairs, history, step]
      · simp [histPairs, history]
    rw [hsucc, ← Measure.map_map (MeasurableEquiv.measurable _)
        (((measurable_histPairs T).prodMap measurable_snd).comp (hH.prodMk hS)),
      ← Measure.map_map ((measurable_histPairs T).prodMap measurable_snd) (hH.prodMk hS),
      (h.hasCondDistrib_step T).map_eq, map_compProd_stepKernel_bandit alg ν T s,
      onlineKernel, Kernel.map_apply _ (MeasurableEquiv.measurable _),
      Kernel.compProd_apply_eq_compProd_sectR, ih,
      Measure.map_map (measurable_histPairs T) hH]
    rfl

/-- The kernel `κ^T_{π^σ,ν}` of the source-ignoring learner is constant: the law of the first `T`
(action, reward) pairs under LML's `trajMeasure σ (Environment.bandit ν)`. -/
lemma onlineKernel_ofAlgorithm (alg : Algorithm Unit α ℝ) (ν : Kernel α ℝ) [IsMarkovKernel ν]
    (T : ℕ) :
    onlineKernel (TransferAlgorithm.ofAlgorithm alg) ν T =
      Kernel.const (Source α) ((trajMeasure alg (Environment.bandit ν)).map
        (fun ω ↦ histPairs (IT.hist T ω))) := by
  ext s : 1
  rw [Kernel.const_apply]
  exact onlineKernel_ofAlgorithm_apply (IT.isAlgEnvSeq_trajMeasure _ _) T s

omit [MeasurableSpace α] in
/-- `N_a(T)` as a sum of indicators. -/
lemma onlineCount_eq_sum [DecidableEq α] {T : ℕ} (a : α) (h : Fin T → α × ℝ) :
    onlineCount a h = ∑ i, if (h i).1 = a then 1 else 0 := by
  rw [onlineCount, Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  by_cases hi : (h i).1 = a <;> simp [hi]

/-- `N_a(T)` is a measurable function of the online history. -/
@[fun_prop]
lemma measurable_onlineCount [MeasurableSingletonClass α] {T : ℕ} (a : α) :
    Measurable (onlineCount (T := T) a) := by
  classical
  have : onlineCount (T := T) a = fun h ↦ ∑ i, if (h i).1 = a then 1 else 0 :=
    funext (onlineCount_eq_sum a)
  rw [this]
  refine Finset.measurable_sum _ fun i _ ↦ Measurable.ite ?_ measurable_const measurable_const
  exact (by fun_prop : Measurable fun h : Fin T → α × ℝ ↦ (h i).1) (measurableSet_singleton a)

omit [MeasurableSpace α] in
/-- The number of pulls of `a` in the first `T` pairs of an LML trajectory is LML's
`pullCount`. -/
lemma onlineCount_histPairs_hist [DecidableEq α] (a : α) (T : ℕ) (ω : ℕ → Round Unit α ℝ) :
    onlineCount a (histPairs (IT.hist T ω)) = pullCount IT.action a T ω := by
  rw [onlineCount_eq_sum, pullCount, Finset.card_filter, Finset.sum_range]
  rfl

/-- **Mixture over the source** [INC-P003, lem:mixture], for a source-ignoring learner: under the
law of the game, the expected number of pulls of the arm `a` by `π^σ` is the expected number of
pulls of `a` by `σ` under LML's law of the trajectory, whatever the source law and the size map. -/
lemma integral_onlineCount_gameMeasure_ofAlgorithm [DecidableEq α] [MeasurableSingletonClass α]
    (alg : Algorithm Unit α ℝ) (ν' ν : Kernel α ℝ) [IsMarkovKernel ν'] [IsMarkovKernel ν]
    (N : SourceSpace α → α → ℕ) (T : ℕ) (a : α) :
    ∫ p, (onlineCount a p.2 : ℝ) ∂(gameMeasure ν' N ν (TransferAlgorithm.ofAlgorithm alg) T) =
      ∫ ω, (pullCount IT.action a T ω : ℝ) ∂(trajMeasure alg (Environment.bandit ν)) := by
  set Q := (trajMeasure alg (Environment.bandit ν)).map (fun ω ↦ histPairs (IT.hist T ω))
  have hQ : Measurable fun ω : ℕ → Round Unit α ℝ ↦ histPairs (IT.hist T ω) :=
    (measurable_histPairs T).comp (IT.measurable_hist T)
  have hc : Measurable fun h : Fin T → α × ℝ ↦ (onlineCount a h : ℝ) :=
    measurable_from_top.comp (measurable_onlineCount a)
  rw [gameMeasure, onlineKernel_ofAlgorithm, Measure.compProd_const,
    ← integral_map measurable_snd.aemeasurable (hc.aestronglyMeasurable), Measure.map_snd_prod,
    measure_univ, one_smul, integral_map hQ.aemeasurable hc.aestronglyMeasurable]
  simp_rw [onlineCount_histPairs_hist]

end Incognita.TransferBandits
