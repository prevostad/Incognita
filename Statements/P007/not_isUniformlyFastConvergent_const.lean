/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.StochasticBandits.UCB
public import LeanMachineLearning.SequentialLearning.Algorithms.RandomSampling.Basic

/-! # P007, `lem:constant` (fast convergence): always pulling `b` is not uniformly fast convergent

One frozen statement of the paper P007 (`papers/P007-stochastic-setting`); its docstring gives the
statement in words and every difference of form with the paper. -/

@[expose] public section

/-- [INC-P007, Lemma `lem:constant`, its consequence on `Cons^b`, "nor uniformly fast
convergent"] On every class `E` that contains an instance `ν` in which the arm `b` is suboptimal,
the learner `Cons^b` that always pulls `b` is not uniformly fast convergent on `E`.

Differences of form with the paper:
* This is one part of the "Consequently" sentence of the lemma; the other parts are the frozen
  statements `Incognita.Statements.P007.not_isConsistent_const` (consistency) and
  `Incognita.Statements.P007.not_isUniformlySuperFastConvergent_const`, or are not frozen (see
  the docstring of `not_isConsistent_const`).
* The arms are a type `α` with `[Finite α] [Nontrivial α]` (`K = |α| ≥ 2`, Definition
  `def:instance`; `Finite` since the statement involves no sum over the arms), `[DecidableEq α]`
  and `[MeasurableSpace α] [MeasurableSingletonClass α]`.
* `Cons^b` is LML's `Algorithm.const (Measure.dirac b)` (`p_t(h, ·) = δ_b`); uniform fast
  convergence is `IsUniformlyFastConvergent` (Definition `def:ufc`: for every Markov `ν` of the
  class, every arm with `0 < gap ν a` and every `p ∈ (0, 1]`, `E[N_a(T)] / T^p → 0`).
* The instance `ν` is a Markov kernel whose laws have finite means (`hν1`: Definition
  `def:instance`, `ν_a ∈ 𝒫_1`); "`b` is suboptimal" is `0 < gap ν b` (LML's `gap`). -/
theorem Incognita.Statements.P007.not_isUniformlyFastConvergent_const {α : Type*} [Finite α]
    [Nontrivial α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
    {E : Set (ProbabilityTheory.Kernel α ℝ)} {ν : ProbabilityTheory.Kernel α ℝ}
    [ProbabilityTheory.IsMarkovKernel ν] (hνE : ν ∈ E)
    (hν1 : ∀ a, MeasureTheory.Integrable id (ν a)) {b : α} (hb : 0 < Bandits.gap ν b) :
    ¬ Incognita.StochasticBandits.IsUniformlyFastConvergent
      (Learning.Algorithm.const (MeasureTheory.Measure.dirac b)) E := by
  sorry
