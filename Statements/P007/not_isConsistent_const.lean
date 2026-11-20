/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.StochasticBandits.GravesLai
public import LeanMachineLearning.SequentialLearning.Algorithms.RandomSampling.Basic

/-! # P007, `lem:constant` (consistency part): the learner that always pulls `b` is not consistent

One frozen statement of the paper P007 (`papers/P007-stochastic-setting`); its docstring gives the
statement in words and every difference of form with the paper. -/

@[expose] public section

/-- [INC-P007, Lemma `lem:constant`, the case `γ = 0` of its consequence on `Cons^b`] On every
class `E` that contains an instance `ν` in which the arm `b` is suboptimal, the learner `Cons^b`
that always pulls `b` is not consistent on `E`.

Differences of form with the paper:
* This statement is the consistency part of the lemma (the exclusion that the roadmap asks of the
  setting paper: "always pull arm `a`" is not consistent). The exclusions of uniform fast and
  super-fast convergence are the frozen statements
  `Incognita.Statements.P007.not_isUniformlyFastConvergent_const` and
  `Incognita.Statements.P007.not_isUniformlySuperFastConvergent_const`.
* Not frozen: items (i) and (ii) of the lemma (the values of `E[N_a(T)]` and of the regret for
  `Cons^b` and for the uniform learner), which use no new class; the first half of (i) is proved
  in the library (`Incognita.StochasticBandits.integral_pullCount_const_self`). Also not frozen:
  the claims on `γ`-consistency for `γ > 0` and on "smarter than the uniform learner", which need
  classes that are not defined yet, and the non-consistency of the uniform learner (its case
  `γ = 0`), left to a later statements pull request.
* The arms are a type `α` with `[Finite α] [Nontrivial α]` (`K = |α| ≥ 2`, Definition
  `def:instance`; `Finite` rather than `Fintype` since the statement involves no sum over the
  arms) and `[MeasurableSpace α] [MeasurableSingletonClass α]`.
* `Cons^b` is LML's `Algorithm.const (Measure.dirac b)` (`p_t(h, ·) = δ_b`); consistency is
  LMLExplore's `IsConsistent` (Definition `def:consistent`).
* The instance `ν` is a Markov kernel whose laws have finite means (`hν1`: Definition
  `def:instance`, `ν_a ∈ 𝒫_1`); "`b` is suboptimal" is `0 < gap ν b` (LML's `gap`). -/
theorem Incognita.Statements.P007.not_isConsistent_const {α : Type*} [Finite α] [Nontrivial α]
    [MeasurableSpace α] [MeasurableSingletonClass α] {E : Set (ProbabilityTheory.Kernel α ℝ)}
    {ν : ProbabilityTheory.Kernel α ℝ} [ProbabilityTheory.IsMarkovKernel ν] (hνE : ν ∈ E)
    (hν1 : ∀ a, MeasureTheory.Integrable id (ν a)) {b : α} (hb : 0 < Bandits.gap ν b) :
    ¬ LMLExplore.Bandits.IsConsistent
      (Learning.Algorithm.const (MeasureTheory.Measure.dirac b)) E := by
  sorry
