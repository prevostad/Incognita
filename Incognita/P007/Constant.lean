/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.StochasticBandits.UCB
public import LeanMachineLearning.SequentialLearning.Algorithms.RandomSampling.Basic

/-! # P007, `lem:constant`: the learner that always pulls `b`

Proofs of the three frozen statements of [INC-P007, Lemma `lem:constant`], its consequence on
`Cons^b`, each with exactly the type of `Incognita.Statements.P007.<name>`: on a class that contains
an instance where `b` is suboptimal, `Cons^b` is not consistent (`not_isConsistent_const`), not
uniformly fast convergent (`not_isUniformlyFastConvergent_const`) and not uniformly super-fast
convergent with any constant (`not_isUniformlySuperFastConvergent_const`). They are the library
checks of the same names in `Incognita.StochasticBandits`.

The finite means of the laws of `ν` (hypothesis `_hν1`) and `[Nontrivial α]` are not used (an arm of
positive gap already forces a second arm), and neither is `[DecidableEq α]` beyond counting the
pulls; the theorems are marked `nolint unusedArguments`: their signature is fixed by the frozen
statement.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Incognita.P007

/-- [INC-P007, Lemma `lem:constant`, the case `γ = 0` of its consequence on `Cons^b`] On every
class `E` that contains an instance `ν` in which the arm `b` is suboptimal, the learner `Cons^b`
that always pulls `b` is not consistent on `E`. The finite means `_hν1` are not used. -/
@[nolint unusedArguments]
theorem not_isConsistent_const {α : Type*} [Finite α] [Nontrivial α]
    [MeasurableSpace α] [MeasurableSingletonClass α] {E : Set (ProbabilityTheory.Kernel α ℝ)}
    {ν : ProbabilityTheory.Kernel α ℝ} [ProbabilityTheory.IsMarkovKernel ν] (hνE : ν ∈ E)
    (_hν1 : ∀ a, MeasureTheory.Integrable id (ν a)) {b : α} (hb : 0 < Bandits.gap ν b) :
    ¬ LMLExplore.Bandits.IsConsistent
      (Learning.Algorithm.const (MeasureTheory.Measure.dirac b)) E :=
  StochasticBandits.not_isConsistent_const hνE hb

/-- [INC-P007, Lemma `lem:constant`, its consequence on `Cons^b`, "nor uniformly fast
convergent"] On every class `E` that contains an instance `ν` in which the arm `b` is suboptimal,
the learner `Cons^b` that always pulls `b` is not uniformly fast convergent on `E`. The finite means
`hν1` are not used. -/
@[nolint unusedArguments]
theorem not_isUniformlyFastConvergent_const {α : Type*} [Finite α]
    [Nontrivial α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
    {E : Set (ProbabilityTheory.Kernel α ℝ)} {ν : ProbabilityTheory.Kernel α ℝ}
    [ProbabilityTheory.IsMarkovKernel ν] (hνE : ν ∈ E)
    (_hν1 : ∀ a, MeasureTheory.Integrable id (ν a)) {b : α} (hb : 0 < Bandits.gap ν b) :
    ¬ Incognita.StochasticBandits.IsUniformlyFastConvergent
      (Learning.Algorithm.const (MeasureTheory.Measure.dirac b)) E :=
  StochasticBandits.not_isUniformlyFastConvergent_const hνE hb

/-- [INC-P007, Lemma `lem:constant`, its consequence on `Cons^b`, "nor uniformly super-fast
convergent with any constant"] On every class `E` that contains an instance `ν` in which the arm
`b` is suboptimal, the learner `Cons^b` that always pulls `b` is not uniformly super-fast
convergent on `E` with any constant `C`. The finite means `_hν1` are not used. -/
@[nolint unusedArguments]
theorem not_isUniformlySuperFastConvergent_const {α : Type*} [Finite α]
    [Nontrivial α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
    {E : Set (ProbabilityTheory.Kernel α ℝ)} {ν : ProbabilityTheory.Kernel α ℝ}
    [ProbabilityTheory.IsMarkovKernel ν] (hνE : ν ∈ E)
    (_hν1 : ∀ a, MeasureTheory.Integrable id (ν a)) {b : α} (hb : 0 < Bandits.gap ν b) :
    ¬ ∃ C : ℝ, Incognita.StochasticBandits.IsUniformlySuperFastConvergent
      (Learning.Algorithm.const (MeasureTheory.Measure.dirac b)) E C :=
  fun ⟨C, hC⟩ ↦ StochasticBandits.not_isUniformlySuperFastConvergent_const hνE hb C hC

end Incognita.P007
