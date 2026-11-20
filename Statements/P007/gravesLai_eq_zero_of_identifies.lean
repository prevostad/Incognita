/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.StochasticBandits.GravesLai

/-! # P007, `prop:gl-zero`: the constant vanishes when the optimal arm identifies the instance

One frozen statement of the paper P007 (`papers/P007-stochastic-setting`); its docstring gives the
statement in words and every difference of form with the paper. -/

@[expose] public section

/-- [INC-P007, Proposition `prop:gl-zero`] Let `E` be a class and `ν` an instance with a unique
optimal arm `a⋆`. If every `ν' ∈ E` with `ν'_{a⋆} = ν_{a⋆}` is equal to `ν`, then `C(ν; E) = 0`.

Differences of form with the paper:
* The arms are a type `α` with `[Fintype α] [Nontrivial α]` (`K = |α| ≥ 2`, Definition
  `def:instance`) and a measurable space, so that instances are kernels `Kernel α ℝ`.
* A class is a set `E` of instances, and an instance is a family of laws of `𝒫_1` (Definition
  `def:instance`): hypotheses `hE` (for the instances of `E`) and `hν` (for `ν`), each law a
  probability measure with `Integrable id`.
* "Unique optimal arm `a⋆`" is `∀ a ≠ a⋆, 0 < gap ν a` (LML's `gap`); `C(ν; E)` is
  `gravesLai E ν` (Definition `def:gl`, in `ℝ≥0∞`).
* The paper does not assume `ν ∈ E`, and neither does the statement. -/
theorem Incognita.Statements.P007.gravesLai_eq_zero_of_identifies {α : Type*} [Fintype α]
    [Nontrivial α] [MeasurableSpace α] {E : Set (ProbabilityTheory.Kernel α ℝ)}
    (hE : ∀ ν' ∈ E, ∀ a, MeasureTheory.IsProbabilityMeasure (ν' a) ∧
      MeasureTheory.Integrable id (ν' a))
    {ν : ProbabilityTheory.Kernel α ℝ}
    (hν : ∀ a, MeasureTheory.IsProbabilityMeasure (ν a) ∧ MeasureTheory.Integrable id (ν a))
    {aStar : α} (haStar : ∀ a ≠ aStar, 0 < Bandits.gap ν a)
    (hid : ∀ ν' ∈ E, ν' aStar = ν aStar → ν' = ν) :
    Incognita.StochasticBandits.gravesLai E ν = 0 := by
  sorry
