/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.StochasticBandits.GravesLai

/-! # P007, `cor:lower`: the Graves–Lai constant is the lower-bound constant

One frozen statement of the paper P007 (`papers/P007-stochastic-setting`); its docstring gives the
statement in words and every difference of form with the paper. -/

@[expose] public section

/-- [INC-P007, Corollary `cor:lower`] Let `D` be a model, `π` a learner consistent on `D^α`, and
`ν ∈ D^α` an instance with a unique optimal arm. Then, in `[0, ∞]`,
`liminf_{T → ∞} R_T(π, ν) / log T ≥ C(ν; D^α)`.

Differences of form with the paper:
* The arms are a type `α` with `[Fintype α] [Nontrivial α]` (`K = |α| ≥ 2`, Definition
  `def:instance`) and `[MeasurableSpace α] [MeasurableSingletonClass α]` (every family of laws is
  a kernel). LMLExplore's Lai–Robbins bound also assumes `[StandardBorelSpace α]`; it is not a
  hypothesis here, since it follows from these (Mathlib's
  `standardBorelSpace_of_discreteMeasurableSpace`).
* The model is a set `D` of probability measures with `Integrable id` (`D ⊆ 𝒫_1`, Definition
  `def:kinf`); `D^α` is `productClass (fun _ ↦ D)`.
* A learner is an LML `Algorithm Unit α ℝ` (anytime, Definition `def:learner`); its run on `ν` is
  `trajMeasure alg (Environment.bandit ν)` (Definition `def:run`; rounds `0, …, T - 1`), and
  `R_T(π, ν)` is the expectation of LML's `regret ν IT.action T = ∑_{t < T} Δ_{A_t}` (Definition
  `def:regret`). Consistency is LMLExplore's `IsConsistent` (Definition `def:consistent`:
  `R_T / T^p → 0` for every `p > 0` and every instance of the class).
* `[IsMarkovKernel ν]` is an instance argument needed to form the run; it follows from `hν` and
  `hD`.
* "Unique optimal arm `a⋆`" is `∀ a ≠ a⋆, 0 < gap ν a`; `C(ν; E)` is `gravesLai E ν` in `ℝ≥0∞`.
* The `liminf` in `[0, ∞]` is written in eventual form (the roadmap's convention): for every real
  `c` with `ENNReal.ofReal c < C(ν; D^α)`, eventually `c log T ≤ R_T(π, ν)`. This is the `liminf`
  inequality: when `C > 0` it covers every `c < C`, and when `C = 0` both sides say nothing. -/
theorem Incognita.Statements.P007.lower_bound_gravesLai {α : Type*} [Fintype α] [Nontrivial α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    {D : Set (MeasureTheory.Measure ℝ)}
    (hD : ∀ Q ∈ D, MeasureTheory.IsProbabilityMeasure Q ∧ MeasureTheory.Integrable id Q)
    {alg : Learning.Algorithm Unit α ℝ}
    (halg : LMLExplore.Bandits.IsConsistent alg
      (Incognita.StochasticBandits.productClass fun _ : α ↦ D))
    {ν : ProbabilityTheory.Kernel α ℝ} [ProbabilityTheory.IsMarkovKernel ν]
    (hν : ν ∈ Incognita.StochasticBandits.productClass fun _ : α ↦ D)
    {aStar : α} (haStar : ∀ a ≠ aStar, 0 < Bandits.gap ν a) {c : ℝ}
    (hc : ENNReal.ofReal c <
      Incognita.StochasticBandits.gravesLai
        (Incognita.StochasticBandits.productClass fun _ : α ↦ D) ν) :
    ∀ᶠ n : ℕ in Filter.atTop, c * Real.log n ≤
      ∫ ω, Bandits.regret ν Learning.IT.action n ω
        ∂(Learning.trajMeasure alg (Learning.Environment.bandit ν)) := by
  sorry
