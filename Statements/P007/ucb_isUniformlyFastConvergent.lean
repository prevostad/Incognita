/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.StochasticBandits.GravesLai
public import Incognita.StochasticBandits.UCB

/-! # P007, `prop:ucb`, fast convergence: `UCB` on laws on `[0, 1]` and on Bernoulli laws

One frozen statement of the paper P007 (`papers/P007-stochastic-setting`); its docstring gives the
statement in words and every difference of form with the paper. -/

@[expose] public section

/-- [INC-P007, Proposition `prop:ucb`, "uniformly fast convergent on both"] For every tie rule,
`UCB` is uniformly fast convergent on `𝒫[0, 1]^α` and on `ℬ^α`.

Differences of form with the paper:
* The arms are a type `α` with `[Finite α] [Nontrivial α]` (`K = |α| ≥ 2`, Definition
  `def:instance`; `Finite` since no sum over the arms appears), `[DecidableEq α]` and
  `[MeasurableSpace α] [MeasurableSingletonClass α]`.
* "`UCB` with some tie rule" is `IsHoeffdingUCB alg` (Definition `def:ucb`, index (`eq:ucb`)).
* `𝒫[0, 1]^α` is `productClass (fun _ ↦ unitLaws)`; `ℬ^α` is the `productClass` of the Bernoulli
  laws `bernoulliMeasure (1 : ℝ) 0 p`, `p ∈ [0, 1]`; uniform fast convergence is
  `IsUniformlyFastConvergent` (Definition `def:ufc`: for every Markov `ν` of the class, every arm
  with `0 < gap ν a` and every `p ∈ (0, 1]`, `E[N_a(T)] / T^p → 0`). -/
theorem Incognita.Statements.P007.ucb_isUniformlyFastConvergent {α : Type*} [Finite α]
    [Nontrivial α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
    {alg : Learning.Algorithm Unit α ℝ} (halg : Incognita.StochasticBandits.IsHoeffdingUCB alg) :
    Incognita.StochasticBandits.IsUniformlyFastConvergent alg
        (Incognita.StochasticBandits.productClass fun _ : α ↦ Incognita.BatchedBandits.unitLaws) ∧
      Incognita.StochasticBandits.IsUniformlyFastConvergent alg
        (Incognita.StochasticBandits.productClass fun _ : α ↦
          Set.range fun p : unitInterval ↦ ProbabilityTheory.bernoulliMeasure (1 : ℝ) 0 p) := by
  sorry
