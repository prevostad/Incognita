/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.StochasticBandits.GravesLai
public import Incognita.StochasticBandits.UCB

/-! # P007, `prop:ucb`, consistency: `UCB` is consistent on laws on `[0, 1]` and on Bernoulli laws

One frozen statement of the paper P007 (`papers/P007-stochastic-setting`); its docstring gives the
statement in words and every difference of form with the paper. -/

@[expose] public section

/-- [INC-P007, Proposition `prop:ucb`, "consistent on `𝒫[0, 1]^α` and on `ℬ^α`"] For every tie
rule, `UCB` is consistent on `𝒫[0, 1]^α` and on `ℬ^α`.

Differences of form with the paper:
* The arms are a type `α` with `[Finite α] [Nontrivial α]` (`K = |α| ≥ 2`, Definition
  `def:instance`; `Finite` since no sum over the arms appears), `[DecidableEq α]` and
  `[MeasurableSpace α] [MeasurableSingletonClass α]`.
* "`UCB` with some tie rule" is `IsHoeffdingUCB alg` (Definition `def:ucb`, index (`eq:ucb`)).
* `𝒫[0, 1]^α` is `productClass (fun _ ↦ unitLaws)`; `ℬ` is the set of the Bernoulli laws
  `bernoulliMeasure (1 : ℝ) 0 p`, `p ∈ [0, 1]` (Definition `def:models`), and `ℬ^α` its
  `productClass`; consistency is LMLExplore's `IsConsistent` (Definition `def:consistent`). -/
theorem Incognita.Statements.P007.ucb_isConsistent {α : Type*} [Finite α] [Nontrivial α]
    [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
    {alg : Learning.Algorithm Unit α ℝ} (halg : Incognita.StochasticBandits.IsHoeffdingUCB alg) :
    LMLExplore.Bandits.IsConsistent alg
        (Incognita.StochasticBandits.productClass fun _ : α ↦ Incognita.BatchedBandits.unitLaws) ∧
      LMLExplore.Bandits.IsConsistent alg
        (Incognita.StochasticBandits.productClass fun _ : α ↦
          Set.range fun p : unitInterval ↦ ProbabilityTheory.bernoulliMeasure (1 : ℝ) 0 p) := by
  sorry
