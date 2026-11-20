/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.StochasticBandits.GravesLai
public import Incognita.StochasticBandits.UCB

/-! # P007, `prop:ucb`, super-fast convergence: `UCB` with the constant `13` on laws on `[0, 1]`

One frozen statement of the paper P007 (`papers/P007-stochastic-setting`); its docstring gives the
statement in words and every difference of form with the paper. -/

@[expose] public section

/-- [INC-P007, Proposition `prop:ucb`, second sentence] For every tie rule, `UCB` satisfies
`E[N_a(T)] ≤ 13 log T / Δ_a²` for every instance of `𝒫[0, 1]^α`, every suboptimal arm `a` and
every `T ≥ 2`: it is uniformly super-fast convergent on `𝒫[0, 1]^α` with the constant `13`.

Differences of form with the paper:
* The arms are a type `α` with `[Finite α] [Nontrivial α]` (`K = |α| ≥ 2`, Definition
  `def:instance`; `Finite` since no sum over the arms appears), `[DecidableEq α]` and
  `[MeasurableSpace α] [MeasurableSingletonClass α]`.
* "`UCB` with some tie rule" is `IsHoeffdingUCB alg` (Definition `def:ucb`, index (`eq:ucb`)).
* `𝒫[0, 1]^α` is `productClass (fun _ ↦ unitLaws)`; uniform super-fast convergence with the
  constant `C` is `IsUniformlySuperFastConvergent alg E C` (Definition `def:ufc`: for every Markov
  `ν ∈ E`, every arm with `0 < gap ν a` and every `T ≥ 2`, `E[N_a(T)] ≤ C log T / Δ_a²`), which
  contains the inequality of the sentence. -/
theorem Incognita.Statements.P007.ucb_isUniformlySuperFastConvergent {α : Type*} [Finite α]
    [Nontrivial α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
    {alg : Learning.Algorithm Unit α ℝ} (halg : Incognita.StochasticBandits.IsHoeffdingUCB alg) :
    Incognita.StochasticBandits.IsUniformlySuperFastConvergent alg
      (Incognita.StochasticBandits.productClass fun _ : α ↦ Incognita.BatchedBandits.unitLaws)
      13 := by
  sorry
