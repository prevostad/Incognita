/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.StochasticBandits.GravesLai
public import Incognita.StochasticBandits.UCB

/-! # P007, `prop:ucb`, finite-time bound: the counts of `UCB` on laws on `[0, 1]`

One frozen statement of the paper P007 (`papers/P007-stochastic-setting`); its docstring gives the
statement in words and every difference of form with the paper. -/

@[expose] public section

/-- [INC-P007, Proposition `prop:ucb`, first display] For every tie rule, every instance
`ν ∈ 𝒫[0, 1]^α`, every suboptimal arm `a` and every `T ≥ 1`, the learner `UCB` satisfies
`E[N_a(T)] ≤ 8 log T / Δ_a² + 2 / Δ_a² + 5 / 4`.

Differences of form with the paper:
* The arms are a type `α` with `[Finite α] [Nontrivial α]` (`K = |α| ≥ 2`, Definition
  `def:instance`; `Finite` since no sum over the arms appears), `[DecidableEq α]` (to count
  pulls) and `[MeasurableSpace α] [MeasurableSingletonClass α]`.
* "`UCB` with some tie rule" is a learner `alg` with `IsHoeffdingUCB alg`: at every round, its
  policy is concentrated on the arms of maximal index `μ̂_a + √(2 log (t + 1) / N_a(t))` (`+∞` for
  an arm never pulled), Definition `def:ucb` and (`eq:ucb`); the tie rule is the policy itself.
* `𝒫[0, 1]^α` is `productClass (fun _ ↦ unitLaws)` (P006's laws on `[0, 1]`); the instance is a
  Markov kernel (`[IsMarkovKernel ν]`, which follows from `hν`).
* `E[N_a(T)]` is the expectation, under LML's run `trajMeasure alg (Environment.bandit ν)`, of
  `pullCount IT.action a T`, the number of pulls of `a` in the rounds `0, …, T - 1` (Definition
  `def:regret`); "`a` suboptimal" is `0 < gap ν a`. -/
theorem Incognita.Statements.P007.ucb_pullCount_le {α : Type*} [Finite α] [Nontrivial α]
    [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
    {alg : Learning.Algorithm Unit α ℝ} (halg : Incognita.StochasticBandits.IsHoeffdingUCB alg)
    {ν : ProbabilityTheory.Kernel α ℝ} [ProbabilityTheory.IsMarkovKernel ν]
    (hν : ν ∈ Incognita.StochasticBandits.productClass fun _ : α ↦
      Incognita.BatchedBandits.unitLaws)
    {a : α} (ha : 0 < Bandits.gap ν a) {T : ℕ} (hT : 1 ≤ T) :
    ∫ ω, (Learning.pullCount Learning.IT.action a T ω : ℝ)
        ∂(Learning.trajMeasure alg (Learning.Environment.bandit ν)) ≤
      8 * Real.log T / Bandits.gap ν a ^ 2 + 2 / Bandits.gap ν a ^ 2 + 5 / 4 := by
  sorry
