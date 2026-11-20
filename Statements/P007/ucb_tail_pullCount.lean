/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.StochasticBandits.GravesLai
public import Incognita.StochasticBandits.UCB

/-! # P007, `prop:ucb-tails`, the tail bound: the counts of `UCB` on laws on `[0, 1]`

One frozen statement of the paper P007 (`papers/P007-stochastic-setting`); its docstring gives the
statement in words and every difference of form with the paper. -/

@[expose] public section

/-- [INC-P007, Proposition `prop:ucb-tails`, the display] For every tie rule, every instance
`ν ∈ 𝒫[0, 1]^α`, every suboptimal arm `a` and every `T ≥ 2`, the learner `UCB` satisfies
`P(N_a(T) ≥ 10 log T / Δ_a²) ≤ 1 / (log T)²`.

Differences of form with the paper:
* Only the display is frozen. The sentence "Hence `UCB` has `f`-upper tailed counts … and
  pseudo-regret …" uses the classes of Definition `def:tails`, which are not defined in this pull
  request; for the counts it is this display with `C = 10`, `C̃ = 1`.
* The arms are a type `α` with `[Finite α] [Nontrivial α]` (`K = |α| ≥ 2`, Definition
  `def:instance`; `Finite` since no sum over the arms appears), `[DecidableEq α]` and
  `[MeasurableSpace α] [MeasurableSingletonClass α]`.
* "`UCB` with some tie rule" is `IsHoeffdingUCB alg` (Definition `def:ucb`, index (`eq:ucb`)).
* `𝒫[0, 1]^α` is `productClass (fun _ ↦ unitLaws)`; the instance is a Markov kernel.
* `P` is LML's run `trajMeasure alg (Environment.bandit ν)` (a probability measure, in `ℝ≥0∞`),
  and `N_a(T)` is `pullCount IT.action a T` (rounds `0, …, T - 1`); the right-hand side is
  `ENNReal.ofReal (1 / (log T)²)`, positive since `T ≥ 2`. -/
theorem Incognita.Statements.P007.ucb_tail_pullCount {α : Type*} [Finite α] [Nontrivial α]
    [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
    {alg : Learning.Algorithm Unit α ℝ} (halg : Incognita.StochasticBandits.IsHoeffdingUCB alg)
    {ν : ProbabilityTheory.Kernel α ℝ} [ProbabilityTheory.IsMarkovKernel ν]
    (hν : ν ∈ Incognita.StochasticBandits.productClass fun _ : α ↦
      Incognita.BatchedBandits.unitLaws)
    {a : α} (ha : 0 < Bandits.gap ν a) {T : ℕ} (hT : 2 ≤ T) :
    Learning.trajMeasure alg (Learning.Environment.bandit ν)
        {ω | 10 * Real.log T / Bandits.gap ν a ^ 2 ≤
          (Learning.pullCount Learning.IT.action a T ω : ℝ)} ≤
      ENNReal.ofReal (1 / Real.log T ^ 2) := by
  sorry
