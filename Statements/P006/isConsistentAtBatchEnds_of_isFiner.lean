/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.Consistency
public import Incognita.BatchedBandits.Instances

/-! # P006, `thm:main`(ii): consistency at the ends of a finer grid passes to the coarser grid

One frozen statement of the paper P006 (`papers/P006-batched-setting`); its
docstring gives the statement in words and every difference of form with the paper. -/

@[expose] public section

/-- [INC-P006, Theorem `thm:main`(ii), second claim] Fix a finite set of arms with `K ≥ 2`. Let `g`
be a grid finer than a grid `g'`, and `E ⊆ 𝒫`. Every learner consistent at the batch ends of
`g` on `E` is consistent at the batch ends of `g'` on `E`.

Differences of form with the paper:
* The arms are a finite type `α` (`Fintype α`, never `Fin K`) with the discrete σ-algebra
  (`MeasurableSingletonClass α`, which for a finite type is the discrete one): the paper's
  convention that the arms form a finite discrete set `𝒜` [INC-P006, Definitions `def:instance`
  and `def:learner`].
* A learner is an LML algorithm `Algorithm Unit α ℝ` (no observation, real rewards); its policy
  at the 0-based round `n` is the paper's `π_{n+1}`. A grid is a `Grid (Fintype.card α)`: the
  condition `t 1 ≥ max(2, K)` of the paper is part of the structure. "`g` is finer than `g'`" is
  `g.IsFiner g'`.
* Consistency at the batch ends is `IsConsistentAtBatchEnds alg g E`: for every Markov kernel
  `ν ∈ E`, every arm `c` with `gap ν c > 0` and every `p > 0`, `E_ν[N_c(t ℓ)] / (t ℓ) ^ p → 0`,
  where `N_c(t) = pullCount IT.action c t` counts the pulls in the rounds `0, …, t - 1` (the
  paper's rounds `1, …, t`: no shift at the batch ends) under
  `trajMeasure alg (Environment.bandit ν)`; the limit runs over all `ℓ ∈ ℕ` (the value at
  `ℓ = 0`, where `t 0 = 0`, does not affect it). `𝒫` is `unitBandits α`. `DecidableEq α` is
  needed to count the pulls.
* The hypothesis `K ≥ 2` of the theorem is kept (`hK`). -/
theorem Incognita.Statements.P006.isConsistentAtBatchEnds_of_isFiner {α : Type*} [Fintype α]
    [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α] (hK : 2 ≤ Fintype.card α)
    {g g' : Incognita.BatchedBandits.Grid (Fintype.card α)} (hgg' : g.IsFiner g')
    {E : Set (ProbabilityTheory.Kernel α ℝ)} (hE : E ⊆ Incognita.BatchedBandits.unitBandits α)
    {alg : Learning.Algorithm Unit α ℝ}
    (halg : Incognita.BatchedBandits.IsConsistentAtBatchEnds alg g E) :
    Incognita.BatchedBandits.IsConsistentAtBatchEnds alg g' E := by
  sorry
