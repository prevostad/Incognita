/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.Batched

/-! # P006, `thm:main`(ii): refining a grid preserves batching

One frozen statement of the paper P006 (`papers/P006-batched-setting`); its
docstring gives the statement in words and every difference of form with the paper. -/

@[expose] public section

/-- [INC-P006, Theorem `thm:main`(ii), first claim] Fix a finite set of arms with `K ≥ 2`. Let `g`
be a grid finer than a grid `g'` (every end of `g'` is an end of `g`). Every learner batched on
`g'` is batched on `g`.

Differences of form with the paper:
* The arms are a finite type `α` (`Fintype α`, never `Fin K`) with the discrete σ-algebra
  (`MeasurableSingletonClass α`, which for a finite type is the discrete one): the paper's
  convention that the arms form a finite discrete set `𝒜` [INC-P006, Definitions `def:instance`
  and `def:learner`].
* A learner is an LML algorithm `Algorithm Unit α ℝ` (no observation, real rewards); its policy
  at the 0-based round `n` is the paper's `π_{n+1}`. A grid is a `Grid (Fintype.card α)`: the
  condition `t 1 ≥ max(2, K)` of the paper is part of the structure. "`g` is finer than `g'`" is
  `g.IsFiner g'`, that is `Set.range g'.t ⊆ Set.range g.t` (both ranges contain `t 0 = 0`, which
  is not a batch end).
* The class `E ⊆ 𝒫` of item (ii) is not used by this claim and does not appear; the hypothesis
  `K ≥ 2` of the theorem is kept (`hK`). -/
theorem Incognita.Statements.P006.isBatched_of_isFiner {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (hK : 2 ≤ Fintype.card α)
    {g g' : Incognita.BatchedBandits.Grid (Fintype.card α)} (hgg' : g.IsFiner g')
    {alg : Learning.Algorithm Unit α ℝ} (halg : Incognita.BatchedBandits.IsBatched alg g') :
    Incognita.BatchedBandits.IsBatched alg g := by
  sorry
