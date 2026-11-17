/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.Batched

/-! # P006, `thm:main`(iii): batched learners on the sequential grid

One frozen statement of the paper P006 (`papers/P006-batched-setting`); its
docstring gives the statement in words and every difference of form with the paper. -/

@[expose] public section

/-- [INC-P006, Theorem `thm:main`(iii), first claim] Fix a finite set of arms with `K ≥ 2`. Let
`s ≥ max(2, K)`. A learner `π` is batched on the sequential grid `𝖲_s` (`t ℓ = s + ℓ - 1` for
`ℓ ≥ 1`) if and only if `π_t` ignores the rewards for every round `t ≤ s`.

Differences of form with the paper:
* The arms are a finite type `α` (`Fintype α`, never `Fin K`) with the discrete σ-algebra
  (`MeasurableSingletonClass α`, which for a finite type is the discrete one): the paper's
  convention that the arms form a finite discrete set `𝒜` [INC-P006, Definitions `def:instance`
  and `def:learner`].
* A learner is an LML algorithm `Algorithm Unit α ℝ` (no observation, real rewards); its policy
  at the 0-based round `n` is the paper's `π_{n+1}`. A grid is a `Grid (Fintype.card α)`: the
  condition `t 1 ≥ max(2, K)` of the paper is part of the structure. Rounds are numbered from
  `0`: the paper's rounds `t = 1, …, s` are the rounds `n = t - 1 < s`, and "`π_t` ignores the
  rewards" is `SeesRewardsUpTo alg (t - 1) 0`. `𝖲_s` is `Grid.sequential s hs`.
* The class `E ⊆ 𝒫` of item (iii) is not used by this claim and does not appear; the hypothesis
  `K ≥ 2` of the theorem is kept (`hK`). -/
theorem Incognita.Statements.P006.isBatched_sequential_iff {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (hK : 2 ≤ Fintype.card α) {s : ℕ}
    (hs : max 2 (Fintype.card α) ≤ s) (alg : Learning.Algorithm Unit α ℝ) :
    Incognita.BatchedBandits.IsBatched alg (Incognita.BatchedBandits.Grid.sequential s hs) ↔
      ∀ n < s, Incognita.BatchedBandits.SeesRewardsUpTo alg n 0 := by
  sorry
