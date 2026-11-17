/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.Batched

/-! # P006, `thm:main`(i): batched learners are the components of the families of `𝓜_∞`

One frozen statement of the paper P006 (`papers/P006-batched-setting`); its
docstring gives the statement in words and every difference of form with the paper. -/

@[expose] public section

/-- [INC-P006, Theorem `thm:main`(i), last claim] Fix a finite set of arms with `K ≥ 2`. A learner
`π` is batched on a grid `g` if and only if `π = π^g` for some learner for imposed grids
`Π ∈ 𝓜_∞`.

Differences of form with the paper:
* The arms are a finite type `α` (`Fintype α`, never `Fin K`) with the discrete σ-algebra
  (`MeasurableSingletonClass α`, which for a finite type is the discrete one): the paper's
  convention that the arms form a finite discrete set `𝒜` [INC-P006, Definitions `def:instance`
  and `def:learner`].
* A learner is an LML algorithm `Algorithm Unit α ℝ` (no observation, real rewards); its policy
  at the 0-based round `n` is the paper's `π_{n+1}`. A grid is a `Grid (Fintype.card α)`: the
  condition `t 1 ≥ max(2, K)` of the paper is part of the structure. `Π ∈ 𝓜_∞` is
  `InfoModel ⊤ π`, and `π^g` is `π g`.
* The hypothesis `K ≥ 2` of the theorem is kept (`hK`). -/
theorem Incognita.Statements.P006.isBatched_iff_exists_infoModel_top {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (hK : 2 ≤ Fintype.card α)
    (alg : Learning.Algorithm Unit α ℝ) (g : Incognita.BatchedBandits.Grid (Fintype.card α)) :
    Incognita.BatchedBandits.IsBatched alg g ↔
      ∃ π : Incognita.BatchedBandits.Grid (Fintype.card α) → Learning.Algorithm Unit α ℝ,
        Incognita.BatchedBandits.InfoModel ⊤ π ∧ π g = alg := by
  sorry
