/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.Batched

/-! # P006, `thm:main`(i): the information models are nested

One frozen statement of the paper P006 (`papers/P006-batched-setting`); its
docstring gives the statement in words and every difference of form with the paper. -/

@[expose] public section

/-- [INC-P006, Theorem `thm:main`(i), inclusions] Fix a finite set of arms with `K ≥ 2`. For all
`k ≤ k'` in `ℕ ∪ {∞}`, `𝓜_k ⊆ 𝓜_k'`: every learner for imposed grids of the information model
`𝓜_k` is in `𝓜_k'`.

Differences of form with the paper:
* The arms are a finite type `α` (`Fintype α`, never `Fin K`) with the discrete σ-algebra
  (`MeasurableSingletonClass α`, which for a finite type is the discrete one): the paper's
  convention that the arms form a finite discrete set `𝒜` [INC-P006, Definitions `def:instance`
  and `def:learner`].
* A learner is an LML algorithm `Algorithm Unit α ℝ` (no observation, real rewards); its policy
  at the 0-based round `n` is the paper's `π_{n+1}`. A grid is a `Grid (Fintype.card α)`: the
  condition `t 1 ≥ max(2, K)` of the paper is part of the structure. A learner for imposed grids
  `Π = (π^g)_{g ∈ 𝒢}` is a function `π : Grid (Fintype.card α) → Algorithm Unit α ℝ`, and
  `Π ∈ 𝓜_k` is `InfoModel k π`; `ℕ ∪ {∞}` is `ℕ∞`.
* The hypothesis `K ≥ 2` of the theorem is kept (`hK`), though the inclusion does not need it. -/
theorem Incognita.Statements.P006.infoModel_mono {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (hK : 2 ≤ Fintype.card α) {k k' : ℕ∞} (hkk' : k ≤ k')
    (π : Incognita.BatchedBandits.Grid (Fintype.card α) → Learning.Algorithm Unit α ℝ)
    (hπ : Incognita.BatchedBandits.InfoModel k π) :
    Incognita.BatchedBandits.InfoModel k' π := by
  sorry
