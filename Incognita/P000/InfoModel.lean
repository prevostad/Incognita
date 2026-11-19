/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.HY.InfoModel

/-! # P000: HY is a learner of the information model `𝓜_0`

Proof of the frozen statement `Incognita.Statements.P000.hy_infoModel_zero`
[INC-P000, Theorem `thm:main`(b), first claim], with exactly its type: a specialisation of
`Incognita.BatchedBandits.infoModel_zero_hy`, which holds for all real parameters `w₀`, `β`. The
hypotheses `K ≥ 2`, `w₀ ≥ 0` and `β ≥ 2` are not used; they are named `_hK`, `_hw₀`, `_hβ` (the type
is the frozen one up to binder names).
-/

@[expose] public section

namespace Incognita.P000

/-- [INC-P000, Theorem `thm:main`(b), first claim] For every `w₀ ≥ 0` and `β ≥ 2`, the family of
learners `g ↦ HY(w₀, β)` on the grid `g` (default `ω^dy`, `ϑ`, `γ`) is in the information model
`𝓜_0`: each is batched on its grid, and during batch `ℓ + 1` its policy depends on the grid only
through `t 1, …, t ℓ`. The hypotheses `K ≥ 2`, `w₀ ≥ 0`, `β ≥ 2` are not used. -/
theorem hy_infoModel_zero {α : Type*}
    [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (_hK : 2 ≤ Fintype.card α) [Nonempty α]
    {w₀ β : ℝ} (_hw₀ : 0 ≤ w₀) (_hβ : 2 ≤ β) :
    Incognita.BatchedBandits.InfoModel (0 : ℕ∞)
      (fun g : Incognita.BatchedBandits.Grid (Fintype.card α) ↦
        (Incognita.BatchedBandits.hy w₀ β g : Learning.Algorithm Unit α ℝ)) :=
  Incognita.BatchedBandits.infoModel_zero_hy w₀ β

end Incognita.P000
