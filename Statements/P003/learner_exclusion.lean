/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.Examples

/-! # P003, lem:learner-exclusion: the learner does not see unobserved values

[INC-P003, Lemma (lem:learner-exclusion)]. Let `N' ≡ (1, 0, …, 0)`. There is no measurable
`f : 𝒮 → [0,1]` with `f(D) = X'_{1,2}` on `Ω'`. Hence there is no transfer learner `π` with
`π_1(D(ω), ·) = δ_1` when `X'_{1,2}(ω) > 1/2` and `π_1(D(ω), ·) = δ_2` otherwise, for every `ω`.

Differences of form with the paper: the paper's arms `1` and `2` are two distinct arms `a₁ ≠ a₂` of
a finite type `α` with `2 ≤ Fintype.card α`; `X'_{1,2}` is the value of index `1` of the stack of
`a₁` (indices from `0`); the stacks of the Lean source space are real-valued, so `f` is real-valued
(the values of `f` play no role in the argument: `D` does not determine `X'_{1,2}`); the first
round is the 0-based round `0`, whose history is the empty sequence `Fin 0 → α × ℝ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Incognita.TransferBandits

namespace Incognita.Statements.P003

/-- [INC-P003, lem:learner-exclusion] For the sizes `(1, 0, …, 0)`, no measurable function of the
source data equals the unobserved value `X'_{1,2}`, and no transfer learner chooses its first arm
according to it. -/
theorem learner_exclusion {α : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (hK : 2 ≤ Fintype.card α) {a₁ a₂ : α} (h₁₂ : a₁ ≠ a₂) :
    (¬ ∃ f : Source α → ℝ, Measurable f ∧
        ∀ ω, f (sourceData (constSize fun a ↦ if a = a₁ then 1 else 0) ω) = ω.2 a₁ 1) ∧
      ¬ ∃ π : TransferAlgorithm α, ∀ ω : SourceSpace α,
        π.policy 0 (sourceData (constSize fun a ↦ if a = a₁ then 1 else 0) ω, fun i ↦ i.elim0) =
          if (1 / 2 : ℝ) < ω.2 a₁ 1 then Measure.dirac a₁ else Measure.dirac a₂ := by
  sorry

end Incognita.Statements.P003
