/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.Consistency

/-! # P003, prop:classes (b): `𝒞_L` stops changing at `L = 𝟏_K`

[INC-P003, Proposition (prop:classes), item (b)]. `𝒞_L = 𝒞_{𝟏_K}` whenever `L ≥ 𝟏_K`, and
`⋂_{L ∈ (0,∞)^K} 𝒞_L = 𝒞_{𝟏_K}`: a transfer learner is in `𝒞_L` for every `L` if and only if it
satisfies the condition of def:consistency with `𝒫_L` replaced by `𝒫^K × 𝒫^K`, that is, for every
pair and every source strategy.

Differences of form with the paper: arms are a finite type `α` with `2 ≤ Fintype.card α` (the
paper's `K ≥ 2`); `𝟏_K` is `fun _ ↦ 1`; the equalities of classes are equivalences for an
arbitrary transfer learner `π`; the three claims are the three conjuncts, the last one being
`π ∈ 𝒞_{𝟏_K}` if and only if the condition of `IsConsistent` holds for every pair of
`unitBandits α`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Incognita.TransferBandits Filter

open scoped Topology

namespace Incognita.Statements.P003

/-- [INC-P003, prop:classes (b)] `𝒞_L = 𝒞_𝟏` for `L ≥ 𝟏`; the intersection of the classes `𝒞_L`
is `𝒞_𝟏`, the class defined with every pair of instances. -/
theorem isConsistent_one {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (hK : 2 ≤ Fintype.card α) (π : TransferAlgorithm α) :
    (∀ L : α → ℝ, (∀ a, 1 ≤ L a) → (IsConsistent L π ↔ IsConsistent (fun _ ↦ 1) π)) ∧
      ((∀ L : α → ℝ, (∀ a, 0 < L a) → IsConsistent L π) ↔ IsConsistent (fun _ ↦ 1) π) ∧
      (IsConsistent (fun _ ↦ 1) π ↔
        ∀ ν ν' : Kernel α ℝ, ν ∈ unitBandits α → ν' ∈ unitBandits α →
          ∀ ρ : ℕ → SourceSpace α → α → ℕ, IsSourceStrategy ρ →
            ∀ a, (∃ b, (ν a)[id] < (ν b)[id]) → ∀ c : ℝ, 0 < c →
              Tendsto (fun T : ℕ ↦
                  (∫ p, (onlineCount a p.2 : ℝ) ∂(gameMeasure ν' (ρ T) ν π T)) / (T : ℝ) ^ c)
                atTop (𝓝 0)) := by
  sorry

end Incognita.Statements.P003
