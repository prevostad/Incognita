/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.Checks

/-! # P003: what the source data do not see

Proofs of [INC-P003, lem:lookahead] and [INC-P003, lem:learner-exclusion].

## Main statements

* `lookahead_not_isSizeRule`: the look-ahead map is measurable and bounded, and not a size rule.
* `learner_exclusion`: for the sizes `(1, 0, …, 0)`, the source data do not determine the value
  `X'_{a₁,2}`, so neither a function of the source data nor the first kernel of a transfer learner
  can follow it.

Both rest on the two points `ω₀` (every value `0`) and `ω₁` (the second value of every stack is
`1`, the others `0`), which agree on every box containing no second value.

The hypothesis `K ≥ 2` (`_hK`) of the frozen statements is not used.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Incognita.TransferBandits

namespace Incognita.P003

/-- The two points `ω₀ = (0, 0)` and `ω₁` (second value of every stack `1`) agree on the box of a
size vector with all sizes at most `1`. -/
lemma boxRestrict_eq_of_le_one {α : Type*} {n : α → ℕ} (hn : ∀ a, n a ≤ 1) :
    boxRestrict n ((fun _ ↦ 0, fun _ _ ↦ 0) : SourceSpace α) =
      boxRestrict n ((fun _ ↦ 0, fun _ j ↦ if j = 1 then 1 else 0) : SourceSpace α) := by
  simp only [boxRestrict, Prod.mk.injEq, true_and]
  funext a j
  have : (j : ℕ) ≠ 1 := by have := j.2; have := hn a; omega
  simp [this]

/-- [INC-P003, lem:lookahead] The look-ahead map is measurable and bounded, and not a size rule. -/
@[nolint unusedArguments]
theorem lookahead_not_isSizeRule {α : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (_hK : 2 ≤ Fintype.card α) (a₁ : α) :
    Measurable (lookahead a₁) ∧ (∃ M : ℕ, ∀ ω a, lookahead a₁ ω a ≤ M) ∧
      ¬ IsSizeRule (lookahead a₁) := by
  refine ⟨measurable_pi_iff.mpr fun a ↦ ?_, ⟨2, fun ω a ↦ ?_⟩, fun h ↦ ?_⟩
  · by_cases ha : a = a₁
    · simp only [lookahead, ha, ↓reduceIte]
      exact Measurable.ite (measurableSet_lt measurable_const
        ((measurable_pi_apply 1).comp ((measurable_pi_apply a₁).comp measurable_snd)))
        measurable_const measurable_const
    · simp only [lookahead, ha, ↓reduceIte]
      exact measurable_const
  · simp only [lookahead]
    split_ifs <;> omega
  · let n : α → ℕ := fun a ↦ if a = a₁ then 1 else 0
    obtain ⟨t, -, ht⟩ := h.measurableSet_eq n
    let ω₀ : SourceSpace α := (fun _ ↦ 0, fun _ _ ↦ 0)
    let ω₁ : SourceSpace α := (fun _ ↦ 0, fun _ j ↦ if j = 1 then 1 else 0)
    have h₁ : ω₁ ∈ {ω : SourceSpace α | lookahead a₁ ω = n} := by
      rw [Set.mem_ofPred_eq]
      funext a
      by_cases ha : a = a₁ <;> norm_num [lookahead, ha, ω₁, n]
    have h₀ : ω₀ ∉ {ω : SourceSpace α | lookahead a₁ ω = n} := by
      intro hω
      have := congrFun (show lookahead a₁ ω₀ = n from hω) a₁
      simp [lookahead, ω₀, n] at this
    have hbox : boxRestrict n ω₀ = boxRestrict n ω₁ :=
      boxRestrict_eq_of_le_one fun a ↦ by simp only [n]; split_ifs <;> omega
    rw [← ht] at h₀ h₁
    exact h₀ (by simpa [Set.mem_preimage, hbox] using h₁)

/-- [INC-P003, lem:learner-exclusion] For the sizes `(1, 0, …, 0)`, no measurable function of the
source data equals the unobserved value `X'_{1,2}`, and no transfer learner chooses its first arm
according to it. -/
theorem learner_exclusion {α : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (_hK : 2 ≤ Fintype.card α) {a₁ a₂ : α} (h₁₂ : a₁ ≠ a₂) :
    (¬ ∃ f : Source α → ℝ, Measurable f ∧
        ∀ ω, f (sourceData (constSize fun a ↦ if a = a₁ then 1 else 0) ω) = ω.2 a₁ 1) ∧
      ¬ ∃ π : TransferAlgorithm α, ∀ ω : SourceSpace α,
        π.policy 0 (sourceData (constSize fun a ↦ if a = a₁ then 1 else 0) ω, fun i ↦ i.elim0) =
          if (1 / 2 : ℝ) < ω.2 a₁ 1 then Measure.dirac a₁ else Measure.dirac a₂ := by
  let N : SourceSpace α → α → ℕ := constSize fun a ↦ if a = a₁ then 1 else 0
  let ω₀ : SourceSpace α := (fun _ ↦ 0, fun _ _ ↦ 0)
  let ω₁ : SourceSpace α := (fun _ ↦ 0, fun _ j ↦ if j = 1 then 1 else 0)
  have hD : sourceData N ω₀ = sourceData N ω₁ := by
    refine sourceData_eq_of_eqOn_box N rfl fun a j hj ↦ ?_
    have hj1 : j ≠ 1 := by
      have : N ω₀ a ≤ 1 := by simp only [N, constSize]; split_ifs <;> omega
      omega
    simp [ω₀, ω₁, hj1]
  refine ⟨fun ⟨f, _, hf⟩ ↦ ?_, fun ⟨π, hπ⟩ ↦ ?_⟩
  · have h0 := hf ω₀
    have h1 := hf ω₁
    -- fold the abbreviation `N` of the size map
    change f (sourceData N ω₀) = _ at h0
    change f (sourceData N ω₁) = _ at h1
    rw [hD, h1] at h0
    simp [ω₀, ω₁] at h0
  · have h0 := hπ ω₀
    have h1 := hπ ω₁
    -- fold the abbreviation `N` of the size map
    change π.policy 0 (sourceData N ω₀, _) = _ at h0
    change π.policy 0 (sourceData N ω₁, _) = _ at h1
    rw [hD, h1] at h0
    norm_num [ω₀, ω₁] at h0
    exact h₁₂ (dirac_eq_dirac_iff.mp h0)

end Incognita.P003
