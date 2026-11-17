/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.Checks
public import Incognita.TransferBandits.SizeRules

/-! # P003: the cyclic map is a size rule

The first part of [INC-P003, prop:stopped-games (c)]: the cyclic map `N^cyc` is a size rule with
total at most `3`.

## Main statements

* `isSizeRule_cyclicSize`, `sum_cyclicSize_le`, from the criterion
  `Incognita.TransferBandits.isSizeRule_of_eqOn_box`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Incognita.TransferBandits

namespace Incognita.P003

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
/-- The event `{X'_{a,1} > 1/2}` is measurable. -/
lemma measurableSet_half_lt (a : α) :
    MeasurableSet {ω : SourceSpace α | (1 / 2 : ℝ) < ω.2 a 0} :=
  measurableSet_lt measurable_const
    ((measurable_pi_apply 0).comp ((measurable_pi_apply a).comp measurable_snd))

omit [Fintype α] in
/-- The cyclic map is measurable. -/
lemma measurable_cyclicSize (a₁ a₂ a₃ : α) : Measurable (cyclicSize a₁ a₂ a₃) := by
  unfold cyclicSize
  exact Measurable.ite ((measurableSet_half_lt a₁).inter (measurableSet_half_lt a₂).compl)
    measurable_const (Measurable.ite
      ((measurableSet_half_lt a₂).inter (measurableSet_half_lt a₃).compl) measurable_const
      (Measurable.ite ((measurableSet_half_lt a₃).inter (measurableSet_half_lt a₁).compl)
        measurable_const measurable_const))

/-- The cyclic map has total at most `3`. -/
lemma sum_cyclicSize_le (a₁ a₂ a₃ : α) (ω : SourceSpace α) :
    ∑ a, cyclicSize a₁ a₂ a₃ ω a ≤ 3 := by
  unfold cyclicSize
  split_ifs <;> simp [Finset.sum_add_distrib]

omit [Fintype α] in
/-- The cyclic map is a size rule. -/
lemma isSizeRule_cyclicSize [Finite α] {a₁ a₂ a₃ : α} (h₁₂ : a₁ ≠ a₂) (h₂₃ : a₂ ≠ a₃)
    (h₁₃ : a₁ ≠ a₃) : IsSizeRule (cyclicSize a₁ a₂ a₃) := by
  refine isSizeRule_of_eqOn_box (measurable_cyclicSize a₁ a₂ a₃) fun n ω ω' _ h2 hN ↦ ?_
  have hb : ∀ a, 1 ≤ n a → ((1 / 2 : ℝ) < ω.2 a 0 ↔ (1 / 2 : ℝ) < ω'.2 a 0) :=
    fun a ha ↦ by rw [h2 a 0 ha]
  subst hN
  have hb1 := hb a₁
  have hb2 := hb a₂
  have hb3 := hb a₃
  clear hb h2
  by_cases p1 : (1 / 2 : ℝ) < ω.2 a₁ 0 <;> by_cases p2 : (1 / 2 : ℝ) < ω.2 a₂ 0 <;>
    by_cases p3 : (1 / 2 : ℝ) < ω.2 a₃ 0 <;>
    simp only [cyclicSize, p1, p2, p3, not_true, not_false_eq_true, and_true, and_false,
      ↓reduceIte] at hb1 hb2 hb3 ⊢ <;>
    simp only [Pi.add_apply, Pi.single_apply, h₁₂, h₂₃, h₁₃, Ne.symm h₁₂, Ne.symm h₂₃,
      Ne.symm h₁₃, ↓reduceIte] at hb1 hb2 hb3 <;>
    norm_num at hb1 hb2 hb3 <;>
    simp only [one_div, ← not_lt] at hb1 hb2 hb3 ⊢ <;>
    simp only [hb1, hb2, hb3, not_true, not_false_eq_true, and_true, and_false, false_and,
      ↓reduceIte]

end Incognita.P003
