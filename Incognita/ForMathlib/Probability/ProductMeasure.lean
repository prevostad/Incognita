/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Mathlib.Probability.ProductMeasure

/-! # The first two coordinates of an infinite product measure

## Main statements

* `Incognita.infinitePi_map_zero_one`: the first two values of an i.i.d. sequence of law `m` have
  law `m ⊗ m`.
-/

@[expose] public section

open MeasureTheory

namespace Incognita

/-- The first two values of an i.i.d. sequence of law `m` have law `m ⊗ m`. -/
lemma infinitePi_map_zero_one (m : Measure ℝ) [IsProbabilityMeasure m] :
    (Measure.infinitePi fun _ : ℕ ↦ m).map (fun w ↦ (w 0, w 1)) = m.prod m := by
  have hmeas : Measurable fun w : ℕ → ℝ ↦ (w 0, w 1) := by fun_prop
  refine (Measure.prod_eq fun s t hs ht ↦ ?_).symm
  rw [Measure.map_apply hmeas (hs.prod ht)]
  have hset : (fun w : ℕ → ℝ ↦ (w 0, w 1)) ⁻¹' (s ×ˢ t) =
      Set.pi (({0, 1} : Finset ℕ) : Set ℕ) (fun i ↦ if i = 0 then s else t) := by
    ext w
    simp
  rw [hset, Measure.infinitePi_pi (μ := fun _ : ℕ ↦ m) (s := {0, 1})
      (t := fun i ↦ if i = 0 then s else t) (fun i _ ↦ by split_ifs <;> assumption),
    Finset.prod_pair (by norm_num : (0 : ℕ) ≠ 1)]
  simp

end Incognita
