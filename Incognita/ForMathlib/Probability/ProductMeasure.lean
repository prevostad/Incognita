/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Mathlib.Probability.Independence.InfinitePi

/-! # The first two coordinates of an infinite product measure

## Main statements

* `Incognita.infinitePi_map_zero_one`: the first two values of an i.i.d. sequence of law `m` have
  law `m ⊗ m`; the case `i = 0`, `j = 1` of Mathlib's `Measure.infinitePi_map_eval_prod` (any
  family of probability measures, any two distinct coordinates).
-/

@[expose] public section

open MeasureTheory

namespace Incognita

/-- The first two values of an i.i.d. sequence of law `m` have law `m ⊗ m` (Mathlib's
`Measure.infinitePi_map_eval_prod`). -/
lemma infinitePi_map_zero_one (m : Measure ℝ) [IsProbabilityMeasure m] :
    (Measure.infinitePi fun _ : ℕ ↦ m).map (fun w ↦ (w 0, w 1)) = m.prod m :=
  Measure.infinitePi_map_eval_prod zero_ne_one

end Incognita
