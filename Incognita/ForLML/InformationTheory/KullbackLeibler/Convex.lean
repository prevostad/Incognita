/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import LeanMachineLearning.ForMathlib.InformationTheory.KullbackLeibler.Convex

/-! # Mixing a measure into the second argument of the Kullback–Leibler divergence

Complements to LML's `LeanMachineLearning.ForMathlib.InformationTheory.KullbackLeibler.Convex`.

## Main statements

* `Incognita.klDiv_mix_le_mul`: `KL(μ, (1 - t) μ + t ν) ≤ t KL(μ, ν)` for `t ∈ [0, 1]`.
* `Incognita.klDiv_mix_le`: `KL(μ, (1 - t) μ + t ν) ≤ KL(μ, ν)` for `t ∈ [0, 1]`.

Both were first written in Mathlib's namespace `InformationTheory`; the old names are deprecated
aliases.
-/

@[expose] public section

open MeasureTheory InformationTheory

open scoped ENNReal NNReal

namespace Incognita

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ ν : Measure Ω}

/-- **Convexity, mixing the first measure into the second**: for finite measures `μ`, `ν` and
`t ∈ [0, 1]`, `KL(μ, (1 - t) μ + t ν) ≤ t KL(μ, ν)` (from `klDiv_smul_add_smul_le`). -/
lemma klDiv_mix_le_mul [IsFiniteMeasure μ] [IsFiniteMeasure ν] {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    klDiv μ (ENNReal.ofReal (1 - t) • μ + ENNReal.ofReal t • ν) ≤ ENNReal.ofReal t * klDiv μ ν := by
  have h := klDiv_smul_add_smul_le μ μ μ ν (1 - t).toNNReal t.toNNReal
  have hμ : ((1 - t).toNNReal : ℝ≥0∞) • μ + (t.toNNReal : ℝ≥0∞) • μ = μ := by
    rw [← add_smul, ← ENNReal.coe_add, ← Real.toNNReal_add (by linarith) ht0]
    simp
  rw [hμ, klDiv_self, mul_zero, zero_add] at h
  exact h

/-- **Convexity, mixing the first measure into the second**: for finite measures `μ`, `ν` and
`t ∈ [0, 1]`, `KL(μ, (1 - t) μ + t ν) ≤ KL(μ, ν)`. -/
lemma klDiv_mix_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    klDiv μ (ENNReal.ofReal (1 - t) • μ + ENNReal.ofReal t • ν) ≤ klDiv μ ν :=
  (klDiv_mix_le_mul ht0 ht1).trans <| mul_le_of_le_one_left zero_le <|
    ENNReal.ofReal_le_one.mpr ht1

end Incognita

namespace InformationTheory

@[deprecated (since := "2026-11-19")] alias klDiv_mix_le_mul := Incognita.klDiv_mix_le_mul

@[deprecated (since := "2026-11-19")] alias klDiv_mix_le := Incognita.klDiv_mix_le

end InformationTheory
