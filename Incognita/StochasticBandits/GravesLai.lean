/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.Instances
public import LMLExplore.Bandits.LaiRobbins
public import LMLExplore.InformationTheory.KullbackLeibler.Gaussian

/-! # Unstructured classes, alternatives and the Graves–Lai constant

The objects of [INC-P007, Definitions `def:product` and `def:gl`], with the conventions of the
roadmap StochasticBandits. An instance is an LML bandit `ν : Kernel α ℝ` (arm `a` returns a reward
of law `ν a`); the mean of a law `Q` is the Bochner integral `Q[id]`, the gap of arm `a` is LML's
`gap ν a = (⨆ b, (ν b)[id]) - (ν a)[id]`, and `KL` is Mathlib's `klDiv`, in `ℝ≥0∞`.

## Main definitions

* `Incognita.StochasticBandits.productClass D`: the unstructured class `∏_a D_a` of the instances
  whose arm `a` has its law in `D a`.
* `Incognita.StochasticBandits.alt E ν`: the alternatives to `ν` in the class `E`, the instances
  of `E` in which no optimal arm of `ν` is optimal (for `ν` with a unique optimal arm `a⋆`, the
  instances of `E` in which `a⋆` is not optimal, `mem_alt_iff_of_unique`).
* `Incognita.StochasticBandits.gravesLai E ν`: the Graves–Lai constant
  `C(ν; E) = inf {∑_a w_a Δ_a : w ∈ [0, ∞]^α, ∑_a w_a KL(ν_a, ν'_a) ≥ 1 for every ν' ∈ Alt(ν; E)}`
  in `ℝ≥0∞`, with the conventions `0 * ∞ = 0` of `ℝ≥0∞`.

## Main statements (the checks of AGENTS.md §6.4)

* `bernoulliBandit_mem_productClass` (witness), `unitBandits_eq_productClass_inter` (known case:
  the class `𝒫` of BatchedBandits), `const_dirac_two_not_mem_productClass` (exclusion).
* `mem_alt_iff_of_unique` (known case: the paper's formula for a unique optimal arm),
  `not_mem_alt_self` (exclusion: an instance is never an alternative to itself), `mem_alt_example`
  (witness).
* `gravesLai_eq_zero_of_alt_eq_empty` (witness: `C = 0` without alternatives),
  `div_klDiv_le_gravesLai` (known case: an alternative that moves one arm `b` gives the
  Lai–Robbins constraint `C ≥ Δ_b / KL(ν_b, ν'_b)`), `gravesLai_example_ne_zero` (exclusion: the
  constant is not identically `0`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Learning Bandits

open scoped ENNReal NNReal unitInterval

namespace Incognita.StochasticBandits

variable {α : Type*} [MeasurableSpace α]

/-- The **unstructured class** `∏_a D_a` [INC-P007, Definition `def:product`]: the instances
`ν : Kernel α ℝ` whose arm `a` has its law `ν a` in the model `D a`. The class `D^α` of a single
model `D` is `productClass (fun _ ↦ D)`. This is the class `{ν | ∀ a, ν a ∈ M a}` of LMLExplore's
Lai–Robbins bound (`LMLExplore.Bandits.eventually_mul_log_le_integral_regret_of_isConsistent`). -/
def productClass (D : α → Set (Measure ℝ)) : Set (Kernel α ℝ) := {ν | ∀ a, ν a ∈ D a}

/-- The **alternatives** to `ν` in the class `E` [INC-P007, Definition `def:gl`]: the instances
`ν' ∈ E` in which no optimal arm of `ν` is optimal, that is `0 < gap ν' a` for every arm `a` with
`gap ν a = 0`. The paper defines `Alt(ν; E)` for an instance `ν` with a unique optimal arm `a⋆`,
as the instances of `E` in which `a⋆` is not optimal; for such a `ν` the two agree
(`mem_alt_iff_of_unique`). -/
def alt (E : Set (Kernel α ℝ)) (ν : Kernel α ℝ) : Set (Kernel α ℝ) :=
  {ν' | ν' ∈ E ∧ ∀ a, gap ν a = 0 → 0 < gap ν' a}

/-- The **Graves–Lai constant** `C(ν; E)` [INC-P007, Definition `def:gl`]: the infimum, over the
weights `w : α → [0, ∞]` such that `∑_a w_a KL(ν_a, ν'_a) ≥ 1` for every alternative
`ν' ∈ alt E ν`, of `∑_a w_a Δ_a`, in `ℝ≥0∞` (infinite weights allowed, `0 * ∞ = 0`, `inf ∅ = ∞`).
`KL` is Mathlib's `klDiv` and `Δ_a` is `ENNReal.ofReal (gap ν a)`. -/
noncomputable def gravesLai [Fintype α] (E : Set (Kernel α ℝ)) (ν : Kernel α ℝ) : ℝ≥0∞ :=
  ⨅ w ∈ {w : α → ℝ≥0∞ | ∀ ν' ∈ alt E ν, 1 ≤ ∑ a, w a * klDiv (ν a) (ν' a)},
    ∑ a, w a * ENNReal.ofReal (gap ν a)

/-! ### Checks of `productClass` -/

/-- **Witness**: every Bernoulli instance lies in the unstructured class of laws on `[0, 1]`. -/
lemma bernoulliBandit_mem_productClass [Countable α] [MeasurableSingletonClass α] (p : α → I) :
    LMLExplore.Bandits.bernoulliBandit p ∈ productClass (fun _ : α ↦ BatchedBandits.unitLaws) :=
  fun a ↦ by
    rw [LMLExplore.Bandits.bernoulliBandit_apply]
    exact BatchedBandits.bernoulliMeasure_mem_unitLaws (p a)

/-- **Known case**: the class `𝒫` of the roadmap BatchedBandits [INC-P006, Definition
`def:instance`] is the unstructured class of laws on `[0, 1]` cut by the condition `m⋆ < 1`. -/
lemma unitBandits_eq_productClass_inter :
    BatchedBandits.unitBandits α =
      productClass (fun _ : α ↦ BatchedBandits.unitLaws) ∩ {ν | (⨆ a, (ν a)[id]) < 1} :=
  rfl

/-- **Exclusion**: the instance whose arms all have the law `δ_2` is not in the unstructured class
of laws on `[0, 1]`. -/
lemma const_dirac_two_not_mem_productClass [Nonempty α] :
    Kernel.const α (Measure.dirac (2 : ℝ)) ∉ productClass (fun _ : α ↦ BatchedBandits.unitLaws) :=
  fun h ↦ BatchedBandits.dirac_two_not_mem_unitLaws (by
    simpa using h (Classical.arbitrary α))

/-! ### Checks of `alt` -/

section Alt

variable [Finite α] {E : Set (Kernel α ℝ)} {ν ν' : Kernel α ℝ}

/-- The unique optimal arm has gap `0`. -/
lemma gap_eq_zero_of_unique {aStar : α} (h : ∀ a ≠ aStar, 0 < gap ν a) : gap ν aStar = 0 := by
  have := Fintype.ofFinite α
  have : Nonempty α := ⟨aStar⟩
  by_contra hne
  have hb : bestArm ν ≠ aStar := fun hb ↦ hne (hb ▸ gap_bestArm)
  exact (h _ hb).ne' gap_bestArm

/-- **Known case**: for an instance `ν` with a unique optimal arm `a⋆`, the alternatives are the
instances of `E` in which `a⋆` is not optimal, the formula of [INC-P007, Definition `def:gl`]. -/
lemma mem_alt_iff_of_unique {aStar : α} (h : ∀ a ≠ aStar, 0 < gap ν a) :
    ν' ∈ alt E ν ↔ ν' ∈ E ∧ 0 < gap ν' aStar := by
  refine ⟨fun h' ↦ ⟨h'.1, h'.2 aStar (gap_eq_zero_of_unique h)⟩, fun h' ↦ ⟨h'.1, fun a ha ↦ ?_⟩⟩
  by_cases haS : a = aStar
  · exact haS ▸ h'.2
  · exact absurd ha (h a haS).ne'

/-- **Exclusion**: an instance is never an alternative to itself. -/
lemma not_mem_alt_self [Nonempty α] : ν ∉ alt E ν := fun h ↦ by
  have := Fintype.ofFinite α
  exact (h.2 (bestArm ν) gap_bestArm).ne' gap_bestArm

end Alt

/-! ### Checks of `gravesLai` -/

section GravesLai

variable [Fintype α] {E : Set (Kernel α ℝ)} {ν ν' : Kernel α ℝ}

/-- **Witness**: without alternatives, the zero weight is feasible and `C(ν; E) = 0`. -/
lemma gravesLai_eq_zero_of_alt_eq_empty (h : alt E ν = ∅) : gravesLai E ν = 0 := by
  refine le_antisymm ?_ zero_le
  calc gravesLai E ν ≤ ∑ a, (0 : α → ℝ≥0∞) a * ENNReal.ofReal (gap ν a) :=
        iInf₂_le (0 : α → ℝ≥0∞) (by simp [h])
    _ = 0 := by simp

/-- **Known case**: an alternative `ν'` that differs from `ν` only at the arm `b` gives the
Lai–Robbins constraint `C(ν; E) ≥ Δ_b / KL(ν_b, ν'_b)`. -/
lemma div_klDiv_le_gravesLai [IsFiniteKernel ν] (hν' : ν' ∈ alt E ν) {b : α}
    (hb : ∀ a ≠ b, ν' a = ν a) :
    ENNReal.ofReal (gap ν b) / klDiv (ν b) (ν' b) ≤ gravesLai E ν := by
  refine le_iInf₂ fun w hw ↦ ?_
  have h1 := hw ν' hν'
  have hsum : ∑ a, w a * klDiv (ν a) (ν' a) = w b * klDiv (ν b) (ν' b) := by
    rw [Finset.sum_eq_single b]
    · intro a _ hab
      rw [hb a hab, klDiv_self, mul_zero]
    · simp
  rw [hsum] at h1
  calc ENNReal.ofReal (gap ν b) / klDiv (ν b) (ν' b) ≤ w b * ENNReal.ofReal (gap ν b) := by
        refine ENNReal.div_le_of_le_mul ?_
        calc ENNReal.ofReal (gap ν b) = ENNReal.ofReal (gap ν b) * 1 := (mul_one _).symm
          _ ≤ ENNReal.ofReal (gap ν b) * (w b * klDiv (ν b) (ν' b)) := by gcongr
          _ = w b * ENNReal.ofReal (gap ν b) * klDiv (ν b) (ν' b) := by ring
    _ ≤ ∑ a, w a * ENNReal.ofReal (gap ν a) :=
        Finset.single_le_sum (f := fun a ↦ w a * ENNReal.ofReal (gap ν a))
          (fun _ _ ↦ zero_le) (Finset.mem_univ b)

end GravesLai

/-! ### An explicit example on two arms -/

/-- The Gaussian instance with variance `1` and means `1` (arm `true`) and `0` (arm `false`). -/
noncomputable abbrev gaussianExampleInst : Kernel Bool ℝ :=
  LMLExplore.Bandits.gaussianBandit (fun b : Bool ↦ if b then (1 : ℝ) else 0) 1

/-- The Gaussian instance with variance `1` and means `1` (arm `true`) and `2` (arm `false`): an
alternative to `gaussianExampleInst` that moves the arm `false` only. -/
noncomputable abbrev gaussianExampleAlt : Kernel Bool ℝ :=
  LMLExplore.Bandits.gaussianBandit (fun b : Bool ↦ if b then (1 : ℝ) else 2) 1

lemma iSup_bool_real (f : Bool → ℝ) : ⨆ b, f b = max (f true) (f false) := by
  refine le_antisymm (ciSup_le fun b ↦ ?_)
    (max_le (le_ciSup (Finite.bddAbove_range _) true) (le_ciSup (Finite.bddAbove_range _) false))
  cases b <;> simp

lemma gap_gaussianBandit_bool (μ : Bool → ℝ) (σ2 : ℝ≥0) (a : Bool) :
    gap (LMLExplore.Bandits.gaussianBandit μ σ2) a = max (μ true) (μ false) - μ a := by
  simp only [gap, LMLExplore.Bandits.integral_id_gaussianBandit, iSup_bool_real]

lemma gap_gaussianExampleInst_false : gap gaussianExampleInst false = 1 := by
  rw [gap_gaussianBandit_bool]; norm_num

lemma gap_gaussianExampleInst_true : gap gaussianExampleInst true = 0 := by
  rw [gap_gaussianBandit_bool]; norm_num

lemma gap_gaussianExampleAlt_true : gap gaussianExampleAlt true = 1 := by
  rw [gap_gaussianBandit_bool]; norm_num

/-- **Witness** for `alt`: `gaussianExampleAlt` is an alternative to `gaussianExampleInst` in every
class that contains it. -/
lemma mem_alt_example {E : Set (Kernel Bool ℝ)} (hE : gaussianExampleAlt ∈ E) :
    gaussianExampleAlt ∈ alt E gaussianExampleInst := by
  refine ⟨hE, fun a ha ↦ ?_⟩
  cases a
  · rw [gap_gaussianExampleInst_false] at ha; norm_num at ha
  · rw [gap_gaussianExampleAlt_true]; norm_num

/-- **Exclusion** for `gravesLai`: the constant is not identically `0`; on the class
`{gaussianExampleAlt}`,
`C(gaussianExampleInst; {gaussianExampleAlt}) ≥ Δ_false / KL(𝒩(0, 1), 𝒩(2, 1)) = 1 / 2`. -/
lemma gravesLai_example_ne_zero : gravesLai {gaussianExampleAlt} gaussianExampleInst ≠ 0 := by
  have h := div_klDiv_le_gravesLai (E := {gaussianExampleAlt}) (ν := gaussianExampleInst)
    (ν' := gaussianExampleAlt) (mem_alt_example rfl) (b := false) (fun a ha ↦ by
      cases a
      · exact absurd rfl ha
      · simp)
  have hkl : klDiv (gaussianExampleInst false) (gaussianExampleAlt false) = ENNReal.ofReal 2 := by
    simp only [LMLExplore.Bandits.gaussianBandit_apply]
    rw [LMLExplore.klDiv_gaussianReal_gaussianReal_same_var one_ne_zero]
    norm_num
  rw [gap_gaussianExampleInst_false, hkl] at h
  refine (lt_of_lt_of_le ?_ h).ne'
  simp

end Incognita.StochasticBandits
