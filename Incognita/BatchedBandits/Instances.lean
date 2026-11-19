/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import LMLExplore.Bandits.Instances

/-! # Laws on `[0, 1]` and the class `𝒫` of instances

The instances of the batched bandit setting [INC-P006, Definition `def:instance`]: an instance is
an LML bandit `ν : Kernel α ℝ` (arm `a` returns a reward of law `ν a`), the mean of a law `Q` is
the Bochner integral `Q[id]`, as in LML's `gap` and LMLExplore's `dInf`, and the largest mean is
`⨆ a, (ν a)[id]`.

## Main definitions

* `Incognita.BatchedBandits.unitLaws`: the set `𝓜` of probability measures on `ℝ` concentrated on
  `[0, 1]`.
* `Incognita.BatchedBandits.unitBandits α`: the class `𝒫` of instances whose arms have laws in
  `𝓜` and whose largest mean is below `1`.

`𝒦_inf(P, μ)` of the paper is `LMLExplore.Bandits.dInf unitLaws P μ`, and `K_a` is
`dInf unitLaws (ν a) (⨆ b, (ν b)[id])`: these are reused, not redefined.

## Main statements

* `bernoulliMeasure_mem_unitLaws`, `dirac_mem_unitLaws`: Bernoulli laws and Dirac masses at points
  of `[0, 1]` are in `𝓜`; `dirac_two_not_mem_unitLaws`: the Dirac mass at `2` is not.
* `bernoulliBandit_mem_unitBandits`: every Bernoulli instance whose means are all below `1` is in
  `𝒫`; `not_mem_unitBandits_of_integral_eq_one`: an instance with an arm of mean `1` (for example
  an arm `δ_1`) is not.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

open scoped unitInterval

namespace Incognita.BatchedBandits

/-- The set `𝓜` of **laws on `[0, 1]`** [INC-P006, Definition `def:instance`]: the probability
measures `Q` on `ℝ` with `Q([0, 1]) = 1`, written `∀ᵐ x ∂Q, x ∈ [0, 1]`. -/
def unitLaws : Set (Measure ℝ) := {Q | IsProbabilityMeasure Q ∧ ∀ᵐ x ∂Q, x ∈ Set.Icc (0 : ℝ) 1}

/-- The class `𝒫` of **instances with rewards in `[0, 1]` and largest mean below `1`**
[INC-P006, Definition `def:instance`]: the kernels `ν : Kernel α ℝ` whose arms all have laws in
`unitLaws`, with `m⋆ = ⨆ a, (ν a)[id] < 1`. Such a kernel is a Markov kernel
(`isMarkovKernel_of_mem_unitBandits`). -/
def unitBandits (α : Type*) [MeasurableSpace α] : Set (Kernel α ℝ) :=
  {ν | (∀ a, ν a ∈ unitLaws) ∧ (⨆ a, (ν a)[id]) < 1}

variable {α : Type*} [MeasurableSpace α] {ν : Kernel α ℝ} {Q : Measure ℝ}

lemma isProbabilityMeasure_of_mem_unitLaws (hQ : Q ∈ unitLaws) : IsProbabilityMeasure Q := hQ.1

lemma isMarkovKernel_of_mem_unitBandits (hν : ν ∈ unitBandits α) : IsMarkovKernel ν :=
  ⟨fun a ↦ (hν.1 a).1⟩

/-- The mean of a law on `[0, 1]` is in `[0, 1]`. -/
lemma integral_id_mem_Icc_of_mem_unitLaws (hQ : Q ∈ unitLaws) : Q[id] ∈ Set.Icc (0 : ℝ) 1 := by
  have := hQ.1
  refine ⟨integral_nonneg_of_ae (hQ.2.mono fun x hx ↦ hx.1), ?_⟩
  calc Q[id] ≤ ∫ _, (1 : ℝ) ∂Q := integral_mono_of_nonneg
        (hQ.2.mono fun x hx ↦ hx.1) (integrable_const 1) (hQ.2.mono fun x hx ↦ hx.2)
    _ = 1 := by simp

/-- A Dirac mass at a point of `[0, 1]` is a law on `[0, 1]`. -/
lemma dirac_mem_unitLaws {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : Measure.dirac x ∈ unitLaws :=
  ⟨inferInstance, (ae_dirac_iff measurableSet_Icc).mpr hx⟩

/-- **Witness and known case**: the Bernoulli law `Ber(p)` on `{0, 1}` is a law on `[0, 1]`. -/
lemma bernoulliMeasure_mem_unitLaws (p : I) : Ber((1 : ℝ), 0, p) ∈ unitLaws :=
  ⟨inferInstance, by
    simpa using LMLExplore.Bandits.ae_mem_Icc_bernoulliBandit (α := Unit) (fun _ ↦ p) ()⟩

/-- **Exclusion**: the Dirac mass at `2` is not a law on `[0, 1]`. -/
lemma dirac_two_not_mem_unitLaws : Measure.dirac (2 : ℝ) ∉ unitLaws := by
  rintro ⟨-, h⟩
  have := (ae_dirac_iff measurableSet_Icc).mp h
  norm_num at this

variable [Countable α] [MeasurableSingletonClass α]

/-- **Witness and known case** [INC-P006, Proposition `prop:witnesses`(a)]: every Bernoulli
instance whose means are all below `1` is in `𝒫`. -/
lemma bernoulliBandit_mem_unitBandits [Finite α] (p : α → I) (hp : ∀ a, (p a : ℝ) < 1) :
    LMLExplore.Bandits.bernoulliBandit p ∈ unitBandits α := by
  refine ⟨fun a ↦ by simpa using bernoulliMeasure_mem_unitLaws (p a), ?_⟩
  simp only [LMLExplore.Bandits.integral_id_bernoulliBandit]
  rcases isEmpty_or_nonempty α with hα | hα
  · simp
  · obtain ⟨a, ha⟩ := exists_eq_ciSup_of_finite (f := fun a ↦ (p a : ℝ))
    rw [← ha]
    exact hp a

omit [Countable α] [MeasurableSingletonClass α] in
/-- **Exclusion** [INC-P006, Proposition `prop:witnesses`(a)]: an instance with an arm of mean
`1`, for example an arm `δ_1`, is not in `𝒫`. -/
lemma not_mem_unitBandits_of_integral_eq_one [Finite α] {a : α} (ha : (ν a)[id] = 1) :
    ν ∉ unitBandits α := by
  rintro ⟨-, h⟩
  have := le_ciSup (Finite.bddAbove_range fun b ↦ (ν b)[id]) a
  rw [ha] at this
  exact absurd h (not_lt.mpr this)

end Incognita.BatchedBandits
