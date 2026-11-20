/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import LMLExplore.Analysis.Convex.Integral
public import LMLExplore.Bandits.Instances
public import LMLExplore.Identification.Task.RealLaws
public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Convex

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
* `integrable_id_of_mem_unitLaws`, `integral_id_mem_Icc_of_mem_unitLaws`: a law of `𝓜` has a mean
  in `[0, 1]`.
* `smul_add_smul_mem_unitLaws`: `𝓜` is convex; `smul_add_smul_dirac_one_mem_unitLaws`,
  `integral_id_smul_add_smul_dirac_one`, `mix_mem_unitLaws`: its two-point mixtures in the
  weight conventions used downstream, whose means mix linearly.
* `bernoulliBandit_mem_unitBandits_of_lt_one`: every Bernoulli instance whose means are all below
  `1` is in `𝒫`; `not_mem_unitBandits_of_integral_eq_one`: an instance with an arm of mean `1` (for
  example an arm `δ_1`) is not.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

open scoped unitInterval NNReal ENNReal

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
lemma integral_id_mem_Icc_of_mem_unitLaws (hQ : Q ∈ unitLaws) : Q[id] ∈ Set.Icc (0 : ℝ) 1 :=
  haveI := hQ.1
  integral_id_mem_Icc_of_ae_mem_Icc hQ.2

/-- A Dirac mass at a point of `[0, 1]` is a law on `[0, 1]`. -/
lemma dirac_mem_unitLaws {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : Measure.dirac x ∈ unitLaws :=
  ⟨inferInstance, (ae_dirac_iff measurableSet_Icc).mpr hx⟩

/-- **Witness and known case**: the Bernoulli law `Ber(p)` on `{0, 1}` is a law on `[0, 1]`. -/
lemma bernoulliMeasure_mem_unitLaws (p : I) : Ber((1 : ℝ), 0, p) ∈ unitLaws :=
  ⟨inferInstance, LMLExplore.Identification.mem_unitIntervalLaws_iff.1
    (LMLExplore.Identification.bernoulliMeasure_mem_unitIntervalLaws p)⟩

/-- **Exclusion**: the Dirac mass at `2` is not a law on `[0, 1]`. -/
lemma dirac_two_not_mem_unitLaws : Measure.dirac (2 : ℝ) ∉ unitLaws := by
  rintro ⟨-, h⟩
  have := (ae_dirac_iff measurableSet_Icc).mp h
  norm_num at this

/-- The identity is integrable for a law on `[0, 1]`. -/
lemma integrable_id_of_mem_unitLaws {P : Measure ℝ} (hP : P ∈ unitLaws) : Integrable id P :=
  haveI := hP.1
  Integrable.of_mem_Icc 0 1 aemeasurable_id hP.2

/-- A measurable function bounded on `[0, 1]` is integrable for a law on `[0, 1]`. -/
lemma integrable_of_abs_le_of_mem_unitLaws {P : Measure ℝ} (hP : P ∈ unitLaws) {f : ℝ → ℝ}
    (hf : Measurable f) (C : ℝ) (hC : ∀ x ∈ Set.Icc (0 : ℝ) 1, |f x| ≤ C) : Integrable f P := by
  have := hP.1
  exact Integrable.of_bound hf.aestronglyMeasurable C (hP.2.mono fun x hx ↦ by
    rw [Real.norm_eq_abs]; exact hC x hx)

/-- `𝓜` is convex: the mixture `a P + b Q` of two laws on `[0, 1]`, with weights `a + b = 1` in
`ℝ≥0∞`, is a law on `[0, 1]` (Tau Ceti's `isProbabilityMeasure_smul_add_smul` for the total
mass). -/
lemma smul_add_smul_mem_unitLaws {P Q : Measure ℝ} (hP : P ∈ unitLaws) (hQ : Q ∈ unitLaws)
    {a b : ℝ≥0∞} (hab : a + b = 1) : a • P + b • Q ∈ unitLaws := by
  have := hP.1
  have := hQ.1
  refine ⟨TauCeti.MeasureTheory.isProbabilityMeasure_smul_add_smul hab P Q, ?_⟩
  rw [ae_add_measure_iff]
  exact ⟨Measure.ae_smul_measure hP.2 _, Measure.ae_smul_measure hQ.2 _⟩

/-- The mixture `(1 - u) P + u δ_1` of a law on `[0, 1]` with the Dirac mass at `1` is a law on
`[0, 1]`, for `u ∈ [0, 1]`. -/
lemma smul_add_smul_dirac_one_mem_unitLaws {P : Measure ℝ} (hP : P ∈ unitLaws) {u : ℝ≥0}
    (hu : u ≤ 1) :
    (1 - u) • P + u • Measure.dirac (1 : ℝ) ∈ unitLaws := by
  rw [ENNReal.smul_def, ENNReal.smul_def]
  exact smul_add_smul_mem_unitLaws hP (dirac_mem_unitLaws ⟨zero_le_one, le_rfl⟩)
    (by rw [← ENNReal.coe_add, tsub_add_cancel_of_le hu, ENNReal.coe_one])

/-- The mean of the mixture `(1 - u) P + u δ_1` is `(1 - u) m(P) + u`. -/
lemma integral_id_smul_add_smul_dirac_one {P : Measure ℝ} (hP : P ∈ unitLaws) {u : ℝ≥0}
    (hu : u ≤ 1) :
    ((1 - u) • P + u • Measure.dirac (1 : ℝ))[id] = (1 - (u : ℝ)) * P[id] + u := by
  have hi := integrable_id_of_mem_unitLaws hP
  rw [integral_add_measure hi.smul_measure_nnreal
      (integrable_dirac (by simp)).smul_measure_nnreal,
    integral_smul_nnreal_measure, integral_smul_nnreal_measure, integral_dirac]
  simp [NNReal.smul_def, NNReal.coe_sub hu]

/-- The mixture `(1 - t) P + t Q` of two laws on `[0, 1]`, `t ∈ [0, 1]`, is a law on `[0, 1]`
with mean `(1 - t) m(P) + t m(Q)`. -/
lemma mix_mem_unitLaws {P Q : Measure ℝ} (hP : P ∈ unitLaws) (hQ : Q ∈ unitLaws) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ENNReal.ofReal (1 - t) • P + ENNReal.ofReal t • Q ∈ unitLaws ∧
      (ENNReal.ofReal (1 - t) • P + ENNReal.ofReal t • Q)[id] = (1 - t) * P[id] + t * Q[id] := by
  refine ⟨smul_add_smul_mem_unitLaws hP hQ ?_, ?_⟩
  · rw [← ENNReal.ofReal_add (by linarith) ht0]
    simp
  · rw [integral_add_measure ((integrable_id_of_mem_unitLaws hP).smul_measure ENNReal.ofReal_ne_top)
      ((integrable_id_of_mem_unitLaws hQ).smul_measure ENNReal.ofReal_ne_top),
      integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal (by linarith),
      ENNReal.toReal_ofReal ht0, smul_eq_mul, smul_eq_mul]

variable [Countable α] [MeasurableSingletonClass α]

/-- **Witness and known case** [INC-P006, Proposition `prop:witnesses`(a)]: every Bernoulli
instance whose means are all below `1` is in `𝒫`. -/
lemma bernoulliBandit_mem_unitBandits_of_lt_one [Finite α] (p : α → I) (hp : ∀ a, (p a : ℝ) < 1) :
    LMLExplore.Bandits.bernoulliBandit p ∈ unitBandits α := by
  refine ⟨fun a ↦ by simpa using bernoulliMeasure_mem_unitLaws (p a), ?_⟩
  simp only [LMLExplore.Bandits.integral_id_bernoulliBandit]
  rcases isEmpty_or_nonempty α with hα | hα
  · simp
  · obtain ⟨a, ha⟩ := exists_eq_ciSup_of_finite (f := fun a ↦ (p a : ℝ))
    rw [← ha]
    exact hp a

@[deprecated (since := "2026-11-19")]
alias bernoulliBandit_mem_unitBandits := bernoulliBandit_mem_unitBandits_of_lt_one

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
