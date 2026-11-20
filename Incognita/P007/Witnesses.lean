/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.StochasticBandits.GravesLai
public import Incognita.StochasticBandits.UCB
public import LMLExplore.Bandits.AsymptoticOptimality

/-! # Joint satisfiability of the hypotheses of the frozen statements of P007

For each frozen statement `Incognita.Statements.P007.<name>`, the lemma
`Incognita.P007.<name>_satisfiable` exhibits an explicit instance that satisfies all its
hypotheses at once. The arms are `Bool` (two arms, `K = 2`); the model is the set `unitLaws` of
laws on `[0, 1]`, contained in `𝒫_1` (`integrable_id_of_mem_unitLaws`); the instance is the
Bernoulli instance `exampleInst = (Ber(7/10), Ber(1/2))` (arm `true` is the unique optimal arm).

* `thm:main`: the unstructured class of laws on `[0, 1]` and `exampleInst`.
* `prop:gl-zero`: the class `{exampleInst, exampleSwap}` with
  `exampleSwap = (Ber(1/2), Ber(7/10))`, in which the law of the arm `true` identifies the
  instance (the example `𝓔_2` of the paper, with other means).
* `cor:lower`: KL-UCB (`LMLExplore.Bandits.klucb`), consistent on the bandits with rewards in
  `[0, 1]` (`LMLExplore.Bandits.KLUCB.isConsistent`), and `c = 0`, below the Graves–Lai constant
  since the constant is positive: the alternative `exampleAlt = (Ber(7/10), Ber(9/10))` moves the
  arm `false` only, at a finite divergence `kl(1/2, 9/10)` (`div_klDiv_le_gravesLai`).
* `lem:constant` (consistency, uniform fast and super-fast convergence): the same class and
  instance, with the suboptimal arm `false`.
* `prop:ucb`: the learner `hoeffdingUCB` (`UCB` with the tie rule of LML's `argmax`,
  `isHoeffdingUCB_hoeffdingUCB`), and for the finite-time bound the instance `exampleInst`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Learning Bandits LMLExplore.Bandits

open scoped ENNReal unitInterval

namespace Incognita.P007

open Incognita.StochasticBandits Incognita.BatchedBandits

/-- A law on `[0, 1]` has a finite mean: `unitLaws ⊆ 𝒫_1`. -/
lemma integrable_id_of_mem_unitLaws {Q : Measure ℝ} (hQ : Q ∈ unitLaws) : Integrable id Q := by
  have := hQ.1
  refine (integrable_const (1 : ℝ)).mono' measurable_id.aestronglyMeasurable
    (hQ.2.mono fun x hx ↦ ?_)
  rw [id, Real.norm_eq_abs, abs_le]
  constructor <;> linarith [hx.1, hx.2]

/-- Every law on `[0, 1]` is a probability measure with a finite mean. -/
lemma unitLaws_subset_finiteMean :
    ∀ Q ∈ unitLaws, IsProbabilityMeasure Q ∧ Integrable id Q :=
  fun _ hQ ↦ ⟨hQ.1, integrable_id_of_mem_unitLaws hQ⟩

/-- The parameter `7/10`. -/
noncomputable def pSeven : I := ⟨7 / 10, by norm_num, by norm_num⟩

/-- The parameter `1/2`. -/
noncomputable def pFive : I := ⟨1 / 2, by norm_num, by norm_num⟩

/-- The parameter `9/10`. -/
noncomputable def pNine : I := ⟨9 / 10, by norm_num, by norm_num⟩

/-- The example instance `(Ber(7/10), Ber(1/2))` (arm `true`, arm `false`). -/
noncomputable abbrev exampleInst : Kernel Bool ℝ :=
  bernoulliBandit (fun b : Bool ↦ if b then pSeven else pFive)

/-- The swapped instance `(Ber(1/2), Ber(7/10))`. -/
noncomputable abbrev exampleSwap : Kernel Bool ℝ :=
  bernoulliBandit (fun b : Bool ↦ if b then pFive else pSeven)

/-- The alternative `(Ber(7/10), Ber(9/10))`, which moves the arm `false` of `exampleInst` only. -/
noncomputable abbrev exampleAlt : Kernel Bool ℝ :=
  bernoulliBandit (fun b : Bool ↦ if b then pSeven else pNine)

lemma gap_bernoulliBandit_bool (f : Bool → I) (a : Bool) :
    gap (bernoulliBandit f) a = max (f true : ℝ) (f false) - f a := by
  simp only [gap, integral_id_bernoulliBandit, iSup_bool_real]

lemma gap_exampleInst_false : gap exampleInst false = 1 / 5 := by
  rw [gap_bernoulliBandit_bool]; simp [pSeven, pFive]; norm_num

lemma gap_exampleAlt_true : gap exampleAlt true = 1 / 5 := by
  rw [gap_bernoulliBandit_bool]; simp [pSeven, pNine]; norm_num

/-- The arm `true` is the unique optimal arm of `exampleInst`. -/
lemma exampleInst_unique : ∀ a ≠ true, 0 < gap exampleInst a := by
  intro a ha
  cases a
  · rw [gap_exampleInst_false]; norm_num
  · exact absurd rfl ha

lemma bernoulliBandit_bool_mem (f : Bool → I) :
    ∀ a, IsProbabilityMeasure (bernoulliBandit f a) ∧ Integrable id (bernoulliBandit f a) :=
  fun a ↦ unitLaws_subset_finiteMean _ (bernoulliBandit_mem_productClass f a)

/-- `thm:main`: the unstructured class of laws on `[0, 1]` and the instance `exampleInst`. -/
lemma gravesLai_productClass_satisfiable :
    ∃ (D : Bool → Set (Measure ℝ)) (ν : Kernel Bool ℝ) (aStar : Bool),
      (∀ a, ∀ Q ∈ D a, IsProbabilityMeasure Q ∧ Integrable id Q) ∧ ν ∈ productClass D ∧
        ∀ a ≠ aStar, 0 < gap ν a :=
  ⟨fun _ ↦ unitLaws, exampleInst, true, fun _ ↦ unitLaws_subset_finiteMean,
    bernoulliBandit_mem_productClass _, exampleInst_unique⟩

lemma exampleSwap_true_ne : exampleSwap true ≠ exampleInst true := by
  intro h
  have := congrArg (fun Q : Measure ℝ ↦ ∫ x, id x ∂Q) h
  simp only [integral_id_bernoulliBandit] at this
  simp [pFive, pSeven] at this
  norm_num at this

/-- `prop:gl-zero`: the class `{exampleInst, exampleSwap}`, in which the law of the arm `true`
identifies the instance, and the instance `exampleInst`. -/
lemma gravesLai_eq_zero_of_identifies_satisfiable :
    ∃ (E : Set (Kernel Bool ℝ)) (ν : Kernel Bool ℝ) (aStar : Bool),
      (∀ ν' ∈ E, ∀ a, IsProbabilityMeasure (ν' a) ∧ Integrable id (ν' a)) ∧
      (∀ a, IsProbabilityMeasure (ν a) ∧ Integrable id (ν a)) ∧
      (∀ a ≠ aStar, 0 < gap ν a) ∧ (∀ ν' ∈ E, ν' aStar = ν aStar → ν' = ν) ∧
      ν ∈ E ∧ exampleSwap ∈ E ∧ exampleSwap ≠ ν := by
  refine ⟨{exampleInst, exampleSwap}, exampleInst, true, ?_, bernoulliBandit_bool_mem _,
    exampleInst_unique, ?_, by simp, by simp, fun h ↦ exampleSwap_true_ne (h ▸ rfl)⟩
  · rintro ν' (rfl | rfl)
    · exact bernoulliBandit_bool_mem _
    · exact bernoulliBandit_bool_mem _
  · rintro ν' (rfl | rfl) h
    · rfl
    · exact absurd h exampleSwap_true_ne

/-- `exampleAlt` is an alternative to `exampleInst` in the unstructured class of laws on
`[0, 1]`. -/
lemma exampleAlt_mem_alt :
    exampleAlt ∈ alt (productClass fun _ : Bool ↦ unitLaws) exampleInst := by
  refine ⟨bernoulliBandit_mem_productClass _, fun a ha ↦ ?_⟩
  cases a
  · rw [gap_exampleInst_false] at ha; norm_num at ha
  · rw [gap_exampleAlt_true]; norm_num

/-- The Graves–Lai constant of `exampleInst` in the unstructured class of laws on `[0, 1]` is
positive. -/
lemma gravesLai_unitLaws_exampleInst_pos :
    0 < gravesLai (productClass fun _ : Bool ↦ unitLaws) exampleInst := by
  have h := div_klDiv_le_gravesLai exampleAlt_mem_alt (b := false) (fun a ha ↦ by
    cases a
    · exact absurd rfl ha
    · simp [bernoulliBandit_apply])
  refine lt_of_lt_of_le ?_ h
  rw [ENNReal.div_pos_iff, gap_exampleInst_false]
  refine ⟨by norm_num, ?_⟩
  simp only [bernoulliBandit_apply, Bool.false_eq_true, ↓reduceIte,
    LMLExplore.klDiv_bernoulliMeasure]
  refine (LMLExplore.klBer_ne_top_iff pFive.2 pNine.2).mpr ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp [pNine] at h
  · simp [pNine] at h; norm_num at h

/-- `cor:lower`: the model `unitLaws`, KL-UCB, the instance `exampleInst` and `c = 0`. -/
lemma lower_bound_gravesLai_satisfiable :
    ∃ (D : Set (Measure ℝ)) (alg : Algorithm Unit Bool ℝ) (ν : Kernel Bool ℝ) (aStar : Bool)
      (c : ℝ), (∀ Q ∈ D, IsProbabilityMeasure Q ∧ Integrable id Q) ∧
      IsConsistent alg (productClass fun _ : Bool ↦ D) ∧ IsMarkovKernel ν ∧
      ν ∈ productClass (fun _ : Bool ↦ D) ∧ (∀ a ≠ aStar, 0 < gap ν a) ∧
      ENNReal.ofReal c < gravesLai (productClass fun _ : Bool ↦ D) ν :=
  ⟨unitLaws, klucb, exampleInst, true, 0, unitLaws_subset_finiteMean,
    KLUCB.isConsistent.mono fun _ hν a ↦ (hν a).2, inferInstance,
    bernoulliBandit_mem_productClass _, exampleInst_unique,
    by simpa using gravesLai_unitLaws_exampleInst_pos⟩

/-- `lem:constant` (consistency part): the unstructured class of laws on `[0, 1]`, the instance
`exampleInst` and the arm `b = false`, suboptimal in it. -/
lemma not_isConsistent_const_satisfiable :
    ∃ (E : Set (Kernel Bool ℝ)) (ν : Kernel Bool ℝ) (b : Bool), IsMarkovKernel ν ∧ ν ∈ E ∧
      (∀ a, Integrable id (ν a)) ∧ 0 < gap ν b :=
  ⟨productClass fun _ : Bool ↦ unitLaws, exampleInst, false, inferInstance,
    bernoulliBandit_mem_productClass _, fun a ↦ (bernoulliBandit_bool_mem _ a).2,
    exampleInst_unique false (by decide)⟩

/-- `lem:constant` (uniform fast convergence): the same class, instance and arm as for
consistency. -/
lemma not_isUniformlyFastConvergent_const_satisfiable :
    ∃ (E : Set (Kernel Bool ℝ)) (ν : Kernel Bool ℝ) (b : Bool), IsMarkovKernel ν ∧ ν ∈ E ∧
      (∀ a, Integrable id (ν a)) ∧ 0 < gap ν b :=
  not_isConsistent_const_satisfiable

/-- `lem:constant` (uniform super-fast convergence): the same class, instance and arm as for
consistency. -/
lemma not_isUniformlySuperFastConvergent_const_satisfiable :
    ∃ (E : Set (Kernel Bool ℝ)) (ν : Kernel Bool ℝ) (b : Bool), IsMarkovKernel ν ∧ ν ∈ E ∧
      (∀ a, Integrable id (ν a)) ∧ 0 < gap ν b :=
  not_isConsistent_const_satisfiable

/-! ### `prop:ucb` -/

/-- `prop:ucb`, finite-time bound: `hoeffdingUCB`, the instance `exampleInst`, its suboptimal arm
`false` and `T = 1`. -/
lemma ucb_pullCount_le_satisfiable :
    ∃ (alg : Algorithm Unit Bool ℝ) (ν : Kernel Bool ℝ) (a : Bool) (T : ℕ),
      IsHoeffdingUCB alg ∧ IsMarkovKernel ν ∧ ν ∈ productClass (fun _ : Bool ↦ unitLaws) ∧
        0 < gap ν a ∧ 1 ≤ T :=
  ⟨hoeffdingUCB, exampleInst, false, 1, isHoeffdingUCB_hoeffdingUCB, inferInstance,
    bernoulliBandit_mem_productClass _, exampleInst_unique false (by decide), le_rfl⟩

/-- `prop:ucb-tails`: `hoeffdingUCB`, the instance `exampleInst`, its suboptimal arm `false` and
`T = 2`. -/
lemma ucb_tail_pullCount_satisfiable :
    ∃ (alg : Algorithm Unit Bool ℝ) (ν : Kernel Bool ℝ) (a : Bool) (T : ℕ),
      IsHoeffdingUCB alg ∧ IsMarkovKernel ν ∧ ν ∈ productClass (fun _ : Bool ↦ unitLaws) ∧
        0 < gap ν a ∧ 2 ≤ T :=
  ⟨hoeffdingUCB, exampleInst, false, 2, isHoeffdingUCB_hoeffdingUCB, inferInstance,
    bernoulliBandit_mem_productClass _, exampleInst_unique false (by decide), le_rfl⟩

/-- The hypothesis of the other three statements of `prop:ucb`: a `UCB` learner exists. -/
lemma exists_isHoeffdingUCB : ∃ alg : Algorithm Unit Bool ℝ, IsHoeffdingUCB alg :=
  ⟨hoeffdingUCB, isHoeffdingUCB_hoeffdingUCB⟩

/-- `prop:ucb`, super-fast convergence: `hoeffdingUCB`. -/
lemma ucb_isUniformlySuperFastConvergent_satisfiable :
    ∃ alg : Algorithm Unit Bool ℝ, IsHoeffdingUCB alg :=
  exists_isHoeffdingUCB

/-- `prop:ucb`, consistency: `hoeffdingUCB`. -/
lemma ucb_isConsistent_satisfiable : ∃ alg : Algorithm Unit Bool ℝ, IsHoeffdingUCB alg :=
  exists_isHoeffdingUCB

/-- `prop:ucb`, fast convergence: `hoeffdingUCB`. -/
lemma ucb_isUniformlyFastConvergent_satisfiable :
    ∃ alg : Algorithm Unit Bool ℝ, IsHoeffdingUCB alg :=
  exists_isHoeffdingUCB

end Incognita.P007
