/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.Wald
public import TauCeti.MeasureTheory.Measure.PiWithDensity

/-! # The law of the source data of a size rule

[INC-P003, lem:source-law], in the form used by the proof of prop:source-kl: on the event
`{N' = n}` of a size rule, the law of the source data under `P'_{ν'}` has, with respect to its law
under `P'_{ν₂'}`, the density `∏_k ∏_{j < n_k} (dν'_k/dν₂'_k)(X'_{k,j})`.

## Main statements

* `sourceLaw_eq_withDensity`: [INC-P003, lem:source-law]: if the sizes of the arms of `Z` vanish
  almost surely under `P'_{ν'}` and `ν'_k ≪ ν₂'_k` for the other arms, the law of the source data
  under `ν'` has the density `1{s_k = 0 for k ∈ Z} ∏_k ∏_{j < n_k(s)} (dν'_k/dν₂'_k)(x_{k,j})` with
  respect to its law under `ν₂'`.
* `map_boxRestrict_sourceMeasure`: the randomisation and the values of the box of `n` have law
  `volume^{⊗ℕ} ⊗ ⊗_k ⊗_{j < n_k} ν'_k`.
* `sourceMeasure_preimage_boxRestrict`: for `F` measurable,
  `P'_{ν'}(boxRestrict n ∈ F) = ∫_{boxRestrict n ∈ F} ∏_k ∏_{j < n_k} r_k(X'_{k,j}) dP'_{ν₂'}`
  when `ν'_k ≪ ν₂'_k` for the arms with `n_k > 0`, `r_k = dν'_k/dν₂'_k`.

A finite product of measures with densities has the product density: this is Tau Ceti's
`TauCeti.pi_withDensity`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

open scoped ENNReal unitInterval

namespace Incognita.TransferBandits

variable {α : Type*} [MeasurableSpace α]

/-- The randomisation and the values of the box of `n` have law
`volume^{⊗ℕ} ⊗ ⊗_k ⊗_{j < n_k} ν'_k` under `P'_{ν'}`. -/
lemma map_boxRestrict_sourceMeasure [Fintype α] (ν' : Kernel α ℝ) [IsMarkovKernel ν']
    (n : α → ℕ) :
    (sourceMeasure ν').map (boxRestrict n) =
      (Measure.infinitePi fun _ : ℕ ↦ (volume : Measure I)).prod
        (Measure.pi fun a ↦ Measure.pi fun _ : Fin (n a) ↦ ν' a) := by
  have h : boxRestrict (α := α) n =
      Prod.map id (fun z : α → ℕ → ℝ ↦ fun a (i : Fin (n a)) ↦ z a i) := rfl
  rw [h, sourceMeasure, ← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id]
  congr 1
  have hpi := Measure.infinitePi_map_pi (μ := fun a : α ↦ Measure.infinitePi fun _ : ℕ ↦ ν' a)
    (f := fun a (w : ℕ → ℝ) (i : Fin (n a)) ↦ w i) (fun a ↦ by fun_prop)
  refine hpi.trans ?_
  rw [Measure.infinitePi_eq_pi]
  congr 1
  funext a
  rw [Measure.map_infinitePi_infinitePi_of_inj (f := (Fin.val : Fin (n a) → ℕ)) Fin.val_injective,
    Measure.infinitePi_eq_pi]

/-- On the box of `n`, the law of the values under `ν'` has the product density
`∏_k ∏_{j < n_k} r_k` with respect to their law under `ν₂'`, where `r_k = dν'_k/dν₂'_k`, as soon
as `ν'_k ≪ ν₂'_k` for the arms with `n_k > 0`. -/
lemma pi_pi_eq_withDensity [Fintype α] (ν' ν₂' : Kernel α ℝ) [IsMarkovKernel ν']
    [IsMarkovKernel ν₂'] (n : α → ℕ) (hac : ∀ a, 0 < n a → ν' a ≪ ν₂' a) :
    (Measure.pi fun a ↦ Measure.pi fun _ : Fin (n a) ↦ ν' a) =
      (Measure.pi fun a ↦ Measure.pi fun _ : Fin (n a) ↦ ν₂' a).withDensity
        (fun y ↦ ∏ a, ∏ i, (ν' a).rnDeriv (ν₂' a) (y a i)) := by
  have hfin : ∀ a, IsFiniteMeasure ((ν₂' a).withDensity ((ν' a).rnDeriv (ν₂' a))) := fun a ↦
    isFiniteMeasure_of_le _ (Measure.withDensity_rnDeriv_le _ _)
  have hinner : ∀ a, (Measure.pi fun _ : Fin (n a) ↦ ν' a) =
      (Measure.pi fun _ : Fin (n a) ↦ ν₂' a).withDensity
        (fun y ↦ ∏ i, (ν' a).rnDeriv (ν₂' a) (y i)) := fun a ↦ by
    rw [← TauCeti.pi_withDensity (fun _ : Fin (n a) ↦ ν₂' a)
      (f := fun _ ↦ (ν' a).rnDeriv (ν₂' a)) (fun _ ↦ Measure.measurable_rnDeriv _ _)]
    rcases Nat.eq_zero_or_pos (n a) with h0 | hpos
    · have : IsEmpty (Fin (n a)) := by rw [h0]; infer_instance
      rw [Measure.pi_of_empty, Measure.pi_of_empty]
    · rw [Measure.withDensity_rnDeriv_eq _ _ (hac a hpos)]
  have hsf : ∀ a, SigmaFinite ((Measure.pi fun _ : Fin (n a) ↦ ν₂' a).withDensity
      (fun y ↦ ∏ i, (ν' a).rnDeriv (ν₂' a) (y i))) := fun a ↦ by
    rw [← hinner a]
    infer_instance
  simp_rw [hinner]
  exact TauCeti.pi_withDensity _ fun a ↦ Finset.measurable_prod _ fun i _ ↦
    (Measure.measurable_rnDeriv _ _).comp (measurable_pi_apply i)

/-- **Change of measure on the box** [INC-P003, proof of lem:source-law]: for a measurable `F`,
`P'_{ν'}(boxRestrict n ∈ F) = ∫_{boxRestrict n ∈ F} ∏_k ∏_{j < n_k} r_k(X'_{k,j}) dP'_{ν₂'}`, as
soon as `ν'_k ≪ ν₂'_k` for the arms with `n_k > 0`. -/
lemma sourceMeasure_preimage_boxRestrict [Fintype α] (ν' ν₂' : Kernel α ℝ) [IsMarkovKernel ν']
    [IsMarkovKernel ν₂'] (n : α → ℕ) (hac : ∀ a, 0 < n a → ν' a ≪ ν₂' a)
    {F : Set ((ℕ → I) × ((a : α) → Fin (n a) → ℝ))} (hF : MeasurableSet F) :
    sourceMeasure ν' (boxRestrict n ⁻¹' F) =
      ∫⁻ ω in boxRestrict n ⁻¹' F, ∏ a, ∏ i : Fin (n a), (ν' a).rnDeriv (ν₂' a) (ω.2 a i)
        ∂(sourceMeasure ν₂') := by
  have hbox : Measurable (boxRestrict (α := α) n) := measurable_boxRestrict n
  have hG : Measurable fun y : (a : α) → Fin (n a) → ℝ ↦
      ∏ a, ∏ i, (ν' a).rnDeriv (ν₂' a) (y a i) :=
    Finset.measurable_prod _ fun a _ ↦ Finset.measurable_prod _ fun i _ ↦
      (Measure.measurable_rnDeriv _ _).comp ((measurable_pi_apply i).comp (measurable_pi_apply a))
  rw [← Measure.map_apply hbox hF, map_boxRestrict_sourceMeasure, pi_pi_eq_withDensity ν' ν₂' n hac,
    prod_withDensity_right hG, ← map_boxRestrict_sourceMeasure ν₂' n,
    withDensity_apply _ hF]
  exact setLIntegral_map (f := fun y : (ℕ → I) × ((a : α) → Fin (n a) → ℝ) ↦
    ∏ a, ∏ i, (ν' a).rnDeriv (ν₂' a) (y.2 a i)) hF (hG.comp measurable_snd) hbox

omit [MeasurableSpace α] in
/-- On the event that the sizes are `n`, the source data are a measurable function of the
randomisation and of the values of the box of `n`. -/
lemma sourceData_eq_of_eq {N : SourceSpace α → α → ℕ} {n : α → ℕ} {ω : SourceSpace α}
    (h : N ω = n) :
    sourceData N ω = (n, fun a j ↦ if hj : j < n a then (boxRestrict n ω).2 a ⟨j, hj⟩ else 0) := by
  simp only [sourceData, h, Prod.mk.injEq, true_and]
  funext a j
  split_ifs <;> rfl

/-- The density `ℓ` of the law of the source data is measurable. -/
lemma measurable_sourceDensity [Fintype α] (ν' ν₂' : Kernel α ℝ) (Z : Finset α) :
    Measurable fun s : Source α ↦ if ∀ a ∈ Z, s.1 a = 0 then
      ∏ a, ∏ j ∈ Finset.range (s.1 a), (ν' a).rnDeriv (ν₂' a) (s.2 a j) else 0 := by
  refine measurable_from_prod_countable_right fun m ↦ ?_
  dsimp only [Function.comp_def]
  split_ifs
  · exact Finset.measurable_prod _ fun a _ ↦ Finset.measurable_prod _ fun j _ ↦
      (Measure.measurable_rnDeriv _ _).comp (by fun_prop : Measurable fun x : α → ℕ → ℝ ↦ x a j)
  · exact measurable_const

/-- **Law of the source data** [INC-P003, lem:source-law]: for a size rule `N'`, a set `Z` of arms
whose sizes vanish almost surely under `P'_{ν'}`, and `ν'_k ≪ ν₂'_k` for the other arms, the law
of the source data under `ν'` has the density
`ℓ(s) = 1{s_k = 0 for k ∈ Z} ∏_k ∏_{j < n_k(s)} (dν'_k/dν₂'_k)(x_{k,j})` with respect to its law
under `ν₂'`. -/
lemma sourceLaw_eq_withDensity [Fintype α] {N : SourceSpace α → α → ℕ} (hN : IsSizeRule N)
    (ν' ν₂' : Kernel α ℝ) [IsMarkovKernel ν'] [IsMarkovKernel ν₂'] (Z : Finset α)
    (hZ : ∀ a ∈ Z, ∀ᵐ ω ∂(sourceMeasure ν'), N ω a = 0) (hac : ∀ a ∉ Z, ν' a ≪ ν₂' a) :
    sourceLaw ν' N = (sourceLaw ν₂' N).withDensity (fun s ↦ if ∀ a ∈ Z, s.1 a = 0 then
        ∏ a, ∏ j ∈ Finset.range (s.1 a), (ν' a).rnDeriv (ν₂' a) (s.2 a j) else 0) := by
  have hℓ := measurable_sourceDensity ν' ν₂' Z
  have hD := measurable_sourceData hN.measurable
  have hbox : ∀ n : α → ℕ, Measurable (boxRestrict (α := α) n) := measurable_boxRestrict
  -- On a measurable `A`, split `{sourceData N ∈ A}` along the values `n` of `N`; on `{N = n}`, an
  -- event of the box `𝒢_n`, the density of `ν'` against `ν₂'` is the product of the `n` first
  -- likelihood ratios (`sourceMeasure_preimage_boxRestrict`).
  ext A hA
  rw [withDensity_apply _ hA, sourceLaw, sourceLaw, Measure.map_apply hD hA,
    setLIntegral_map hA hℓ hD]
  have hEq : ∀ n : α → ℕ, MeasurableSet {ω : SourceSpace α | N ω = n} := fun n ↦
    hN.measurable (measurableSet_singleton n)
  have hcover : sourceData N ⁻¹' A = ⋃ n : α → ℕ, (sourceData N ⁻¹' A ∩ {ω | N ω = n}) := by
    ext ω
    simp
  have hdisj : Pairwise (Function.onFun Disjoint
      fun n : α → ℕ ↦ sourceData N ⁻¹' A ∩ {ω | N ω = n}) := by
    intro n m hnm
    refine Set.disjoint_left.mpr fun ω h1 h2 ↦ hnm ?_
    exact (h1.2 : N ω = n).symm.trans h2.2
  have hmeasE : ∀ n, MeasurableSet (sourceData N ⁻¹' A ∩ {ω | N ω = n}) := fun n ↦
    (hD hA).inter (hEq n)
  rw [hcover, measure_iUnion hdisj hmeasE, lintegral_iUnion hmeasE hdisj]
  refine tsum_congr fun n ↦ ?_
  by_cases hadm : ∀ a ∈ Z, n a = 0
  · -- `n` vanishes on `Z`: `{N = n}` is the preimage of some `G` under the box restriction
    obtain ⟨G, hG, hGeq⟩ := hN.measurableSet_eq n
    have hφ : Measurable fun y : (ℕ → I) × ((a : α) → Fin (n a) → ℝ) ↦
        ((n, fun a j ↦ if hj : j < n a then y.2 a ⟨j, hj⟩ else 0) : Source α) := by
      refine measurable_const.prodMk (measurable_pi_iff.mpr fun a ↦
        measurable_pi_iff.mpr fun j ↦ ?_)
      by_cases hj : j < n a
      · simp only [hj, ↓reduceDIte]
        fun_prop
      · simp only [hj, ↓reduceDIte]
        exact measurable_const
    have hmemG : ∀ ω, ω ∈ boxRestrict n ⁻¹' G ↔ N ω = n := fun ω ↦ by
      rw [hGeq]
      rfl
    have hset : sourceData N ⁻¹' A ∩ {ω | N ω = n} = boxRestrict n ⁻¹' (G ∩
        (fun y : (ℕ → I) × ((a : α) → Fin (n a) → ℝ) ↦
          ((n, fun a j ↦ if hj : j < n a then y.2 a ⟨j, hj⟩ else 0) : Source α)) ⁻¹' A) := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨(hmemG ω).mpr h2, ?_⟩
        rw [← sourceData_eq_of_eq h2]
        exact h1
      · rintro ⟨h1, h2⟩
        have hn : N ω = n := (hmemG ω).mp h1
        exact ⟨by rw [sourceData_eq_of_eq hn]; exact h2, hn⟩
    have hac' : ∀ a, 0 < n a → ν' a ≪ ν₂' a := fun a ha ↦ hac a fun hz ↦ by
      have := hadm a hz
      omega
    rw [hset, sourceMeasure_preimage_boxRestrict ν' ν₂' n hac' (hG.inter (hφ hA))]
    refine setLIntegral_congr_fun ((hbox n) (hG.inter (hφ hA))) fun ω hω ↦ ?_
    have hn : N ω = n := (hmemG ω).mp hω.1
    -- the density at the source data `(n, x)`, whose values `x` are read in the box
    rw [sourceData_eq_of_eq hn]
    simp only
    rw [ite_eq_left hadm]
    refine Finset.prod_congr rfl fun a _ ↦ ?_
    rw [Finset.prod_range]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [dite_eq_left i.2]
    -- `(boxRestrict n ω).2 a i = ω.2 a i`, by definition of `boxRestrict`
    rfl
  · -- `n a ≠ 0` for some `a ∈ Z`: `{N = n}` is null under `ν'` and the density vanishes on it
    push Not at hadm
    obtain ⟨a, haZ, hna⟩ := hadm
    have h0 : sourceMeasure ν' (sourceData N ⁻¹' A ∩ {ω | N ω = n}) = 0 := by
      refine measure_mono_null (fun ω hω ↦ ?_) (ae_iff.mp (hZ a haZ))
      simp only [Set.mem_ofPred_eq]
      rw [(hω.2 : N ω = n)]
      exact hna
    rw [h0]
    symm
    refine (setLIntegral_congr_fun (hmeasE n) fun ω hω ↦ ?_).trans (lintegral_zero)
    have hn : N ω = n := hω.2
    rw [sourceData_eq_of_eq hn]
    simp only
    refine ite_eq_right ?_
    push Not
    exact ⟨a, haZ, hna⟩

end Incognita.TransferBandits
