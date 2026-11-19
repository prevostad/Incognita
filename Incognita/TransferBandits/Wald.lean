/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.Setting
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Independence.Integration

/-! # Wald's identity for size rules

[INC-P003, lem:wald]: for a size rule `N'`, an arm `k` and a measurable `φ ≥ 0`,
`E_{ν'}[∑_{j < N'_k} φ(X'_{k,j})] = E_{ν'}[N'_k] ∫ φ dν'_k` (0-based indices).

The proof is that of Wald's identity [W44] (to be checked), with a stopping point in place of a
stopping time: the event `{j < N'_k}` is the complement of the countable union of the events
`{N' = n}` with `n_k ≤ j`, each of which reads only the randomisation and the values of the box of
`n`, which does not contain `(k, j)`; so it is independent of `X'_{k,j}` (the coordinates of the
stacks are independent).

## Main statements

* `iIndepFun_stacks`: the values of the stacks are independent under `⊗_{k,j} ν'_k`.
* `measurable_sizeRule_section_lt`: for a fixed randomisation, `{j < N'_k}` is measurable with
  respect to the values other than `X'_{k,j}`.
* `lintegral_indicator_lt_mul`: `E[1{j < N'_k} φ(X'_{k,j})] = P(j < N'_k) ∫ φ dν'_k`.
* `lintegral_sum_range_sizeRule`: Wald's identity.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

open scoped ENNReal unitInterval

namespace Incognita.TransferBandits

variable {α : Type*} [MeasurableSpace α]

/-- The values of the stacks are independent under `⊗_{k,j} ν'_k`. -/
lemma iIndepFun_stacks (ν' : Kernel α ℝ) [IsMarkovKernel ν'] :
    iIndepFun (fun (p : α × ℕ) (z : α → ℕ → ℝ) ↦ z p.1 p.2)
      (Measure.infinitePi fun a : α ↦ Measure.infinitePi fun _ : ℕ ↦ ν' a) := by
  have := iIndepFun_uncurry_infinitePi' (Ω := fun (_ : α) (_ : ℕ) ↦ ℝ)
    (𝓧 := fun (_ : α) (_ : ℕ) ↦ ℝ) (X := fun _ _ x ↦ x) (fun a (_ : ℕ) ↦ ν' a)
    (fun _ _ ↦ measurable_id)
  exact this

/-- The σ-algebra of the values of the stacks other than `X'_{k,j}`. -/
lemma indep_rest_coord (ν' : Kernel α ℝ) [IsMarkovKernel ν'] (k : α) (j : ℕ) :
    Indep (⨆ p ∈ ({(k, j)}ᶜ : Set (α × ℕ)),
        MeasurableSpace.comap (fun z : α → ℕ → ℝ ↦ z p.1 p.2) inferInstance)
      (⨆ p ∈ ({(k, j)} : Set (α × ℕ)),
        MeasurableSpace.comap (fun z : α → ℕ → ℝ ↦ z p.1 p.2) inferInstance)
      (Measure.infinitePi fun a : α ↦ Measure.infinitePi fun _ : ℕ ↦ ν' a) := by
  have hi : iIndep (fun p : α × ℕ ↦
      MeasurableSpace.comap (fun z : α → ℕ → ℝ ↦ z p.1 p.2) inferInstance)
      (Measure.infinitePi fun a : α ↦ Measure.infinitePi fun _ : ℕ ↦ ν' a) :=
    (iIndepFun_stacks ν').iIndep
  exact indep_iSup_of_disjoint (m := fun p : α × ℕ ↦
      MeasurableSpace.comap (fun z : α → ℕ → ℝ ↦ z p.1 p.2) inferInstance)
    (fun p ↦ (show Measurable (fun z : α → ℕ → ℝ ↦ z p.1 p.2) by fun_prop).comap_le)
    hi disjoint_compl_left

omit [MeasurableSpace α] in
/-- For a size rule and a fixed randomisation `u`, the event `{j < N'_k}` reads only the values
other than `X'_{k,j}`. -/
lemma measurable_sizeRule_section_lt [Finite α] {N : SourceSpace α → α → ℕ} (hN : IsSizeRule N)
    (u : ℕ → I) (k : α) (j : ℕ) :
    MeasurableSet[⨆ p ∈ ({(k, j)}ᶜ : Set (α × ℕ)),
        MeasurableSpace.comap (fun z : α → ℕ → ℝ ↦ z p.1 p.2) inferInstance]
      {z | j < N (u, z) k} := by
  set M := ⨆ p ∈ ({(k, j)}ᶜ : Set (α × ℕ)),
    MeasurableSpace.comap (fun z : α → ℕ → ℝ ↦ z p.1 p.2) inferInstance
  have hset : {z : α → ℕ → ℝ | j < N (u, z) k} =
      (⋃ n : {n : α → ℕ // n k ≤ j}, {z | N (u, z) = n.1})ᶜ := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    constructor
    · rintro h ⟨n, hn⟩ hz
      have h2 : N (u, z) k = n k := congrFun hz k
      omega
    · intro h
      by_contra h'
      exact h ⟨N (u, z), not_lt.mp h'⟩ rfl
  rw [hset]
  refine MeasurableSet.compl (MeasurableSet.iUnion fun n ↦ ?_)
  obtain ⟨G, hG, hGeq⟩ := hN.measurableSet_eq n.1
  have hbox : Measurable[M] fun z : α → ℕ → ℝ ↦
      boxRestrict n.1 ((u, z) : SourceSpace α) := by
    change Measurable[M] fun z : α → ℕ → ℝ ↦ (u, fun b (i : Fin (n.1 b)) ↦ z b i)
    refine Measurable.prodMk measurable_const ?_
    refine measurable_pi_iff.mpr fun b ↦ ?_
    refine measurable_pi_iff.mpr fun i ↦ ?_
    have hmem : (b, (i : ℕ)) ∈ ({(k, j)}ᶜ : Set (α × ℕ)) := by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Prod.mk.injEq, not_and]
      intro hb
      subst hb
      have h1 := i.2
      have h2 := n.2
      omega
    exact (comap_measurable (fun z : α → ℕ → ℝ ↦ z b i)).mono
      (le_iSup₂ (f := fun p (_ : p ∈ ({(k, j)}ᶜ : Set (α × ℕ))) ↦
        MeasurableSpace.comap (fun z : α → ℕ → ℝ ↦ z p.1 p.2) inferInstance) (b, (i : ℕ)) hmem)
      le_rfl
  have : {z : α → ℕ → ℝ | N (u, z) = n.1} =
      (fun z : α → ℕ → ℝ ↦ boxRestrict n.1 ((u, z) : SourceSpace α)) ⁻¹' G := by
    ext z
    have := congrArg (fun s : Set (SourceSpace α) ↦ (u, z) ∈ s) hGeq
    simp only [Set.mem_preimage, eq_iff_iff] at this
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    exact this.symm
  rw [this]
  exact hbox hG

/-- Under the stacks' law, `∫ φ(X'_{k,j}) = ∫ φ dν'_k`. -/
lemma lintegral_stacks_coord (ν' : Kernel α ℝ) [IsMarkovKernel ν'] (k : α) (j : ℕ)
    {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ z, φ (z k j) ∂(Measure.infinitePi fun a : α ↦ Measure.infinitePi fun _ : ℕ ↦ ν' a) =
      ∫⁻ x, φ x ∂(ν' k) := by
  have h : (fun z : α → ℕ → ℝ ↦ z k j) = (fun w : ℕ → ℝ ↦ w j) ∘ (fun z : α → ℕ → ℝ ↦ z k) := rfl
  rw [← lintegral_map hφ (by fun_prop), h, ← Measure.map_map (by fun_prop) (by fun_prop),
    Measure.infinitePi_map_eval, Measure.infinitePi_map_eval]

/-- **Independence of `{j < N'_k}` and `X'_{k,j}`**: for a size rule,
`E[1{j < N'_k} φ(X'_{k,j})] = P(j < N'_k) ∫ φ dν'_k`. -/
lemma lintegral_indicator_lt_mul [Finite α] {N : SourceSpace α → α → ℕ} (hN : IsSizeRule N)
    (ν' : Kernel α ℝ) [IsMarkovKernel ν'] (k : α) (j : ℕ) {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ ω, (if j < N ω k then φ (ω.2 k j) else 0) ∂(sourceMeasure ν') =
      sourceMeasure ν' {ω | j < N ω k} * ∫⁻ x, φ x ∂(ν' k) := by
  set ρ := Measure.infinitePi fun a : α ↦ Measure.infinitePi fun _ : ℕ ↦ ν' a
  have hNk : Measurable fun ω : SourceSpace α ↦ N ω k := (measurable_pi_apply k).comp hN.measurable
  have hset : MeasurableSet {ω : SourceSpace α | j < N ω k} :=
    measurableSet_lt measurable_const hNk
  have hcoord : Measurable fun ω : SourceSpace α ↦ ω.2 k j := by fun_prop
  have hf : Measurable fun ω : SourceSpace α ↦ (if j < N ω k then φ (ω.2 k j) else 0) :=
    Measurable.ite hset (hφ.comp hcoord) measurable_const
  rw [sourceMeasure, lintegral_prod _ hf.aemeasurable, Measure.prod_apply hset]
  rw [← lintegral_mul_const _ (measurable_measure_prodMk_left hset)]
  refine lintegral_congr fun u ↦ ?_
  -- For a fixed randomisation, independence of the section and of the coordinate.
  have hrest := measurable_sizeRule_section_lt hN u k j
  have hcoordM : Measurable[⨆ p ∈ ({(k, j)} : Set (α × ℕ)),
      MeasurableSpace.comap (fun z : α → ℕ → ℝ ↦ z p.1 p.2) inferInstance]
      fun z : α → ℕ → ℝ ↦ φ (z k j) :=
    hφ.comp ((comap_measurable (fun z : α → ℕ → ℝ ↦ z k j)).mono
      (le_iSup₂ (f := fun p (_ : p ∈ ({(k, j)} : Set (α × ℕ))) ↦
        MeasurableSpace.comap (fun z : α → ℕ → ℝ ↦ z p.1 p.2) inferInstance) (k, j) rfl) le_rfl)
  have hle : ∀ (S : Set (α × ℕ)), (⨆ p ∈ S,
      MeasurableSpace.comap (fun z : α → ℕ → ℝ ↦ z p.1 p.2) inferInstance) ≤
      (inferInstance : MeasurableSpace (α → ℕ → ℝ)) := fun S ↦
    iSup₂_le fun p _ ↦ (show Measurable (fun z : α → ℕ → ℝ ↦ z p.1 p.2) by fun_prop).comap_le
  have heq : (fun z : α → ℕ → ℝ ↦ if j < N (u, z) k then φ (z k j) else 0) =
      fun z ↦ ({z : α → ℕ → ℝ | j < N (u, z) k}.indicator (fun _ ↦ (1 : ℝ≥0∞)) z) *
        φ (z k j) := by
    funext z
    by_cases h : j < N (u, z) k <;> simp [h, Set.indicator]
  simp only [heq]
  rw [lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace (hle _) (hle _)
      (indep_rest_coord ν' k j) (measurable_const.indicator hrest) hcoordM,
    lintegral_indicator_const ((hle _) _ hrest), one_mul, lintegral_stacks_coord ν' k j hφ]
  rfl

/-- A finite sum over `j < n` as a series of indicators. -/
lemma sum_range_eq_tsum_ite (n : ℕ) (f : ℕ → ℝ≥0∞) :
    ∑ j ∈ Finset.range n, f j = ∑' j, (if j < n then f j else 0) := by
  rw [tsum_eq_sum (s := Finset.range n) (fun j hj ↦ by simp_all)]
  exact Finset.sum_congr rfl fun j hj ↦ by simp [Finset.mem_range.mp hj]

/-- **Wald's identity for size rules** [INC-P003, lem:wald]: for a size rule `N'`, an arm `k` and
a measurable `φ ≥ 0`, `E_{ν'}[∑_{j < N'_k} φ(X'_{k,j})] = E_{ν'}[N'_k] ∫ φ dν'_k`. -/
lemma lintegral_sum_range_sizeRule [Finite α] {N : SourceSpace α → α → ℕ} (hN : IsSizeRule N)
    (ν' : Kernel α ℝ) [IsMarkovKernel ν'] (k : α) {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ ω, ∑ j ∈ Finset.range (N ω k), φ (ω.2 k j) ∂(sourceMeasure ν') =
      (∫⁻ ω, (N ω k : ℝ≥0∞) ∂(sourceMeasure ν')) * ∫⁻ x, φ x ∂(ν' k) := by
  have hNk : Measurable fun ω : SourceSpace α ↦ N ω k := (measurable_pi_apply k).comp hN.measurable
  have hmeas : ∀ (ψ : ℝ → ℝ≥0∞), Measurable ψ → ∀ j, Measurable fun ω : SourceSpace α ↦
      (if j < N ω k then ψ (ω.2 k j) else 0) := fun ψ hψ j ↦
    Measurable.ite (measurableSet_lt measurable_const hNk) (hψ.comp (by fun_prop))
      measurable_const
  have htsum : ∀ (ψ : ℝ → ℝ≥0∞), Measurable ψ →
      ∫⁻ ω, ∑ j ∈ Finset.range (N ω k), ψ (ω.2 k j) ∂(sourceMeasure ν') =
        (∑' j, sourceMeasure ν' {ω | j < N ω k}) * ∫⁻ x, ψ x ∂(ν' k) := fun ψ hψ ↦ by
    simp_rw [sum_range_eq_tsum_ite]
    rw [lintegral_tsum fun j ↦ (hmeas ψ hψ j).aemeasurable, ← ENNReal.tsum_mul_right]
    exact tsum_congr fun j ↦ lintegral_indicator_lt_mul hN ν' k j hψ
  have hN1 := htsum (fun _ ↦ 1) measurable_const
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, lintegral_const,
    measure_univ] at hN1
  rw [htsum φ hφ, hN1]

end Incognita.TransferBandits
