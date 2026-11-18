/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.SourceLaw
public import Incognita.TransferBandits.OnlineKL

/-! # The divergence of the source data of a size rule

[INC-P003, prop:source-kl]: for a size rule `N'` with `E_{ν'}[N'_k] < ∞` for every arm,
`KL(P^D_{ν',N'}, P^D_{ν₂',N'}) = ∑_k E_{ν'}[N'_k] KL(ν'_k, ν₂'_k)`.

## Main statements

* `integrable_sum_range_sizeRule`, `integral_sum_range_sizeRule`: Wald's identity for integrable
  real functions.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory

open scoped ENNReal unitInterval

namespace Incognita.TransferBandits

variable {α : Type*} [MeasurableSpace α]

omit [MeasurableSpace α] in
/-- The partial sums `∑_{j < N'_k} φ(X'_{k,j})` are measurable. -/
lemma measurable_sum_range_sizeRule {N : SourceSpace α → α → ℕ} (hN : Measurable N)
    (k : α) {E : Type*} [AddCommMonoid E] [MeasurableSpace E] [MeasurableAdd₂ E] {φ : ℝ → E}
    (hφ : Measurable φ) :
    Measurable fun ω : SourceSpace α ↦ ∑ j ∈ Finset.range (N ω k), φ (ω.2 k j) := by
  have hF : Measurable fun p : ℕ × SourceSpace α ↦ ∑ j ∈ Finset.range p.1, φ (p.2.2 k j) :=
    measurable_from_prod_countable_right fun m ↦ by
      simp only
      exact Finset.measurable_sum (f := fun j (y : SourceSpace α) ↦ φ (y.2 k j)) _
        fun j _ ↦ hφ.comp (by fun_prop)
  exact hF.comp (((measurable_pi_apply k).comp hN).prodMk measurable_id)

/-- **Wald's identity for size rules**, integrability: for a size rule with `E[N'_k] < ∞` and a
measurable `φ` integrable under `ν'_k`, `∑_{j < N'_k} φ(X'_{k,j})` is integrable. -/
lemma integrable_sum_range_sizeRule [Finite α] {N : SourceSpace α → α → ℕ} (hN : IsSizeRule N)
    (ν' : Kernel α ℝ) [IsMarkovKernel ν'] (k : α)
    (hNk : ∫⁻ ω, (N ω k : ℝ≥0∞) ∂(sourceMeasure ν') ≠ ∞) {φ : ℝ → ℝ} (hφm : Measurable φ)
    (hφ : Integrable φ (ν' k)) :
    Integrable (fun ω ↦ ∑ j ∈ Finset.range (N ω k), φ (ω.2 k j)) (sourceMeasure ν') := by
  refine ⟨(measurable_sum_range_sizeRule hN.measurable k hφm).aestronglyMeasurable, ?_⟩
  refine (lintegral_mono fun ω ↦ enorm_sum_le _ _).trans_lt ?_
  rw [lintegral_sum_range_sizeRule hN ν' k hφm.enorm]
  exact ENNReal.mul_lt_top hNk.lt_top hφ.2

/-- **Wald's identity for size rules** [INC-P003, lem:wald], real version: for a size rule with
`E[N'_k] < ∞` and a measurable `φ` integrable under `ν'_k`,
`E[∑_{j < N'_k} φ(X'_{k,j})] = E[N'_k] ∫ φ dν'_k`. -/
lemma integral_sum_range_sizeRule [Finite α] {N : SourceSpace α → α → ℕ} (hN : IsSizeRule N)
    (ν' : Kernel α ℝ) [IsMarkovKernel ν'] (k : α)
    (hNk : ∫⁻ ω, (N ω k : ℝ≥0∞) ∂(sourceMeasure ν') ≠ ∞) {φ : ℝ → ℝ} (hφm : Measurable φ)
    (hφ : Integrable φ (ν' k)) :
    ∫ ω, ∑ j ∈ Finset.range (N ω k), φ (ω.2 k j) ∂(sourceMeasure ν') =
      (∫⁻ ω, (N ω k : ℝ≥0∞) ∂(sourceMeasure ν')).toReal * ∫ x, φ x ∂(ν' k) := by
  -- Positive and negative parts.
  set φp : ℝ → ℝ := fun x ↦ max (φ x) 0
  set φn : ℝ → ℝ := fun x ↦ max (-φ x) 0
  have hφp : Measurable φp := hφm.max measurable_const
  have hφn : Measurable φn := hφm.neg.max measurable_const
  have hip : Integrable φp (ν' k) := hφ.pos_part
  have hin : Integrable φn (ν' k) := hφ.neg.pos_part
  have hsplit : ∀ x, φ x = φp x - φn x := fun x ↦ by
    simp only [φp, φn]
    rcases le_total (φ x) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]
      ring
    · rw [max_eq_left h, max_eq_right (by linarith)]
      ring
  have hpart : ∀ ψ : ℝ → ℝ, Measurable ψ → (∀ x, 0 ≤ ψ x) → Integrable ψ (ν' k) →
      ∫ ω, ∑ j ∈ Finset.range (N ω k), ψ (ω.2 k j) ∂(sourceMeasure ν') =
        (∫⁻ ω, (N ω k : ℝ≥0∞) ∂(sourceMeasure ν')).toReal * ∫ x, ψ x ∂(ν' k) :=
    fun ψ hψm hψ0 hψ ↦ by
      rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω ↦
          Finset.sum_nonneg fun j _ ↦ hψ0 _)
          (measurable_sum_range_sizeRule hN.measurable k hψm).aestronglyMeasurable,
        integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hψ0) hψm.aestronglyMeasurable,
        ← ENNReal.toReal_mul]
      congr 1
      simp_rw [ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ hψ0 _)]
      exact lintegral_sum_range_sizeRule hN ν' k hψm.ennreal_ofReal
  have hsum : ∀ ω : SourceSpace α, ∑ j ∈ Finset.range (N ω k), φ (ω.2 k j) =
      ∑ j ∈ Finset.range (N ω k), φp (ω.2 k j) - ∑ j ∈ Finset.range (N ω k), φn (ω.2 k j) :=
    fun ω ↦ by rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ ↦ hsplit _
  simp_rw [hsum]
  rw [integral_sub (integrable_sum_range_sizeRule hN ν' k hNk hφp hip)
      (integrable_sum_range_sizeRule hN ν' k hNk hφn hin),
    hpart φp hφp (fun x ↦ le_max_right _ _) hip, hpart φn hφn (fun x ↦ le_max_right _ _) hin,
    ← mul_sub, ← integral_sub hip hin]
  congr 1
  exact integral_congr_ae (ae_of_all _ fun x ↦ (hsplit x).symm)

/-- Under `P'_{ν'}`, the value `X'_{k,j}` has law `ν'_k`. -/
lemma map_eval_sourceMeasure (ν' : Kernel α ℝ) [IsMarkovKernel ν'] (k : α) (j : ℕ) :
    (sourceMeasure ν').map (fun ω : SourceSpace α ↦ ω.2 k j) = ν' k := by
  have h : (fun ω : SourceSpace α ↦ ω.2 k j) =
      (fun w : ℕ → ℝ ↦ w j) ∘ (fun z : α → ℕ → ℝ ↦ z k) ∘ Prod.snd := rfl
  rw [h, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_map (by fun_prop) measurable_snd, sourceMeasure, Measure.map_snd_prod,
    measure_univ, one_smul, Measure.infinitePi_map_eval, Measure.infinitePi_map_eval]

/-- **Divergence of the source data**, finite case [INC-P003, prop:source-kl]: for a size rule
with `E_{ν'}[N'_k] < ∞` for every arm, and `KL(ν'_k, ν₂'_k) < ∞` for the arms with
`E_{ν'}[N'_k] > 0`, `KL(P^D_{ν',N'}, P^D_{ν₂',N'}) = ∑_k E_{ν'}[N'_k] KL(ν'_k, ν₂'_k)`. -/
lemma klDiv_sourceLaw_of_ne_top [Fintype α] {N : SourceSpace α → α → ℕ} (hN : IsSizeRule N)
    (ν' ν₂' : Kernel α ℝ) [IsMarkovKernel ν'] [IsMarkovKernel ν₂']
    (hfin : ∀ a, ∫⁻ ω, (N ω a : ℝ≥0∞) ∂(sourceMeasure ν') ≠ ∞)
    (hKL : ∀ a, ∫⁻ ω, (N ω a : ℝ≥0∞) ∂(sourceMeasure ν') ≠ 0 → klDiv (ν' a) (ν₂' a) ≠ ∞) :
    klDiv (sourceLaw ν' N) (sourceLaw ν₂' N) =
      ∑ a, (∫⁻ ω, (N ω a : ℝ≥0∞) ∂(sourceMeasure ν')) * klDiv (ν' a) (ν₂' a) := by
  set P := sourceMeasure ν'
  set E : α → ℝ≥0∞ := fun a ↦ ∫⁻ ω, (N ω a : ℝ≥0∞) ∂P
  set Z : Finset α := Finset.univ.filter fun a ↦ E a = 0
  have hNa : ∀ a, Measurable fun ω : SourceSpace α ↦ N ω a := fun a ↦
    (measurable_pi_apply a).comp hN.measurable
  have hZ : ∀ a ∈ Z, ∀ᵐ ω ∂P, N ω a = 0 := fun a ha ↦ by
    have h0 : E a = 0 := (Finset.mem_filter.mp ha).2
    have := (lintegral_eq_zero_iff (measurable_from_top.comp (hNa a))).mp h0
    filter_upwards [this] with ω hω
    simpa using hω
  have hnZ : ∀ a ∉ Z, E a ≠ 0 := fun a ha h0 ↦ ha (Finset.mem_filter.mpr ⟨Finset.mem_univ a, h0⟩)
  have hac : ∀ a ∉ Z, ν' a ≪ ν₂' a := fun a ha ↦ (klDiv_ne_top_iff.mp (hKL a (hnZ a ha))).1
  have hint : ∀ a ∉ Z, Integrable (llr (ν' a) (ν₂' a)) (ν' a) := fun a ha ↦
    (klDiv_ne_top_iff.mp (hKL a (hnZ a ha))).2
  have hlaw := sourceLaw_eq_withDensity hN ν' ν₂' Z hZ hac
  set ℓ : Source α → ℝ≥0∞ := fun s ↦ if ∀ a ∈ Z, s.1 a = 0 then
    ∏ a, ∏ j ∈ Finset.range (s.1 a), (ν' a).rnDeriv (ν₂' a) (s.2 a j) else 0
  have hℓ : Measurable ℓ := measurable_sourceDensity ν' ν₂' Z
  have hD := measurable_sourceData hN.measurable
  have hllrm : ∀ a, Measurable (llr (ν' a) (ν₂' a)) := fun a ↦
    (Measure.measurable_rnDeriv _ _).ennreal_toReal.log
  -- The log-likelihood ratio of the source data, along the source space.
  set F : SourceSpace α → ℝ := fun ω ↦
    ∑ a, ∑ j ∈ Finset.range (N ω a), llr (ν' a) (ν₂' a) (ω.2 a j)
  have hpos : ∀ a ∉ Z, ∀ j, ∀ᵐ ω ∂P, 0 < (ν' a).rnDeriv (ν₂' a) (ω.2 a j) ∧
      (ν' a).rnDeriv (ν₂' a) (ω.2 a j) < ∞ := fun a ha j ↦ by
    refine ae_of_ae_map (p := fun x ↦ 0 < (ν' a).rnDeriv (ν₂' a) x ∧
      (ν' a).rnDeriv (ν₂' a) x < ∞) (by fun_prop) ?_
    rw [map_eval_sourceMeasure]
    filter_upwards [Measure.rnDeriv_pos (hac a ha),
      (hac a ha).ae_le (Measure.rnDeriv_lt_top (ν' a) (ν₂' a))] with x h1 h2 using ⟨h1, h2⟩
  have hae : ∀ᵐ ω ∂P, Real.log (ℓ (sourceData N ω)).toReal = F ω := by
    have h1 : ∀ᵐ ω ∂P, ∀ a ∈ Z, N ω a = 0 := by
      rw [ae_all_iff]
      intro a
      by_cases ha : a ∈ Z
      · filter_upwards [hZ a ha] with ω hω using fun _ ↦ hω
      · exact ae_of_all _ fun ω h ↦ absurd h ha
    have h2 : ∀ᵐ ω ∂P, ∀ a, a ∉ Z → ∀ j, 0 < (ν' a).rnDeriv (ν₂' a) (ω.2 a j) ∧
        (ν' a).rnDeriv (ν₂' a) (ω.2 a j) < ∞ := by
      rw [ae_all_iff]
      intro a
      by_cases ha : a ∈ Z
      · exact ae_of_all _ fun ω h ↦ absurd ha h
      · have : ∀ᵐ ω ∂P, ∀ j, 0 < (ν' a).rnDeriv (ν₂' a) (ω.2 a j) ∧
            (ν' a).rnDeriv (ν₂' a) (ω.2 a j) < ∞ := ae_all_iff.mpr (hpos a ha)
        filter_upwards [this] with ω hω using fun _ ↦ hω
    filter_upwards [h1, h2] with ω hω1 hω2
    have hcond : ∀ a ∈ Z, (sourceData N ω).1 a = 0 := hω1
    simp only [ℓ]
    rw [ite_eq_left hcond]
    have hfac : ∀ a, ∀ j ∈ Finset.range ((sourceData N ω).1 a),
        (ν' a).rnDeriv (ν₂' a) ((sourceData N ω).2 a j) = (ν' a).rnDeriv (ν₂' a) (ω.2 a j) :=
      fun a j hj ↦ by
        simp only [sourceData] at hj ⊢
        rw [ite_eq_left (Finset.mem_range.mp hj)]
    rw [Finset.prod_congr rfl fun a _ ↦ Finset.prod_congr rfl (hfac a), ENNReal.toReal_prod,
      Real.log_prod]
    · refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [ENNReal.toReal_prod, Real.log_prod]
      · rfl
      · intro j hj
        have hjN : j < N ω a := Finset.mem_range.mp hj
        have ha : a ∉ Z := fun ha ↦ by rw [hω1 a ha] at hjN; omega
        exact (ENNReal.toReal_pos (hω2 a ha j).1.ne' (hω2 a ha j).2.ne).ne'
    · intro a _
      rw [ENNReal.toReal_prod]
      refine Finset.prod_ne_zero_iff.mpr fun j hj ↦ ?_
      have hjN : j < N ω a := Finset.mem_range.mp hj
      have ha : a ∉ Z := fun ha ↦ by rw [hω1 a ha] at hjN; omega
      exact (ENNReal.toReal_pos (hω2 a ha j).1.ne' (hω2 a ha j).2.ne).ne'
  -- Each arm's term is integrable, with the expected value.
  have hterm : ∀ a, Integrable (fun ω ↦ ∑ j ∈ Finset.range (N ω a),
      llr (ν' a) (ν₂' a) (ω.2 a j)) P ∧
      ∫ ω, ∑ j ∈ Finset.range (N ω a), llr (ν' a) (ν₂' a) (ω.2 a j) ∂P =
        (E a).toReal * (klDiv (ν' a) (ν₂' a)).toReal := fun a ↦ by
    by_cases ha : a ∈ Z
    · have h0 : (fun ω ↦ ∑ j ∈ Finset.range (N ω a), llr (ν' a) (ν₂' a) (ω.2 a j)) =ᵐ[P] 0 := by
        filter_upwards [hZ a ha] with ω hω
        simp [hω]
      refine ⟨(integrable_zero _ _ _).congr h0.symm, ?_⟩
      rw [integral_congr_ae h0, (Finset.mem_filter.mp ha).2]
      simp
    · refine ⟨integrable_sum_range_sizeRule hN ν' a (hfin a) (hllrm a) (hint a ha), ?_⟩
      rw [integral_sum_range_sizeRule hN ν' a (hfin a) (hllrm a) (hint a ha),
        toReal_klDiv (hac a ha) (hint a ha), probReal_univ, probReal_univ, add_sub_cancel_right]
  have hFint : Integrable F P := integrable_finsetSum _ fun a _ ↦ (hterm a).1
  have hFval : ∫ ω, F ω ∂P = ∑ a, (E a).toReal * (klDiv (ν' a) (ν₂' a)).toReal := by
    rw [integral_finsetSum _ fun a _ ↦ (hterm a).1]
    exact Finset.sum_congr rfl fun a _ ↦ (hterm a).2
  -- The log-likelihood ratio of the laws of the source data.
  have hlogm : Measurable fun s : Source α ↦ Real.log (ℓ s).toReal := hℓ.ennreal_toReal.log
  have hac' : sourceLaw ν' N ≪ sourceLaw ν₂' N := by
    rw [hlaw]
    exact withDensity_absolutelyContinuous _ _
  have hllr : llr (sourceLaw ν' N) (sourceLaw ν₂' N) =ᵐ[sourceLaw ν' N]
      fun s ↦ Real.log (ℓ s).toReal := by
    have h := hac'.ae_le (Measure.rnDeriv_withDensity (sourceLaw ν₂' N) hℓ)
    rw [← hlaw] at h
    filter_upwards [h] with s hs
    rw [llr, hs]
  have hlogint : Integrable (fun s : Source α ↦ Real.log (ℓ s).toReal) (sourceLaw ν' N) := by
    rw [sourceLaw, integrable_map_measure hlogm.aestronglyMeasurable hD.aemeasurable]
    exact hFint.congr (hae.mono fun ω h ↦ h.symm)
  have hint' : Integrable (llr (sourceLaw ν' N) (sourceLaw ν₂' N)) (sourceLaw ν' N) :=
    hlogint.congr hllr.symm
  rw [klDiv_of_ac_of_integrable hac' hint', integral_congr_ae hllr, probReal_univ,
    probReal_univ, add_sub_cancel_right]
  rw [show ∫ s, Real.log (ℓ s).toReal ∂(sourceLaw ν' N) = ∫ ω, F ω ∂P by
    rw [sourceLaw, integral_map hD.aemeasurable hlogm.aestronglyMeasurable]
    exact integral_congr_ae hae, hFval,
    ENNReal.ofReal_sum_of_nonneg fun a _ ↦ mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hfin a)]
  by_cases ha : a ∈ Z
  · have h0 : E a = 0 := (Finset.mem_filter.mp ha).2
    simp [E] at h0
    simp [h0]
  · rw [ENNReal.ofReal_toReal (hKL a (hnZ a ha))]

/-- **Divergence of the source data**, infinite case [INC-P003, prop:source-kl]: if
`E_{ν'}[N'_k] > 0` and `KL(ν'_k, ν₂'_k) = ∞` for some arm, the divergence of the laws of the
source data is infinite. The statistic `(1{N'_k > 0}, x_{k,1})` of the source data has the law
`Ber(P(N'_k > 0)) ⊗ (ν'_k on {N'_k > 0}, δ_0 otherwise)`, since `{N'_k > 0}` is independent of
`X'_{k,1}`; the chain rule bounds its divergence from below by `P(N'_k > 0) KL(ν'_k, ν₂'_k)`. -/
lemma klDiv_sourceLaw_eq_top [Finite α] {N : SourceSpace α → α → ℕ} (hN : IsSizeRule N)
    (ν' ν₂' : Kernel α ℝ) [IsMarkovKernel ν'] [IsMarkovKernel ν₂'] (k : α)
    (hE : ∫⁻ ω, (N ω k : ℝ≥0∞) ∂(sourceMeasure ν') ≠ 0) (hKL : klDiv (ν' k) (ν₂' k) = ∞) :
    klDiv (sourceLaw ν' N) (sourceLaw ν₂' N) = ∞ := by
  have hNk : Measurable fun ω : SourceSpace α ↦ N ω k :=
    (measurable_pi_apply k).comp hN.measurable
  have hD := measurable_sourceData hN.measurable
  set B : SourceSpace α → Bool := fun ω ↦ decide (0 < N ω k)
  have hB : Measurable B := measurable_to_countable' fun b ↦ by
    have : B ⁻¹' {b} = {ω | (0 < N ω k) = (b = true)} := by
      ext ω
      cases b <;> simp [B]
    rw [this]
    cases b
    · simpa using (measurableSet_eq_fun hNk measurable_const :
        MeasurableSet {ω : SourceSpace α | N ω k = 0})
    · simpa using measurableSet_lt measurable_const hNk
  set Fs : Source α → Bool × ℝ := fun s ↦ (decide (0 < s.1 k), s.2 k 0)
  have hFs : Measurable Fs := by
    refine Measurable.prodMk ?_ (by fun_prop)
    refine measurable_to_countable' fun b ↦ ?_
    have : (fun s : Source α ↦ decide (0 < s.1 k)) ⁻¹' {b} = {s | (0 < s.1 k) = (b = true)} := by
      ext s
      cases b <;> simp
    rw [this]
    have hm : MeasurableSet {s : Source α | 0 < s.1 k} :=
      measurableSet_lt measurable_const ((measurable_pi_apply k).comp measurable_fst)
    cases b
    · simpa using (measurableSet_eq_fun ((measurable_pi_apply k).comp measurable_fst)
        measurable_const : MeasurableSet {s : Source α | s.1 k = 0})
    · simpa using hm
  -- The law of the statistic.
  have hlaw : ∀ (μ' : Kernel α ℝ) [IsMarkovKernel μ'], (sourceLaw μ' N).map Fs =
      ((sourceMeasure μ').map B) ⊗ₘ
        Kernel.ofFunOfCountable (fun b : Bool ↦ if b then μ' k else Measure.dirac 0) := by
    intro μ' _
    have : IsMarkovKernel
        (Kernel.ofFunOfCountable (fun b : Bool ↦ if b then μ' k else Measure.dirac (0 : ℝ))) :=
      ⟨fun b ↦ by
        cases b <;> simp only [Kernel.ofFunOfCountable_apply, Bool.false_eq_true, ↓reduceIte] <;>
          infer_instance⟩
    ext S hS
    rw [sourceLaw, Measure.map_map hFs hD, Measure.map_apply (hFs.comp hD) hS,
      Measure.compProd_apply hS, lintegral_map (Kernel.measurable_kernel_prodMk_left hS) hB]
    have hS1 : MeasurableSet (Prod.mk true ⁻¹' S) := measurable_prodMk_left hS
    have hS0 : MeasurableSet (Prod.mk false ⁻¹' S) := measurable_prodMk_left hS
    have hset : (Fs ∘ sourceData N) ⁻¹' S =
        ({ω | 0 < N ω k} ∩ (fun ω : SourceSpace α ↦ ω.2 k 0) ⁻¹' (Prod.mk true ⁻¹' S)) ∪
          ({ω | N ω k = 0} ∩ {_ω | (false, (0 : ℝ)) ∈ S}) := by
      ext ω
      simp only [Set.mem_preimage, Function.comp_apply, Fs, sourceData, Set.mem_union,
        Set.mem_inter_iff, Set.mem_ofPred_eq]
      rcases Nat.eq_zero_or_pos (N ω k) with h0 | hpos
      · simp [h0]
      · simp [hpos, hpos.ne']
    have hm1 : MeasurableSet ({ω | 0 < N ω k} ∩
        (fun ω : SourceSpace α ↦ ω.2 k 0) ⁻¹' (Prod.mk true ⁻¹' S)) :=
      (measurableSet_lt measurable_const hNk).inter ((by fun_prop :
        Measurable fun ω : SourceSpace α ↦ ω.2 k 0) hS1)
    have hm0 : MeasurableSet ({ω : SourceSpace α | N ω k = 0} ∩ {_ω | (false, (0 : ℝ)) ∈ S}) :=
      (hNk (measurableSet_singleton 0)).inter (MeasurableSet.const _)
    have hdisj : Disjoint ({ω | 0 < N ω k} ∩
        (fun ω : SourceSpace α ↦ ω.2 k 0) ⁻¹' (Prod.mk true ⁻¹' S))
        ({ω : SourceSpace α | N ω k = 0} ∩ {_ω | (false, (0 : ℝ)) ∈ S}) :=
      Set.disjoint_left.mpr fun ω h1 h2 ↦ by
        have := h1.1
        have := h2.1
        simp_all
    rw [hset, measure_union hdisj hm0]
    -- The integrand, split along `B`.
    have hint : ∀ ω, Kernel.ofFunOfCountable (fun b : Bool ↦ if b then μ' k else
        Measure.dirac (0 : ℝ)) (B ω) (Prod.mk (B ω) ⁻¹' S) =
        ({ω | 0 < N ω k}.indicator (fun _ ↦ μ' k (Prod.mk true ⁻¹' S)) ω) +
          ({ω | N ω k = 0}.indicator
            (fun _ ↦ Measure.dirac (0 : ℝ) (Prod.mk false ⁻¹' S)) ω) := fun ω ↦ by
      rcases Nat.eq_zero_or_pos (N ω k) with h0 | hpos
      · simp [B, h0, Kernel.ofFunOfCountable, Set.indicator]
      · simp [B, hpos, hpos.ne', Kernel.ofFunOfCountable, Set.indicator]
    simp_rw [hint]
    rw [lintegral_add_left ((measurable_const.indicator
      (measurableSet_lt measurable_const hNk))), lintegral_indicator_const
      (measurableSet_lt measurable_const hNk), lintegral_indicator_const
      (measurableSet_eq_fun hNk measurable_const :
        MeasurableSet {ω : SourceSpace α | N ω k = 0})]
    congr 1
    · -- independence of `{N'_k > 0}` and `X'_{k,1}`
      have h := lintegral_indicator_lt_mul hN μ' k 0
        (measurable_const.indicator hS1 : Measurable ((Prod.mk true ⁻¹' S).indicator
          (fun _ ↦ (1 : ℝ≥0∞))))
      rw [lintegral_indicator_const hS1, one_mul] at h
      rw [mul_comm, ← h, ← lintegral_indicator_one hm1]
      refine lintegral_congr fun ω ↦ ?_
      by_cases hω : 0 < N ω k
      · by_cases hx : (true, ω.2 k 0) ∈ S
        · simp [hω, hx, Set.indicator]
        · simp [hω, hx, Set.indicator]
      · simp [hω, Set.indicator]
    · by_cases h0 : (false, (0 : ℝ)) ∈ S
      · have : MeasurableSet (Prod.mk false ⁻¹' S) := hS0
        rw [Measure.dirac_apply' _ hS0, Set.indicator_of_mem (by exact h0), Pi.one_apply, one_mul]
        congr 1
        ext ω
        simp [h0]
      · rw [Measure.dirac_apply' _ hS0, Set.indicator_of_notMem (by exact h0), zero_mul]
        simp [h0]
  -- The chain rule bounds the divergence from below.
  have : IsMarkovKernel
      (Kernel.ofFunOfCountable (fun b : Bool ↦ if b then ν' k else Measure.dirac (0 : ℝ))) :=
    ⟨fun b ↦ by
        cases b <;> simp only [Kernel.ofFunOfCountable_apply, Bool.false_eq_true, ↓reduceIte] <;>
          infer_instance⟩
  have : IsMarkovKernel
      (Kernel.ofFunOfCountable (fun b : Bool ↦ if b then ν₂' k else Measure.dirac (0 : ℝ))) :=
    ⟨fun b ↦ by
        cases b <;> simp only [Kernel.ofFunOfCountable_apply, Bool.false_eq_true, ↓reduceIte] <;>
          infer_instance⟩
  have hp : (sourceMeasure ν').map B {true} ≠ 0 := by
    rw [Measure.map_apply hB (measurableSet_singleton true)]
    intro h0
    apply hE
    rw [lintegral_eq_zero_iff (f := fun ω ↦ (N ω k : ℝ≥0∞)) (measurable_from_top.comp hNk)]
    refine measure_mono_null (fun ω hω ↦ ?_) h0
    simp only [Set.mem_preimage, Set.mem_singleton_iff, B, decide_eq_true_eq]
    by_contra h
    exact hω (by simp [Nat.eq_zero_of_not_pos h])
  refine eq_top_mono (klDiv_map_le _ _ hFs) ?_
  rw [hlaw ν', hlaw ν₂', TauCeti.klDiv_compProd_eq_add_lintegral, lintegral_fintype]
  refine eq_top_mono (le_add_self) ?_
  refine eq_top_mono (Finset.single_le_sum (fun b _ ↦ bot_le) (Finset.mem_univ true)) ?_
  simp only [Kernel.ofFunOfCountable, Kernel.coe_mk, ite_true]
  rw [hKL, ENNReal.top_mul hp]

/-- **Divergence of the source data** [INC-P003, prop:source-kl]: for a size rule with
`E_{ν'}[N'_k] < ∞` for every arm,
`KL(P^D_{ν',N'}, P^D_{ν₂',N'}) = ∑_k E_{ν'}[N'_k] KL(ν'_k, ν₂'_k)` (in `ℝ≥0∞`, `0 · ∞ = 0`). -/
lemma klDiv_sourceLaw [Fintype α] {N : SourceSpace α → α → ℕ} (hN : IsSizeRule N)
    (ν' ν₂' : Kernel α ℝ) [IsMarkovKernel ν'] [IsMarkovKernel ν₂']
    (hfin : ∀ a, ∫⁻ ω, (N ω a : ℝ≥0∞) ∂(sourceMeasure ν') ≠ ∞) :
    klDiv (sourceLaw ν' N) (sourceLaw ν₂' N) =
      ∑ a, (∫⁻ ω, (N ω a : ℝ≥0∞) ∂(sourceMeasure ν')) * klDiv (ν' a) (ν₂' a) := by
  by_cases h : ∃ a, ∫⁻ ω, (N ω a : ℝ≥0∞) ∂(sourceMeasure ν') ≠ 0 ∧ klDiv (ν' a) (ν₂' a) = ∞
  · obtain ⟨a, hE, hKL⟩ := h
    rw [klDiv_sourceLaw_eq_top hN ν' ν₂' a hE hKL]
    symm
    refine eq_top_mono (Finset.single_le_sum (fun b _ ↦ bot_le) (Finset.mem_univ a)) ?_
    rw [hKL, ENNReal.mul_top hE]
  · push Not at h
    exact klDiv_sourceLaw_of_ne_top hN ν' ν₂' hfin h

/-- The expected size of an arm under the law of the game is its expected size under `P'_{ν'}`
[INC-P003, lem:mixture]. -/
lemma lintegral_sourceCount_gameMeasure {N : SourceSpace α → α → ℕ} (hN : Measurable N)
    (ν' ν : Kernel α ℝ) [IsMarkovKernel ν'] [IsMarkovKernel ν] (π : TransferAlgorithm α) (T : ℕ)
    (a : α) :
    ∫⁻ x, (sourceCount a x.1 : ℝ≥0∞) ∂(gameMeasure ν' N ν π T) =
      ∫⁻ ω, (N ω a : ℝ≥0∞) ∂(sourceMeasure ν') := by
  have hcount : Measurable fun s : Source α ↦ (sourceCount a s : ℝ≥0∞) :=
    measurable_from_top.comp (by unfold sourceCount; fun_prop)
  rw [← lintegral_map hcount measurable_fst]
  change ∫⁻ s, _ ∂((gameMeasure ν' N ν π T).fst) = _
  rw [gameMeasure, Measure.fst_compProd, sourceLaw,
    lintegral_map hcount (measurable_sourceData hN)]
  rfl

end Incognita.TransferBandits
