/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.MaskedHistory

/-! # A one-sided change of measure for the histories of a run

Let `e₁`, `e₂` be two environments (no observation) whose feedback kernels satisfy, at every
round `n` and for every action `b`, `w n b • e₂.feedback n ≤ e₁.feedback n` for weights
`w n b ∈ [0, ∞]`. Then the law of the history of the first `n` rounds under `e₁` dominates the law
under `e₂` with the density `h ↦ ∏_{i < n} w i (action of round i of h)`.

For two bandits `ν⁻`, `ν⁺` that differ only at the arm `a`, with `ν⁻_a ≥ (1 - s) ν⁺_a`, this gives
`P⁻(A) ≥ E⁺[(1 - s) ^ N_a 1_A]`: the change of measure of the lower bound "two batches ahead"
(`formalisation.tex`, the route to [INC-P000, Lemma `lem:twobatches`]), which needs no
concentration of the log-likelihood ratios.

## Main statements

* `Incognita.BatchedBandits.setLIntegral_stepKernel_le`: the domination for one round.
* `Incognita.BatchedBandits.withDensity_map_hist_le`: the domination for the histories.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Finset

open scoped ENNReal

namespace Incognita.BatchedBandits

variable {𝓐 𝓨 : Type*} [MeasurableSpace 𝓐] [MeasurableSpace 𝓨]

/-- **One round.** If `w b • e₂.feedback n z ≤ e₁.feedback n z` whenever `b` is the action of `z`,
then the step kernel of the round `n` under `e₁` dominates the step kernel under `e₂` with the
density `x ↦ w (action of x)`. -/
lemma setLIntegral_stepKernel_le (alg : Algorithm Unit 𝓐 𝓨) {e₁ e₂ : Environment Unit 𝓐 𝓨}
    (n : ℕ) {w : 𝓐 → ℝ≥0∞} (hw : Measurable w)
    (hfb : ∀ z, w z.2 • e₂.feedback n z ≤ e₁.feedback n z) (h : Hist Unit 𝓐 𝓨 n)
    {S : Set (Round Unit 𝓐 𝓨)} (hS : MeasurableSet S) :
    ∫⁻ x in S, w x.action ∂(stepKernel alg e₂ n h) ≤ stepKernel alg e₁ n h S := by
  have hobs : e₁.obs n = e₂.obs n :=
    (Kernel.eq_const_dirac_of_subsingleton _ ()).trans
      (Kernel.eq_const_dirac_of_subsingleton _ ()).symm
  have hf : Measurable (S.indicator fun x : Round Unit 𝓐 𝓨 ↦ w x.action) :=
    (hw.comp Round.measurable_action).indicator hS
  rw [stepKernel_def, stepKernel_def, hobs, ← lintegral_indicator hS,
    Kernel.lintegral_compProd _ _ _ hf, Kernel.compProd_apply hS]
  refine lintegral_mono fun o ↦ ?_
  rw [Kernel.lintegral_compProd _ _ _
      (f := fun c ↦ S.indicator (fun x : Round Unit 𝓐 𝓨 ↦ w x.action) (o, c))
      (hf.comp measurable_prodMk_left),
    Kernel.compProd_apply (measurable_prodMk_left hS)]
  refine lintegral_mono fun b ↦ ?_
  have hslice : MeasurableSet (Prod.mk b ⁻¹' (Prod.mk o ⁻¹' S)) :=
    measurable_prodMk_left (measurable_prodMk_left hS)
  calc ∫⁻ y, S.indicator (fun x : Round Unit 𝓐 𝓨 ↦ w x.action) (o, b, y)
        ∂(e₂.feedback n ((h, o), b))
      = ∫⁻ y, (Prod.mk b ⁻¹' (Prod.mk o ⁻¹' S)).indicator (fun _ ↦ w b) y
          ∂(e₂.feedback n ((h, o), b)) := by
        refine lintegral_congr fun y ↦ ?_
        by_cases hy : (o, b, y) ∈ S <;> simp [Set.indicator, hy, Round.action]
    _ = w b * e₂.feedback n ((h, o), b) (Prod.mk b ⁻¹' (Prod.mk o ⁻¹' S)) :=
        lintegral_indicator_const hslice _
    _ ≤ e₁.feedback n ((h, o), b) (Prod.mk b ⁻¹' (Prod.mk o ⁻¹' S)) := by
        have := Measure.le_iff'.mp (hfb ((h, o), b)) (Prod.mk b ⁻¹' (Prod.mk o ⁻¹' S))
        rwa [smul_apply, smul_eq_mul] at this

/-- **The histories.** If `w n b • e₂.feedback n z ≤ e₁.feedback n z` at every round `n`, whenever
`b` is the action of `z`, then the law of the history of the first `n` rounds under `e₁` dominates
the law under `e₂` with the density `h ↦ ∏_{i < n} w i (action of round i of h)`. -/
lemma withDensity_map_hist_le (alg : Algorithm Unit 𝓐 𝓨) {e₁ e₂ : Environment Unit 𝓐 𝓨}
    {w : ℕ → 𝓐 → ℝ≥0∞} (hw : ∀ n, Measurable (w n))
    (hfb : ∀ n z, w n z.2 • e₂.feedback n z ≤ e₁.feedback n z) (n : ℕ) :
    ((trajMeasure alg e₂).map (IT.hist n)).withDensity
        (fun h ↦ ∏ i : Fin n, w i (h i).action) ≤
      (trajMeasure alg e₁).map (IT.hist n) := by
  have h₁ := IT.isAlgEnvSeq_trajMeasure alg e₁
  have h₂ := IT.isAlgEnvSeq_trajMeasure alg e₂
  have hD : ∀ m, Measurable fun h : Hist Unit 𝓐 𝓨 m ↦ ∏ i : Fin m, w i (h i).action := fun m ↦
    Finset.measurable_prod _ fun i _ ↦
      (hw i).comp (Round.measurable_action.comp (measurable_pi_apply i))
  rw [← IT.history_obs_action_feedback]
  induction n with
  | zero =>
    simp only [history_zero, Measure.map_const, measure_univ, one_smul]
    simp
  | succ n ih =>
    set φ := (MeasurableEquiv.finSuccProd (Round Unit 𝓐 𝓨) n).symm
    have hlaw : ∀ (e : Environment Unit 𝓐 𝓨),
        (trajMeasure alg e).map (history IT.obs IT.action IT.feedback (n + 1)) =
          ((trajMeasure alg e).map (history IT.obs IT.action IT.feedback n) ⊗ₘ
            stepKernel alg e n).map φ := fun e ↦ by
      have he := IT.isAlgEnvSeq_trajMeasure alg e
      rw [history_succ, ← Measure.map_map φ.measurable
        ((he.measurable_history n).prodMk (he.measurable_step n)),
        (he.hasCondDistrib_step n).map_eq]
    have hprod : ∀ (h : Hist Unit 𝓐 𝓨 n) (x : Round Unit 𝓐 𝓨),
        ∏ i : Fin (n + 1), w i (φ (h, x) i).action =
          (∏ i : Fin n, w i (h i).action) * w n x.action := fun h x ↦ by
      rw [Fin.prod_univ_castSucc]
      simp [φ, MeasurableEquiv.finSuccProd_symm_apply]
    refine Measure.le_iff.mpr fun A hA ↦ ?_
    rw [withDensity_apply _ hA, hlaw, hlaw, Measure.map_apply φ.measurable hA,
      setLIntegral_map hA (hD _) φ.measurable, Measure.compProd_apply (φ.measurable hA)]
    set μ₂ := (trajMeasure alg e₂).map (history IT.obs IT.action IT.feedback n)
    set μ₁ := (trajMeasure alg e₁).map (history IT.obs IT.action IT.feedback n)
    have hslice : ∀ h, MeasurableSet (Prod.mk h ⁻¹' (φ ⁻¹' A)) := fun h ↦
      measurable_prodMk_left (φ.measurable hA)
    calc ∫⁻ z in φ ⁻¹' A, ∏ i : Fin (n + 1), w i (φ z i).action ∂(μ₂ ⊗ₘ stepKernel alg e₂ n)
        = ∫⁻ z, (φ ⁻¹' A).indicator (fun z ↦ (∏ i : Fin n, w i (z.1 i).action) *
            w n z.2.action) z ∂(μ₂ ⊗ₘ stepKernel alg e₂ n) := by
          rw [← lintegral_indicator (φ.measurable hA)]
          congr 1
          funext z
          obtain ⟨h, x⟩ := z
          simp only [Set.indicator, hprod]
      _ = ∫⁻ h, (∏ i : Fin n, w i (h i).action) *
            ∫⁻ x in Prod.mk h ⁻¹' (φ ⁻¹' A), w n x.action ∂(stepKernel alg e₂ n h) ∂μ₂ := by
          have hmeas : Measurable fun z : Hist Unit 𝓐 𝓨 n × Round Unit 𝓐 𝓨 ↦
              (∏ i : Fin n, w i (z.1 i).action) * w n z.2.action :=
            ((hD n).comp measurable_fst).mul
              ((hw n).comp (Round.measurable_action.comp measurable_snd))
          rw [Measure.lintegral_compProd (hmeas.indicator (φ.measurable hA))]
          refine lintegral_congr fun h ↦ ?_
          rw [← lintegral_indicator (hslice h), ← lintegral_const_mul
            (f := (Prod.mk h ⁻¹' (φ ⁻¹' A)).indicator fun x : Round Unit 𝓐 𝓨 ↦ w n x.action) _
            (((hw n).comp Round.measurable_action).indicator (hslice h))]
          refine lintegral_congr fun x ↦ ?_
          by_cases hx : (h, x) ∈ φ ⁻¹' A
          · simp [Set.indicator, hx, Set.mem_preimage]
          · simp only [Set.indicator, Set.mem_preimage] at hx ⊢
            simp [hx]
      _ ≤ ∫⁻ h, (∏ i : Fin n, w i (h i).action) *
            stepKernel alg e₁ n h (Prod.mk h ⁻¹' (φ ⁻¹' A)) ∂μ₂ := by
          refine lintegral_mono fun h ↦ ?_
          gcongr
          exact setLIntegral_stepKernel_le alg n (hw n) (hfb n) h (hslice h)
      _ = ∫⁻ h, stepKernel alg e₁ n h (Prod.mk h ⁻¹' (φ ⁻¹' A))
            ∂(μ₂.withDensity fun h ↦ ∏ i : Fin n, w i (h i).action) :=
          (lintegral_withDensity_eq_lintegral_mul _ (hD n)
            (Kernel.measurable_kernel_prodMk_left (φ.measurable hA))).symm
      _ ≤ ∫⁻ h, stepKernel alg e₁ n h (Prod.mk h ⁻¹' (φ ⁻¹' A)) ∂μ₁ :=
          lintegral_mono' ih le_rfl

end Incognita.BatchedBandits
