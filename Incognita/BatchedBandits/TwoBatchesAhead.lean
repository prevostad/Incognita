/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.ChangeOfMeasure
public import Incognita.BatchedBandits.OneBatchAhead
public import Incognita.ForLML.InformationTheory.KullbackLeibler.Convex
public import Incognita.ForLML.SequentialLearning.Algorithm
public import LMLExplore.InformationTheory.KullbackLeibler.Bernoulli

/-! # Two batches ahead

The lower bound "two batches ahead" of [INC-P000, Lemma `lem:twobatches`(ii)], by the route of
`formalisation.tex` (a one-sided change of measure and data processing, with no concentration
of the log-likelihood ratios).

## Main statements

* `eventually_lt_integral_pullCount_div_log_t_add_two`: [INC-P000, Lemma `lem:twobatches`(ii)]: for
  a learner batched on a grid and consistent at its batch ends on `𝒫`, and a suboptimal arm `a`
  with `E_ν[N_a(t_(ℓ+1))] = O(log t_(ℓ+2))`, `liminf_ℓ E_ν[N_a(t_ℓ)] / log t_(ℓ+2) ≥
  1 / 𝒦_inf(ν_a, m⋆)`.
* `two_batches_finite`: the finite-horizon inequality behind it, for three bandits that differ
  only at `a`.
* `exists_two_alternatives`: the alternative instances `κ⁺, κ⁻ ∈ 𝒫`.
* `two_batches_step`: the bound at a fixed index `ℓ`, given the alternative instances.
* `exp_neg_div_le_of_klBer_le`: data processing in multiplicative form: if `d(q, p) ≤ D` with
  `q > 0`, then `p ≥ exp (-(D + log 2) / q)`.
* `klDiv_map_hist_switch_left`: the divergence between the switched environment (`ν` before `r`,
  `ν'` afterwards) and the bandit `ν'` is the divergence between `ν` and `ν'` on the first `r`
  rounds (with `Learning.IsAlgEnvSeq.isAlgEnvSeqUntil_of_feedback_eq` of
  `Incognita.ForLML.SequentialLearning.Algorithm`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Learning Bandits Filter Real Finset

open scoped ENNReal Topology

namespace Incognita.BatchedBandits

/-- **Data processing, multiplicative form.** If the binary relative entropy `d(q, p)` is at most
`D ≥ 0`, with `q ∈ (0, 1]` and `p ∈ [0, 1]`, then `p ≥ exp (-(D + log 2) / q)`: from
`d(q, p) ≥ q log (1 / p) - log 2`, which follows from the decomposition [GMS19, (11)]. -/
lemma exp_neg_div_le_of_klBer_le {p q D : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) (hp : p ∈ Set.Icc 0 1)
    (hD : 0 ≤ D) (hkl : LMLExplore.klBer q p ≤ ENNReal.ofReal D) :
    exp (-(D + log 2) / q) ≤ p := by
  have hq : q ∈ Set.Icc (0 : ℝ) 1 := ⟨hq0.le, hq1⟩
  have hne : LMLExplore.klBer q p ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hkl
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact hne ((LMLExplore.klBer_eq_top_iff hq hp).mpr (Or.inl ⟨rfl, hq0.ne'⟩))
  have hexp : exp (-(D + log 2) / q) ≤ 1 := by
    rw [exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [log_nonneg one_le_two]) hq0.le
  rcases eq_or_lt_of_le hp.2 with hp1 | hp1
  · rw [hp1]
    exact hexp
  have hpos : 0 < p := lt_of_le_of_ne hp.1 (Ne.symm hp0)
  rw [LMLExplore.klBer_eq_ofReal_klBerReal hq hp hne,
    ENNReal.ofReal_le_ofReal_iff hD,
    LMLExplore.klBerReal_eq_neg_binEntropy_sub hp0 hp1.ne] at hkl
  have hb := Real.binEntropy_le_log_two (p := q)
  have hl : log (1 - p) ≤ 0 := log_nonpos (by linarith) (by linarith)
  have h1q : 0 ≤ 1 - q := by linarith
  have hlogp : -(D + log 2) / q ≤ log p := by
    rw [div_le_iff₀ hq0]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos h1q hl]
  calc exp (-(D + log 2) / q) ≤ exp (log p) := exp_le_exp.mpr hlogp
    _ = p := exp_log hpos

variable {𝓐 𝓨 : Type*} [MeasurableSpace 𝓐] [MeasurableSpace 𝓨]

/-- **Divergence for the switched environment, bandit on the right.** Let `e` be the environment
that follows the bandit `ν` at the rounds `< r` and the bandit `ν'` at the rounds `≥ r`. For
`r ≤ M`, the relative entropy between the laws of the histories of the first `M` rounds under `e`
and under `ν'` is the relative entropy between the laws of the histories of the first `r` rounds
under `ν` and under `ν'`. -/
lemma klDiv_map_hist_switch_left (alg : Algorithm Unit 𝓐 𝓨) (ν ν' : Kernel 𝓐 𝓨)
    [IsMarkovKernel ν] [IsMarkovKernel ν'] {e : Environment Unit 𝓐 𝓨} {r M : ℕ} (hrM : r ≤ M)
    (hlt : ∀ n < r, e.feedback n = ν.prodMkLeft _)
    (hge : ∀ n, r ≤ n → e.feedback n = ν'.prodMkLeft _) :
    klDiv ((trajMeasure alg e).map (IT.hist M))
        ((trajMeasure alg (Environment.bandit ν')).map (IT.hist M)) =
      klDiv ((trajMeasure alg (Environment.bandit ν)).map (IT.hist r))
        ((trajMeasure alg (Environment.bandit ν')).map (IT.hist r)) := by
  have he := IT.isAlgEnvSeq_trajMeasure alg e
  have hν := IT.isAlgEnvSeq_trajMeasure alg (Environment.bandit ν)
  have hν' := IT.isAlgEnvSeq_trajMeasure alg (Environment.bandit ν')
  rw [← IT.history_obs_action_feedback, ← IT.history_obs_action_feedback,
    he.klDiv_map_history_stepKernel hν' M,
    hν.klDiv_map_history_stepKernel hν' r, ← Finset.sum_range_add_sum_Ico _ hrM]
  have hobs : ∀ (κ : Kernel 𝓐 𝓨) [IsMarkovKernel κ] n,
      e.obs n = (Environment.bandit κ).obs n := fun κ _ n ↦
    (Kernel.eq_const_dirac_of_subsingleton _ ()).trans (obs_bandit n).symm
  have h0 : ∑ t ∈ Ico r M, klDiv
      ((trajMeasure alg e).map (history IT.obs IT.action IT.feedback t) ⊗ₘ stepKernel alg e t)
      ((trajMeasure alg e).map (history IT.obs IT.action IT.feedback t) ⊗ₘ
        stepKernel alg (Environment.bandit ν') t) = 0 := by
    refine Finset.sum_eq_zero fun t ht ↦ ?_
    have hrt : r ≤ t := (Finset.mem_Ico.mp ht).1
    have hs : stepKernel alg e t = stepKernel alg (Environment.bandit ν') t := by
      rw [stepKernel_def, stepKernel_def, hobs ν' t, hge t hrt, feedback_bandit]
    rw [hs, klDiv_self]
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun t ht ↦ ?_
  have htr : t < r := Finset.mem_range.mp ht
  have hs : stepKernel alg e t = stepKernel alg (Environment.bandit ν) t := by
    rw [stepKernel_def, stepKernel_def, hobs ν t, hlt t htr, feedback_bandit]
  -- Before `r`, the run against `e` is a run against `ν`: the histories have the same law.
  have hlaw : (trajMeasure alg e).map (history IT.obs IT.action IT.feedback t) =
      (trajMeasure alg (Environment.bandit ν)).map (history IT.obs IT.action IT.feedback t) := by
    have hu := he.isAlgEnvSeqUntil_of_feedback_eq (env' := Environment.bandit ν) (N := t)
      fun n hn ↦ by rw [feedback_bandit, hlt n (hn.trans htr)]
    rw [hu.map_history, (hν.isAlgEnvSeqUntil t).map_history]
  rw [hs, hlaw]

section Counts

variable {α : Type*} [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- The product over the rounds `i < M` of `x` if `i < r` and `a` is played at `i`, `1`
otherwise, is `x ^ N_a(r)` (for `r ≤ M`). -/
lemma prod_ite_eq_pow_pullCount {𝓨' : Type*} {r M : ℕ} (hrM : r ≤ M) (a : α)
    (ω : ℕ → Round Unit α 𝓨') {M' : Type*} [CommMonoid M'] (x : M') :
    ∏ i : Fin M, (if (i : ℕ) < r ∧ (ω i).action = a then x else 1) =
      x ^ pullCount IT.action a r ω := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  congr 1
  rw [pullCount, ← Finset.card_map Fin.valEmbedding]
  congr 1
  ext s
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
    Finset.mem_range]
  constructor
  · rintro ⟨i, ⟨hi, hia⟩, rfl⟩
    exact ⟨hi, hia⟩
  · rintro ⟨hs, hsa⟩
    exact ⟨⟨s, hs.trans_le hrM⟩, ⟨hs, hsa⟩, rfl⟩

/-- Markov's inequality for the count of `a`: `P(2 N_a(M) ≥ M) ≤ 2 E[N_a(M)] / M`. -/
lemma measureReal_le_two_mul_integral_pullCount_div (alg : Algorithm Unit α ℝ)
    (env : Environment Unit α ℝ) (a : α) {M : ℕ} (hM : 0 < M) :
    (trajMeasure alg env).real {ω | (M : ℝ) ≤ 2 * (pullCount IT.action a M ω : ℝ)} ≤
      2 * (∫ ω, (pullCount IT.action a M ω : ℝ) ∂(trajMeasure alg env)) / M := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hset : {ω : ℕ → Round Unit α ℝ | (M : ℝ) ≤ 2 * (pullCount IT.action a M ω : ℝ)} =
      {ω | (M : ℝ) / 2 ≤ (pullCount IT.action a M ω : ℝ)} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro h <;> linarith
  rw [hset, le_div_iff₀ hMpos]
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := trajMeasure alg env)
    (f := fun ω ↦ (pullCount IT.action a M ω : ℝ)) (ae_of_all _ fun _ ↦ Nat.cast_nonneg _)
    (integrable_pullCount IT.measurable_action a M) ((M : ℝ) / 2)
  linarith

/-- Markov's inequality for the other arms: `P(2 N_a(M) < M) ≤ 2 (M - E[N_a(M)]) / M`. -/
lemma measureReal_compl_le_two_mul_sub_integral_pullCount_div (alg : Algorithm Unit α ℝ)
    (env : Environment Unit α ℝ) (a : α) {M : ℕ} (hM : 0 < M) :
    (trajMeasure alg env).real {ω | (M : ℝ) ≤ 2 * (pullCount IT.action a M ω : ℝ)}ᶜ ≤
      2 * (M - ∫ ω, (pullCount IT.action a M ω : ℝ) ∂(trajMeasure alg env)) / M := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hsub : {ω : ℕ → Round Unit α ℝ | (M : ℝ) ≤ 2 * (pullCount IT.action a M ω : ℝ)}ᶜ ⊆
      {ω | (M : ℝ) / 2 ≤ (M : ℝ) - (pullCount IT.action a M ω : ℝ)} := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω
    simp only [Set.mem_ofPred_eq]
    linarith
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := trajMeasure alg env)
    (f := fun ω ↦ (M : ℝ) - (pullCount IT.action a M ω : ℝ))
    (ae_of_all _ fun ω ↦ sub_nonneg.mpr (by exact_mod_cast pullCount_le a M ω))
    ((integrable_const _).sub (integrable_pullCount IT.measurable_action a M)) ((M : ℝ) / 2)
  rw [integral_sub (integrable_const _) (integrable_pullCount IT.measurable_action a M),
    integral_const, probReal_univ, one_smul] at hmk
  have hmono := measureReal_mono (μ := trajMeasure alg env) hsub
  rw [le_div_iff₀ hMpos]
  nlinarith

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- The event `{N_a(r) ≤ L}` read on the history of the first `r` rounds. -/
lemma hist_preimage_pullCount'_le (a : α) (r L : ℕ) :
    IT.hist r ⁻¹' {h : Hist Unit α ℝ r | pullCount' r h a ≤ L} =
      {ω | pullCount IT.action a r ω ≤ L} := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  rw [← IT.history_obs_action_feedback,
    ← pullCount_eq_pullCount' (O := IT.obs) (R' := IT.feedback)]

/-- **Finite-horizon inequality two batches ahead.** Let `r₀ ≤ r ≤ M`, `0 < M`, and let the
learner see the rewards before `r₀` at the rounds `< r` and the rewards before `r` at the rounds
`< M` (for a learner batched on a grid: `r₀ = t ℓ`, `r = t (ℓ + 1)`, `M = t (ℓ + 2)`). Let the
bandits `ν`, `κ⁺`, `κ⁻` agree outside the arm `a`, with `κ⁻_a ≥ c κ⁺_a` for some `c ∈ [0, 1]` and
`KL(ν_a, κ⁺_a) < ∞`, and let `q = P_ν(N_a(r) ≤ L) > 0`. Then
`c ^ L exp (-(E_ν[N_a(r₀)] KL(ν_a, κ⁺_a) + log 2) / q)
  ≤ 2 E_{κ⁻}[N_a(M)] / M + 2 (M - E_{κ⁺}[N_a(M)]) / M`.
Only the pulls of `a` before `r₀` pay the divergence `KL(ν_a, κ⁺_a)`; the pulls of `a` in the
rounds `[r₀, r)` pay the factor `c` each. -/
lemma two_batches_finite [Finite α] {alg : Algorithm Unit α ℝ} {r₀ r M L : ℕ} (hr₀r : r₀ ≤ r)
    (hrM : r ≤ M) (hM : 0 < M) (halg₀ : ∀ n < r, SeesRewardsUpTo alg n r₀)
    (halg : ∀ n < M, SeesRewardsUpTo alg n r) {ν κp κm : Kernel α ℝ} [IsMarkovKernel ν]
    [IsMarkovKernel κp] [IsMarkovKernel κm] {a : α} (hνp : ∀ b ≠ a, ν b = κp b)
    (hmp : ∀ b ≠ a, κm b = κp b) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hdom : ENNReal.ofReal c • κp a ≤ κm a) (hD : klDiv (ν a) (κp a) ≠ ∞)
    (hq : 0 < (trajMeasure alg (Environment.bandit ν)).real
      {ω | pullCount IT.action a r ω ≤ L}) :
    c ^ L * exp (-((∫ ω, (pullCount IT.action a r₀ ω : ℝ)
        ∂(trajMeasure alg (Environment.bandit ν))) * (klDiv (ν a) (κp a)).toReal + log 2) /
        (trajMeasure alg (Environment.bandit ν)).real {ω | pullCount IT.action a r ω ≤ L}) ≤
      2 * (∫ ω, (pullCount IT.action a M ω : ℝ) ∂(trajMeasure alg (Environment.bandit κm))) / M +
        2 * (M - ∫ ω, (pullCount IT.action a M ω : ℝ)
          ∂(trajMeasure alg (Environment.bandit κp))) / M := by
  set Pν := trajMeasure alg (Environment.bandit ν)
  set Pp := trajMeasure alg (Environment.bandit κp)
  set Pm := trajMeasure alg (Environment.bandit κm)
  set T₀ := ∫ ω, (pullCount IT.action a r₀ ω : ℝ) ∂Pν
  set D := (klDiv (ν a) (κp a)).toReal
  set SL := {ω : ℕ → Round Unit α ℝ | pullCount IT.action a r ω ≤ L} with hSL
  set q := Pν.real SL
  have hT₀D : 0 ≤ T₀ * D :=
    mul_nonneg (integral_nonneg fun _ ↦ Nat.cast_nonneg _) ENNReal.toReal_nonneg
  -- Step 1. The switched environment `eQ`: `ν` before `r₀`, `κ⁺` afterwards.
  let eQ : Environment Unit α ℝ :=
    { obs := fun _ ↦ Kernel.const _ (Measure.dirac ())
      feedback := fun n ↦ if n < r₀ then ν.prodMkLeft _ else κp.prodMkLeft _
      isMarkovKernel_feedback := fun n ↦ by
        by_cases hn : n < r₀
        · simp only [hn, ↓reduceIte]
          infer_instance
        · simp only [hn, ↓reduceIte]
          infer_instance }
  set F : Set (Hist Unit α ℝ r) := {h | pullCount' r h a ≤ L} with hF
  have hFm : MeasurableSet F := measurableSet_le (measurable_pullCount' r a) measurable_const
  -- Under `eQ` and under `ν`, the count `N_a(r)` has the same law (masked histories at `r₀`).
  have hqQ : (trajMeasure alg eQ).real SL = q := by
    set Ym : ℕ → (ℕ → Round Unit α ℝ) → ℝ := fun n ↦ if n < r₀ then IT.feedback n else fun _ ↦ 0
      with hYm
    have hYmm : ∀ n, Measurable (Ym n) := fun n ↦ by
      by_cases hn : n < r₀
      · simp only [hYm, hn, ↓reduceIte]
        exact IT.measurable_feedback n
      · simp only [hYm, hn, ↓reduceIte]
        exact measurable_const
    have hmeas : Measurable (history IT.obs IT.action Ym r) :=
      measurable_history IT.measurable_obs IT.measurable_action hYmm r
    have hpre : history IT.obs IT.action Ym r ⁻¹' F = SL := by
      ext ω
      simp only [Set.mem_preimage, hF, hSL, Set.mem_ofPred_eq]
      rw [← pullCount_eq_pullCount' (O := IT.obs) (R' := Ym)]
    have hlaw := map_history_maskFeedback_eq (M := r) alg (env := eQ)
      (env' := Environment.bandit ν) (fun n hn ↦ by simp [eQ, hn]) halg₀ 0
    rw [← hpre, ← map_measureReal_apply hmeas hFm, hlaw, map_measureReal_apply hmeas hFm, hpre]
  -- Data processing between `eQ` and `κ⁺` on the histories of the first `r` rounds.
  have hKL : klDiv ((trajMeasure alg eQ).map (IT.hist r)) (Pp.map (IT.hist r)) ≤
      ENNReal.ofReal (T₀ * D) := by
    rw [klDiv_map_hist_switch_left alg ν κp hr₀r (fun n hn ↦ by simp [eQ, hn])
      (fun n hn ↦ by simp [eQ, not_lt.mpr hn])]
    exact (IT.isAlgEnvSeq_trajMeasure alg _).klDiv_map_history_le_ofReal_integral_pullCount_mul
      (IT.isAlgEnvSeq_trajMeasure alg _) hνp (ENNReal.ofReal_toReal hD).ge r₀
  have hkl := (LMLExplore.klBer_measureReal_le_klDiv hFm).trans hKL
  rw [map_measureReal_apply (IT.measurable_hist r) hFm,
    map_measureReal_apply (IT.measurable_hist r) hFm, hF, hist_preimage_pullCount'_le, ← hSL,
    hqQ] at hkl
  have hpp : exp (-(T₀ * D + log 2) / q) ≤ Pp.real SL :=
    exp_neg_div_le_of_klBer_le hq measureReal_le_one ⟨measureReal_nonneg, measureReal_le_one⟩
      hT₀D hkl
  -- Step 2. The change of measure between `κ⁻` (before `r`) and `κ⁺`.
  let e₁ : Environment Unit α ℝ :=
    { obs := fun _ ↦ Kernel.const _ (Measure.dirac ())
      feedback := fun n ↦ if n < r then κm.prodMkLeft _ else κp.prodMkLeft _
      isMarkovKernel_feedback := fun n ↦ by
        by_cases hn : n < r
        · simp only [hn, ↓reduceIte]
          infer_instance
        · simp only [hn, ↓reduceIte]
          infer_instance }
  set w : ℕ → α → ℝ≥0∞ := fun n b ↦ if n < r ∧ b = a then ENNReal.ofReal c else 1 with hw_def
  have hw : ∀ n, Measurable (w n) := fun n ↦ Measurable.of_discrete
  have hfb : ∀ n z, w n z.2 • (Environment.bandit κp).feedback n z ≤ e₁.feedback n z := by
    intro n z
    rw [feedback_bandit, Kernel.prodMkLeft_apply]
    by_cases hn : n < r
    · simp only [e₁, hn, ↓reduceIte, Kernel.prodMkLeft_apply]
      by_cases hb : z.2 = a
      · simp only [hw_def, hn, hb, and_self, ↓reduceIte]
        exact hdom
      · simp only [hw_def, hb, and_false, ↓reduceIte, one_smul]
        rw [hmp _ hb]
    · simp [e₁, hw_def, hn]
  have hcm := withDensity_map_hist_le alg hw hfb M
  -- Step 3. The event `G = {M ≤ 2 N_a(M)}`.
  set G' : Set (Hist Unit α ℝ M) := {h | (M : ℝ) ≤ 2 * (pullCount' M h a : ℝ)} with hG'
  have hG'm : MeasurableSet G' := measurableSet_le measurable_const
    ((Measurable.of_discrete.comp (measurable_pullCount' M a)).const_mul 2)
  set G := {ω : ℕ → Round Unit α ℝ | (M : ℝ) ≤ 2 * (pullCount IT.action a M ω : ℝ)} with hG
  have hGG' : IT.hist M ⁻¹' G' = G := by
    ext ω
    simp only [Set.mem_preimage, hG', hG, Set.mem_ofPred_eq]
    rw [← IT.history_obs_action_feedback,
      ← pullCount_eq_pullCount' (O := IT.obs) (R' := IT.feedback)]
  have hGm : MeasurableSet G := by
    rw [← hGG']
    exact (IT.measurable_hist M) hG'm
  -- Under `κ⁻` and `e₁`, `G` has the same probability (masked histories at `r`).
  have hPmG : Pm G = trajMeasure alg e₁ G := by
    set Ym : ℕ → (ℕ → Round Unit α ℝ) → ℝ := fun n ↦ if n < r then IT.feedback n else fun _ ↦ 0
      with hYm
    have hYmm : ∀ n, Measurable (Ym n) := fun n ↦ by
      by_cases hn : n < r
      · simp only [hYm, hn, ↓reduceIte]
        exact IT.measurable_feedback n
      · simp only [hYm, hn, ↓reduceIte]
        exact measurable_const
    have hmeas : Measurable (history IT.obs IT.action Ym M) :=
      measurable_history IT.measurable_obs IT.measurable_action hYmm M
    have hpre : history IT.obs IT.action Ym M ⁻¹' G' = G := by
      ext ω
      simp only [Set.mem_preimage, hG', hG, Set.mem_ofPred_eq]
      rw [← pullCount_eq_pullCount' (O := IT.obs) (R' := Ym)]
    have hlaw := map_history_maskFeedback_eq (M := M) alg (env := Environment.bandit κm)
      (env' := e₁) (fun n hn ↦ by simp [e₁, hn]) halg 0
    rw [← hpre, ← Measure.map_apply hmeas hG'm, hlaw, Measure.map_apply hmeas hG'm]
  have hdens : ∀ ω : ℕ → Round Unit α ℝ, ∏ i : Fin M, w i (IT.hist M ω i).action =
      ENNReal.ofReal c ^ pullCount IT.action a r ω := fun ω ↦ by
    rw [← prod_ite_eq_pow_pullCount hrM a ω]
    rfl
  have hDm : Measurable fun h : Hist Unit α ℝ M ↦ ∏ i : Fin M, w i (h i).action :=
    Finset.measurable_prod _ fun i _ ↦
      (hw i).comp (Round.measurable_action.comp (measurable_pi_apply i))
  have hZm : Measurable fun ω : ℕ → Round Unit α ℝ ↦
      ENNReal.ofReal c ^ pullCount IT.action a r ω :=
    Measurable.of_discrete.comp (measurable_pullCount IT.measurable_action a r)
  have hG1 : ∫⁻ ω in G, ENNReal.ofReal c ^ pullCount IT.action a r ω ∂Pp ≤
      trajMeasure alg e₁ G := by
    calc ∫⁻ ω in G, ENNReal.ofReal c ^ pullCount IT.action a r ω ∂Pp
        = ∫⁻ h in G', ∏ i : Fin M, w i (h i).action ∂(Pp.map (IT.hist M)) := by
          rw [setLIntegral_map hG'm hDm (IT.measurable_hist M), hGG']
          exact setLIntegral_congr_fun hGm fun ω _ ↦ (hdens ω).symm
      _ = (Pp.map (IT.hist M)).withDensity (fun h ↦ ∏ i : Fin M, w i (h i).action) G' :=
          (withDensity_apply _ hG'm).symm
      _ ≤ (trajMeasure alg e₁).map (IT.hist M) G' := Measure.le_iff'.mp hcm G'
      _ = trajMeasure alg e₁ G := by rw [Measure.map_apply (IT.measurable_hist M) hG'm, hGG']
  have hc1' : ENNReal.ofReal c ≤ 1 := ENNReal.ofReal_le_one.mpr hc1
  have hG2 : ∫⁻ ω in Gᶜ, ENNReal.ofReal c ^ pullCount IT.action a r ω ∂Pp ≤ Pp Gᶜ := by
    calc ∫⁻ ω in Gᶜ, ENNReal.ofReal c ^ pullCount IT.action a r ω ∂Pp
        ≤ ∫⁻ _ in Gᶜ, 1 ∂Pp := lintegral_mono fun ω ↦ pow_le_one₀ (zero_le) hc1'
      _ = Pp Gᶜ := by rw [setLIntegral_one]
  have hSLm : MeasurableSet SL := by
    rw [hSL, ← hist_preimage_pullCount'_le a r L]
    exact (IT.measurable_hist r) hFm
  have hL : ENNReal.ofReal (c ^ L) * Pp SL ≤
      ∫⁻ ω, ENNReal.ofReal c ^ pullCount IT.action a r ω ∂Pp := by
    calc ENNReal.ofReal (c ^ L) * Pp SL = ∫⁻ _ in SL, ENNReal.ofReal (c ^ L) ∂Pp := by
          rw [setLIntegral_const]
      _ ≤ ∫⁻ ω in SL, ENNReal.ofReal c ^ pullCount IT.action a r ω ∂Pp := by
          refine setLIntegral_mono hZm fun ω hω ↦ ?_
          rw [ENNReal.ofReal_pow hc0]
          exact pow_le_pow_of_le_one (zero_le) hc1' hω
      _ ≤ _ := setLIntegral_le_lintegral _ _
  have htot : ENNReal.ofReal (c ^ L) * Pp SL ≤ Pm G + Pp Gᶜ := by
    rw [hPmG]
    calc ENNReal.ofReal (c ^ L) * Pp SL
        ≤ ∫⁻ ω, ENNReal.ofReal c ^ pullCount IT.action a r ω ∂Pp := hL
      _ = ∫⁻ ω in G, ENNReal.ofReal c ^ pullCount IT.action a r ω ∂Pp +
          ∫⁻ ω in Gᶜ, ENNReal.ofReal c ^ pullCount IT.action a r ω ∂Pp :=
          (lintegral_add_compl _ hGm).symm
      _ ≤ _ := add_le_add hG1 hG2
  have htotR : c ^ L * Pp.real SL ≤ Pm.real G + Pp.real Gᶜ := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩)
      htot
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hc0 L),
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at this
  calc c ^ L * exp (-(T₀ * D + log 2) / q) ≤ c ^ L * Pp.real SL :=
        mul_le_mul_of_nonneg_left hpp (pow_nonneg hc0 L)
    _ ≤ Pm.real G + Pp.real Gᶜ := htotR
    _ ≤ _ := add_le_add (measureReal_le_two_mul_integral_pullCount_div alg _ a hM)
        (measureReal_compl_le_two_mul_sub_integral_pullCount_div alg _ a hM)

end Counts

section Laws

/-- **A law just above the level.** Let `P` have mean `m_P < m`, and let `Q` be a law on `[0, 1]`
with mean `> m`. For every `δ > 0` there is a law `ρ` on `[0, 1]` with
`m < m(ρ) < min(m + δ, m(Q))` and `KL(P, ρ) ≤ KL(P, Q)`: a mixture of `P` and `Q`. -/
lemma exists_unitLaws_mean_mem_Ioo {P Q : Measure ℝ} (hP : P ∈ unitLaws) (hQ : Q ∈ unitLaws)
    {m δ : ℝ} (hPm : P[id] < m) (hQm : m < Q[id]) (hδ : 0 < δ) :
    ∃ ρ ∈ unitLaws, m < ρ[id] ∧ ρ[id] < m + δ ∧ ρ[id] < Q[id] ∧ klDiv P ρ ≤ klDiv P Q := by
  have := hP.1
  have := hQ.1
  set η := min (δ / 2) ((Q[id] - m) / 2) with hη
  have hη0 : 0 < η := lt_min (by linarith) (by linarith)
  have hηδ : η < δ := (min_le_left _ _).trans_lt (by linarith)
  have hηQ : η < Q[id] - m := (min_le_right _ _).trans_lt (by linarith)
  set t := (m - P[id] + η) / (Q[id] - P[id]) with ht
  have hden : 0 < Q[id] - P[id] := by linarith
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hden.le
  have ht1 : t ≤ 1 := by rw [div_le_one hden]; linarith
  obtain ⟨hmem, hmean⟩ := mix_mem_unitLaws hP hQ ht0 ht1
  have hmean' : (1 - t) * P[id] + t * Q[id] = m + η := by
    have : t * (Q[id] - P[id]) = m - P[id] + η := by rw [ht]; field_simp
    linarith
  refine ⟨_, hmem, ?_, ?_, ?_, klDiv_mix_le ht0 ht1⟩ <;> rw [hmean, hmean'] <;> linarith

end Laws

section Asymptotic

variable {α : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The right-hand side of the finite-horizon inequalities is at most `M ^ p / M / 2` when
`E_{κ⁻}[N_a(M)] ≤ δ M ^ p` and `E_{κ⁺}[N_b(M)] ≤ δ M ^ p` for every `b ≠ a`, with `K δ ≤ 1/8`. -/
lemma rhs_le_of_counts_le (alg : Algorithm Unit α ℝ) (κm κp : Kernel α ℝ) [IsMarkovKernel κm]
    [IsMarkovKernel κp] (a : α) {M : ℕ} (hM : 0 < M) {p δ : ℝ} (hδ : 0 ≤ δ)
    (hδK : (Fintype.card α : ℝ) * δ ≤ 1 / 8)
    (hA : ∫ ω, (pullCount IT.action a M ω : ℝ) ∂(trajMeasure alg (Environment.bandit κm)) ≤
      δ * (M : ℝ) ^ p)
    (hB : ∀ b, b ≠ a → ∫ ω, (pullCount IT.action b M ω : ℝ)
      ∂(trajMeasure alg (Environment.bandit κp)) ≤ δ * (M : ℝ) ^ p) :
    2 * (∫ ω, (pullCount IT.action a M ω : ℝ) ∂(trajMeasure alg (Environment.bandit κm))) / M +
        2 * (M - ∫ ω, (pullCount IT.action a M ω : ℝ)
          ∂(trajMeasure alg (Environment.bandit κp))) / M ≤ (M : ℝ) ^ p / M / 2 := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hMp : 0 ≤ (M : ℝ) ^ p := Real.rpow_nonneg hMpos.le p
  set Pp := trajMeasure alg (Environment.bandit κp)
  have hsum : (M : ℝ) - ∫ ω, (pullCount IT.action a M ω : ℝ) ∂Pp =
      ∑ b ∈ univ.erase a, ∫ ω, (pullCount IT.action b M ω : ℝ) ∂Pp := by
    have htot : ∑ b, ∫ ω, (pullCount IT.action b M ω : ℝ) ∂Pp = M := by
      rw [← integral_finsetSum Finset.univ fun b _ ↦
        integrable_pullCount IT.measurable_action b M]
      have : (fun ω : ℕ → Round Unit α ℝ ↦ ∑ b : α, (pullCount IT.action b M ω : ℝ)) =
          fun _ ↦ (M : ℝ) := by
        funext ω
        have := sum_pullCount (A := (IT.action : ℕ → (ℕ → Round Unit α ℝ) → α)) (t := M)
          (ω := ω)
        exact_mod_cast this
      rw [this, integral_const, probReal_univ, one_smul]
    rw [← htot, ← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
    ring
  have hB' : (M : ℝ) - ∫ ω, (pullCount IT.action a M ω : ℝ) ∂Pp ≤
      Fintype.card α * (δ * (M : ℝ) ^ p) := by
    rw [hsum]
    calc ∑ b ∈ univ.erase a, ∫ ω, (pullCount IT.action b M ω : ℝ) ∂Pp
        ≤ ∑ b ∈ univ.erase a, δ * (M : ℝ) ^ p :=
          Finset.sum_le_sum fun b hb ↦ hB b (Finset.ne_of_mem_erase hb)
      _ ≤ ∑ b : α, δ * (M : ℝ) ^ p :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            fun _ _ _ ↦ mul_nonneg hδ hMp
      _ = Fintype.card α * (δ * (M : ℝ) ^ p) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hK1 : (1 : ℝ) ≤ Fintype.card α := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨a⟩
  have h3 : δ * (M : ℝ) ^ p ≤ Fintype.card α * (δ * (M : ℝ) ^ p) :=
    le_mul_of_one_le_left (mul_nonneg hδ hMp) hK1
  have h4 : (Fintype.card α : ℝ) * (δ * (M : ℝ) ^ p) ≤ (M : ℝ) ^ p / 8 := by
    rw [← mul_assoc]
    nlinarith
  have e : (M : ℝ) ^ p / M / 2 = ((M : ℝ) ^ p / 2) / M := by ring
  rw [e, ← add_div]
  refine div_le_div_of_nonneg_right ?_ hMpos.le
  linarith

/-- **Arithmetic two batches ahead.** Let `0 < γ ≤ 1`, `D ≥ 0`, `lM > 0` and `lam > 0`. If
`-lam L - (T₀ D + log 2) / q ≤ (γ / 4) lM - lM`, `lam L ≤ (γ / 4) lM + lam`, `q ≥ 1 - γ / 4`,
`c' D ≤ 1 - γ` and `lam + log 2 + 1 < (γ / 4) lM`, then `c' lM < T₀`. -/
lemma two_batches_arith {T₀ D c' γ lM lam L q : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hD : 0 ≤ D) (hlM : 0 < lM) (hlam : 0 < lam)
    (hlog : L * -lam + -(T₀ * D + Real.log 2) / q ≤ γ / 4 * lM - lM)
    (hLlam : L * lam ≤ γ / 4 * lM + lam) (hq : 1 - γ / 4 ≤ q)
    (hc'D : c' * D ≤ 1 - γ) (hlarge : lam + Real.log 2 + 1 < γ / 4 * lM) : c' * lM < T₀ := by
  have hqpos : 0 < q := by linarith
  have hY : (1 - γ / 4) * lM - L * lam ≤ (T₀ * D + Real.log 2) / q := by
    rw [neg_div] at hlog
    have e2 : (1 - γ / 4) * lM = lM - γ / 4 * lM := by ring
    rw [e2]
    linarith
  have hB' : (1 - γ / 2) * lM - lam ≤ (1 - γ / 4) * lM - L * lam := by
    have e1 : (1 - γ / 2) * lM = lM - γ / 2 * lM := by ring
    have e2 : (1 - γ / 4) * lM = lM - γ / 4 * lM := by ring
    have e3 : γ / 2 * lM = 2 * (γ / 4 * lM) := by ring
    rw [e1, e2, e3]
    linarith
  have hBpos : 0 ≤ (1 - γ / 4) * lM - L * lam := by
    have e1 : (1 - γ / 2) * lM = lM - 2 * (γ / 4 * lM) := by ring
    have hγlM : γ / 4 * lM ≤ lM / 4 := by nlinarith
    have : 0 ≤ (1 - γ / 2) * lM - lam := by
      rw [e1]
      linarith [Real.log_pos one_lt_two]
    linarith
  have h1 : q * ((1 - γ / 4) * lM - L * lam) ≤ T₀ * D + Real.log 2 := by
    rw [le_div_iff₀ hqpos] at hY
    linarith
  have h3 : (1 - γ / 4) * ((1 - γ / 2) * lM - lam) ≤ T₀ * D + Real.log 2 :=
    calc (1 - γ / 4) * ((1 - γ / 2) * lM - lam) ≤ (1 - γ / 4) * ((1 - γ / 4) * lM - L * lam) :=
          mul_le_mul_of_nonneg_left hB' (by linarith)
      _ ≤ q * ((1 - γ / 4) * lM - L * lam) := mul_le_mul_of_nonneg_right hq hBpos
      _ ≤ _ := h1
  have h4 : lM - 3 * (γ / 4 * lM) - lam ≤ (1 - γ / 4) * ((1 - γ / 2) * lM - lam) := by
    have : 0 ≤ γ ^ 2 / 8 * lM + γ / 4 * lam := by positivity
    have e : (1 - γ / 4) * ((1 - γ / 2) * lM - lam) =
        lM - 3 * (γ / 4 * lM) - lam + (γ ^ 2 / 8 * lM + γ / 4 * lam) := by ring
    rw [e]
    linarith
  by_contra hcon
  rw [not_lt] at hcon
  have hT₀D : T₀ * D ≤ lM - 4 * (γ / 4 * lM) :=
    calc T₀ * D ≤ c' * lM * D := mul_le_mul_of_nonneg_right hcon hD
      _ = (c' * D) * lM := by ring
      _ ≤ (1 - γ) * lM := mul_le_mul_of_nonneg_right hc'D hlM.le
      _ = lM - 4 * (γ / 4 * lM) := by ring
  linarith

omit [Fintype α] [DecidableEq α] in
/-- **The alternative instances two batches ahead.** For `ν ∈ 𝒫`, a suboptimal arm `a`, a law `Q`
on `[0, 1]` with mean above `m⋆` and `KL(ν_a, Q) < ∞`, and `s ∈ (0, 1)`, there are instances
`κ⁺, κ⁻ ∈ 𝒫` that differ from `ν` only at `a`, with `a` the unique optimal arm of `κ⁺`, `a`
suboptimal in `κ⁻`, `κ⁻_a ≥ (1 - s) κ⁺_a` and `KL(ν_a, κ⁺_a) ≤ KL(ν_a, Q)`: `κ⁺_a` is a mixture
of `ν_a` and `Q` with mean in `(m⋆, m⋆ / (1 - s))`, and `κ⁻_a = (1 - s) κ⁺_a + s δ_0`. -/
lemma exists_two_alternatives [Finite α] {ν : Kernel α ℝ} [IsMarkovKernel ν]
    (hν : ν ∈ unitBandits α)
    {a : α} (ha : 0 < gap ν a) {Q : Measure ℝ} (hQ : Q ∈ unitLaws)
    (hQm : (⨆ b, (ν b)[id]) < Q[id]) (hDQ : klDiv (ν a) Q ≠ ∞) {s : ℝ} (hs0 : 0 < s)
    (hs1 : s < 1) :
    ∃ κp κm : Kernel α ℝ, IsMarkovKernel κp ∧ IsMarkovKernel κm ∧ κp ∈ unitBandits α ∧
      κm ∈ unitBandits α ∧ (∀ b ≠ a, ν b = κp b) ∧ (∀ b ≠ a, κm b = κp b) ∧
      (∀ b ≠ a, 0 < gap κp b) ∧ 0 < gap κm a ∧ ENNReal.ofReal (1 - s) • κp a ≤ κm a ∧
      klDiv (ν a) (κp a) ≤ klDiv (ν a) Q := by
  classical
  set m := ⨆ b, (ν b)[id] with hm
  have hmean_le : ∀ b, (ν b)[id] ≤ m := fun b ↦
    le_ciSup (f := fun b ↦ (ν b)[id]) (Set.finite_range _).bddAbove b
  have : Nonempty α := ⟨a⟩
  obtain ⟨bs, hbs⟩ := exists_eq_ciSup_of_finite (f := fun b ↦ (ν b)[id])
  have hma : (ν a)[id] < m := by
    have := ha
    rw [gap, ← hm] at this
    linarith
  have hm0 : 0 < m :=
    lt_of_le_of_lt (integral_id_mem_Icc_of_mem_unitLaws (hν.1 a)).1 hma
  have hbsa : bs ≠ a := by
    rintro rfl
    have : (ν bs)[id] = m := hbs
    linarith
  have hQ1 : Q[id] < 1 :=
    integral_id_lt_one_of_klDiv_ne_top hQ hDQ ((hmean_le a).trans_lt hν.2)
  -- `κ⁺_a = ρ⁺`, a mixture of `ν_a` and `Q` with mean in `(m⋆, m⋆ + δ)`, `m⋆ + δ = m⋆ / (1 - s)`
  set δ := m * s / (1 - s) with hδ_def
  have hδ : 0 < δ := div_pos (mul_pos hm0 hs0) (by linarith)
  obtain ⟨ρp, hρp, hρp1, hρp2, hρp3, hρpKL⟩ :=
    exists_unitLaws_mean_mem_Ioo (hν.1 a) hQ hma hQm hδ
  obtain ⟨hρm, hρmmean⟩ := mix_mem_unitLaws hρp (dirac_mem_unitLaws ⟨le_rfl, zero_le_one⟩)
    hs0.le hs1.le
  -- `κ⁻_a = ρ⁻ = (1 - s) ρ⁺ + s δ_0`, of mean `(1 - s) m(ρ⁺) < m⋆`
  set ρm := ENNReal.ofReal (1 - s) • ρp + ENNReal.ofReal s • Measure.dirac (0 : ℝ) with hρm_def
  have hρmlt : ρm[id] < m := by
    rw [hρmmean]
    have h0 : (Measure.dirac (0 : ℝ))[id] = 0 := by simp
    rw [h0, mul_zero, add_zero]
    have h2 : m + δ = m / (1 - s) := by
      rw [hδ_def]
      field_simp
      ring
    have : ρp[id] < m / (1 - s) := by linarith
    rwa [lt_div_iff₀ (by linarith), mul_comm] at this
  -- the kernels `κ± = ν` with the law of `a` replaced by `ρ±`
  have hupd : ∀ ρ : Measure ℝ, IsProbabilityMeasure ρ →
      ∀ b, IsProbabilityMeasure (Function.update (fun b ↦ ν b) a ρ b) := fun ρ hρ b ↦ by
    rcases eq_or_ne b a with rfl | hb
    · rwa [Function.update_self]
    · rw [Function.update_of_ne hb]
      infer_instance
  have hupdp := hupd ρp hρp.1
  have hupdm := hupd ρm hρm.1
  set κp := Kernel.ofFunOfCountable (Function.update (fun b ↦ ν b) a ρp)
  set κm := Kernel.ofFunOfCountable (Function.update (fun b ↦ ν b) a ρm)
  have hκpa : κp a = ρp := by simp [κp]
  have hκma : κm a = ρm := by simp [κm]
  have hκp : ∀ b ≠ a, ν b = κp b := fun b hb ↦ by simp [κp, Function.update_of_ne hb]
  have hκm : ∀ b ≠ a, ν b = κm b := fun b hb ↦ by simp [κm, Function.update_of_ne hb]
  -- a kernel equal to `ν` off `a`, whose law at `a` is in `𝓜` with mean `< 1`, is in `𝒫`
  have hmem : ∀ κ : Kernel α ℝ, (∀ b ≠ a, ν b = κ b) → κ a ∈ unitLaws → (κ a)[id] < 1 →
      κ ∈ unitBandits α := by
    intro κ hκ hκa hκa1
    refine ⟨fun b ↦ ?_, ?_⟩
    · rcases eq_or_ne b a with rfl | hb
      · exact hκa
      · rw [← hκ b hb]
        exact hν.1 b
    · obtain ⟨b₀, hb₀⟩ := exists_eq_ciSup_of_finite (f := fun b ↦ (κ b)[id])
      rw [← hb₀]
      rcases eq_or_ne b₀ a with rfl | hb
      · exact hκa1
      · rw [← hκ b₀ hb]
        exact (hmean_le b₀).trans_lt hν.2
  refine ⟨κp, κm, inferInstance, inferInstance,
    hmem κp hκp (by rwa [hκpa]) (by rw [hκpa]; linarith),
    hmem κm hκm (by rwa [hκma]) (by rw [hκma]; linarith [hν.2]), hκp,
    fun b hb ↦ (hκm b hb).symm.trans (hκp b hb), fun b hb ↦ ?_, ?_, ?_, ?_⟩
  -- the gaps: `a` is the unique optimal arm of `κ⁺`, and sub-optimal in `κ⁻`
  · have h1 := LMLExplore.Bandits.sub_le_gap κp b a
    rw [hκpa, ← hκp b hb] at h1
    linarith [hmean_le b]
  · have h1 := LMLExplore.Bandits.sub_le_gap κm a bs
    rw [hκma, ← hκm bs hbsa] at h1
    have : (ν bs)[id] = m := hbs
    linarith
  · rw [hκpa, hκma, hρm_def]
    exact Measure.le_add_right le_rfl
  · rw [hκpa]
    exact hρpKL

/-- **One index two batches ahead.** The bound of
`eventually_lt_integral_pullCount_div_log_t_add_two` at a fixed index `ℓ`, given the alternative
instances (`exists_two_alternatives`), the consistency bounds at `t (ℓ + 2)` and the logarithmic
bound on `E_ν[N_a(t (ℓ + 1))]`: `c' log t (ℓ + 2) < E_ν[N_a(t ℓ)]`. -/
lemma two_batches_step {K : ℕ} (g : Grid K) {alg : Algorithm Unit α ℝ} (hb : IsBatched alg g)
    {ν κp κm : Kernel α ℝ} [IsMarkovKernel ν] [IsMarkovKernel κp] [IsMarkovKernel κm] {a : α}
    (hκp : ∀ b ≠ a, ν b = κp b) (hmp : ∀ b ≠ a, κm b = κp b) {s lam : ℝ} (hs0 : 0 < s)
    (hs1 : s < 1) (h1s : 1 - s = exp (-lam)) (hlam : 0 < lam)
    (hdom : ENNReal.ofReal (1 - s) • κp a ≤ κm a) (hDne : klDiv (ν a) (κp a) ≠ ∞)
    {c' γ C' : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hc'D : c' * (klDiv (ν a) (κp a)).toReal ≤ 1 - γ) (hC'1 : 1 ≤ C')
    (hlam_def : lam = γ * (γ / 4) / (4 * C')) {δc : ℝ} (hδc : 0 ≤ δc)
    (hδcK : (Fintype.card α : ℝ) * δc ≤ 1 / 8) (ℓ : ℕ)
    (hA : ∫ ω, (pullCount IT.action a (g.t (ℓ + 2)) ω : ℝ)
      ∂(trajMeasure alg (Environment.bandit κm)) ≤ δc * (g.t (ℓ + 2) : ℝ) ^ (γ / 4))
    (hB : ∀ b, b ≠ a → ∫ ω, (pullCount IT.action b (g.t (ℓ + 2)) ω : ℝ)
      ∂(trajMeasure alg (Environment.bandit κp)) ≤ δc * (g.t (ℓ + 2) : ℝ) ^ (γ / 4))
    (hC : ∫ ω, (pullCount IT.action a (g.t (ℓ + 1)) ω : ℝ)
      ∂(trajMeasure alg (Environment.bandit ν)) ≤ C' * Real.log (g.t (ℓ + 2)))
    (hlarge : lam + Real.log 2 + 1 < γ / 4 * Real.log (g.t (ℓ + 2))) :
    c' * Real.log (g.t (ℓ + 2)) < ∫ ω, (pullCount IT.action a (g.t ℓ) ω : ℝ)
      ∂(trajMeasure alg (Environment.bandit ν)) := by
  have hr₀r : g.t ℓ ≤ g.t (ℓ + 1) := g.strictMono.monotone (Nat.le_succ ℓ)
  have hrM : g.t (ℓ + 1) ≤ g.t (ℓ + 2) := g.strictMono.monotone (Nat.le_succ (ℓ + 1))
  have hM2 : 2 ≤ g.t (ℓ + 2) := g.two_le_t (by omega)
  have hMpos : (0 : ℝ) < g.t (ℓ + 2) := by exact_mod_cast (show 0 < g.t (ℓ + 2) by omega)
  have hlogM : 0 < Real.log (g.t (ℓ + 2)) := g.logEnd_pos (ℓ := ℓ + 2) (by omega)
  have hsees : ∀ j n, n < g.t (j + 1) → SeesRewardsUpTo alg n (g.t j) :=
    fun _ _ hn ↦ hb.seesRewardsUpTo_of_lt hn
  have hη0 : 0 < γ / 4 := by positivity
  set T := ∫ ω, (pullCount IT.action a (g.t (ℓ + 1)) ω : ℝ)
    ∂(trajMeasure alg (Environment.bandit ν)) with hT_def
  have hT0 : 0 ≤ T := integral_nonneg fun _ ↦ Nat.cast_nonneg _
  set L := ⌈T / (γ / 4)⌉₊ with hL_def
  have hTL : T ≤ γ / 4 * L := by
    have := Nat.le_ceil (T / (γ / 4))
    rw [← hL_def, div_le_iff₀ hη0] at this
    linarith
  have hL1 : (L : ℝ) ≤ T / (γ / 4) + 1 := (Nat.ceil_lt_add_one (div_nonneg hT0 hη0.le)).le
  set SL := {ω : ℕ → Round Unit α ℝ | pullCount IT.action a (g.t (ℓ + 1)) ω ≤ L} with hSL
  have hSLm : MeasurableSet SL := measurableSet_le
    (measurable_pullCount IT.measurable_action a _) measurable_const
  have hcompl : SLᶜ = {ω | ((L : ℝ) + 1) ≤ (pullCount IT.action a (g.t (ℓ + 1)) ω : ℝ)} := by
    ext ω
    simp only [hSL, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
    constructor
    · intro h
      exact_mod_cast h
    · intro h
      exact_mod_cast h
  have hq : 1 - γ / 4 ≤ (trajMeasure alg (Environment.bandit ν)).real SL := by
    have hmk := mul_meas_ge_le_integral_of_nonneg (μ := trajMeasure alg (Environment.bandit ν))
      (f := fun ω ↦ (pullCount IT.action a (g.t (ℓ + 1)) ω : ℝ))
      (ae_of_all _ fun _ ↦ Nat.cast_nonneg _)
      (integrable_pullCount IT.measurable_action a _) ((L : ℝ) + 1)
    rw [← hcompl, probReal_compl_eq_one_sub hSLm] at hmk
    have hL0 : (0 : ℝ) < L + 1 := by positivity
    have : ((L : ℝ) + 1) * (1 - (trajMeasure alg (Environment.bandit ν)).real SL) ≤
        ((L : ℝ) + 1) * (γ / 4) := by
      have e : ((L : ℝ) + 1) * (γ / 4) = γ / 4 * L + γ / 4 := by ring
      rw [e]
      linarith
    have := le_of_mul_le_mul_left this hL0
    linarith
  have hqpos : 0 < (trajMeasure alg (Environment.bandit ν)).real SL := by linarith
  have key := two_batches_finite (L := L) hr₀r hrM (by omega)
    (fun n hn ↦ hsees ℓ n hn) (fun n hn ↦ hsees (ℓ + 1) n hn) hκp hmp
    (by linarith : (0 : ℝ) ≤ 1 - s) (by linarith : 1 - s ≤ 1) hdom hDne hqpos
  have hrhs := rhs_le_of_counts_le alg κm κp a (show 0 < g.t (ℓ + 2) by omega) hδc hδcK hA hB
  have hfin := key.trans hrhs
  set D := (klDiv (ν a) (κp a)).toReal with hD_def
  set T₀ := ∫ ω, (pullCount IT.action a (g.t ℓ) ω : ℝ) ∂(trajMeasure alg (Environment.bandit ν))
  set q := (trajMeasure alg (Environment.bandit ν)).real SL
  have hMp : 0 < (g.t (ℓ + 2) : ℝ) ^ (γ / 4) := Real.rpow_pos_of_pos hMpos _
  have hlhs_pos : 0 < (1 - s) ^ L * exp (-(T₀ * D + Real.log 2) / q) :=
    mul_pos (pow_pos (by linarith) L) (exp_pos _)
  have hhalf : (g.t (ℓ + 2) : ℝ) ^ (γ / 4) / (g.t (ℓ + 2)) / 2 ≤
      (g.t (ℓ + 2) : ℝ) ^ (γ / 4) / (g.t (ℓ + 2)) := by
    have : 0 ≤ (g.t (ℓ + 2) : ℝ) ^ (γ / 4) / (g.t (ℓ + 2)) := div_nonneg hMp.le hMpos.le
    linarith
  have hlog := Real.log_le_log hlhs_pos (hfin.trans hhalf)
  rw [Real.log_mul (pow_pos (by linarith) L).ne' (exp_pos _).ne', Real.log_pow, Real.log_exp,
    h1s, Real.log_exp, Real.log_div hMp.ne' hMpos.ne', Real.log_rpow hMpos] at hlog
  have hTC : T ≤ C' * Real.log (g.t (ℓ + 2)) := hC
  have hLlam : (L : ℝ) * lam ≤ γ / 4 * Real.log (g.t (ℓ + 2)) + lam := by
    have h1 : (L : ℝ) ≤ C' * Real.log (g.t (ℓ + 2)) / (γ / 4) + 1 := hL1.trans (by
      have : T / (γ / 4) ≤ C' * Real.log (g.t (ℓ + 2)) / (γ / 4) :=
        div_le_div_of_nonneg_right hTC hη0.le
      linarith)
    have hC'0 : 0 < C' := by linarith
    calc (L : ℝ) * lam ≤ (C' * Real.log (g.t (ℓ + 2)) / (γ / 4) + 1) * lam :=
          mul_le_mul_of_nonneg_right h1 hlam.le
      _ = γ / 4 * Real.log (g.t (ℓ + 2)) + lam := by
          rw [hlam_def]
          field_simp
  exact two_batches_arith hγ hγ1 ENNReal.toReal_nonneg hlogM hlam
    (by linarith) hLlam hq hc'D hlarge

omit [Fintype α] in
/-- **Two batches ahead** [INC-P000, Lemma `lem:twobatches`(ii), at the index `ℓ + 1`]. For every
grid, every learner batched on it and consistent at its batch ends on `𝒫`, every `ν ∈ 𝒫` and every
arm `a` with `gap ν a > 0` whose counts satisfy `E_ν[N_a(t_(ℓ+1))] = O(log t_(ℓ+2))`:
`liminf_ℓ E_ν[N_a(t_ℓ)] / log t_(ℓ+2) ≥ 1 / 𝒦_inf(ν_a, m⋆)`. The route is that of
`formalisation.tex`: the change of measure between `κ⁻` and `κ⁺` (`two_batches_finite`), which
costs `1 - s` per pull of `a` in batch `ℓ + 1`, data processing from the environment that is `ν`
before `t ℓ`, and consistency under `κ⁻` and `κ⁺`. -/
lemma eventually_lt_integral_pullCount_div_log_t_add_two [Finite α] {K : ℕ} (g : Grid K)
    {alg : Algorithm Unit α ℝ} (hb : IsBatched alg g)
    (hc : IsConsistentAtBatchEnds alg g (unitBandits α)) {ν : Kernel α ℝ} [IsMarkovKernel ν]
    (hν : ν ∈ unitBandits α) {a : α} (ha : 0 < gap ν a)
    (hlog : ∃ C, ∀ᶠ ℓ in atTop, (∫ ω, (pullCount IT.action a (g.t (ℓ + 1)) ω : ℝ)
        ∂(trajMeasure alg (Environment.bandit ν))) ≤ C * Real.log (g.t (ℓ + 2))) :
    ∀ c < 1 / (LMLExplore.Bandits.dInf unitLaws (ν a) (⨆ b, ∫ y, id y ∂(ν b))).toReal,
      ∀ᶠ ℓ in atTop, c < (∫ ω, (pullCount IT.action a (g.t ℓ) ω : ℝ)
          ∂(trajMeasure alg (Environment.bandit ν))) / Real.log (g.t (ℓ + 2)) := by
  intro c hcd
  have := Fintype.ofFinite α
  have hlogpos : ∀ ℓ, 0 < Real.log (g.t (ℓ + 2)) := fun ℓ ↦ g.logEnd_pos (ℓ := ℓ + 2) (by omega)
  rcases lt_or_ge c 0 with hc0 | hc0
  · exact Eventually.of_forall fun ℓ ↦ hc0.trans_le
      (div_nonneg (integral_nonneg fun _ ↦ Nat.cast_nonneg _) (hlogpos ℓ).le)
  set m := ⨆ b, ∫ y, id y ∂(ν b) with hm
  set d := (LMLExplore.Bandits.dInf unitLaws (ν a) m).toReal with hd_def
  have hd : 0 < d := by
    have h1 : 0 < 1 / d := hc0.trans_lt hcd
    rwa [one_div_pos] at h1
  have hdtop : LMLExplore.Bandits.dInf unitLaws (ν a) m ≠ ∞ := fun h ↦ by
    simp [hd_def, h] at hd
  obtain ⟨c', hcc', hc'd⟩ := exists_between hcd
  have hc'0 : 0 < c' := hc0.trans_lt hcc'
  have hdc' : d < 1 / c' := by
    rw [lt_div_iff₀ hc'0]
    rwa [lt_div_iff₀ hd, mul_comm] at hc'd
  have hlt : LMLExplore.Bandits.dInf unitLaws (ν a) m < ENNReal.ofReal (1 / c') := by
    rw [← ENNReal.ofReal_toReal hdtop]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hdc'
  obtain ⟨Q, hQ, hQm, hQD⟩ := LMLExplore.Bandits.dInf_lt_iff.mp hlt
  have hDQne : klDiv (ν a) Q ≠ ∞ := ne_top_of_lt hQD
  have hc'DQ : c' * (klDiv (ν a) Q).toReal < 1 := by
    have : (klDiv (ν a) Q).toReal < 1 / c' := ENNReal.toReal_lt_of_lt_ofReal hQD
    rwa [lt_div_iff₀ hc'0, mul_comm] at this
  -- The margins.
  set γ := 1 - c' * (klDiv (ν a) Q).toReal with hγ_def
  have hγ : 0 < γ := by rw [hγ_def]; linarith
  have hγ1 : γ ≤ 1 := by
    rw [hγ_def]
    nlinarith [ENNReal.toReal_nonneg (a := klDiv (ν a) Q)]
  obtain ⟨C, hC⟩ := hlog
  set C' := max C 1 with hC'_def
  have hC'1 : 1 ≤ C' := le_max_right _ _
  set lam := γ * (γ / 4) / (4 * C') with hlam_def
  have hlam : 0 < lam := by positivity
  set s := 1 - exp (-lam) with hs_def
  have hs0 : 0 < s := by
    rw [hs_def]
    linarith [Real.exp_lt_one_iff.mpr (show -lam < 0 by linarith)]
  have hs1 : s < 1 := by rw [hs_def]; linarith [exp_pos (-lam)]
  have h1s : 1 - s = exp (-lam) := by rw [hs_def]; ring
  -- The alternative instances.
  obtain ⟨κp, κm, hκpM, hκmM, hκp_mem, hκm_mem, hκp, hmp, hgapp, hgapm, hdom, hKL⟩ :=
    exists_two_alternatives hν ha hQ hQm hDQne hs0 hs1
  have hDne : klDiv (ν a) (κp a) ≠ ∞ := ne_top_of_le_ne_top hDQne hKL
  have hc'D : c' * (klDiv (ν a) (κp a)).toReal ≤ 1 - γ := by
    rw [hγ_def]
    have := ENNReal.toReal_mono hDQne hKL
    nlinarith
  -- Consistency under `κ⁻` (for `a`) and `κ⁺` (for the other arms), at the index `ℓ + 2`.
  have hKα : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨a⟩
  set δc := 1 / (8 * (Fintype.card α : ℝ)) with hδc_def
  have hδc : 0 < δc := by positivity
  have hδcK : (Fintype.card α : ℝ) * δc ≤ 1 / 8 := by
    rw [hδc_def]
    exact le_of_eq (by field_simp)
  have hp0 : 0 < γ / 4 := by positivity
  have hA := (tendsto_order.1 ((hc κm hκm_mem a hgapm (γ / 4) hp0).comp
    (tendsto_add_atTop_nat 2))).2 δc hδc
  have hB : ∀ᶠ ℓ in atTop, ∀ b, b ≠ a →
      (∫ ω, (pullCount IT.action b (g.t (ℓ + 2)) ω : ℝ)
        ∂(trajMeasure alg (Environment.bandit κp))) / (g.t (ℓ + 2) : ℝ) ^ (γ / 4) < δc := by
    refine eventually_all.2 fun b ↦ ?_
    by_cases hba : b = a
    · exact Eventually.of_forall fun _ h ↦ absurd hba h
    · exact ((tendsto_order.1 ((hc κp hκp_mem b (hgapp b hba) (γ / 4) hp0).comp
        (tendsto_add_atTop_nat 2))).2 δc hδc).mono fun _ h _ ↦ h
  have hlarge : ∀ᶠ ℓ in atTop, lam + Real.log 2 + 1 < γ / 4 * Real.log (g.t (ℓ + 2)) := by
    have ht : Tendsto (fun ℓ ↦ Real.log (g.t (ℓ + 2))) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp
        (g.strictMono.tendsto_atTop.comp (tendsto_add_atTop_nat 2)))
    exact (ht.const_mul_atTop hp0).eventually_gt_atTop (lam + Real.log 2 + 1)
  filter_upwards [hA, hB, hC, hlarge] with ℓ hAℓ hBℓ hCℓ hLℓ
  simp only [Function.comp_apply] at hAℓ
  have hMp : 0 < (g.t (ℓ + 2) : ℝ) ^ (γ / 4) := Real.rpow_pos_of_pos (by
    have := g.two_le_t (ℓ := ℓ + 2) (by omega)
    exact_mod_cast (show 0 < g.t (ℓ + 2) by omega)) _
  have hstep := two_batches_step g hb hκp hmp hs0 hs1 h1s hlam hdom hDne hγ hγ1 hc'D hC'1 rfl
    hδc.le hδcK ℓ ((div_lt_iff₀ hMp).mp hAℓ).le (fun b hb ↦ ((div_lt_iff₀ hMp).mp (hBℓ b hb)).le)
    (hCℓ.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hlogpos ℓ).le)) hLℓ
  rw [lt_div_iff₀ (hlogpos ℓ)]
  calc c * Real.log (g.t (ℓ + 2)) ≤ c' * Real.log (g.t (ℓ + 2)) :=
        mul_le_mul_of_nonneg_right hcc'.le (hlogpos ℓ).le
    _ < _ := hstep

end Asymptotic

end Incognita.BatchedBandits
