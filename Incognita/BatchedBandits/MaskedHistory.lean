/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.Batched
public import Incognita.ForLML.Probability.HasCondDistrib
public import LeanMachineLearning.SequentialLearning.DivergenceDecomposition
public import LeanMachineLearning.SequentialLearning.IonescuTulceaSpace

/-! # The actions of a batched learner do not see the rewards of the current batch

Let `alg` be a learner whose policies at the rounds `n < M` see the rewards of the rounds `< r`
only (for a learner batched on a grid `g`, `r = t ℓ` and `M = t (ℓ + 1)`: the rounds of batch
`ℓ + 1` see the rewards of the first `ℓ` batches, `IsBatched`). Then the law of the history of
the first `M` rounds **with the rewards of the rounds `≥ r` replaced by a fixed value `y₀`**
(the *masked history*) is the same under any two environments that have the same feedback kernels
at the rounds `< r`. In particular the actions of the rounds `< M`, and the counts `N_c(M)`,
have the same law under the two environments. This is the step "the actions of batch `ℓ + 1` do
not depend on the rewards of batch `ℓ + 1`" of [INC-P000, Appendix `sec:app-lower`].

The second part computes the divergence for the *switched* environment, which follows a bandit
`ν'` at the rounds `< r` and a bandit `ν` afterwards: the relative entropy between the laws of the
histories of the first `M ≥ r` rounds under `ν` and under the switched environment is the one
between the laws of the histories of the first `r` rounds under `ν` and under `ν'`.

## Main statements

* `Learning.IsAlgEnvSeq.isAlgEnvSeqUntil_ite_lt`: the masked process of a run is an
  algorithm-environment sequence until `M` for an environment whose feedback is `δ_{y₀}` at the
  rounds `≥ r`.
* `Incognita.BatchedBandits.map_history_ite_lt_eq`: the masked histories have the same law
  under two environments that agree at the rounds `< r`.
* `Incognita.BatchedBandits.klDiv_map_hist_switch`: the divergence for the switched environment.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Learning Finset

namespace Incognita.BatchedBandits

variable {𝓐 𝓨 : Type*} [MeasurableSpace 𝓐] [MeasurableSpace 𝓨]

/-- The map that replaces the rewards of the rounds `≥ r` of an `n`-round history by `y₀` is
measurable. -/
lemma measurable_hist_ite_lt (r n : ℕ) (y₀ : 𝓨) :
    Measurable (fun (h : Hist Unit 𝓐 𝓨 n) (i : Fin n) ↦
      if (i : ℕ) < r then h i else ((), (h i).action, y₀)) := by
  refine Measurable.of_eval fun i ↦ ?_
  by_cases hi : (i : ℕ) < r
  · simp only [hi, ↓reduceIte]
    exact measurable_pi_apply i
  · simp only [hi, ↓reduceIte]
    exact measurable_const.prodMk
      ((Round.measurable_action.comp (measurable_pi_apply i)).prodMk measurable_const)

@[deprecated (since := "2026-11-19")] alias measurable_maskFeedback := measurable_hist_ite_lt

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {O : ℕ → Ω → Unit} {A : ℕ → Ω → 𝓐}
  {Y : ℕ → Ω → 𝓨}

omit [MeasurableSpace 𝓐] [MeasurableSpace 𝓨] in
/-- The history of the masked process is the masked history. -/
lemma history_ite_lt (r : ℕ) (y₀ : 𝓨) (n : ℕ) (ω : Ω) :
    history O A (fun m ↦ if m < r then Y m else fun _ ↦ y₀) n ω =
      fun i : Fin n ↦
        if (i : ℕ) < r then history O A Y n ω i else ((), (history O A Y n ω i).action, y₀) := by
  funext i
  by_cases hi : (i : ℕ) < r
  · simp [history, hi]
  · simp [history, hi, Round.action]

@[deprecated (since := "2026-11-19")] alias history_maskFeedback := history_ite_lt

omit [MeasurableSpace 𝓐] [MeasurableSpace 𝓨] in
/-- Below `r`, the masked history is the history. -/
lemma history_ite_lt_of_le {r n : ℕ} (hn : n ≤ r) (y₀ : 𝓨) :
    history O A (fun m ↦ if m < r then Y m else fun _ ↦ y₀) n = history O A Y n := by
  funext ω i
  simp [history, show (i : ℕ) < r from i.2.trans_le hn]

@[deprecated (since := "2026-11-19")] alias history_maskFeedback_of_le := history_ite_lt_of_le

/-- The masked rewards (`Y m` for `m < r`, the constant `y₀` afterwards) are measurable. -/
private lemma measurable_maskedFeedback (hY : ∀ n, Measurable (Y n)) (r : ℕ) (y₀ : 𝓨) (m : ℕ) :
    Measurable (if m < r then Y m else fun _ : Ω ↦ y₀) := by
  by_cases hm : m < r
  · simp only [hm, ↓reduceIte]
    exact hY m
  · simp only [hm, ↓reduceIte]
    exact measurable_const

variable {P : Measure Ω} [IsProbabilityMeasure P] {alg : Algorithm Unit 𝓐 𝓨}
  {env envM : Environment Unit 𝓐 𝓨}

/-- **The masked process is an algorithm-environment sequence until `M`.** Let `(O, A, Y)` be a
run of `alg` against `env`, and let `alg` see the rewards of the rounds `< r` only at the rounds
`n < M`. Replace the rewards of the rounds `≥ r` by `y₀`. The process obtained is a run of `alg`
until `M` against any environment `envM` whose feedback kernels are those of `env` at the rounds
`< r` and `δ_{y₀}` at the rounds `≥ r`. -/
lemma _root_.Learning.IsAlgEnvSeq.isAlgEnvSeqUntil_ite_lt (h : IsAlgEnvSeq O A Y alg env P)
    {r M : ℕ} (y₀ : 𝓨)
    (halg : ∀ n < M, SeesRewardsUpTo alg n r)
    (hlt : ∀ n < r, envM.feedback n = env.feedback n)
    (hge : ∀ n, r ≤ n → envM.feedback n = Kernel.const _ (Measure.dirac y₀)) :
    IsAlgEnvSeqUntil O A (fun n ↦ if n < r then Y n else fun _ ↦ y₀) alg envM P M where
  measurable_obs := h.measurable_obs
  measurable_action := h.measurable_action
  measurable_feedback := measurable_maskedFeedback h.measurable_feedback r y₀
  hasCondDistrib_obs n _ :=
    hasCondDistrib_unit (measurable_history h.measurable_obs h.measurable_action
      (measurable_maskedFeedback h.measurable_feedback r y₀) n).aemeasurable _ _
  -- the policies see the masked history only through the rewards of the rounds `< r`
  hasCondDistrib_action n hn := by
    have hf : Measurable (Prod.map (fun (h : Hist Unit 𝓐 𝓨 n) (i : Fin n) ↦
        if (i : ℕ) < r then h i else ((), (h i).action, y₀)) (id : Unit → Unit)) :=
      (measurable_hist_ite_lt r n y₀).prodMap measurable_id
    have heq : (fun ω ↦ (history O A (fun m ↦ if m < r then Y m else fun _ ↦ y₀) n ω, O n ω)) =
        (Prod.map (fun (h : Hist Unit 𝓐 𝓨 n) (i : Fin n) ↦
          if (i : ℕ) < r then h i else ((), (h i).action, y₀)) id) ∘
          (fun ω ↦ (history O A Y n ω, O n ω)) := by
      funext ω
      simp only [Function.comp_apply, Prod.map_apply, id_eq]
      rw [history_ite_lt]
    rw [heq]
    refine HasCondDistrib.comp_right (hf := hf) ?_
    have hk : (alg.policy n).comap _ hf = alg.policy n := by
      ext1 x
      obtain ⟨x, u⟩ := x
      rw [Kernel.comap_apply]
      simp only [Prod.map_apply, id_eq]
      obtain rfl : u = () := Subsingleton.elim _ _
      refine halg n hn _ _ (fun i ↦ ?_) (fun i hi ↦ ?_)
      · by_cases hi : (i : ℕ) < r <;> simp [hi, Round.action]
      · simp [hi]
    rw [hk]
    exact h.hasCondDistrib_action n
  -- before `r` the feedback is that of `env`, from `r` on it is `δ_(y₀)`
  hasCondDistrib_feedback n hn := by
    by_cases hnr : n < r
    · have h1 : (if n < r then Y n else fun _ ↦ y₀) = Y n := by simp [hnr]
      rw [h1, history_ite_lt_of_le hnr.le, hlt n hnr]
      exact h.hasCondDistrib_feedback n
    · have h1 : (if n < r then Y n else fun _ ↦ y₀) = fun _ ↦ y₀ := by simp [hnr]
      rw [h1, hge n (not_lt.mp hnr)]
      exact hasCondDistrib_const_dirac (((measurable_history h.measurable_obs h.measurable_action
        (measurable_maskedFeedback h.measurable_feedback r y₀) n).prodMk
        (h.measurable_obs n)).prodMk (h.measurable_action n)) y₀

@[deprecated (since := "2026-11-19")]
alias isAlgEnvSeqUntil_maskFeedback := Learning.IsAlgEnvSeq.isAlgEnvSeqUntil_ite_lt

/-- **The masked histories have the same law under two environments that agree before `r`.**
If the policies of `alg` at the rounds `n < M` see the rewards of the rounds `< r` only, and the
environments `env`, `env'` have the same feedback kernels at the rounds `< r`, then the histories
of the first `M` rounds with the rewards of the rounds `≥ r` replaced by `y₀` have the same law
under `env` and `env'`. -/
lemma map_history_ite_lt_eq (alg : Algorithm Unit 𝓐 𝓨) {env env' : Environment Unit 𝓐 𝓨}
    {r M : ℕ} (henv : ∀ n < r, env.feedback n = env'.feedback n)
    (halg : ∀ n < M, SeesRewardsUpTo alg n r) (y₀ : 𝓨) :
    (trajMeasure alg env).map
        (history IT.obs IT.action (fun n ↦ if n < r then IT.feedback n else fun _ ↦ y₀) M) =
      (trajMeasure alg env').map
        (history IT.obs IT.action (fun n ↦ if n < r then IT.feedback n else fun _ ↦ y₀) M) := by
  let envM : Environment Unit 𝓐 𝓨 :=
    { obs := fun _ ↦ Kernel.const _ (Measure.dirac ())
      feedback := fun n ↦ if n < r then env.feedback n else Kernel.const _ (Measure.dirac y₀)
      isMarkovKernel_feedback := fun n ↦ by
        by_cases hn : n < r
        · simp only [hn, ↓reduceIte]
          infer_instance
        · simp only [hn, ↓reduceIte]
          infer_instance }
  have hlt : ∀ n < r, envM.feedback n = env.feedback n := fun n hn ↦ by simp [envM, hn]
  have hlt' : ∀ n < r, envM.feedback n = env'.feedback n := fun n hn ↦
    by simp [envM, hn, henv n hn]
  have hge : ∀ n, r ≤ n → envM.feedback n = Kernel.const _ (Measure.dirac y₀) :=
    fun n hn ↦ by simp [envM, not_lt.mpr hn]
  rw [((IT.isAlgEnvSeq_trajMeasure alg env).isAlgEnvSeqUntil_ite_lt y₀ halg hlt
      hge).map_history,
    ((IT.isAlgEnvSeq_trajMeasure alg env').isAlgEnvSeqUntil_ite_lt y₀ halg hlt'
      hge).map_history]

@[deprecated (since := "2026-11-19")] alias map_history_maskFeedback_eq := map_history_ite_lt_eq

/-- **Divergence for the switched environment.** Let `env` be the environment that follows the
bandit `ν'` at the rounds `< r` and the bandit `ν` at the rounds `≥ r`. For `r ≤ M`, the relative
entropy between the laws of the histories of the first `M` rounds under `ν` and under `env` is the
relative entropy between the laws of the histories of the first `r` rounds under `ν` and under
`ν'`: the rounds `≥ r` contribute nothing. -/
lemma klDiv_map_hist_switch (alg : Algorithm Unit 𝓐 𝓨) (ν ν' : Kernel 𝓐 𝓨) [IsMarkovKernel ν]
    [IsMarkovKernel ν'] {env : Environment Unit 𝓐 𝓨} {r M : ℕ} (hrM : r ≤ M)
    (hlt : ∀ n < r, env.feedback n = ν'.prodMkLeft _)
    (hge : ∀ n, r ≤ n → env.feedback n = ν.prodMkLeft _) :
    klDiv ((trajMeasure alg (Environment.bandit ν)).map (IT.hist M))
        ((trajMeasure alg env).map (IT.hist M)) =
      klDiv ((trajMeasure alg (Environment.bandit ν)).map (IT.hist r))
        ((trajMeasure alg (Environment.bandit ν')).map (IT.hist r)) := by
  have h := IT.isAlgEnvSeq_trajMeasure alg (Environment.bandit ν)
  have h₂ := IT.isAlgEnvSeq_trajMeasure alg env
  have h' := IT.isAlgEnvSeq_trajMeasure alg (Environment.bandit ν')
  rw [← IT.history_obs_action_feedback, ← IT.history_obs_action_feedback,
    h.klDiv_map_history_stepKernel h₂ M, h.klDiv_map_history_stepKernel h' r,
    ← Finset.sum_range_add_sum_Ico _ hrM]
  have hobs : ∀ n, env.obs n = (Environment.bandit ν).obs n := fun n ↦
    (Kernel.eq_const_dirac_of_subsingleton _ ()).trans (obs_bandit n).symm
  have hobs' : ∀ n, env.obs n = (Environment.bandit ν').obs n := fun n ↦
    (Kernel.eq_const_dirac_of_subsingleton _ ()).trans (obs_bandit n).symm
  have h0 : ∑ t ∈ Ico r M, klDiv
      ((trajMeasure alg (Environment.bandit ν)).map (history IT.obs IT.action IT.feedback t) ⊗ₘ
        stepKernel alg (Environment.bandit ν) t)
      ((trajMeasure alg (Environment.bandit ν)).map (history IT.obs IT.action IT.feedback t) ⊗ₘ
        stepKernel alg env t) = 0 := by
    refine Finset.sum_eq_zero fun t ht ↦ ?_
    have hrt : r ≤ t := (Finset.mem_Ico.mp ht).1
    have hs : stepKernel alg env t = stepKernel alg (Environment.bandit ν) t := by
      rw [stepKernel_def, stepKernel_def, hobs t, hge t hrt, feedback_bandit]
    rw [hs, klDiv_self]
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun t ht ↦ ?_
  have hs : stepKernel alg env t = stepKernel alg (Environment.bandit ν') t := by
    rw [stepKernel_def, stepKernel_def, hobs' t, hlt t (Finset.mem_range.mp ht), feedback_bandit]
  rw [hs]

end Incognita.BatchedBandits
