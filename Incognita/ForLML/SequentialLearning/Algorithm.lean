/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Kernel.Basic
public import LeanMachineLearning.SequentialLearning.Algorithm

/-! # Runs against environments with the same feedback

Complements to LML's `LeanMachineLearning.SequentialLearning.Algorithm`.

## Main statements

* `Learning.IsAlgEnvSeq.isAlgEnvSeqUntil_of_feedback_eq`: a run against an environment is a run
  until `N` against any environment with the same feedback kernels before `N` (no observation).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Learning

variable {𝓐 𝓨 : Type*} [MeasurableSpace 𝓐] [MeasurableSpace 𝓨]

/-- A run of `alg` against `env` is a run until `N` against every environment `env'` with the same
feedback kernels at the rounds `< N` (no observation). -/
lemma IsAlgEnvSeq.isAlgEnvSeqUntil_of_feedback_eq {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {O : ℕ → Ω → Unit} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}
    {alg : Algorithm Unit 𝓐 𝓨} {env env' : Environment Unit 𝓐 𝓨}
    (h : IsAlgEnvSeq O A Y alg env P) {N : ℕ}
    (hfb : ∀ n < N, env'.feedback n = env.feedback n) :
    IsAlgEnvSeqUntil O A Y alg env' P N where
  measurable_obs := h.measurable_obs
  measurable_action := h.measurable_action
  measurable_feedback := h.measurable_feedback
  hasCondDistrib_obs n _ := by
    rw [Kernel.eq_const_dirac_of_subsingleton (env'.obs n) (),
      ← Kernel.eq_const_dirac_of_subsingleton (env.obs n) ()]
    exact h.hasCondDistrib_obs n
  hasCondDistrib_action n _ := h.hasCondDistrib_action n
  hasCondDistrib_feedback n hn := by
    rw [hfb n hn]
    exact h.hasCondDistrib_feedback n

end Learning
