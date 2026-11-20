/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.StochasticBandits.GravesLaiProduct

/-! # P007, Section `sec:main`: the Graves–Lai constant

Proofs of the frozen statements of [INC-P007, Section `sec:main`], each with exactly the type of
`Incognita.Statements.P007.<name>`:

* `gravesLai_productClass` (`thm:main`): the constant of an unstructured class, from
  `Incognita.StochasticBandits.gravesLai_productClass`;
* `gravesLai_eq_zero_of_identifies` (`prop:gl-zero`), from
  `Incognita.StochasticBandits.gravesLai_eq_zero_of_identifies`;
* `lower_bound_gravesLai` (`cor:lower`): `thm:main` and LMLExplore's Lai–Robbins bound
  `LMLExplore.Bandits.eventually_mul_log_le_integral_regret_of_isConsistent`.

The proofs use only that the laws are finite measures (probability measures for `cor:lower`); the
integrability hypotheses of the frozen types (`𝒫_1`) are not used, and the theorems that carry them
unused are marked `nolint unusedArguments`: their signature is fixed by the frozen statement.
The proofs do not go through the paper's reduction `lem:gl-reduction`: see
`papers/P007-stochastic-setting/formalisation.tex`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Incognita.P007

/-- [INC-P007, Theorem `thm:main`] For every family `(D_a)_{a ∈ α}` of models and every instance
`ν ∈ ∏_a D_a` with a unique optimal arm `a⋆`,
`C(ν; ∏_a D_a) = ∑_{a ≠ a⋆} Δ_a / 𝒦_inf(ν_a, m⋆; D_a)` in `[0, ∞]`. The integrability of the laws
of the models is not used. -/
@[nolint unusedArguments]
theorem gravesLai_productClass {α : Type*} [Fintype α] [Nontrivial α]
    [MeasurableSpace α] [MeasurableSingletonClass α] {D : α → Set (MeasureTheory.Measure ℝ)}
    (hD : ∀ a, ∀ Q ∈ D a, MeasureTheory.IsProbabilityMeasure Q ∧ MeasureTheory.Integrable id Q)
    {ν : ProbabilityTheory.Kernel α ℝ} (hν : ν ∈ Incognita.StochasticBandits.productClass D)
    {aStar : α} (haStar : ∀ a ≠ aStar, 0 < Bandits.gap ν a) :
    Incognita.StochasticBandits.gravesLai (Incognita.StochasticBandits.productClass D) ν =
      ∑ a ∈ Finset.univ.filter (fun a ↦ 0 < Bandits.gap ν a),
        ENNReal.ofReal (Bandits.gap ν a) /
          LMLExplore.Bandits.dInf (D a) (ν a) (⨆ b, ∫ x, id x ∂(ν b)) :=
  StochasticBandits.gravesLai_productClass (fun a Q hQ ↦ by have := (hD a Q hQ).1; infer_instance)
    hν haStar

/-- [INC-P007, Proposition `prop:gl-zero`] Let `E` be a class and `ν` an instance with a unique
optimal arm `a⋆`. If every `ν' ∈ E` with `ν'_{a⋆} = ν_{a⋆}` is equal to `ν`, then `C(ν; E) = 0`.
Only the finiteness of the laws of `a⋆` is used. -/
@[nolint unusedArguments]
theorem gravesLai_eq_zero_of_identifies {α : Type*} [Fintype α]
    [Nontrivial α] [MeasurableSpace α] {E : Set (ProbabilityTheory.Kernel α ℝ)}
    (hE : ∀ ν' ∈ E, ∀ a, MeasureTheory.IsProbabilityMeasure (ν' a) ∧
      MeasureTheory.Integrable id (ν' a))
    {ν : ProbabilityTheory.Kernel α ℝ}
    (hν : ∀ a, MeasureTheory.IsProbabilityMeasure (ν a) ∧ MeasureTheory.Integrable id (ν a))
    {aStar : α} (haStar : ∀ a ≠ aStar, 0 < Bandits.gap ν a)
    (hid : ∀ ν' ∈ E, ν' aStar = ν aStar → ν' = ν) :
    Incognita.StochasticBandits.gravesLai E ν = 0 := by
  have := (hν aStar).1
  exact StochasticBandits.gravesLai_eq_zero_of_identifies haStar
    (fun ν' hν' ↦ by have := (hE ν' hν' aStar).1; infer_instance) hid

/-- [INC-P007, Corollary `cor:lower`] Let `D` be a model, `π` a learner consistent on `D^α`, and
`ν ∈ D^α` an instance with a unique optimal arm. Then, in `[0, ∞]`,
`liminf_{T → ∞} R_T(π, ν) / log T ≥ C(ν; D^α)`, in eventual form: for every real `c` with
`ofReal c < C(ν; D^α)`, eventually `c log T ≤ R_T(π, ν)`. By `thm:main`, `C(ν; D^α)` is the
Lai–Robbins constant, and LMLExplore's Lai–Robbins bound applies. -/
@[nolint unusedArguments]
theorem lower_bound_gravesLai {α : Type*} [Fintype α] [Nontrivial α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    {D : Set (MeasureTheory.Measure ℝ)}
    (hD : ∀ Q ∈ D, MeasureTheory.IsProbabilityMeasure Q ∧ MeasureTheory.Integrable id Q)
    {alg : Learning.Algorithm Unit α ℝ}
    (halg : LMLExplore.Bandits.IsConsistent alg
      (Incognita.StochasticBandits.productClass fun _ : α ↦ D))
    {ν : ProbabilityTheory.Kernel α ℝ} [ProbabilityTheory.IsMarkovKernel ν]
    (hν : ν ∈ Incognita.StochasticBandits.productClass fun _ : α ↦ D)
    {aStar : α} (haStar : ∀ a ≠ aStar, 0 < Bandits.gap ν a) {c : ℝ}
    (hc : ENNReal.ofReal c <
      Incognita.StochasticBandits.gravesLai
        (Incognita.StochasticBandits.productClass fun _ : α ↦ D) ν) :
    ∀ᶠ n : ℕ in Filter.atTop, c * Real.log n ≤
      ∫ ω, Bandits.regret ν Learning.IT.action n ω
        ∂(Learning.trajMeasure alg (Learning.Environment.bandit ν)) := by
  rw [gravesLai_productClass (fun _ Q hQ ↦ hD Q hQ) hν haStar] at hc
  exact LMLExplore.Bandits.eventually_mul_log_le_integral_regret_of_isConsistent
    (M := fun _ ↦ D) (fun _ Q hQ ↦ (hD Q hQ).1) halg hν hc

end Incognita.P007
