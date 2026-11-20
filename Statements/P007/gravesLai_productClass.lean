/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.StochasticBandits.GravesLai

/-! # P007, `thm:main`: the Graves–Lai constant of an unstructured class

One frozen statement of the paper P007 (`papers/P007-stochastic-setting`); its docstring gives the
statement in words and every difference of form with the paper. -/

@[expose] public section

/-- [INC-P007, Theorem `thm:main`] For every family `(D_a)_{a ∈ α}` of models and every instance
`ν ∈ ∏_a D_a` with a unique optimal arm `a⋆`,
`C(ν; ∏_a D_a) = ∑_{a ≠ a⋆} Δ_a / 𝒦_inf(ν_a, m⋆; D_a)` in `[0, ∞]`, with `x / 0 = ∞` for `x > 0`
and `x / ∞ = 0`.

Differences of form with the paper:
* The arms are a type `α` with `[Fintype α] [Nontrivial α]` (the paper's finite set with
  `K = |α| ≥ 2`, Definition `def:instance`); `[MeasurableSpace α] [MeasurableSingletonClass α]`
  make every family of laws `(ν_a)_a` a kernel, as the paper's instances are arbitrary families
  (the roadmap's Lean convention).
* A model is a set `D a` of measures on `ℝ` contained in `𝒫_1` (Definition `def:kinf`): hypothesis
  `hD`, every `Q ∈ D a` is a probability measure with `∫ |x| dQ < ∞` (`Integrable id Q`).
* An instance is a kernel `ν : Kernel α ℝ`; `ν ∈ ∏_a D_a` is `ν ∈ productClass D`.
* "Unique optimal arm `a⋆`" is `∀ a ≠ a⋆, 0 < gap ν a` (LML's `gap ν a = m⋆ - m_a`, with
  `m⋆ = ⨆ b, (ν b)[id]`); it implies `gap ν a⋆ = 0`.
* `C(ν; E)` is `gravesLai E ν` (Definition `def:gl`, in `ℝ≥0∞`); `𝒦_inf(P, μ; D)` is LMLExplore's
  `dInf D P μ = ⨅ Q ∈ {Q ∈ D | μ < Q[id]}, klDiv P Q` (Definition `def:kinf`; the Bochner mean is
  the paper's mean on `D ⊆ 𝒫_1`); `m⋆` is `⨆ b, ∫ x, id x ∂(ν b)`; `Δ_a` is
  `ENNReal.ofReal (gap ν a)`; division is that of `ℝ≥0∞`, which has `x / 0 = ∞` for `x ≠ 0` and
  `x / ∞ = 0` for `x ≠ ∞`.
* The sum runs over the arms with `0 < gap ν a`, which are exactly the arms `a ≠ a⋆` (the form
  `∑_{a : Δ_a > 0}` of the abstract and of LMLExplore's Lai–Robbins bound).
* The "in particular" sentence (one model `D` for every arm) is the case `D = fun _ ↦ D`, not a
  separate statement. -/
theorem Incognita.Statements.P007.gravesLai_productClass {α : Type*} [Fintype α] [Nontrivial α]
    [MeasurableSpace α] [MeasurableSingletonClass α] {D : α → Set (MeasureTheory.Measure ℝ)}
    (hD : ∀ a, ∀ Q ∈ D a, MeasureTheory.IsProbabilityMeasure Q ∧ MeasureTheory.Integrable id Q)
    {ν : ProbabilityTheory.Kernel α ℝ} (hν : ν ∈ Incognita.StochasticBandits.productClass D)
    {aStar : α} (haStar : ∀ a ≠ aStar, 0 < Bandits.gap ν a) :
    Incognita.StochasticBandits.gravesLai (Incognita.StochasticBandits.productClass D) ν =
      ∑ a ∈ Finset.univ.filter (fun a ↦ 0 < Bandits.gap ν a),
        ENNReal.ofReal (Bandits.gap ν a) /
          LMLExplore.Bandits.dInf (D a) (ν a) (⨆ b, ∫ x, id x ∂(ν b)) := by
  sorry
