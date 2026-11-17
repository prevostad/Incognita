/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.Consistency
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.Distributions.Bernoulli

/-! # P003, cor:fundamental: the fundamental inequality with a source

[INC-P003, Corollary (cor:fundamental)]. Under the hypotheses of thm:main (a), with `P` and `P₂`
as there, for every measurable `Z : 𝒮 × ℋ_T → [0,1]`,

`∑_k E_{ν'}[N'_k] KL(ν'_k, ν₂'_k) + ∑_k E_P[N_k(T)] KL(ν_k, ν₂_k) ≥ kl(E_P[Z], E_{P₂}[Z])`.

Differences of form with the paper: the conventions of `divergence_decomposition`
(thm:main (a)); `Z` is real-valued with values in `[0,1]` at every point; `E_P[Z]` is the Bochner
integral, sent to `I = [0,1]` by `Set.projIcc 0 1` (the identity on `[0,1]`, where the integral
lies) so that `kl(x, y) = KL(Ber(x), Ber(y))` is Mathlib's `klDiv (Ber((1 : ℝ), 0, x)) …`;
`E_{ν'}[N'_k]` is the lower integral under `P'_{ν'}` (`sourceMeasure ν'`), as in the paper.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Incognita.TransferBandits

open scoped ENNReal

namespace Incognita.Statements.P003

/-- [INC-P003, cor:fundamental] The source and online terms of the divergence decomposition bound
`kl(E_P[Z], E_{P₂}[Z])` from above, for every measurable `Z` with values in `[0,1]`. -/
theorem fundamental_inequality {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (hK : 2 ≤ Fintype.card α)
    {N : SourceSpace α → α → ℕ} (hN : IsSizeRule N) (π : TransferAlgorithm α) (T : ℕ)
    {ν ν' ν₂ ν₂' : Kernel α ℝ} (hν : ν ∈ unitBandits α) (hν' : ν' ∈ unitBandits α)
    (hν₂ : ν₂ ∈ unitBandits α) (hν₂' : ν₂' ∈ unitBandits α)
    (hfin : ∀ a, ∫⁻ ω, (N ω a : ℝ≥0∞) ∂(sourceMeasure ν') < ∞)
    {Z : Source α × (Fin T → α × ℝ) → ℝ} (hZ : Measurable Z) (hZ01 : ∀ x, Z x ∈ Set.Icc 0 1) :
    klDiv (Ber((1 : ℝ), 0, Set.projIcc 0 1 zero_le_one (∫ x, Z x ∂(gameMeasure ν' N ν π T))))
        (Ber((1 : ℝ), 0, Set.projIcc 0 1 zero_le_one (∫ x, Z x ∂(gameMeasure ν₂' N ν₂ π T)))) ≤
      ∑ a, (∫⁻ ω, (N ω a : ℝ≥0∞) ∂(sourceMeasure ν')) * klDiv (ν' a) (ν₂' a) +
      ∑ a, (∫⁻ x, (onlineCount a x.2 : ℝ≥0∞) ∂(gameMeasure ν' N ν π T)) * klDiv (ν a) (ν₂ a) := by
  sorry

end Incognita.Statements.P003
