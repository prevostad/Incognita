/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.Consistency
public import Incognita.TransferBandits.SourceKL
public import Incognita.ForLML.InformationTheory.KullbackLeibler.Bernoulli

/-! # P003, thm:main (a) and cor:fundamental: the divergence decomposition

Proofs of [INC-P003, thm:main (a)] and [INC-P003, cor:fundamental], following the paper: the chain
rule splits `KL(P, P₂)` into the divergence of the source data and the expected divergence of the
online phase (`Incognita.TransferBandits.klDiv_gameMeasure_eq_add`, with lem:online-kl); the first
is `∑_k E_{ν'}[N'_k] KL(ν'_k, ν₂'_k)` (`Incognita.TransferBandits.klDiv_sourceLaw`,
prop:source-kl), and `E_{ν'}[N'_k] = E_P[N'_k]` (lem:mixture). The fundamental inequality is the
data processing inequality for the Bernoulli laws of the means of `Z`
(`Incognita.klDiv_bernoulli_integral_le`).

## Main statements

* `divergence_decomposition`, `fundamental_inequality`: the frozen statements.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Incognita.TransferBandits

open scoped ENNReal

namespace Incognita.P003

/-- [INC-P003, thm:main (a)] The divergence decomposition for a size rule with finite expected
sizes: `KL(P, P₂) = ∑_k E_P[N'_k] KL(ν'_k, ν₂'_k) + ∑_k E_P[N_k(T)] KL(ν_k, ν₂_k)`. The hypothesis
`2 ≤ Fintype.card α` is not used. -/
theorem divergence_decomposition {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (_hK : 2 ≤ Fintype.card α)
    {N : SourceSpace α → α → ℕ} (hN : IsSizeRule N) (π : TransferAlgorithm α) (T : ℕ)
    {ν ν' ν₂ ν₂' : Kernel α ℝ} (hν : ν ∈ unitBandits α) (hν' : ν' ∈ unitBandits α)
    (hν₂ : ν₂ ∈ unitBandits α) (hν₂' : ν₂' ∈ unitBandits α)
    (hfin : ∀ a, ∫⁻ ω, (N ω a : ℝ≥0∞) ∂(sourceMeasure ν') < ∞) :
    klDiv (gameMeasure ν' N ν π T) (gameMeasure ν₂' N ν₂ π T) =
      ∑ a, (∫⁻ x, (sourceCount a x.1 : ℝ≥0∞) ∂(gameMeasure ν' N ν π T)) * klDiv (ν' a) (ν₂' a) +
      ∑ a, (∫⁻ x, (onlineCount a x.2 : ℝ≥0∞) ∂(gameMeasure ν' N ν π T)) * klDiv (ν a) (ν₂ a) := by
  have : IsMarkovKernel ν := hν.1
  have : IsMarkovKernel ν' := hν'.1
  have : IsMarkovKernel ν₂ := hν₂.1
  have : IsMarkovKernel ν₂' := hν₂'.1
  rw [klDiv_gameMeasure_eq_add N π T ν ν' ν₂ ν₂',
    klDiv_sourceLaw hN ν' ν₂' fun a ↦ (hfin a).ne]
  congr 1
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [lintegral_sourceCount_gameMeasure hN.measurable ν' ν π T a]

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
  have : IsMarkovKernel ν := hν.1
  have : IsMarkovKernel ν' := hν'.1
  have : IsMarkovKernel ν₂ := hν₂.1
  have : IsMarkovKernel ν₂' := hν₂'.1
  refine (klDiv_bernoulli_integral_le _ _ hZ hZ01).trans (le_of_eq ?_)
  rw [divergence_decomposition hK hN π T hν hν' hν₂ hν₂' hfin]
  congr 1
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [lintegral_sourceCount_gameMeasure hN.measurable ν' ν π T a]

end Incognita.P003
