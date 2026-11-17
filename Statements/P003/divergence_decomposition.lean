/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.Consistency
public import Mathlib.InformationTheory.KullbackLeibler.Basic

/-! # P003, thm:main (a): the divergence decomposition

[INC-P003, Theorem (thm:main), part (a)]. For every size rule `N'` with `E_{ν'}[N'_k] < ∞` for every
arm, every transfer learner `π`, every horizon `T` and all pairs `(ν, ν')`, `(ν₂, ν₂')` of
instances on `[0,1]`, with `P := P^T_{ν',N',ν,π}` and `P₂ := P^T_{ν₂',N',ν₂,π}`, in `[0, ∞]`,

`KL(P, P₂) = ∑_k E_P[N'_k] KL(ν'_k, ν₂'_k) + ∑_k E_P[N_k(T)] KL(ν_k, ν₂_k)`.

Differences of form with the paper (conventions of `Incognita.TransferBandits.Setting`):

* the paper's second instance `(ν̃, ν̃')` is `(ν₂, ν₂')`;
* arms are a finite type `α` with `2 ≤ Fintype.card α` (the paper's `K ≥ 2`); laws on `[0,1]` are
  Markov kernels `Kernel α ℝ` concentrated on `[0,1]` (`unitBandits α`);
* `KL` is Mathlib's `klDiv` (the paper notes that its `KL` is this divergence); expectations are
  lower Lebesgue integrals in `ℝ≥0∞`, where `0 * ∞ = 0` as in the paper;
* the source data are the pair (sizes, kept values with `0` outside the box), and online histories
  are `Fin T → α × ℝ` (rounds from `0`);
* the hypothesis `E_{ν'}[N'_k] < ∞` is written under `P'_{ν'}` (`sourceMeasure ν'`), as in the
  paper; the identity uses `E_P[N'_k]`, as in eq:main.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Incognita.TransferBandits

open scoped ENNReal

namespace Incognita.Statements.P003

/-- [INC-P003, thm:main (a)] The divergence decomposition for a size rule with finite expected
sizes: `KL(P, P₂) = ∑_k E_P[N'_k] KL(ν'_k, ν₂'_k) + ∑_k E_P[N_k(T)] KL(ν_k, ν₂_k)`. -/
theorem divergence_decomposition {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (hK : 2 ≤ Fintype.card α)
    {N : SourceSpace α → α → ℕ} (hN : IsSizeRule N) (π : TransferAlgorithm α) (T : ℕ)
    {ν ν' ν₂ ν₂' : Kernel α ℝ} (hν : ν ∈ unitBandits α) (hν' : ν' ∈ unitBandits α)
    (hν₂ : ν₂ ∈ unitBandits α) (hν₂' : ν₂' ∈ unitBandits α)
    (hfin : ∀ a, ∫⁻ ω, (N ω a : ℝ≥0∞) ∂(sourceMeasure ν') < ∞) :
    klDiv (gameMeasure ν' N ν π T) (gameMeasure ν₂' N ν₂ π T) =
      ∑ a, (∫⁻ x, (sourceCount a x.1 : ℝ≥0∞) ∂(gameMeasure ν' N ν π T)) * klDiv (ν' a) (ν₂' a) +
      ∑ a, (∫⁻ x, (onlineCount a x.2 : ℝ≥0∞) ∂(gameMeasure ν' N ν π T)) * klDiv (ν a) (ν₂ a) := by
  sorry

end Incognita.Statements.P003
