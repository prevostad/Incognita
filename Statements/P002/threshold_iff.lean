/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.LawDrift

/-! # P002, prop:threshold (a): the constant vanishes exactly above the threshold

[INC-P002, Proposition (prop:threshold), item (a)]. Let `L ∈ (0,∞)^K`, `(ν, ν') ∈ 𝒫_S^K × 𝒫_S^K`,
and let `a` be an arm with `μ_a < μ⋆ < x_max`. With `ω_d(q') = max {m(q) - m(q') : q ∈ 𝒫_S, d(q, q')
≤ L_a}` and `G^d = min {KL(ν'_a, q') : q' ∈ 𝒫_S, m(q') + ω_d(q') ≥ μ⋆}`: for `c ≥ 0`, `D^d_a(c) = 0`
if and only if `c G^d ≥ 1`.

Differences of form with the paper: the support is a `Finset ℝ` `S` with `S ⊆ [0,1]` and `2 ≤
S.card`, and `x_max`, `x_min` are `S.max' hSne` and `S.min' hSne`, where the hypothesis `hSne :
S.Nonempty` (implied by `2 ≤ S.card`) only names the nonemptiness proof; arms are a finite type `α`
with `2 ≤ Fintype.card α` (the paper's `K ≥ 2` of def:model) and `L ∈ (0,∞)^K`; the pair `(ν, ν') ∈
𝒫_S^K × 𝒫_S^K` is a pair of Markov kernels carried by `S` (`supportBandits S α`), identified with
probability vectors by `lawVec S`; means are Bochner integrals `(ν k)[id]` (equal to the paper's
`m(ν_k)` for laws carried by `S`), `μ⋆ = bestMean ν`. A superscript `D^d_a` is `armConstant 𝓕 L ν ν'
a`, with `𝓕` the test functions of `d`: `tvClass S`, `ksClass S`, `w1Class S`, `meanClass S` for
`TV`, `KS`, `W₁` and the mean gap, and a general `𝓕` with `IsTestClass 𝓕` for "every `d`" (a
pseudo-distance of def:ipm). `K_0` is `vecKs S (lawVec S (ν a)) μ⋆` and `K'_0` is `vecKs S (lawVec S
(ν' a)) (μ⋆ - L_a)`, in `ℝ≥0∞`. `ω_d` is `reachGain 𝓕 L_a` (a real supremum, the paper's maximum)
and `G^d` is `thresholdKL 𝓕 L_a ν'_a μ⋆` (an infimum in `ℝ≥0∞`, the paper's minimum); `c G^d ≥ 1` is
written in `ℝ≥0∞`, with `0 · ∞ = 0`. The statement is for every `d = d_𝓕` with `IsTestClass 𝓕`, as
the proposition is (it fixes no `d`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Incognita.TransferBandits

open scoped ENNReal

namespace Incognita.Statements.P002

/-- [INC-P002, prop:threshold (a)] `D^d_a(c) = 0` if and only if `c G^d ≥ 1`. -/
theorem threshold_iff
    {α : Type*} [Fintype α] [MeasurableSpace α] (hK : 2 ≤ Fintype.card α)
    {S : Finset ℝ} (hS : ∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) (hS2 : 2 ≤ S.card)
    (hSne : S.Nonempty) {L : α → ℝ}
    (hL : ∀ k, 0 < L k) {ν ν' : Kernel α ℝ} (hν : ν ∈ supportBandits S α)
    (hν' : ν' ∈ supportBandits S α) {a : α} (ha : (ν a)[id] < bestMean ν)
    (hmax : bestMean ν < S.max' hSne)
    {𝓕 : Set (S → ℝ)} (h𝓕 : IsTestClass 𝓕) :
    ∀ c : ℝ, 0 ≤ c →
      (armConstant (𝓕) L ν ν' a c = 0 ↔
        1 ≤ ENNReal.ofReal c * thresholdKL 𝓕 (L a) (lawVec S (ν' a)) (bestMean ν)) := by
  sorry

end Incognita.Statements.P002
