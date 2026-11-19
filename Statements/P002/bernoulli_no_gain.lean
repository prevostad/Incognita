/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.LawDrift

/-! # P002, prop:bernoulli: Bernoulli laws gain nothing

[INC-P002, Proposition (prop:bernoulli)]. Let `L ∈ (0,∞)^K`, `(ν, ν') ∈ 𝒫_S^K × 𝒫_S^K`, and let `a`
be an arm with `μ_a < μ⋆ < x_max`. Assume also `m(ν'_a) ≤ μ⋆ + L_a`. If `{0, 1} ⊂ S` and `ν_a`,
`ν'_a` are carried by `{0, 1}`, then `D^d_a = D^mean_a` for every `d` with `(M)`.

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
(ν' a)) (μ⋆ - L_a)`, in `ℝ≥0∞`. "Carried by `{0,1}`" is `ν a {0, 1}ᶜ = 0` (and the same for `ν' a`);
`D^d_a = D^mean_a` is the equality on the domain `c ≥ 0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Incognita.TransferBandits

open scoped ENNReal

namespace Incognita.Statements.P002

/-- [INC-P002, prop:bernoulli] For laws carried by `{0, 1}`, every distance with the mean property
has the constant of the mean gap. -/
theorem bernoulli_no_gain
    {α : Type*} [Fintype α] [MeasurableSpace α] (hK : 2 ≤ Fintype.card α)
    {S : Finset ℝ} (hS : ∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) (hS2 : 2 ≤ S.card)
    (hSne : S.Nonempty) {L : α → ℝ}
    (hL : ∀ k, 0 < L k) {ν ν' : Kernel α ℝ} (hν : ν ∈ supportBandits S α)
    (hν' : ν' ∈ supportBandits S α) {a : α} (ha : (ν a)[id] < bestMean ν)
    (hmax : bestMean ν < S.max' hSne)
    (hν'a : (ν' a)[id] ≤ bestMean ν + L a) (h01 : {0, 1} ⊆ S)
    (hνa : ν a ({0, 1} : Set ℝ)ᶜ = 0) (hν'a01 : ν' a ({0, 1} : Set ℝ)ᶜ = 0)
    {𝓕 : Set (S → ℝ)} (h𝓕 : IsTestClass 𝓕) (hM : HasMeanProperty 𝓕) :
    ∀ c : ℝ, 0 ≤ c → armConstant (𝓕) L ν ν' a c = armConstant (meanClass S) L ν ν' a c := by
  sorry

end Incognita.Statements.P002
