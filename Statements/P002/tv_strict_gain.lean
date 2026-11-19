/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.LawDrift

/-! # P002, prop:tv (b): total variation gains strictly

[INC-P002, Proposition (prop:tv), item (b)]. Let `L ∈ (0,∞)^K`, `(ν, ν') ∈ 𝒫_S^K × 𝒫_S^K`, and let
`a` be an arm with `μ_a < μ⋆ < x_max`. Assume `K'_0 > 0`. Then `D^TV_a(c) < D^mean_a(c)` for every
`c ∈ (0, 1/K'_0)` as soon as `x_max - x_min < 1` or `Q⋆(y) ≠ Q'⋆(y)` for some `y ∈ S` with `x_min <
y < x_max`.

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
(ν' a)) (μ⋆ - L_a)`, in `ℝ≥0∞`. The projections `Q⋆`, `Q'⋆` of def:constant (unique minimisers,
which exist by lem:projection) are quantified universally through `IsKLProj`: the claim holds for
every minimiser `Q` of `KL(ν_a, ·)` on `{m(q) ≥ μ⋆}` (and `Q'` of `KL(ν'_a, ·)` on `{m(q') ≥ μ⋆ -
L_a}`), which, by uniqueness, are `Q⋆` and `Q'⋆`. `c < 1/K'_0` is written `c K'_0 < 1` in `ℝ≥0∞`
(equivalent, `K'_0 ∈ (0,∞)`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Incognita.TransferBandits

open scoped ENNReal

namespace Incognita.Statements.P002

/-- [INC-P002, prop:tv (b)] Total variation beats the mean as soon as `x_max - x_min < 1` or the
projections differ at an interior atom. -/
theorem tv_strict_gain
    {α : Type*} [Fintype α] [MeasurableSpace α] (hK : 2 ≤ Fintype.card α)
    {S : Finset ℝ} (hS : ∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) (hS2 : 2 ≤ S.card)
    (hSne : S.Nonempty) {L : α → ℝ}
    (hL : ∀ k, 0 < L k) {ν ν' : Kernel α ℝ} (hν : ν ∈ supportBandits S α)
    (hν' : ν' ∈ supportBandits S α) {a : α} (ha : (ν a)[id] < bestMean ν)
    (hmax : bestMean ν < S.max' hSne)
    (hK'0 : 0 < vecKs S (lawVec S (ν' a)) (bestMean ν - L a)) :
    ∀ Q Q' : S → ℝ, IsKLProj (lawVec S (ν a)) (bestMean ν) Q →
      IsKLProj (lawVec S (ν' a)) (bestMean ν - L a) Q' →
      (S.max' hSne - S.min' hSne < 1 ∨
        ∃ y : S, S.min' hSne < y ∧ (y : ℝ) < S.max' hSne ∧ Q y ≠ Q' y) →
      ∀ c : ℝ, 0 < c → ENNReal.ofReal c * vecKs S (lawVec S (ν' a)) (bestMean ν - L a) < 1 →
        armConstant (tvClass S) L ν ν' a c < armConstant (meanClass S) L ν ν' a c := by
  sorry

end Incognita.Statements.P002
