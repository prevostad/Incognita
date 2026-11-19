/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.LawDrift

/-! # P002, prop:tv (a): total variation separates the projections

[INC-P002, Proposition (prop:tv), item (a)]. Let `L ∈ (0,∞)^K`, `(ν, ν') ∈ 𝒫_S^K × 𝒫_S^K`, and let
`a` be an arm with `μ_a < μ⋆ < x_max`. Assume `K'_0 > 0`. Then `TV(Q⋆, Q'⋆) ≥ L_a / (x_max -
x_min)`, with equality only if `Q⋆ - Q'⋆` is carried by `{x_min, x_max}`.

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
L_a}`), which, by uniqueness, are `Q⋆` and `Q'⋆`. `TV` is the distance `ipm (tvClass S)` of def:ipm
(equal to the `TV` of def:laws, lem:ipm (c)); "`Q⋆ - Q'⋆` carried by `{x_min, x_max}`" is `Q⋆(y) =
Q'⋆(y)` for every other `y`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Incognita.TransferBandits

open scoped ENNReal

namespace Incognita.Statements.P002

/-- [INC-P002, prop:tv (a)] `TV(Q⋆, Q'⋆) ≥ L_a / (x_max - x_min)`, with equality only if the two
projections differ only at `x_min` and `x_max`. -/
theorem tv_projections
    {α : Type*} [Fintype α] [MeasurableSpace α] (hK : 2 ≤ Fintype.card α)
    {S : Finset ℝ} (hS : ∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) (hS2 : 2 ≤ S.card)
    (hSne : S.Nonempty) {L : α → ℝ}
    (hL : ∀ k, 0 < L k) {ν ν' : Kernel α ℝ} (hν : ν ∈ supportBandits S α)
    (hν' : ν' ∈ supportBandits S α) {a : α} (ha : (ν a)[id] < bestMean ν)
    (hmax : bestMean ν < S.max' hSne)
    (hK'0 : 0 < vecKs S (lawVec S (ν' a)) (bestMean ν - L a)) :
    ∀ Q Q' : S → ℝ, IsKLProj (lawVec S (ν a)) (bestMean ν) Q →
      IsKLProj (lawVec S (ν' a)) (bestMean ν - L a) Q' →
      L a / (S.max' hSne - S.min' hSne) ≤ ipm (tvClass S) Q Q' ∧
        (ipm (tvClass S) Q Q' = L a / (S.max' hSne - S.min' hSne) →
          ∀ y : S, (y : ℝ) ≠ S.min' hSne → (y : ℝ) ≠ S.max' hSne → Q y = Q' y) := by
  sorry

end Incognita.Statements.P002
