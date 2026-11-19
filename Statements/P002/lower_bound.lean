/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.LawTransferAlgorithm

/-! # P002, prop:lower: the lower bound `D_a(c̄_a)` on `Cons(N')`

[INC-P002, Proposition (prop:lower)]. Let `π ∈ Cons(N')`, `(ν, ν') ∈ Θ`, and let `a` be an arm with
`μ_a < μ⋆` and `c̄_a := limsup_T N'_a(T) / log T < ∞`. Then `liminf_T E[N_a(T)] / log T ≥
D_a(c̄_a)`.

Differences of form with the paper: the support is a `Finset ℝ` `S` with `S ⊆ [0,1]` and `2 ≤
S.card`; the integral probability metric is `d = ipm 𝓕` for a set `𝓕` of test functions with
`IsTestClass 𝓕` (nonempty, values in `[0,1]`); arms are a finite type `α` with `2 ≤ Fintype.card α`
(the paper's `K ≥ 2`); instances are Markov kernels carried by `S` (`supportBandits S α`),
identified with probability vectors by `lawVec S`, the mean of arm `k` being `(ν k)[id]` and `μ⋆`
being `bestMean ν`; the deterministic source sizes are `N' : ℕ → α → ℕ`, the game at horizon `T`
being `gameMeasure ν' (constSize (N' T)) ν π T` of [INC-P003] (rounds from `0`); `E[N_a(T)]` is the
lower integral of the pull count in `ℝ≥0∞`, and the ratios `E[N_a(T)] / log T` are taken in `ℝ≥0∞`
(at `T ≤ 1`, where `log T = 0`, the ratio is `⊤` or `0`; finitely many horizons do not change a
`limsup`, a `liminf` or a limit), so the `limsup`, `liminf` and limits are those of `ℝ≥0∞`, without
junk values; a real constant `D` is compared through `ENNReal.ofReal D`. The setting of the node
(def:laws, def:ipm, def:model, def:class) is made explicit: `S`, `d = ipm 𝓕` with `IsTestClass 𝓕`,
`K ≥ 2`, `L ∈ (0,∞)^K` (the bounds `L_k > 0` of def:model). `π ∈ Cons(N')` is `IsLawConsistent 𝓕 L
N' π`, `Θ` is `lawDriftClass 𝓕 L`. `c̄_a` is the `limsup` in `ℝ≥0∞` of `N'_a(T) / log T`, assumed `<
∞`, and enters `D_a` through `ENNReal.toReal` (exact, since it is finite).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Incognita.TransferBandits

open scoped ENNReal Topology

namespace Incognita.Statements.P002

/-- [INC-P002, prop:lower] Every learner of `Cons(N')` pulls a suboptimal arm at least
`(D_a(c̄_a) - o(1)) log T` times in expectation. -/
theorem lower_bound {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (hK : 2 ≤ Fintype.card α) {S : Finset ℝ}
    (hS : ∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) (hS2 : 2 ≤ S.card) {𝓕 : Set (S → ℝ)}
    (h𝓕 : IsTestClass 𝓕) {L : α → ℝ} (hL : ∀ k, 0 < L k)
    (N' : ℕ → α → ℕ) {π : TransferAlgorithm α} (hπ : IsLawConsistent 𝓕 L N' π)
    {ν ν' : Kernel α ℝ} (hνν' : (ν, ν') ∈ lawDriftClass 𝓕 L) {a : α}
    (ha : (ν a)[id] < bestMean ν)
    (hcbar : limsup (fun T : ℕ ↦ (N' T a : ℝ≥0∞) / ENNReal.ofReal (Real.log T)) atTop < ∞) :
    ENNReal.ofReal (armConstant 𝓕 L ν ν' a
        (limsup (fun T : ℕ ↦ (N' T a : ℝ≥0∞) / ENNReal.ofReal (Real.log T)) atTop).toReal) ≤
      liminf (fun T : ℕ ↦ (∫⁻ x, (onlineCount a x.2 : ℝ≥0∞)
          ∂(gameMeasure ν' (constSize (N' T)) ν π T)) /
        ENNReal.ofReal (Real.log T)) atTop := by
  sorry

end Incognita.Statements.P002
