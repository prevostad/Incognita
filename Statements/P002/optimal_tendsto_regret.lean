/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.LawTransferAlgorithm

/-! # P002, cor:optimal, third claim: `R_T / log T → 𝓡`

[INC-P002, Corollary (cor:optimal)]. Let `(ν, ν') ∈ Θ`, and assume that `N'_k(T) / log T → c_k ∈
[0,∞)` for every arm `k` with `μ_k < μ⋆`. Then the learner KL-UCB-`d`-Transfer belongs to `Cons(N')`
for every sequence `N'`, and, for every arm `a` with `μ_a < μ⋆`, `E[N_a(T)] / log T → D_a(c_a)`. Let
`𝓡 := ∑_{a : μ_a < μ⋆} (μ⋆ - μ_a) D_a(c_a)`. Then its regret satisfies `R_T / log T → 𝓡`, and every
`π ∈ Cons(N')` has `liminf_T R_T / log T ≥ 𝓡`.

This file freezes the third claim: the regret `R_T = ∑_k (μ⋆ - μ_k) E[N_k(T)]` of
KL-UCB-`d`-Transfer satisfies `R_T / log T → 𝓡`. The regret and `𝓡` are sums in `ℝ≥0∞` of
`ENNReal.ofReal (μ⋆ - μ_k)` (nonnegative) times the expected pull counts (resp. the constants
`ENNReal.ofReal (D_a(c_a))`); `𝓡` sums over the arms with `μ_a < μ⋆`, as in the paper. The gap
`μ⋆ - μ_k` is LML's `Bandits.gap ν k` (`(⨆ i, (ν i)[id]) - (ν k)[id]`, equal to
`bestMean ν - (ν k)[id]` by definition).

Differences of form with the paper: the support is a `Finset ℝ` `S` with `S ⊆ [0,1]` and `2 ≤
S.card`; the integral probability metric is `d = ipm 𝓕` for a set `𝓕` of test functions with
`IsTestClass 𝓕` (nonempty, values in `[0,1]`); arms are a finite type `α` with `2 ≤ Fintype.card α`
(the paper's `K ≥ 2`; `[Nonempty α]`, implied by it, is the instance the algorithm's kernels need);
instances are Markov kernels carried by `S` (`supportBandits S α`), identified with probability
vectors by `lawVec S`, the mean of arm `k` being `(ν k)[id]` and `μ⋆` being `bestMean ν`; the
deterministic source sizes are `N' : ℕ → α → ℕ`, the game at horizon `T` being `gameMeasure ν'
(constSize (N' T)) ν π T` of [INC-P003] (rounds from `0`); `E[N_a(T)]` is the lower integral of the
pull count in `ℝ≥0∞`, and the ratios `E[N_a(T)] / log T` are taken in `ℝ≥0∞` (at `T ≤ 1`, where `log
T = 0`, the ratio is `⊤` or `0`; finitely many horizons do not change a `limsup`, a `liminf` or a
limit), so the `limsup`, `liminf` and limits are those of `ℝ≥0∞`, without junk values; a real
constant `D` is compared through `ENNReal.ofReal D`. The setting of the node is made explicit (`S`,
`d = ipm 𝓕` with `IsTestClass 𝓕`, `K ≥ 2`, `L ∈ (0,∞)^K`). `Θ` is `lawDriftClass 𝓕 L`, `Cons(N')` is
`IsLawConsistent 𝓕 L N'`, `D_a(c)` is `armConstant 𝓕 L ν ν' a c`, KL-UCB-`d`-Transfer is
`klucbLawTransfer 𝓕 L`; the rates are real limits `(N'_k(T) : ℝ) / Real.log T → c_k` (so `c_k ≥ 0`),
assumed for the suboptimal arms only, the values `c_k` of the other arms playing no role. The node
has four claims, one theorem each: `optimal_isLawConsistent`, `optimal_tendsto_pulls`,
`optimal_tendsto_regret`, `optimal_regret_lower`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Incognita.TransferBandits

open scoped ENNReal Topology

namespace Incognita.Statements.P002

/-- [INC-P002, cor:optimal] On `Θ`, with rates `c_k`, the regret of KL-UCB-`d`-Transfer is
`(𝓡 + o(1)) log T`. -/
theorem optimal_tendsto_regret {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (hK : 2 ≤ Fintype.card α) {S : Finset ℝ}
    (hS : ∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) (hS2 : 2 ≤ S.card) {𝓕 : Set (S → ℝ)}
    (h𝓕 : IsTestClass 𝓕) {L : α → ℝ} (hL : ∀ k, 0 < L k)
    {ν ν' : Kernel α ℝ} (hνν' : (ν, ν') ∈ lawDriftClass 𝓕 L) (N' : ℕ → α → ℕ) {c : α → ℝ}
    (hc : ∀ k, (ν k)[id] < bestMean ν →
      Tendsto (fun T : ℕ ↦ (N' T k : ℝ) / Real.log T) atTop (𝓝 (c k))) :
    Tendsto (fun T : ℕ ↦ (∑ k, ENNReal.ofReal (Bandits.gap ν k) *
          ∫⁻ x, (onlineCount k x.2 : ℝ≥0∞)
            ∂(gameMeasure ν' (constSize (N' T)) ν (klucbLawTransfer 𝓕 L) T)) /
        ENNReal.ofReal (Real.log T)) atTop
      (𝓝 (∑ a ∈ Finset.univ.filter (fun a ↦ (ν a)[id] < bestMean ν),
        ENNReal.ofReal (Bandits.gap ν a) *
          ENNReal.ofReal (armConstant 𝓕 L ν ν' a (c a)))) := by
  sorry

end Incognita.Statements.P002
