/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.LawTransferAlgorithm

/-! # P002, thm:main (ii): KL-UCB-`d`-Transfer attains the constant `D_a(c_a)`

[INC-P002, Theorem (thm:main), item (ii)]. Under the hypotheses of thm:main (for every finite `S ⊂
[0,1]` with `|S| ≥ 2`, every integral probability metric `d = d_𝓕`, every `K ≥ 2` and `L ∈ (0,∞)^K`,
every pair of instances `(ν, ν')` on `S` such that some arm `i⋆` with `μ_{i⋆} = μ⋆` satisfies
`d(ν_{i⋆}, ν'_{i⋆}) < L_{i⋆}`, deterministic source sizes), for every arm `a` with `μ_a < μ⋆`: if
`N'_a(T) / log T → c_a ∈ [0,∞)`, then `limsup_T E[N_a(T)] / log T ≤ D_a(c_a)`.

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
constant `D` is compared through `ENNReal.ofReal D`. The rate hypothesis is the real limit `(N'_a(T)
: ℝ) / Real.log T → c` (so `c ≥ 0`; at `T ≤ 1` the real quotient is `0`, finitely many horizons);
`D_a(c)` is `armConstant 𝓕 L ν ν' a c`. KL-UCB-`d`-Transfer is `klucbLawTransfer 𝓕 L`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Incognita.TransferBandits

open scoped ENNReal Topology

namespace Incognita.Statements.P002

/-- [INC-P002, thm:main (ii)] If `N'_a(T) / log T → c`, KL-UCB-`d`-Transfer pulls the suboptimal
arm `a` at most `(D_a(c) + o(1)) log T` times in expectation. -/
theorem upper_bound_transfer {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (hK : 2 ≤ Fintype.card α) {S : Finset ℝ}
    (hS : ∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) (hS2 : 2 ≤ S.card) {𝓕 : Set (S → ℝ)}
    (h𝓕 : IsTestClass 𝓕) {L : α → ℝ} (hL : ∀ k, 0 < L k)
    {ν ν' : Kernel α ℝ} (hν : ν ∈ supportBandits S α) (hν' : ν' ∈ supportBandits S α)
    (hopt : ∃ i, (ν i)[id] = bestMean ν ∧ ipm 𝓕 (lawVec S (ν i)) (lawVec S (ν' i)) < L i)
    (N' : ℕ → α → ℕ) {a : α} (ha : (ν a)[id] < bestMean ν) {c : ℝ}
    (hc : Tendsto (fun T : ℕ ↦ (N' T a : ℝ) / Real.log T) atTop (𝓝 c)) :
    limsup (fun T : ℕ ↦ (∫⁻ x, (onlineCount a x.2 : ℝ≥0∞) ∂(gameMeasure ν' (constSize (N' T)) ν
          (klucbLawTransfer 𝓕 L) T)) /
        ENNReal.ofReal (Real.log T)) atTop ≤
      ENNReal.ofReal (armConstant 𝓕 L ν ν' a c) := by
  sorry

end Incognita.Statements.P002
