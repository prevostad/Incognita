/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.LawTransferAlgorithm

/-! # P002, thm:main (i): KL-UCB-`d`-Transfer is never worse than KL-UCB on `S`

[INC-P002, Theorem (thm:main), item (i)]. For every finite `S ⊂ [0,1]` with `|S| ≥ 2`, every
integral probability metric `d = d_𝓕`, every `K ≥ 2` and `L ∈ (0,∞)^K`, every pair of instances `(ν,
ν')` on `S` such that some arm `i⋆` with `μ_{i⋆} = μ⋆` satisfies `d(ν_{i⋆}, ν'_{i⋆}) < L_{i⋆}`, and
every sequence of deterministic source sizes, the learner KL-UCB-`d`-Transfer satisfies, for every
arm `a` with `μ_a < μ⋆`, `limsup_T E[N_a(T)] / log T ≤ 1 / K_S(ν_a, μ⋆)` (read as `0` if `K_S(ν_a,
μ⋆) = ∞`).

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
constant `D` is compared through `ENNReal.ofReal D`. The bound `1 / K_S` is the inverse in `ℝ≥0∞`,
which is `0` when `K_S = ∞` (the paper's reading). KL-UCB-`d`-Transfer is `klucbLawTransfer 𝓕 L`
(its conventions: the first `K` rounds follow the enumeration `Fintype.equivFin α`, the index is a
supremum in `EReal`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Incognita.TransferBandits

open scoped ENNReal Topology

namespace Incognita.Statements.P002

/-- [INC-P002, thm:main (i)] Whatever the source sizes, KL-UCB-`d`-Transfer pulls a suboptimal arm
at most `(1 / K_S(ν_a, μ⋆) + o(1)) log T` times in expectation. -/
theorem upper_bound_klucb {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (hK : 2 ≤ Fintype.card α) {S : Finset ℝ}
    (hS : ∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) (hS2 : 2 ≤ S.card) {𝓕 : Set (S → ℝ)}
    (h𝓕 : IsTestClass 𝓕) {L : α → ℝ} (hL : ∀ k, 0 < L k)
    {ν ν' : Kernel α ℝ} (hν : ν ∈ supportBandits S α) (hν' : ν' ∈ supportBandits S α)
    (hopt : ∃ i, (ν i)[id] = bestMean ν ∧ ipm 𝓕 (lawVec S (ν i)) (lawVec S (ν' i)) < L i)
    (N' : ℕ → α → ℕ) {a : α} (ha : (ν a)[id] < bestMean ν) :
    limsup (fun T : ℕ ↦ (∫⁻ x, (onlineCount a x.2 : ℝ≥0∞) ∂(gameMeasure ν' (constSize (N' T)) ν
          (klucbLawTransfer 𝓕 L) T)) /
        ENNReal.ofReal (Real.log T)) atTop ≤
      (vecKs S (lawVec S (ν a)) (bestMean ν))⁻¹ := by
  sorry

end Incognita.Statements.P002
