/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.Examples

/-! # P003, prop:exclusion: the learner that follows the source is not consistent

[INC-P003, Proposition (prop:exclusion)]. Let `π^tr` be the transfer learner that, when
`n_k(s) ≥ 1` for every `k`, pulls at every round the smallest arm `k̂(s)` maximising `m̂'_k(s)`,
and otherwise pulls arm `1` at every round. Then `π^tr ∉ 𝒞_L` for every `L ∈ (0,∞)^K`, and the
failure already occurs on a pair with `ν' = ν` and deterministic source sizes.

Differences of form with the paper: arms are a finite linear order `α` with
`2 ≤ Fintype.card α` (the paper's `[K]` with its order), "arm `1`" being its smallest element (the
instance `Nonempty α`, which the definition of `π^tr` needs, follows from `2 ≤ Fintype.card α`);
`π^tr` is `TransferAlgorithm.followSource`; the second claim says that some `ν ∈ 𝒫^K`, some sizes
`n`, some suboptimal arm `a` and some `c > 0` make `E[N_a(T)] / T ^ c` not tend to `0` under the
game with source `ν' = ν` and the constant size rule `constSize n` at every horizon (the pair
`(ν, ν)` is in every `𝒫_L`, and this strategy is a source strategy, by lem:prior-game (a)).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Incognita.TransferBandits Filter

open scoped Topology

namespace Incognita.Statements.P003

/-- [INC-P003, prop:exclusion] The learner `π^tr` is in no class `𝒞_L`; it already fails on a pair
`(ν, ν)` with deterministic source sizes. -/
theorem followSource_not_isConsistent {α : Type*} [Fintype α] [LinearOrder α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (hK : 2 ≤ Fintype.card α) :
    (∀ L : α → ℝ, (∀ a, 0 < L a) → ¬ IsConsistent L (TransferAlgorithm.followSource (α := α))) ∧
      ∃ ν ∈ unitBandits α, ∃ n : α → ℕ, ∃ a, (∃ b, (ν a)[id] < (ν b)[id]) ∧ ∃ c : ℝ, 0 < c ∧
        ¬ Tendsto (fun T : ℕ ↦ (∫ p, (onlineCount a p.2 : ℝ) ∂(gameMeasure ν (constSize n) ν
            (TransferAlgorithm.followSource (α := α)) T)) / (T : ℝ) ^ c) atTop (𝓝 0) := by
  sorry

end Incognita.Statements.P003
