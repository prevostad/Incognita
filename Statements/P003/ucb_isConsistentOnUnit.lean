/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.Consistency
public import LeanMachineLearning.Online.Bandit.Algorithms.UCB

/-! # P003, prop:witness (second claim): UCB is consistent on `𝒫^K`

[INC-P003, Proposition (prop:witness), second sentence]. The algorithm UCB, in the form formalised
in LML, with parameter `c > 1/2` (round robin on the first `K` rounds, then an arm maximising
`μ̂_a + √(2 c log t / N_a(t - 1))` at round `t`, ties broken by a fixed rule) is consistent on
`𝒫^K`.

Differences of form with the paper: UCB is LML's `Bandits.ucbAlgorithm K c`, whose arms are
`Fin K` (LML's choice), with `2 ≤ K` (the paper's `K ≥ 2`; `NeZero K` is the instance LML's
definition needs, implied by `2 ≤ K`); its index at the 0-based round `n ≥ K` is
`μ̂_a + √(2 c log (n + 1) / N_a)`, the paper's round `t = n + 1`; consistency on `𝒫^K` is
`IsConsistentOnUnit`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Incognita.TransferBandits

namespace Incognita.Statements.P003

/-- [INC-P003, prop:witness] LML's UCB with parameter `c > 1/2` is consistent on `𝒫^K`. -/
theorem ucb_isConsistentOnUnit (K : ℕ) [NeZero K] (hK : 2 ≤ K) {c : ℝ} (hc : 1 / 2 < c) :
    IsConsistentOnUnit (Bandits.ucbAlgorithm K c) := by
  sorry

end Incognita.Statements.P003
