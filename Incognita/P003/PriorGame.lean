/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.Checks
public import Incognita.TransferBandits.SizeRules

/-! # P003: prior games give size rules

Proofs of [INC-P003, lem:prior-game (b)] and [INC-P003, prop:stopped-games (a)].

## Main statements

* `stoppedCounts_isSizeRule`, `priorCounts_isSizeRule`.

The general facts on the prior game are in `Incognita.TransferBandits.SizeRules`: the stopped game
reads only values of the box of its counts (`PriorStrategy.stoppedCounts_eq_of_eqOn_box`), so the
criterion `isSizeRule_of_eqOn_box` applies.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Incognita.TransferBandits

namespace Incognita.P003

/-- [INC-P003, prop:stopped-games (a)] The stopped counts of a prior game over `T'` rounds form a
size rule whose total is at most `T'`. -/
theorem stoppedCounts_isSizeRule {α : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (_hK : 2 ≤ Fintype.card α) (g : PriorStrategy α) {T' : ℕ}
    {τ : SourceSpace α → ℕ} (hτ : g.IsStoppingTime T' τ) :
    IsSizeRule (g.stoppedCounts τ) ∧ ∀ ω, ∑ a, g.stoppedCounts τ ω a ≤ T' :=
  ⟨isSizeRule_of_eqOn_box (g.measurable_stoppedCounts hτ)
      fun _ _ _ h1 h2 h ↦ g.stoppedCounts_eq_of_eqOn_box hτ h1 h2 h,
    fun ω ↦ (g.sum_stoppedCounts τ ω).le.trans (hτ.le ω)⟩

/-- [INC-P003, lem:prior-game (b)] The counts of a prior bandit game over `T'` rounds form a size
rule, and each count is at most `T'`. -/
theorem priorCounts_isSizeRule {α : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (hK : 2 ≤ Fintype.card α) (g : PriorStrategy α) (T' : ℕ) :
    IsSizeRule (g.counts T') ∧ ∀ ω a, g.counts T' ω a ≤ T' := by
  have h := stoppedCounts_isSizeRule hK g (PriorStrategy.isStoppingTime_const g T')
  refine ⟨h.1, fun ω a ↦ ?_⟩
  calc g.counts T' ω a ≤ ∑ b, g.counts T' ω b :=
        Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)
    _ ≤ T' := h.2 ω

end Incognita.P003
