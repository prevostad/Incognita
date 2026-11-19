/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.ForLML.Online.Bandit.Algorithms.Regret.UCB
public import Incognita.TransferBandits.LMLHistory
public import Incognita.TransferBandits.Relations

/-! # P003, prop:witness: source-ignoring learners of consistent algorithms are in `𝒞_L`

Proofs of the three frozen statements of [INC-P003, prop:witness].

## Main statements

* `ofAlgorithm_isConsistent`: if a bandit algorithm `σ` is consistent on `𝒫^K`, its
  source-ignoring learner `π^σ` is in `𝒞_𝟏` and in every `𝒞_L`. Under the law of the game,
  `E[N_a(T)]` for `π^σ` is LML's `E_{σ,ν}[N_a(T)]`, whatever the source
  (`integral_onlineCount_gameMeasure_ofAlgorithm`, which is lem:lml-history and lem:mixture for
  `π^σ`); so the condition of def:consistency is the consistency of `σ` on the target `ν`.
* `ucb_isConsistentOnUnit`: LML's UCB with `c > 1/2` is consistent on `𝒫^K`, from LML's regret
  bound (`Incognita.isConsistent_ucbAlgorithm_unit`) and `Δ_a E[N_a(T)] ≤ E[R_T]`
  (`Relations.isConsistentOnUnit_of_isConsistent_of_isConsistentAtBatchEnds`).
* `exists_isConsistent`: `𝒞_L ≠ ∅`, witnessed by `π^σ` for LMLExplore's KL-UCB [CGMMS13] on the arms
  `α` (any algorithm consistent on `𝒫^K` would do; UCB is defined on `Fin K` only).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Incognita.TransferBandits

namespace Incognita.P003

/-- [INC-P003, prop:witness] The source-ignoring learner of a bandit algorithm consistent on `𝒫^K`
is in `𝒞_𝟏`, and in `𝒞_L` for every `L ∈ (0,∞)^K`. The hypothesis `2 ≤ Fintype.card α` is not
used. -/
theorem ofAlgorithm_isConsistent {α : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (_hK : 2 ≤ Fintype.card α) {σ : Algorithm Unit α ℝ}
    (hσ : IsConsistentOnUnit σ) :
    IsConsistent (fun _ ↦ 1) (TransferAlgorithm.ofAlgorithm σ) ∧
      ∀ L : α → ℝ, (∀ a, 0 < L a) → IsConsistent L (TransferAlgorithm.ofAlgorithm σ) := by
  have h : ∀ L : α → ℝ, IsConsistent L (TransferAlgorithm.ofAlgorithm σ) := by
    intro L ν ν' hνν' ρ _ a ha c hc
    have : IsMarkovKernel ν := hνν'.1.1
    have : IsMarkovKernel ν' := hνν'.2.1.1
    simp_rw [integral_onlineCount_gameMeasure_ofAlgorithm]
    exact hσ ν hνν'.1.2 a ha c hc
  exact ⟨h _, fun L _ ↦ h L⟩

/-- [INC-P003, prop:witness] LML's UCB with parameter `c > 1/2` is consistent on `𝒫^K`. The
hypothesis `2 ≤ K` is not used. -/
theorem ucb_isConsistentOnUnit (K : ℕ) [NeZero K] (_hK : 2 ≤ K) {c : ℝ} (hc : 1 / 2 < c) :
    IsConsistentOnUnit (Bandits.ucbAlgorithm K c) :=
  Relations.isConsistentOnUnit_of_isConsistent_of_isConsistentAtBatchEnds
    (isConsistent_ucbAlgorithm_unit hc)

/-- [INC-P003, prop:witness] For every `L ∈ (0,∞)^K`, some transfer learner belongs to `𝒞_L`: the
source-ignoring learner of KL-UCB [CGMMS13]. -/
theorem exists_isConsistent {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (hK : 2 ≤ Fintype.card α) {L : α → ℝ} (hL : ∀ a, 0 < L a) :
    ∃ π : TransferAlgorithm α, IsConsistent L π := by
  classical
  have : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  exact ⟨TransferAlgorithm.ofAlgorithm LMLExplore.Bandits.klucb,
    (ofAlgorithm_isConsistent hK Relations.isConsistentOnUnit_klucb).2 L hL⟩

end Incognita.P003
