/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.Instances
public import Incognita.BatchedBandits.Relations
public import Incognita.TransferBandits.Consistency

/-! # Relations between the consistency notions of TransferBandits and BatchedBandits

Gardening relations (recorded in `catalogue/relations.toml`) between the bandit consistency of
[INC-P003, Definition `def:consistency`] (`IsConsistentOnUnit`), the classical consistency of
LMLExplore (`LMLExplore.Bandits.IsConsistent`, in terms of the expected regret) and the
consistency at the batch ends of [INC-P006, Definition `def:consistent`]
(`Incognita.BatchedBandits.IsConsistentAtBatchEnds`), and between the two classes of instances
`𝒫^K` [INC-P003, Definition `def:instance`] and `𝒫` [INC-P006, Definition `def:instance`].

## Main statements

* `Relations.batchedUnitBandits_eq_inter`: `𝒫 = 𝒫^K ∩ {m⋆ < 1}`; the two classes are not the
  same object (an instance with an arm `δ_1` is in `𝒫^K` and not in `𝒫`).
* `Relations.isConsistentOnUnit_iff_isConsistentAtBatchEnds_sequential`: a learner is consistent
  on `𝒫^K` in the sense of P003 iff it is consistent at the batch ends of `𝖲_s` on `𝒫^K`, for any
  `s`.
* `Relations.isConsistentOnUnit_iff_isConsistent`: P003's pull-count consistency on `𝒫^K` is
  LMLExplore's regret-based consistency on `𝒫^K` (finitely many arms).
* `Relations.isConsistentOnUnit_of_isConsistent_of_isConsistentAtBatchEnds`: the lemma
  `Incognita.P003.isConsistentOnUnit_of_isConsistent`, proved again from the BatchedBandits lemma
  `LMLExplore.Bandits.IsConsistent.isConsistentAtBatchEnds` (the same computation
  `Δ_a E[N_a(T)] ≤ E[R_T]`).
* `Relations.isConsistentAtBatchEnds_of_isConsistentOnUnit`: a learner consistent on `𝒫^K` in the
  sense of P003 is consistent at the batch ends of every grid on `𝒫`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Bandits Filter

open scoped Topology

namespace Incognita.TransferBandits.Relations

variable {α : Type*} [MeasurableSpace α]

/-- The class `𝒫` of BatchedBandits [INC-P006, Definition `def:instance`] is the class `𝒫^K` of
TransferBandits [INC-P003, Definitions `def:laws` and `def:instance`] restricted to the instances
whose largest mean is below `1`. -/
lemma batchedUnitBandits_eq_inter :
    Incognita.BatchedBandits.unitBandits α = unitBandits α ∩ {ν | (⨆ a, (ν a)[id]) < 1} := by
  ext ν
  simp only [Incognita.BatchedBandits.unitBandits, Incognita.BatchedBandits.unitLaws, unitBandits,
    Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h, hm⟩
    exact ⟨⟨⟨fun a ↦ (h a).1⟩, fun a ↦ (h a).2⟩, hm⟩
  · rintro ⟨⟨hM, h⟩, hm⟩
    exact ⟨fun a ↦ ⟨hM.isProbabilityMeasure a, h a⟩, hm⟩

/-- `𝒫 ⊆ 𝒫^K`. -/
lemma batchedUnitBandits_subset : Incognita.BatchedBandits.unitBandits α ⊆ unitBandits α := by
  rw [batchedUnitBandits_eq_inter]
  exact Set.inter_subset_left

/-- With finitely many arms, an arm is suboptimal in the sense of P003 (some arm has a larger mean)
iff its gap is positive, the sense of P006 and of LML. -/
lemma gap_pos_iff_exists_lt [Finite α] {ν : Kernel α ℝ} {a : α} :
    0 < gap ν a ↔ ∃ b, (ν a)[id] < (ν b)[id] := by
  have : Nonempty α := ⟨a⟩
  rw [gap, sub_pos]
  exact lt_ciSup_iff (Finite.bddAbove_range _)

variable [DecidableEq α]

/-- **Same object** [INC-P003, Definition `def:consistency`; INC-P006, Definition
`def:consistent`]: a learner is consistent on `𝒫^K` in the sense of P003 (pull counts at every
horizon) iff it is consistent at the batch ends of the sequential grid `𝖲_s` on `𝒫^K`. The batch
ends of `𝖲_s` are `s, s + 1, …`, and a limit along every horizon is a limit along the horizons
`≥ s`. -/
lemma isConsistentOnUnit_iff_isConsistentAtBatchEnds_sequential [Finite α] {K s : ℕ}
    (hs : max 2 K ≤ s) {alg : Algorithm Unit α ℝ} :
    IsConsistentOnUnit alg ↔ Incognita.BatchedBandits.IsConsistentAtBatchEnds alg
      (Incognita.BatchedBandits.Grid.sequential s hs) (unitBandits α) := by
  constructor
  · intro h ν hν _ c hc p hp
    exact (h ν hν.2 c (gap_pos_iff_exists_lt.mp hc) p hp).comp
      (Incognita.BatchedBandits.Grid.sequential s hs).strictMono.tendsto_atTop
  · intro h ν _ hν a ha c hc
    have hψ : Tendsto (fun n : ℕ ↦ n - s + 1) atTop atTop :=
      tendsto_atTop_atTop.mpr fun b ↦ ⟨b + s, fun n hn ↦ by omega⟩
    refine ((h ν ⟨inferInstance, hν⟩ a (gap_pos_iff_exists_lt.mpr ha) c hc).comp hψ).congr' ?_
    filter_upwards [eventually_ge_atTop s] with n hn
    simp only [Function.comp_apply]
    rw [Incognita.BatchedBandits.Grid.sequential_t (by omega),
      show s + (n - s + 1) - 1 = n by omega]

/-- **Same object** [INC-P003, Definition `def:consistency`; LS, Definition 16.1]: with finitely
many arms, P003's consistency on `𝒫^K` (pull counts) is LMLExplore's consistency on `𝒫^K`
(expected regret). Proved through the sequential grid `𝖲_2` and [INC-P006, Theorem
`thm:main`(iii)] (`Incognita.BatchedBandits.isConsistentAtBatchEnds_sequential_iff`, which does not
assume `E ⊆ 𝒫`). -/
lemma isConsistentOnUnit_iff_isConsistent [Finite α] [MeasurableSingletonClass α]
    {alg : Algorithm Unit α ℝ} :
    IsConsistentOnUnit alg ↔ LMLExplore.Bandits.IsConsistent alg (unitBandits α) :=
  (isConsistentOnUnit_iff_isConsistentAtBatchEnds_sequential (K := 0) le_rfl).trans
    (Incognita.BatchedBandits.isConsistentAtBatchEnds_sequential_iff _)

/-- **Duplicate**: `Incognita.P003.isConsistentOnUnit_of_isConsistent` (same type), proved from the
BatchedBandits lemma `LMLExplore.Bandits.IsConsistent.isConsistentAtBatchEnds`: both bound
`Δ_a E[N_a(T)]` by `E[R_T]`; on `𝖲_2` the batch ends are every horizon `T ≥ 2`. -/
lemma isConsistentOnUnit_of_isConsistent_of_isConsistentAtBatchEnds [Finite α]
    [MeasurableSingletonClass α] {alg : Algorithm Unit α ℝ}
    (h : LMLExplore.Bandits.IsConsistent alg {ν : Kernel α ℝ | ∀ a, ∀ᵐ x ∂(ν a), x ∈ Set.Icc 0 1}) :
    IsConsistentOnUnit alg :=
  (isConsistentOnUnit_iff_isConsistentAtBatchEnds_sequential (K := 0) le_rfl).mpr
    ((h.isConsistentAtBatchEnds _).mono fun _ hν ↦ hν.2)

/-- A learner consistent on `𝒫^K` in the sense of P003 [INC-P003, Definition `def:consistency`] is
consistent at the batch ends of every grid on `𝒫` [INC-P006, Definition `def:consistent`]. -/
lemma isConsistentAtBatchEnds_of_isConsistentOnUnit [Finite α] [MeasurableSingletonClass α]
    {alg : Algorithm Unit α ℝ} (h : IsConsistentOnUnit alg) {K : ℕ}
    (g : Incognita.BatchedBandits.Grid K) :
    Incognita.BatchedBandits.IsConsistentAtBatchEnds alg g
      (Incognita.BatchedBandits.unitBandits α) :=
  ((isConsistentOnUnit_iff_isConsistent.mp h).isConsistentAtBatchEnds g).mono
    batchedUnitBandits_subset

end Incognita.TransferBandits.Relations
