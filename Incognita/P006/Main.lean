/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.Relations
public import Incognita.BatchedBandits.Instances

/-! # P006, `thm:main`: the basic relations of the batched setting

Proofs of the seven frozen statements of [INC-P006, Theorem `thm:main`], each with exactly the type
of `Incognita.Statements.P006.<name>`. Each is a specialisation of a lemma of
`Incognita.BatchedBandits.Relations`, stated there for any action and feedback types.

* (i) `infoModel_mono`, `infoModel_strict`, `isBatched_iff_exists_infoModel_top`;
* (ii) `isBatched_of_isFiner`, `isConsistentAtBatchEnds_of_isFiner`;
* (iii) `isBatched_sequential_iff`, `isConsistentAtBatchEnds_sequential_iff`.

The hypothesis `K ≥ 2` is used only by `infoModel_strict` (two distinct arms) and
`isBatched_iff_exists_infoModel_top` (one arm); the hypothesis `E ⊆ 𝒫` of (ii) and (iii) is not
used. Unused hypotheses are named `_hK`, `_hE` (the type is the frozen one up to binder names), and
the theorems whose frozen type carries an unused `[MeasurableSingletonClass α]` are marked
`nolint unusedArguments`: their signature is fixed by the frozen statement.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning

namespace Incognita.P006

open Incognita.BatchedBandits

/-- [INC-P006, Theorem `thm:main`(i), inclusions] `𝓜_k ⊆ 𝓜_k'` for `k ≤ k'`. The hypothesis
`K ≥ 2` is not used. -/
@[nolint unusedArguments]
theorem infoModel_mono {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (_hK : 2 ≤ Fintype.card α) {k k' : ℕ∞} (hkk' : k ≤ k')
    (π : Incognita.BatchedBandits.Grid (Fintype.card α) → Learning.Algorithm Unit α ℝ)
    (hπ : Incognita.BatchedBandits.InfoModel k π) :
    Incognita.BatchedBandits.InfoModel k' π :=
  hπ.mono hkk'

/-- [INC-P006, Theorem `thm:main`(i), strictness] For `k < k'`, some family is in `𝓜_k'` and not
in `𝓜_k`: the parity learner `Par^{(k)}` on two distinct arms (they exist since `K ≥ 2`). -/
theorem infoModel_strict {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (hK : 2 ≤ Fintype.card α) {k k' : ℕ∞} (hkk' : k < k') :
    ∃ π : Incognita.BatchedBandits.Grid (Fintype.card α) → Learning.Algorithm Unit α ℝ,
      Incognita.BatchedBandits.InfoModel k' π ∧ ¬ Incognita.BatchedBandits.InfoModel k π := by
  obtain ⟨c₁, c₂, hc⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card α)
  exact exists_infoModel_and_not_infoModel hc hkk'

/-- [INC-P006, Theorem `thm:main`(i), last claim] A learner is batched on `g` iff it is the
component at `g` of a family in `𝓜_⊤`. The hypothesis `K ≥ 2` is used only to have an arm. -/
@[nolint unusedArguments]
theorem isBatched_iff_exists_infoModel_top {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (hK : 2 ≤ Fintype.card α)
    (alg : Learning.Algorithm Unit α ℝ) (g : Incognita.BatchedBandits.Grid (Fintype.card α)) :
    Incognita.BatchedBandits.IsBatched alg g ↔
      ∃ π : Incognita.BatchedBandits.Grid (Fintype.card α) → Learning.Algorithm Unit α ℝ,
        Incognita.BatchedBandits.InfoModel ⊤ π ∧ π g = alg := by
  have : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  exact Incognita.BatchedBandits.isBatched_iff_exists_infoModel_top

/-- [INC-P006, Theorem `thm:main`(ii), first claim] A learner batched on `g'` is batched on every
grid `g` finer than `g'`. The hypothesis `K ≥ 2` is not used. -/
@[nolint unusedArguments]
theorem isBatched_of_isFiner {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (_hK : 2 ≤ Fintype.card α)
    {g g' : Incognita.BatchedBandits.Grid (Fintype.card α)} (hgg' : g.IsFiner g')
    {alg : Learning.Algorithm Unit α ℝ} (halg : Incognita.BatchedBandits.IsBatched alg g') :
    Incognita.BatchedBandits.IsBatched alg g :=
  halg.of_isFiner hgg'

/-- [INC-P006, Theorem `thm:main`(ii), second claim] Consistency at the batch ends of `g` on `E`
passes to every grid `g'` coarser than `g`. The hypotheses `K ≥ 2` and `E ⊆ 𝒫` are not used. -/
@[nolint unusedArguments]
theorem isConsistentAtBatchEnds_of_isFiner {α : Type*} [Fintype α]
    [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α] (_hK : 2 ≤ Fintype.card α)
    {g g' : Incognita.BatchedBandits.Grid (Fintype.card α)} (hgg' : g.IsFiner g')
    {E : Set (ProbabilityTheory.Kernel α ℝ)} (_hE : E ⊆ Incognita.BatchedBandits.unitBandits α)
    {alg : Learning.Algorithm Unit α ℝ}
    (halg : Incognita.BatchedBandits.IsConsistentAtBatchEnds alg g E) :
    Incognita.BatchedBandits.IsConsistentAtBatchEnds alg g' E :=
  halg.of_isFiner hgg'

/-- [INC-P006, Theorem `thm:main`(iii), first claim] A learner is batched on `𝖲_s` iff its
policies ignore the rewards at the rounds `n < s`. The hypothesis `K ≥ 2` is not used. -/
@[nolint unusedArguments]
theorem isBatched_sequential_iff {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (_hK : 2 ≤ Fintype.card α) {s : ℕ}
    (hs : max 2 (Fintype.card α) ≤ s) (alg : Learning.Algorithm Unit α ℝ) :
    Incognita.BatchedBandits.IsBatched alg (Incognita.BatchedBandits.Grid.sequential s hs) ↔
      ∀ n < s, Incognita.BatchedBandits.SeesRewardsUpTo alg n 0 :=
  Incognita.BatchedBandits.isBatched_sequential_iff hs

/-- [INC-P006, Theorem `thm:main`(iii), second claim] A learner is consistent at the batch ends
of `𝖲_s` on `E` iff it is sequentially consistent on `E`. The hypotheses `K ≥ 2` and `E ⊆ 𝒫` are
not used. -/
theorem isConsistentAtBatchEnds_sequential_iff {α : Type*}
    [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (_hK : 2 ≤ Fintype.card α) {s : ℕ} (hs : max 2 (Fintype.card α) ≤ s)
    {E : Set (ProbabilityTheory.Kernel α ℝ)} (_hE : E ⊆ Incognita.BatchedBandits.unitBandits α)
    (alg : Learning.Algorithm Unit α ℝ) :
    Incognita.BatchedBandits.IsConsistentAtBatchEnds alg
        (Incognita.BatchedBandits.Grid.sequential s hs) E ↔
      LMLExplore.Bandits.IsConsistent alg E :=
  Incognita.BatchedBandits.isConsistentAtBatchEnds_sequential_iff hs

end Incognita.P006
