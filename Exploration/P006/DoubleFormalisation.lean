/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.P006.Main

/-! # P006, `thm:main`(iii): a double formalisation (gardening re-check)

A `double-formalisation` re-check of [INC-P006, Theorem `thm:main`(iii)] (AGENTS.md, section 8).
The statement is written again from the paper's definitions (`def:instance`, `def:learner`,
`def:counts`, `def:exgrids`, `def:batched`, `def:consistent`, `def:seqcons`) with the primitives of
the dependencies only (LML's `Algorithm`, `Hist`, `trajMeasure`, `IT.action`), none of the
definitions of `Incognita.BatchedBandits` (`Grid`, `Grid.batchOf`, `SeesRewardsUpTo`, `IsBatched`,
`IsConsistentAtBatchEnds`, `unitBandits`) nor LML's `pullCount`, `gap`, `regret` or LMLExplore's
`IsConsistent`:

* the class `𝒫` is written with the paper's `Q([0, 1]) = 1` and `m⋆ = max_c ∫ x dν_c < 1`;
* the sequential grid is the paper's `t_0 = 0`, `t_ℓ = s + ℓ - 1` (`ℓ ≥ 1`), written inline;
* "batched on `𝖲_s`": at the round `n + 1` (Lean's round `n`, a history of `n` rounds), the policy
  sees the reward of the round `i + 1` whenever a batch end `t_j` satisfies `i + 1 ≤ t_j < n + 1`,
  that is, the batch of `i + 1` ended before the round `n + 1`; this is the paper's
  "`π_t` sees the rewards up to `t_{b(t)-1}`", with `t_{b(t)-1}` the last end before `t`, written
  without the batch index `b`;
* the counts are `N_c(T) = ∑_{n < T} 1(A_n = c)` and the regret is the paper's
  `ℛ(T) = ∑_c Δ_c E[N_c(T)]` with `Δ_c = m⋆ - m_c`; "suboptimal" is "some arm has a larger mean";
* the limit along the batch ends `t_ℓ = s + ℓ - 1`, `ℓ ≥ 1`, is written along `ℓ ↦ s + ℓ`,
  `ℓ ≥ 0` (the same sequence of ends, `t_{ℓ+1} = s + ℓ`).

`thm_main_iii` is this statement; it is proved from the frozen statements
`Incognita.Statements.P006.isBatched_sequential_iff` and
`Incognita.Statements.P006.isConsistentAtBatchEnds_sequential_iff` (through their proofs
`Incognita.P006.*`, of exactly the frozen types), by proving each side equivalent to the
corresponding side of the frozen statement (`batched_iff`, `ignores_iff`, `mem_unitBandits`,
`consistentAtEnds_iff`, `consistent_iff`). Conversely, `conclusion_iff_frozen` and
`mem_unitBandits_iff` show that the two statements are equivalent (same hypotheses, equivalent
conclusions), so the two formalisations agree: no difference found.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Filter Finset
open scoped Topology

namespace Incognita.Exploration.P006

open Incognita.BatchedBandits

variable {α : Type*}

/-- On `𝖲_s`, a reward of the round `i + 1` is seen at the round `n + 1` (some end `t_j` with
`i + 1 ≤ t_j < n + 1`) iff `i < t_{b-1}`, where `b` is the batch of the round `n` in `Grid`. -/
lemma exists_end_iff {K s : ℕ} (hs : max 2 K ≤ s) (n i : ℕ) :
    (∃ j : ℕ, i + 1 ≤ (if j = 0 then 0 else s + j - 1) ∧ (if j = 0 then 0 else s + j - 1) < n + 1)
      ↔ i < (Grid.sequential s hs).t ((Grid.sequential s hs).batchOf n - 1) := by
  have h2 : 2 ≤ s := (le_max_left 2 K).trans hs
  rcases lt_or_ge n s with hn | hn
  · rw [Grid.sequential_batchOf_of_lt hn, Nat.sub_self, Grid.t_zero]
    simp only [Nat.not_lt_zero, iff_false, not_exists, not_and]
    intro j hj
    split_ifs at hj ⊢ with h0
    · omega
    · omega
  · rw [Grid.sequential_batchOf hn, show n - s + 2 - 1 = n - s + 1 by omega,
      Grid.sequential_t (by omega), show s + (n - s + 1) - 1 = n by omega]
    constructor
    · rintro ⟨j, hj1, hj2⟩
      split_ifs at hj1 hj2 <;> omega
    · intro hi
      refine ⟨n - s + 1, ?_, ?_⟩ <;> simp only [Nat.add_one_ne_zero, ite_false] <;> omega

/-- The paper's "batched on `𝖲_s`", written with the ends of `𝖲_s`, is `IsBatched` on
`Grid.sequential s hs`. -/
lemma batched_iff {K s : ℕ} (hs : max 2 K ≤ s) [MeasurableSpace α] (π : Algorithm Unit α ℝ) :
    (∀ n : ℕ, ∀ h h' : Hist Unit α ℝ n, (∀ i, (h i).action = (h' i).action) →
        (∀ i : Fin n, (∃ j : ℕ, (i : ℕ) + 1 ≤ (if j = 0 then 0 else s + j - 1) ∧
          (if j = 0 then 0 else s + j - 1) < n + 1) → (h i).feedback = (h' i).feedback) →
        π.policy n (h, ()) = π.policy n (h', ())) ↔
      IsBatched π (Grid.sequential s hs) := by
  unfold IsBatched SeesRewardsUpTo
  exact forall_congr' fun n ↦ forall₂_congr fun h h' ↦ imp_congr_right fun _ ↦
    imp_congr_left (forall_congr' fun i ↦ imp_congr_left (exists_end_iff hs n i))

/-- The paper's "ignores the rewards" is `SeesRewardsUpTo π n 0`. -/
lemma ignores_iff [MeasurableSpace α] (π : Algorithm Unit α ℝ) (s : ℕ) :
    (∀ n < s, ∀ h h' : Hist Unit α ℝ n, (∀ i, (h i).action = (h' i).action) →
        π.policy n (h, ()) = π.policy n (h', ())) ↔
      ∀ n < s, SeesRewardsUpTo π n 0 := by
  unfold SeesRewardsUpTo
  exact forall₂_congr fun n _ ↦ forall₂_congr fun h h' ↦ imp_congr_right fun _ ↦
    ⟨fun H _ ↦ H, fun H ↦ H fun i hi ↦ absurd hi (Nat.not_lt_zero _)⟩

/-- The paper's class `𝒫` (`Q([0, 1]) = 1`, `m⋆ < 1`) is `unitBandits`. -/
lemma mem_unitBandits [MeasurableSpace α] {ν : Kernel α ℝ}
    (hν : (∀ c, IsProbabilityMeasure (ν c) ∧ ν c (Set.Icc 0 1) = 1) ∧
      (⨆ c, ∫ x, x ∂(ν c)) < 1) : ν ∈ unitBandits α :=
  ⟨fun c ↦ ⟨(hν.1 c).1, by
    have := (hν.1 c).1
    exact mem_ae_iff.2 ((prob_compl_eq_zero_iff measurableSet_Icc).2 (hν.1 c).2)⟩, hν.2⟩

/-- The paper's class `𝒫` is exactly `unitBandits`. -/
lemma mem_unitBandits_iff [MeasurableSpace α] {ν : Kernel α ℝ} :
    ν ∈ unitBandits α ↔ (∀ c, IsProbabilityMeasure (ν c) ∧ ν c (Set.Icc 0 1) = 1) ∧
      (⨆ c, ∫ x, x ∂(ν c)) < 1 := by
  refine ⟨fun hν ↦ ⟨fun c ↦ ⟨(hν.1 c).1, ?_⟩, hν.2⟩, mem_unitBandits⟩
  have := (hν.1 c).1
  exact (prob_compl_eq_zero_iff measurableSet_Icc).1 (mem_ae_iff.1 (hν.1 c).2)

/-- The count `∑_{n < T} 1(A_n = c)` is LML's `pullCount`. -/
lemma sum_ite_eq_pullCount [DecidableEq α] {Ω : Type*} (A : ℕ → Ω → α) (c : α) (T : ℕ) (ω : Ω) :
    (∑ n ∈ range T, if A n ω = c then (1 : ℝ) else 0) = (pullCount A c T ω : ℝ) := by
  rw [pullCount, Finset.natCast_card_filter]

/-- "Some arm has a larger mean" is `0 < gap ν c`. -/
lemma exists_lt_iff_gap_pos [Finite α] [MeasurableSpace α] (ν : Kernel α ℝ) (c : α) :
    (∃ b, ∫ x, x ∂(ν c) < ∫ x, x ∂(ν b)) ↔ 0 < Bandits.gap ν c := by
  have : Nonempty α := ⟨c⟩
  rw [Bandits.gap, sub_pos]
  exact (lt_ciSup_iff (Finite.bddAbove_range _)).symm

/-- The paper's "consistent at the batch ends of `𝖲_s`", along `t_{ℓ+1} = s + ℓ`, is
`IsConsistentAtBatchEnds` on `Grid.sequential s hs`. -/
lemma consistentAtEnds_iff [Finite α] [DecidableEq α] [MeasurableSpace α] {K s : ℕ}
    (hs : max 2 K ≤ s) (E : Set (Kernel α ℝ)) (π : Algorithm Unit α ℝ) :
    (∀ ν ∈ E, ∀ [IsMarkovKernel ν], ∀ c, (∃ b, ∫ x, x ∂(ν c) < ∫ x, x ∂(ν b)) →
        ∀ a : ℝ, 0 < a →
        Tendsto (fun ℓ : ℕ ↦ (∫ ω, (∑ n ∈ range (s + ℓ), if IT.action n ω = c then (1 : ℝ) else 0)
          ∂(trajMeasure π (Environment.bandit ν))) / ((s + ℓ : ℕ) : ℝ) ^ a) atTop (𝓝 0)) ↔
      IsConsistentAtBatchEnds π (Grid.sequential s hs) E := by
  unfold IsConsistentAtBatchEnds
  refine forall₂_congr fun ν _ ↦ forall_congr' fun _ ↦ forall_congr' fun c ↦
    imp_congr (exists_lt_iff_gap_pos ν c) (forall₂_congr fun a _ ↦ ?_)
  conv_rhs => rw [← tendsto_add_atTop_iff_nat 1]
  refine Iff.of_eq (congrArg (fun f ↦ Tendsto f atTop (𝓝 0)) (funext fun ℓ ↦ ?_))
  rw [Grid.sequential_t (by omega), show s + (ℓ + 1) - 1 = s + ℓ by omega]
  simp_rw [sum_ite_eq_pullCount]

/-- The paper's "sequentially consistent", with `ℛ(T) = ∑_c Δ_c E[N_c(T)]`, is LMLExplore's
`IsConsistent` (expected pathwise regret `o(T^a)`). -/
lemma consistent_iff [Fintype α] [DecidableEq α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (E : Set (Kernel α ℝ)) (π : Algorithm Unit α ℝ) :
    (∀ ν ∈ E, ∀ [IsMarkovKernel ν], ∀ a : ℝ, 0 < a →
        Tendsto (fun T : ℕ ↦ (∑ c, ((⨆ b, ∫ x, x ∂(ν b)) - ∫ x, x ∂(ν c)) *
          ∫ ω, (∑ n ∈ range T, if IT.action n ω = c then (1 : ℝ) else 0)
            ∂(trajMeasure π (Environment.bandit ν))) / (T : ℝ) ^ a) atTop (𝓝 0)) ↔
      LMLExplore.Bandits.IsConsistent π E := by
  rw [LMLExplore.Bandits.isConsistent_def]
  refine forall₂_congr fun ν _ ↦ forall_congr' fun _ ↦ forall₂_congr fun a _ ↦ ?_
  refine Iff.of_eq (congrArg (fun f ↦ Tendsto f atTop (𝓝 0)) (funext fun T ↦ ?_))
  rw [Bandits.integral_regret_eq_sum_gap_mul_integral_pullCount (fun n ↦ IT.measurable_action n)]
  simp_rw [sum_ite_eq_pullCount]
  rfl

/-- The conclusion of `thm_main_iii` is equivalent, for every `E`, to the conjunction of the
conclusions of the two frozen statements `Incognita.Statements.P006.isBatched_sequential_iff` and
`Incognita.Statements.P006.isConsistentAtBatchEnds_sequential_iff`; with `mem_unitBandits_iff`
(the hypotheses `E ⊆ 𝒫` agree), the two formalisations are equivalent statements. -/
theorem conclusion_iff_frozen [Fintype α] [DecidableEq α] [MeasurableSpace α]
    [MeasurableSingletonClass α] {K s : ℕ} (hs : max 2 K ≤ s) (E : Set (Kernel α ℝ))
    (π : Algorithm Unit α ℝ) :
    (((∀ n : ℕ, ∀ h h' : Hist Unit α ℝ n, (∀ i, (h i).action = (h' i).action) →
        (∀ i : Fin n, (∃ j : ℕ, (i : ℕ) + 1 ≤ (if j = 0 then 0 else s + j - 1) ∧
          (if j = 0 then 0 else s + j - 1) < n + 1) → (h i).feedback = (h' i).feedback) →
        π.policy n (h, ()) = π.policy n (h', ())) ↔
      (∀ n < s, ∀ h h' : Hist Unit α ℝ n, (∀ i, (h i).action = (h' i).action) →
        π.policy n (h, ()) = π.policy n (h', ()))) ∧
    ((∀ ν ∈ E, ∀ [IsMarkovKernel ν], ∀ c, (∃ b, ∫ x, x ∂(ν c) < ∫ x, x ∂(ν b)) →
        ∀ a : ℝ, 0 < a →
        Tendsto (fun ℓ : ℕ ↦ (∫ ω, (∑ n ∈ range (s + ℓ), if IT.action n ω = c then (1 : ℝ) else 0)
          ∂(trajMeasure π (Environment.bandit ν))) / ((s + ℓ : ℕ) : ℝ) ^ a) atTop (𝓝 0)) ↔
      (∀ ν ∈ E, ∀ [IsMarkovKernel ν], ∀ a : ℝ, 0 < a →
        Tendsto (fun T : ℕ ↦ (∑ c, ((⨆ b, ∫ x, x ∂(ν b)) - ∫ x, x ∂(ν c)) *
          ∫ ω, (∑ n ∈ range T, if IT.action n ω = c then (1 : ℝ) else 0)
            ∂(trajMeasure π (Environment.bandit ν))) / (T : ℝ) ^ a) atTop (𝓝 0)))) ↔
    ((IsBatched π (Grid.sequential s hs) ↔ ∀ n < s, SeesRewardsUpTo π n 0) ∧
      (IsConsistentAtBatchEnds π (Grid.sequential s hs) E ↔
        LMLExplore.Bandits.IsConsistent π E)) := by
  rw [batched_iff hs π, ignores_iff π s, consistentAtEnds_iff hs E π, consistent_iff E π]

/-- **[INC-P006, Theorem `thm:main`(iii)], stated again from the paper.** Let `K = |𝒜| ≥ 2`,
`s ≥ max(2, K)` and `E ⊆ 𝒫`, and let `𝖲_s` be the grid `t_0 = 0`, `t_ℓ = s + ℓ - 1`. Then
(1) a learner `π` is batched on `𝖲_s` iff `π_t` ignores the rewards for every `t ≤ s` (Lean's
rounds `n = t - 1 < s`); (2) `π` is consistent at the batch ends of `𝖲_s` on `E` iff it is
sequentially consistent on `E`. Proved equivalent to the frozen statements: see the module
docstring. -/
theorem thm_main_iii [Fintype α] [DecidableEq α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (hK : 2 ≤ Fintype.card α) {s : ℕ}
    (hs : max 2 (Fintype.card α) ≤ s) {E : Set (Kernel α ℝ)}
    (hE : ∀ ν ∈ E, (∀ c, IsProbabilityMeasure (ν c) ∧ ν c (Set.Icc 0 1) = 1) ∧
      (⨆ c, ∫ x, x ∂(ν c)) < 1)
    (π : Algorithm Unit α ℝ) :
    ((∀ n : ℕ, ∀ h h' : Hist Unit α ℝ n, (∀ i, (h i).action = (h' i).action) →
        (∀ i : Fin n, (∃ j : ℕ, (i : ℕ) + 1 ≤ (if j = 0 then 0 else s + j - 1) ∧
          (if j = 0 then 0 else s + j - 1) < n + 1) → (h i).feedback = (h' i).feedback) →
        π.policy n (h, ()) = π.policy n (h', ())) ↔
      (∀ n < s, ∀ h h' : Hist Unit α ℝ n, (∀ i, (h i).action = (h' i).action) →
        π.policy n (h, ()) = π.policy n (h', ()))) ∧
    ((∀ ν ∈ E, ∀ [IsMarkovKernel ν], ∀ c, (∃ b, ∫ x, x ∂(ν c) < ∫ x, x ∂(ν b)) →
        ∀ a : ℝ, 0 < a →
        Tendsto (fun ℓ : ℕ ↦ (∫ ω, (∑ n ∈ range (s + ℓ), if IT.action n ω = c then (1 : ℝ) else 0)
          ∂(trajMeasure π (Environment.bandit ν))) / ((s + ℓ : ℕ) : ℝ) ^ a) atTop (𝓝 0)) ↔
      (∀ ν ∈ E, ∀ [IsMarkovKernel ν], ∀ a : ℝ, 0 < a →
        Tendsto (fun T : ℕ ↦ (∑ c, ((⨆ b, ∫ x, x ∂(ν b)) - ∫ x, x ∂(ν c)) *
          ∫ ω, (∑ n ∈ range T, if IT.action n ω = c then (1 : ℝ) else 0)
            ∂(trajMeasure π (Environment.bandit ν))) / (T : ℝ) ^ a) atTop (𝓝 0))) := by
  have hE' : E ⊆ unitBandits α := fun ν hν ↦ mem_unitBandits (hE ν hν)
  refine ⟨?_, ?_⟩
  · rw [batched_iff hs π, ignores_iff π s]
    exact Incognita.P006.isBatched_sequential_iff hK hs π
  · rw [consistentAtEnds_iff hs E π, consistent_iff E π]
    exact Incognita.P006.isConsistentAtBatchEnds_sequential_iff hK hs hE' π

end Incognita.Exploration.P006
