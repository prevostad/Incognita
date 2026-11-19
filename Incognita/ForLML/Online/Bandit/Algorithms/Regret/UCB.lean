/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import LeanMachineLearning.Online.Bandit.Algorithms.Regret.UCB
public import LMLExplore.Bandits.LaiRobbins
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # UCB is consistent on sub-Gaussian bandits

LML bounds the expected regret of its UCB algorithm `ucbAlgorithm K c` at horizon `n` by
`∑ a, (8 c log (n + 1) / Δ_a + Δ_a (4 + 2 σ² / (c - 2 σ²)))` for σ²-sub-Gaussian rewards and
`c > 2 σ²` (`Bandits.UCB.regret_le_of_gt_two`). This is `O(log n)`, so UCB is consistent, in the
regret sense of LMLExplore (`LMLExplore.Bandits.IsConsistent`), over the bandits whose rewards are
σ²-sub-Gaussian. The logarithmic regret of UCB is [ACF02, Theorem 1] for rewards in `[0, 1]`;
the bound used here is LML's.

## Main statements

* `Incognita.isConsistent_ucbAlgorithm_subgaussian`: consistency over the σ²-sub-Gaussian bandits.
* `Incognita.isConsistent_ucbAlgorithm_unit`: consistency over the bandits with rewards in
  `[0, 1]`, for `c > 1/2` (Hoeffding's lemma: such rewards are `1/4`-sub-Gaussian).

The file mirrors LML's `LeanMachineLearning/Online/Bandit/Algorithms/Regret/UCB.lean`. Its
declarations were first written in LML's namespace `Bandits.UCB`; the old names are deprecated
aliases.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Real Finset Learning Bandits Bandits.UCB

open scoped NNReal

namespace Incognita

variable {K : ℕ} [NeZero K] {c : ℝ}

/-- For `n ≥ 3`, `log (n + 1) ≤ 2 log n` and `1 ≤ log n`. -/
lemma log_succ_le_two_mul_log {n : ℕ} (hn : 3 ≤ n) :
    log (n + 1) ≤ 2 * log n ∧ 1 ≤ log n := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < n := by linarith
  refine ⟨?_, ?_⟩
  · rw [← log_rpow hpos, show ((n : ℝ) ^ (2 : ℝ)) = n * n by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, rpow_natCast]; ring]
    exact log_le_log (by positivity) (by nlinarith)
  · rw [← log_exp 1]
    exact log_le_log (exp_pos 1) (exp_one_lt_three.le.trans hn')

/-- **UCB is consistent on sub-Gaussian bandits.** For `c > 2 σ²`, LML's UCB algorithm
`ucbAlgorithm K c` has expected regret `o(n ^ p)` for every `p > 0` on every bandit whose rewards
are σ²-sub-Gaussian. -/
lemma isConsistent_ucbAlgorithm_subgaussian (σ2 : ℝ≥0) (hc : 2 * σ2 < c) :
    LMLExplore.Bandits.IsConsistent (ucbAlgorithm K c)
      {ν : Kernel (Fin K) ℝ | ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)} := by
  refine LMLExplore.Bandits.isConsistent_of_eventually_le_mul_log fun ν hν _ ↦ ?_
  have hc0 : 0 < c := lt_of_le_of_lt (by positivity) hc
  set D : ℝ := 4 + 2 * σ2 / (c - 2 * σ2)
  have hD : 0 ≤ D := add_nonneg (by norm_num) (div_nonneg (by positivity) (by linarith))
  refine ⟨∑ a, (16 * c / gap ν a + gap ν a * D), ?_⟩
  filter_upwards [eventually_ge_atTop 3] with n hn
  obtain ⟨hlog2, hlog1⟩ := log_succ_le_two_mul_log hn
  refine (regret_le_of_gt_two (IT.isAlgEnvSeq_trajMeasure _ _) hν hc n).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ ↦ ?_
  have hg : 0 ≤ gap ν a := gap_nonneg
  have h1 : 8 * c * log (n + 1) / gap ν a ≤ 16 * c / gap ν a * log n := by
    rw [div_mul_eq_mul_div, show 16 * c * log n = 8 * c * (2 * log n) by ring]
    gcongr
  have h2 : gap ν a * D ≤ gap ν a * D * log n :=
    le_mul_of_one_le_right (mul_nonneg hg hD) hlog1
  rw [add_mul]
  exact add_le_add h1 h2

/-- **UCB is consistent on bandits with rewards in `[0, 1]`** for `c > 1/2`: such rewards are
`1/4`-sub-Gaussian (Hoeffding's lemma), and `2 · 1/4 < c`. -/
lemma isConsistent_ucbAlgorithm_unit (hc : 1 / 2 < c) :
    LMLExplore.Bandits.IsConsistent (ucbAlgorithm K c)
      {ν : Kernel (Fin K) ℝ | ∀ a, ∀ᵐ x ∂(ν a), x ∈ Set.Icc 0 1} := by
  have hσ : (2 * ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) < c := by
    have : ‖(1 : ℝ) - 0‖₊ = 1 := by simp
    rw [this]
    push_cast
    linarith
  rw [LMLExplore.Bandits.isConsistent_def]
  intro ν hν _
  refine (LMLExplore.Bandits.isConsistent_def _ _).mp (isConsistent_ucbAlgorithm_subgaussian _ hσ) ν
    (fun a ↦ ?_)
  exact hasSubgaussianMGF_of_mem_Icc (X := id) aemeasurable_id (hν a)

end Incognita

namespace Bandits.UCB

@[deprecated (since := "2026-11-19")]
alias log_succ_le_two_mul_log := Incognita.log_succ_le_two_mul_log

@[deprecated (since := "2026-11-19")]
alias isConsistent_subgaussian := Incognita.isConsistent_ucbAlgorithm_subgaussian

@[deprecated (since := "2026-11-19")]
alias isConsistent_unit := Incognita.isConsistent_ucbAlgorithm_unit

end Bandits.UCB
