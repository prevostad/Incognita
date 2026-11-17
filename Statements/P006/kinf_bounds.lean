/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.Instances
public import LMLExplore.Bandits.LaiRobbins

/-! # P006, `prop:kinf`(iii): bounds on `𝒦_inf(P, μ)` for `m(P) ≤ μ < 1`

One frozen statement of the paper P006 (`papers/P006-batched-setting`); its
docstring gives the statement in words and every difference of form with the paper. -/

@[expose] public section

/-- [INC-P006, Proposition `prop:kinf`(iii)] Let `P ∈ 𝓜` with mean `p = m(P)`, and `μ ∈ ℝ`. If
`p ≤ μ < 1`, then `2 (μ - p)² ≤ kl(p, μ) ≤ 𝒦_inf(P, μ) ≤ log ((1 - p) / (1 - μ)) < ∞`.

Differences of form with the paper:
* `𝓜` is `unitLaws` (probability measures on `ℝ` with `∀ᵐ x, x ∈ [0, 1]`, the paper's
  `Q([0, 1]) = 1`); the mean `m(Q)` is the Bochner integral `∫ x, id x ∂Q`; `𝒦_inf(P, μ)` is
  LMLExplore's `dInf unitLaws P μ = ⨅ Q ∈ {Q ∈ unitLaws | μ < Q[id]}, klDiv P Q` in `ℝ≥0∞`
  (Mathlib's `klDiv`, with `inf ∅ = ∞`), which is the paper's primal definition [INC-P006,
  Definition `def:kinf`].
* `kl(p, q)` is LMLExplore's `klBer p q`, the relative entropy between the Bernoulli laws on
  `{0, 1}` of means `p` and `q` (arguments clamped to `[0, 1]`, which changes nothing here since
  `p, μ ∈ [0, 1]`); it is `∞` when `q ∈ {0, 1}` and `q ≠ p`, as in the paper.
* The real numbers in the bounds (all `≥ 0` under the hypotheses) are compared with `𝒦_inf`
  through `ENNReal.ofReal`.
* The last inequality of the paper, `log ((1 - p) / (1 - μ)) < ∞`, says that the upper bound is
  finite; in Lean the bound is a real number, so the statement records the finiteness it gives,
  `𝒦_inf(P, μ) ≠ ∞`. -/
theorem Incognita.Statements.P006.kinf_bounds {P : MeasureTheory.Measure ℝ}
    (hP : P ∈ Incognita.BatchedBandits.unitLaws) {μ : ℝ} (hpμ : ∫ x, id x ∂P ≤ μ) (hμ : μ < 1) :
    ENNReal.ofReal (2 * (μ - ∫ x, id x ∂P) ^ 2) ≤ LMLExplore.klBer (∫ x, id x ∂P) μ ∧
      LMLExplore.klBer (∫ x, id x ∂P) μ ≤
        LMLExplore.Bandits.dInf Incognita.BatchedBandits.unitLaws P μ ∧
      LMLExplore.Bandits.dInf Incognita.BatchedBandits.unitLaws P μ ≤
        ENNReal.ofReal (Real.log ((1 - ∫ x, id x ∂P) / (1 - μ))) ∧
      LMLExplore.Bandits.dInf Incognita.BatchedBandits.unitLaws P μ ≠ ⊤ := by
  sorry
