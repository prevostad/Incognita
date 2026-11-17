/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.Instances
public import LMLExplore.Bandits.LaiRobbins

/-! # P006, `prop:kinf`(iv): `𝒦_inf(Ber(p), μ) = kl(p, μ)` for `p ≤ μ < 1`

One frozen statement of the paper P006 (`papers/P006-batched-setting`); its
docstring gives the statement in words and every difference of form with the paper. -/

@[expose] public section

/-- [INC-P006, Proposition `prop:kinf`(iv)] If `P = Ber(p)` and `p ≤ μ < 1`, then
`𝒦_inf(P, μ) = kl(p, μ)`.

Differences of form with the paper:
* `𝓜` is `unitLaws` (probability measures on `ℝ` with `∀ᵐ x, x ∈ [0, 1]`, the paper's
  `Q([0, 1]) = 1`); the mean `m(Q)` is the Bochner integral `∫ x, id x ∂Q`; `𝒦_inf(P, μ)` is
  LMLExplore's `dInf unitLaws P μ = ⨅ Q ∈ {Q ∈ unitLaws | μ < Q[id]}, klDiv P Q` in `ℝ≥0∞`
  (Mathlib's `klDiv`, with `inf ∅ = ∞`), which is the paper's primal definition [INC-P006,
  Definition `def:kinf`].
* `Ber(p) = (1 - p) δ_0 + p δ_1` is Mathlib's `bernoulliMeasure (1 : ℝ) 0 p`, with `p` in the
  unit interval `unitInterval` (mass `p` at `1` and `1 - p` at `0`); its mean is `p`.
* `kl(p, q)` is LMLExplore's `klBer p q`, the relative entropy between the Bernoulli laws on
  `{0, 1}` of means `p` and `q` (arguments clamped to `[0, 1]`, which changes nothing here since
  `p, μ ∈ [0, 1]`); it is `∞` when `q ∈ {0, 1}` and `q ≠ p`, as in the paper.
* The infimum defining `𝒦_inf` is over all of `𝓜`, not over the Bernoulli laws only: this is not
  LMLExplore's `dInf_range_bernoulliMeasure`, whose class is the set of Bernoulli laws. -/
theorem Incognita.Statements.P006.kinf_bernoulli {p : unitInterval} {μ : ℝ}
    (hpμ : (p : ℝ) ≤ μ) (hμ : μ < 1) :
    LMLExplore.Bandits.dInf Incognita.BatchedBandits.unitLaws
        (ProbabilityTheory.bernoulliMeasure (1 : ℝ) 0 p) μ = LMLExplore.klBer p μ := by
  sorry
