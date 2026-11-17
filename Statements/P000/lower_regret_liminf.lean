/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.Consistency
public import Incognita.BatchedBandits.Instances

/-! # P000, `thm:lower`: (iii), the lower bound on the regret (liminf)

One frozen statement of the paper P000 (`papers/P000-hy-unknown-imposed-grid`); its
docstring gives the statement in words and every difference of form with the paper. -/

@[expose] public section

/-- [INC-P000, Theorem `thm:lower`(iii)] Let the grid be convergent with limit `x ∈ [1, ∞)`, let
a batched learner be consistent on `𝒫` and let `ν ∈ 𝒫`. If `x = 1`, or if `x > 1` and
`E_ν[N_c(t_ℓ)] = O(log t_ℓ)` for every sub-optimal arm `c`, then
`liminf_ℓ ℛ(t_ℓ) / log t_ℓ ≥ x² ∑_(c : Δ_c > 0) Δ_c / 𝒦_inf(ν_c, m⋆)`.

Differences of form with the paper (common to the frozen statements of P000):
* Arms: a finite type `α` with the discrete σ-algebra (`Fintype α`, `MeasurableSingletonClass α`),
  `K = Fintype.card α ≥ 2` (`hK`); `DecidableEq α` is needed to count pulls.
* Grid: `g : Grid (Fintype.card α)` [INC-P006]: batch ends `0 = t 0 < t 1 < ⋯` with
  `t 1 ≥ max(2, K)`, the paper's `B_1 ≥ max(2, K)`; `x_ℓ` is `g.ratio ℓ`, `log t_ℓ` is
  `Real.log (g.t ℓ)`. Rounds are numbered from `0`; quantities at the batch ends are unchanged:
  the paper's `N_c(t_ℓ)` (pulls in the rounds `1, …, t_ℓ`) is `pullCount IT.action c (g.t ℓ)`
  (pulls in the rounds `0, …, t_ℓ - 1`), and `E_ν` is the integral under
  `trajMeasure alg (Environment.bandit ν)`.
* Instances: `ν : Kernel α ℝ` in `unitBandits α`, the class `𝒫` (laws on `[0, 1]`, largest mean
  `m⋆ = ⨆ b, ∫ y, id y ∂(ν b) < 1`); `[IsMarkovKernel ν]` is implied by `ν ∈ unitBandits α` and
  only makes `Environment.bandit ν` well formed. A sub-optimal arm is `0 < Bandits.gap ν a`
  (`Δ_a = m⋆ - m_a`).
* `𝒦_inf(ν_a, m⋆)` is `LMLExplore.Bandits.dInf unitLaws (ν a) m⋆` (the primal formula, which the
  paper identifies with its dual definition by [HT10, Theorem 8], Definition `def:kinf`), an
  `ℝ≥0∞`; the statements use its `toReal`, which is faithful because for `ν ∈ 𝒫` and a
  sub-optimal arm it is in `(0, ∞)` [INC-P006, Proposition `prop:kinf`(v)].
* The grid is convergent with limit `x ∈ [1, ∞)`: `g.ratio → x` and `1 ≤ x`. Since `x ≥ 1`, the
  paper's condition "`x = 1`, or `x > 1` and the counts are logarithmic" is written, equivalently,
  "`x = 1` or the counts are logarithmic" (`hlog`), with `Asymptotics.IsBigO` along `ℓ → ∞`.
* The (pseudo-)regret `ℛ(t) = ∑_c Δ_c E_ν[N_c(t)]` (Definition `def:learner`) is written as this
  sum, with `Δ_c = Bandits.gap ν c`; the constant sums over the arms with `0 < gap ν c`.
* The fixed sub-optimal arm `a` of the theorem is not used by this item and does not appear.
* Batched learner: an LML algorithm `alg : Algorithm Unit α ℝ` with `IsBatched alg g` [INC-P006,
  Definition `def:batched`]: during batch `ℓ + 1` its policy sees the rewards of the rounds
  `< t ℓ` only, its actions and its internal randomisation. It may depend on the whole grid (the
  paper's "even one that knows the grid"). Consistency on `𝒫` is
  `IsConsistentAtBatchEnds alg g (unitBandits α)` (the paper's Definition `def:learner`:
  `E_ν[N_c(t_ℓ)] = o(t_ℓ ^ p)` for every `ν ∈ 𝒫`, sub-optimal `c`, `p > 0`).
* `liminf_ℓ u_ℓ ≥ L` is written `∀ c < L, ∀ᶠ ℓ in atTop, c < u_ℓ`, and `limsup_ℓ u_ℓ ≥ L` is
  written `∀ c < L, ∃ᶠ ℓ in atTop, c < u_ℓ`: the sequences may be unbounded, where `Filter.liminf`
  in `ℝ` takes junk values (AGENTS.md 6.5). The terms at `ℓ = 0` (`t 0 = 0`) do not matter. -/
theorem Incognita.Statements.P000.lower_regret_liminf {α : Type*}
    [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (hK : 2 ≤ Fintype.card α) (g : Incognita.BatchedBandits.Grid (Fintype.card α))
    {x : ℝ} (hx : 1 ≤ x) (hg : Filter.Tendsto g.ratio Filter.atTop (nhds x))
    (alg : Learning.Algorithm Unit α ℝ)
    (hb : Incognita.BatchedBandits.IsBatched alg g)
    (hc : Incognita.BatchedBandits.IsConsistentAtBatchEnds alg g
      (Incognita.BatchedBandits.unitBandits α))
    (ν : ProbabilityTheory.Kernel α ℝ)
    [ProbabilityTheory.IsMarkovKernel ν] (hν : ν ∈ Incognita.BatchedBandits.unitBandits α)
    (hlog : x = 1 ∨ ∀ c, 0 < Bandits.gap ν c → Asymptotics.IsBigO Filter.atTop
      (fun ℓ ↦ (∫ ω, (Learning.pullCount Learning.IT.action c (g.t ℓ) ω : ℝ)
          ∂(Learning.trajMeasure alg
            (Learning.Environment.bandit ν))))
      (fun ℓ ↦ Real.log (g.t ℓ))) :
    ∀ c' < x ^ 2 * ∑ c ∈ Finset.univ.filter (fun c ↦ 0 < Bandits.gap ν c),
        Bandits.gap ν c / (LMLExplore.Bandits.dInf Incognita.BatchedBandits.unitLaws (ν c)
          (⨆ b, ∫ y, id y ∂(ν b))).toReal,
      ∀ᶠ ℓ in Filter.atTop, c' < (∑ c, Bandits.gap ν c *
          ∫ ω, (Learning.pullCount Learning.IT.action c (g.t ℓ) ω : ℝ)
          ∂(Learning.trajMeasure alg
            (Learning.Environment.bandit ν))) /
          Real.log (g.t ℓ) := by
  sorry
