/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.Consistency
public import Incognita.BatchedBandits.HY
public import Incognita.BatchedBandits.Instances

/-! # P000, `thm:main`: (b), HY is a learner of 𝓜_0

One frozen statement of the paper P000 (`papers/P000-hy-unknown-imposed-grid`); its
docstring gives the statement in words and every difference of form with the paper. -/

@[expose] public section

/-- [INC-P000, Theorem `thm:main`(b); Definition `def:hy`, Properties (i)] HY is a learner of
`𝓜_0`: the family `g ↦ HY(w₀, β, ω^dy, ϑ, γ)` on the grid `g` is batched on every grid, and during
batch `ℓ + 1` its policy depends on the grid only through `t_1, …, t_ℓ` (and the current round).

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
* `𝓜_0` is `InfoModel 0` [INC-P006, Definition `def:infomodel`], applied to the family
  `fun g ↦ hy w₀ β g` indexed by the grids; the paper's "it does not know `t_(ℓ+1)`, and it does
  not know any horizon" (Definition `def:M0`) is its condition (b) with `k = 0`.
* HY is `Incognita.BatchedBandits.hy w₀ β g`, the algorithm `HY(w₀, β, ω^dy, ϑ, γ)` of
  Definition `def:hy` on the grid `g` with the default `ω^dy`, `ϑ`, `γ` (`Grid.hyOmega`,
  `Grid.hyTheta`, `Grid.hyGamma`); its tie rules are fixed functions of the values (LML's
  `argmax`/`argmin`, the enumeration `Fintype.equivFin α`), which the paper allows (it fixes the
  tie rules and does not use them); its divergences use the dual formula with rational `λ`, as the
  paper allows for empirical laws (module docstring of `Incognita.BatchedBandits.HY`).
  `[Nonempty α]` (implied by `hK`) is needed to define the leader.
* The parameters `w₀ ≥ 0`, `β ≥ 2` are those of Definition `def:hy` (`hw₀`, `hβ`); the default
  parameters are `w₀ = 1`, `β = 2`, and Theorem `thm:upper` covers every `w₀ ≥ 0`, `β ≥ 2`. The
  determinism of HY holds by construction (`hyAlg` is an `Algorithm.deterministic`). -/
theorem Incognita.Statements.P000.hy_infoModel_zero {α : Type*}
    [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (hK : 2 ≤ Fintype.card α) [Nonempty α]
    {w₀ β : ℝ} (hw₀ : 0 ≤ w₀) (hβ : 2 ≤ β) :
    Incognita.BatchedBandits.InfoModel (0 : ℕ∞)
      (fun g : Incognita.BatchedBandits.Grid (Fintype.card α) ↦
        (Incognita.BatchedBandits.hy w₀ β g : Learning.Algorithm Unit α ℝ)) := by
  sorry
