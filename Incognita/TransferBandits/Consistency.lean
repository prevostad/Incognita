/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.Setting

/-! # Drift conditions and the consistency class `𝒞_L`

The objects of [INC-P003, def:drift and def:consistency] (paper `P003-transfer-setting`).

## Main definitions

* `unitBandits α`: the instances `𝒫^K`, Markov kernels whose laws are concentrated on `[0,1]`.
* `DriftBound L ν ν'`: the one-sided drift condition `Drift_L`, `μ_k - μ'_k < L_k` for every arm
  (def:drift); `TwoSidedDriftBound L ν ν'`: `|μ_k - μ'_k| < L_k`.
* `meanBand L`: the set `𝒫_L` of pairs of instances with `|μ_k - μ'_k| ≤ L_k` (def:drift).
* `IsConsistent L π`: the transfer learner `π` belongs to the class `𝒞_L` of [PMRM26, Section 4.2]
  (def:consistency).
* `IsConsistentOnUnit σ`: the bandit algorithm `σ` is consistent on `𝒫^K` (def:consistency).

Means are Bochner integrals `(ν a)[id]`, as in LML. An arm `a` is suboptimal for `ν` if some arm
has a larger mean. The vector `L` is any function `α → ℝ`; the paper takes `L ∈ (0, ∞)^K`, and the
statements that use these notions assume `∀ a, 0 < L a`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Filter

open scoped ENNReal Topology

namespace Incognita.TransferBandits

variable {α : Type*} [MeasurableSpace α]

/-- The instances `𝒫^K` [INC-P003, def:laws and def:instance]: Markov kernels `ν : Kernel α ℝ` such
that every law `ν a` is concentrated on `[0, 1]`. -/
def unitBandits (α : Type*) [MeasurableSpace α] : Set (Kernel α ℝ) :=
  {ν | IsMarkovKernel ν ∧ ∀ a, ∀ᵐ x ∂(ν a), x ∈ Set.Icc 0 1}

/-- The **drift condition** `Drift_L` [INC-P003, def:drift]: `μ_k - μ'_k < L_k` for every
arm `k`, with `μ_k` and `μ'_k` the means of `ν k` and `ν' k`. -/
def DriftBound (L : α → ℝ) (ν ν' : Kernel α ℝ) : Prop :=
  ∀ a, (ν a)[id] - (ν' a)[id] < L a

/-- The **two-sided strict drift condition** [INC-P003, def:drift]: `|μ_k - μ'_k| < L_k` for
every arm `k`. -/
def TwoSidedDriftBound (L : α → ℝ) (ν ν' : Kernel α ℝ) : Prop :=
  ∀ a, |(ν a)[id] - (ν' a)[id]| < L a

/-- The set `𝒫_L` [INC-P003, def:drift; PMRM26, Section 4.2]: the pairs `(ν, ν')` of
instances of `𝒫^K` with `|μ_k - μ'_k| ≤ L_k` for every arm `k`. -/
def meanBand (L : α → ℝ) : Set (Kernel α ℝ × Kernel α ℝ) :=
  {p | p.1 ∈ unitBandits α ∧ p.2 ∈ unitBandits α ∧ ∀ a, |(p.1 a)[id] - (p.2 a)[id]| ≤ L a}

/-- The **consistency class** `𝒞_L` of [PMRM26, Section 4.2], as formalised in
[INC-P003, def:consistency]: for every pair `(ν, ν') ∈ 𝒫_L`, every source strategy `ρ`, every
suboptimal arm `a` of `ν` and every `c > 0`, `E[N_a(T)] / T ^ c → 0` as `T → ∞`, the expectation
being under the law of the game at horizon `T` with the size rule `ρ T`. -/
def IsConsistent (L : α → ℝ) (π : TransferAlgorithm α) : Prop :=
  ∀ ν ν' : Kernel α ℝ, (ν, ν') ∈ meanBand L →
    ∀ ρ : ℕ → SourceSpace α → α → ℕ, IsSourceStrategy ρ →
      ∀ a, (∃ b, (ν a)[id] < (ν b)[id]) → ∀ c : ℝ, 0 < c →
        Tendsto (fun T : ℕ ↦
            (∫ p, (onlineCount a p.2 : ℝ) ∂(gameMeasure ν' (ρ T) ν π T)) / (T : ℝ) ^ c)
          atTop (𝓝 0)

/-- A bandit algorithm `σ = alg` of LML is **consistent on `𝒫^K`** [INC-P003, def:consistency;
PMRM26, Section 4.1]: for every instance `ν ∈ 𝒫^K`, every suboptimal arm `a` and every `c > 0`,
`E_{σ,ν}[N_a(T)] / T ^ c → 0`, with `N_a(T)` the number of pulls of `a` in the rounds
`0, …, T - 1` (LML's `pullCount`) under LML's law of the trajectory. -/
def IsConsistentOnUnit [DecidableEq α] (alg : Algorithm Unit α ℝ) : Prop :=
  ∀ ν : Kernel α ℝ, ∀ [IsMarkovKernel ν], (∀ a, ∀ᵐ x ∂(ν a), x ∈ Set.Icc 0 1) →
    ∀ a, (∃ b, (ν a)[id] < (ν b)[id]) → ∀ c : ℝ, 0 < c →
      Tendsto (fun T : ℕ ↦
          (∫ ω, (pullCount IT.action a T ω : ℝ) ∂(trajMeasure alg (Environment.bandit ν))) /
            (T : ℝ) ^ c)
        atTop (𝓝 0)

end Incognita.TransferBandits
