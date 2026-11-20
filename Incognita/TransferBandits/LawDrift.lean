/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.Examples

/-! # Drift measured between laws on a finite support

The objects of [INC-P002, sec:setting and def:constant] (paper `P002-transfer-drift-between-laws`,
direction D8 of the roadmap TransferBandits): laws on a known finite set `S ⊂ [0,1]`, their
Kullback–Leibler divergence, integral probability metrics `d_𝓕` between them, the class `Θ` of
instances with `d(ν_k, ν'_k) < L_k`, the consistency class `Cons(N')` for deterministic source
sizes, and the constant `D_a(c)` of the transfer setting.

## Conventions

* `S : Finset ℝ` is the support (the statements assume `S ⊆ [0,1]` and `2 ≤ S.card`). A law on `S`
  is a probability vector `q : S → ℝ` (`probVecs S`, the paper's `𝒫_S`); a law of the game is a
  probability measure on `ℝ` carried by `S`, and `lawVec S P` is its vector `y ↦ P {y}`.
* An instance is a Markov kernel `ν : Kernel α ℝ` with `ν a Sᶜ = 0` for every arm
  (`supportBandits S α`), as in the setting of [INC-P003]; the mean of arm `k` is the Bochner
  integral `(ν k)[id]`, which is the paper's `m(ν_k) = ∑_y ν_k(y) y` for a law carried by `S`.
* `KL` and `K_S` take values in `ℝ≥0∞`, with `KL(r, q) = ∞` when `q(y) = 0 < r(y)`, and
  `inf ∅ = ∞` (the paper's conventions). Products `x · KL` are products in `ℝ≥0∞` of
  `ENNReal.ofReal x`, so `0 · ∞ = 0`, as in the paper.
* The source sizes are deterministic: `N' : ℕ → α → ℕ`, the size rule at horizon `T` being the
  constant rule `constSize (N' T)` of [INC-P003].

## Main definitions

* `probVecs S`, `lawVec S P`, `vecMean q`, `vecKL r q`, `vecKs S r ℓ` (def:laws).
* `ipm 𝓕 q q'` (`d_𝓕`), `IsTestClass 𝓕`, the four examples `tvClass`, `ksClass`, `w1Class`,
  `meanClass`, and the mean property `HasMeanProperty` (def:ipm).
* `supportBandits S α`, `bestMean ν` (def:model).
* `lawDriftClass 𝓕 L` (`Θ`) and `IsLawConsistent 𝓕 L N' π` (`π ∈ Cons(N')`) (def:class).
* `altPairs`, `programme`, `driftConstant`, `armConstant` (`Γ_a(μ)`, `J_a(x,c;μ)`, `D_a(c)`)
  (def:constant).
* `IsKLProj` (the projections `Q⋆`, `Q'⋆` of def:constant), `reachGain` and `thresholdKL`
  (`ω_d` and `G^d` of prop:threshold).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal Topology

namespace Incognita.TransferBandits

/-! ### Laws on a finite support -/

/-- The probability vectors `𝒫_S` on a finite set `S` [INC-P002, def:laws]. -/
def probVecs (S : Finset ℝ) : Set (S → ℝ) :=
  {q | (∀ y, 0 ≤ q y) ∧ ∑ y, q y = 1}

/-- The vector `y ↦ P {y}` of a measure `P` on `ℝ`, on the points of `S`. For a probability
measure carried by `S` it is the probability vector with which the paper identifies the law. -/
noncomputable def lawVec (S : Finset ℝ) (P : Measure ℝ) : S → ℝ :=
  fun y ↦ (P {(y : ℝ)}).toReal

/-- The mean `m(q) = ∑_y q(y) y` of a vector on `S` [INC-P002, def:laws]. -/
def vecMean {S : Finset ℝ} (q : S → ℝ) : ℝ :=
  ∑ y, q y * y

open Classical in
/-- The Kullback–Leibler divergence `KL(r, q) = ∑_{y : r(y) > 0} r(y) log (r(y)/q(y))` of two
vectors on `S` [INC-P002, def:laws], with `KL(r, q) = ∞` if `q(y) = 0 < r(y)` for some `y`. On
probability vectors the sum is nonnegative, so `ENNReal.ofReal` loses nothing there. -/
noncomputable def vecKL {S : Finset ℝ} (r q : S → ℝ) : ℝ≥0∞ :=
  if ∀ y, 0 < r y → 0 < q y then
    ENNReal.ofReal (∑ y, if 0 < r y then r y * Real.log (r y / q y) else 0)
  else ∞

/-- The smallest divergence `K_S(ρ, ℓ) = inf {KL(ρ, q) : q ∈ 𝒫_S, m(q) ≥ ℓ}` from `ρ` to a law
of mean at least `ℓ` [INC-P002, def:laws], with `inf ∅ = ∞`. -/
noncomputable def vecKs (S : Finset ℝ) (ρ : S → ℝ) (ℓ : ℝ) : ℝ≥0∞ :=
  ⨅ q ∈ {q ∈ probVecs S | ℓ ≤ vecMean q}, vecKL ρ q

/-! ### Integral probability metrics -/

/-- The integral probability metric `d_𝓕(q, q') = sup_{f ∈ 𝓕} |∑_y f(y) (q(y) - q'(y))|`
[INC-P002, def:ipm]. The statements assume `IsTestClass 𝓕` (nonempty, values in `[0,1]`), so the
supremum is that of a nonempty set bounded by `∑_y |q(y) - q'(y)|`. -/
noncomputable def ipm {S : Finset ℝ} (𝓕 : Set (S → ℝ)) (q q' : S → ℝ) : ℝ :=
  ⨆ f : 𝓕, |∑ y, (f : S → ℝ) y * (q y - q' y)|

/-- A set of test functions of [INC-P002, def:ipm]: a nonempty set of functions `S → [0,1]`. -/
def IsTestClass {S : Finset ℝ} (𝓕 : Set (S → ℝ)) : Prop :=
  𝓕.Nonempty ∧ ∀ f ∈ 𝓕, ∀ y, f y ∈ Set.Icc 0 1

/-- The test functions of the total variation: all functions `S → [0,1]`. -/
def tvClass (S : Finset ℝ) : Set (S → ℝ) :=
  {f | ∀ y, f y ∈ Set.Icc 0 1}

/-- The test functions of the Kolmogorov distance: the indicators of `(-∞, s]`, `s ∈ ℝ`. -/
noncomputable def ksClass (S : Finset ℝ) : Set (S → ℝ) :=
  Set.range fun s : ℝ ↦ fun y : S ↦ if (y : ℝ) ≤ s then 1 else 0

/-- The test functions of the Wasserstein distance `W₁`: the `1`-Lipschitz functions
`S → [0,1]`. -/
def w1Class (S : Finset ℝ) : Set (S → ℝ) :=
  {f | (∀ y, f y ∈ Set.Icc 0 1) ∧ ∀ y z : S, |f y - f z| ≤ |(y : ℝ) - z|}

/-- The test function of the mean gap: `{y ↦ y}`, so that `d(q, q') = |m(q) - m(q')|`. -/
def meanClass (S : Finset ℝ) : Set (S → ℝ) :=
  {fun y : S ↦ (y : ℝ)}

/-- The mean property `(M)` of [INC-P002, def:ipm]: `|m(q) - m(q')| ≤ d_𝓕(q, q')` for all
`q, q' ∈ 𝒫_S`. -/
def HasMeanProperty {S : Finset ℝ} (𝓕 : Set (S → ℝ)) : Prop :=
  ∀ q ∈ probVecs S, ∀ q' ∈ probVecs S, |vecMean q - vecMean q'| ≤ ipm 𝓕 q q'

/-! ### Instances on `S`, the class `Θ` and consistency -/

variable {α : Type*} [MeasurableSpace α]

/-- The instances on `S` [INC-P002, def:model]: Markov kernels `ν : Kernel α ℝ` whose laws are
carried by `S`, `ν a Sᶜ = 0` for every arm `a`. -/
def supportBandits (S : Finset ℝ) (α : Type*) [MeasurableSpace α] : Set (Kernel α ℝ) :=
  {ν | IsMarkovKernel ν ∧ ∀ a, ν a (↑S : Set ℝ)ᶜ = 0}

/-- The best mean `μ⋆ = max_k μ_k` of an instance (a supremum over the finite set of arms). -/
noncomputable def bestMean (ν : Kernel α ℝ) : ℝ :=
  ⨆ k, (ν k)[id]

/-- The class of instances `Θ` [INC-P002, def:class]: the pairs `(ν, ν')` of instances on `S`
with `d_𝓕(ν_k, ν'_k) < L_k` for every arm `k`. -/
def lawDriftClass {S : Finset ℝ} (𝓕 : Set (S → ℝ)) (L : α → ℝ) :
    Set (Kernel α ℝ × Kernel α ℝ) :=
  {p | p.1 ∈ supportBandits S α ∧ p.2 ∈ supportBandits S α ∧
    ∀ k, ipm 𝓕 (lawVec S (p.1 k)) (lawVec S (p.2 k)) < L k}

/-- The consistency class `Cons(N')` [INC-P002, def:class] for a sequence `N' = (N'(T))_T` of
deterministic source sizes: for every `(ν, ν') ∈ Θ`, every arm `k` with `μ_k < μ⋆` and every
`c > 0`, `E[N_k(T)] / T ^ c → 0` (that is, `E[N_k(T)] = o(T^c)`), the expectation being under the
law of the game of [INC-P003] at horizon `T` with the constant size rule `N'(T)`. -/
def IsLawConsistent {S : Finset ℝ} (𝓕 : Set (S → ℝ)) (L : α → ℝ) (N' : ℕ → α → ℕ)
    (π : TransferAlgorithm α) : Prop :=
  ∀ ν ν' : Kernel α ℝ, (ν, ν') ∈ lawDriftClass 𝓕 L →
    ∀ k, (ν k)[id] < bestMean ν → ∀ c : ℝ, 0 < c →
      Tendsto (fun T : ℕ ↦
          (∫ p, (onlineCount k p.2 : ℝ) ∂(gameMeasure ν' (constSize (N' T)) ν π T)) /
            (T : ℝ) ^ c)
        atTop (𝓝 0)

/-! ### The constant -/

/-- The alternative pairs `Γ_a(μ) = {(q, q') ∈ 𝒫_S² : m(q) ≥ μ, d(q, q') ≤ l}`
[INC-P002, def:constant], with `l = L_a`. -/
def altPairs {S : Finset ℝ} (𝓕 : Set (S → ℝ)) (l μ : ℝ) : Set ((S → ℝ) × (S → ℝ)) :=
  {p | p.1 ∈ probVecs S ∧ p.2 ∈ probVecs S ∧ μ ≤ vecMean p.1 ∧ ipm 𝓕 p.1 p.2 ≤ l}

/-- The programme `J_a(x, c; μ) = inf_{(q,q') ∈ Γ_a(μ)} [x KL(ν_a, q) + c KL(ν'_a, q')]`
[INC-P002, def:constant], with `r = ν_a`, `r' = ν'_a` and `l = L_a`; in `ℝ≥0∞`, with
`inf ∅ = ∞` and `0 · ∞ = 0`. -/
noncomputable def programme {S : Finset ℝ} (𝓕 : Set (S → ℝ)) (l : ℝ) (r r' : S → ℝ)
    (μ x c : ℝ) : ℝ≥0∞ :=
  ⨅ p ∈ altPairs 𝓕 l μ, ENNReal.ofReal x * vecKL r p.1 + ENNReal.ofReal c * vecKL r' p.2

/-- The constant `D_a(c) = inf {x > 0 : J_a(x, c; μ⋆) ≥ 1}` [INC-P002, def:constant], with
`r = ν_a`, `r' = ν'_a`, `l = L_a` and `μ = μ⋆`. The infimum is a real infimum: for a suboptimal arm
the set is nonempty (it contains every `x ≥ 1/K_S(ν_a, μ⋆)` when `K_S(ν_a, μ⋆) < ∞`, and every
`x > 0` otherwise), so no junk value of `sInf ∅` enters the statements. -/
noncomputable def driftConstant {S : Finset ℝ} (𝓕 : Set (S → ℝ)) (l : ℝ) (r r' : S → ℝ)
    (μ c : ℝ) : ℝ :=
  sInf {x : ℝ | 0 < x ∧ 1 ≤ programme 𝓕 l r r' μ x c}

/-- The constant `D_a(c)` of an arm `a` of the pair of instances `(ν, ν')` on `S`, with the drift
bound `L_a` and the best mean `μ⋆` of `ν` [INC-P002, def:constant]. -/
noncomputable def armConstant {S : Finset ℝ} (𝓕 : Set (S → ℝ)) (L : α → ℝ)
    (ν ν' : Kernel α ℝ) (a : α) (c : ℝ) : ℝ :=
  driftConstant 𝓕 (L a) (lawVec S (ν a)) (lawVec S (ν' a)) (bestMean ν) c

/-! ### Objects of the structure results -/

/-- `Q` is a Kullback–Leibler projection of `ρ` on `{q ∈ 𝒫_S : m(q) ≥ ℓ}`: a minimiser of
`KL(ρ, ·)` on this set [INC-P002, def:constant] (the paper's `Q⋆` for `ρ = ν_a`, `ℓ = μ⋆`, and
`Q'⋆` for `ρ = ν'_a`, `ℓ = μ⋆ - L_a`; unique by [INC-P002, lem:projection]). -/
def IsKLProj {S : Finset ℝ} (ρ : S → ℝ) (ℓ : ℝ) (Q : S → ℝ) : Prop :=
  Q ∈ probVecs S ∧ ℓ ≤ vecMean Q ∧ ∀ q ∈ probVecs S, ℓ ≤ vecMean q → vecKL ρ Q ≤ vecKL ρ q

/-- The largest increase of the mean allowed by the drift bound from `q'`,
`ω_d(q') = max {m(q) - m(q') : q ∈ 𝒫_S, d(q, q') ≤ l}` [INC-P002, prop:threshold], with
`l = L_a`; a real supremum (for `q' ∈ 𝒫_S`, `l ≥ 0` and `𝓕` a test class the set contains `0`, at
`q = q'`, and is bounded by `1`; the paper shows the maximum is attained). -/
noncomputable def reachGain {S : Finset ℝ} (𝓕 : Set (S → ℝ)) (l : ℝ) (q' : S → ℝ) : ℝ :=
  sSup {m | ∃ q ∈ probVecs S, ipm 𝓕 q q' ≤ l ∧ m = vecMean q - vecMean q'}

/-- The threshold divergence `G^d = min {KL(ν'_a, q') : q' ∈ 𝒫_S, m(q') + ω_d(q') ≥ μ⋆}`
[INC-P002, prop:threshold], with `r' = ν'_a`, `l = L_a` and `μ = μ⋆`; an infimum in `ℝ≥0∞`
(`inf ∅ = ∞`; the paper's minimum when it is attained). -/
noncomputable def thresholdKL {S : Finset ℝ} (𝓕 : Set (S → ℝ)) (l : ℝ) (r' : S → ℝ) (μ : ℝ) :
    ℝ≥0∞ :=
  ⨅ q' ∈ {q' ∈ probVecs S | μ ≤ vecMean q' + reachGain 𝓕 l q'}, vecKL r' q'

end Incognita.TransferBandits
