/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.StochasticBandits.GravesLai
public import Incognita.StochasticBandits.UCB
public import LMLExplore.Bandits.MinimaxLowerBound
public import LMLExplore.Probability.Distributions.ExponentialFamily.Basic
public import TauCeti.Probability.Distributions.Bernoulli.Basic
public import TauCeti.Probability.Distributions.Tilted

/-! # The minimax regret, the classes `𝒞(a, b, σ̄, σ_p)` and the regular classes

The objects of [INC-P001, Definitions `def:regret`, `def:class` and `def:regular`], with the
conventions of the roadmap StochasticBandits: an instance is an LML bandit `ν : Kernel α ℝ`, a
learner is LML's `Algorithm Unit α ℝ`, run by `trajMeasure alg (Environment.bandit ν)`, rounds are
numbered from `0` (horizon `T` means the rounds `0, …, T - 1`), and the regret at horizon `T` is the
expectation of LML's `regret ν IT.action T = ∑_{s < T} Δ_{A_s}`, which is `∑_a Δ_a E[N_a(T)]`.

## Main definitions

* `Incognita.StochasticBandits.minimaxRegret E T`: the minimax regret
  `R⋆(T) = inf_π sup_{ν ∈ E} R_T(π, ν)` of a class `E` of instances, in `ℝ≥0∞`.
* `Incognita.StochasticBandits.subGaussClass a b σ̄ σ_p`: the laws with mean in `[a, b]`, variance
  at most `σ̄²` and `σ_p²`-sub-Gaussian centred moment generating function.
* `Incognita.StochasticBandits.RegularR1`, `Incognita.StochasticBandits.RegularR2`,
  `Incognita.StochasticBandits.IsRegular`: conditions (R1), (R2), and the regular classes, with
  the two cases of (R2), `ContainsExpFamily` and `ContainsPerturbations` [INC-P001, Definition
  `def:lowR2`].

## Main statements (the checks of AGENTS.md §6.4)

* `minimaxRegret_singleton` (witness: one instance, `R⋆ = 0`),
  `ofReal_le_minimaxRegret_gaussian` (known case: the minimax lower bound of [LS, Theorem 15.2]
  for Gaussian rewards, from LMLExplore), `minimaxRegret_gaussian_ne_zero` (exclusion).
* `gaussianReal_mem_subGaussClass` (witness), `unitLaws_subset_subGaussClass` (known case: the
  laws on `[0, 1]`, by Popoviciu's inequality and Hoeffding's lemma), `dirac_not_mem_subGaussClass`
  (exclusion).
* `regularR1_subGaussClass` (known case), `not_regularR1_dirac` (exclusion);
  `isRegular_gaussian` (witness of `RegularR2` and `IsRegular`: the Gaussian laws with means in
  `[a, b]` and variance at most `σ̄²`, an example of the paper), `isRegular_unitLaws` (known case:
  the laws on `[0, 1]`, with variance `1/2`, another example of the paper),
  `containsPerturbations_univ` (witness), `not_regularR2_dirac` (exclusion: the Dirac laws satisfy
  (R1) but not (R2)).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Bandits Filter

open scoped ENNReal NNReal unitInterval

namespace Incognita.StochasticBandits

section Minimax

variable {α : Type*} [MeasurableSpace α]

/-- The **minimax regret** `R⋆_{K, 𝒞}(T) = inf_π sup_{ν ∈ E} R_T(π, ν)` of a class `E` of
instances at horizon `T` [INC-P001, Definition `def:regret`], in `ℝ≥0∞`. The infimum runs over
LML's learners `Algorithm Unit α ℝ`: a horizon-dependent policy `(π_T)_T` has, at horizon `T`, the
regret of `π_T`, so the infimum over families at a fixed `T` is the infimum over single learners.
An LML learner draws its action at each round from a kernel of the history, which describes every
policy with an external randomization (the history contains the past actions: Kuhn's theorem).
The regret `R_T(π, ν)` is the expectation of LML's `regret ν IT.action T`, the sum of the gaps of
the actions of the rounds `0, …, T - 1`, which equals `∑_a Δ_a E[N_a(T)]`. Only Markov kernels
are bandit instances, so the supremum runs over the Markov kernels of `E` (every element of a
class `productClass fun _ ↦ 𝒞` with `𝒞` a set of laws is one). -/
noncomputable def minimaxRegret (E : Set (Kernel α ℝ)) (T : ℕ) : ℝ≥0∞ :=
  ⨅ alg : Algorithm Unit α ℝ, ⨆ ν ∈ E, ⨆ h : IsMarkovKernel ν,
    letI := h
    ENNReal.ofReal (∫ ω, regret ν IT.action T ω ∂(trajMeasure alg (Environment.bandit ν)))

variable [Fintype α] [MeasurableSingletonClass α]

omit [Fintype α] in
/-- **Witness**: on a class with a single instance `ν`, the learner that always pulls an optimal
arm has regret `0`, so the minimax regret is `0`. -/
lemma minimaxRegret_singleton (ν : Kernel α ℝ) {c : α} (hc : gap ν c = 0) (T : ℕ) :
    minimaxRegret {ν} T = 0 := by
  refine le_antisymm ((iInf_le _ (Algorithm.const (Measure.dirac c))).trans ?_) bot_le
  simp only [Set.mem_singleton_iff, iSup_iSup_eq_left]
  refine iSup_le fun h ↦ ?_
  have : ∀ᵐ ω ∂(trajMeasure (Algorithm.const (Measure.dirac c)) (Environment.bandit ν)),
      regret ν IT.action T ω = 0 := by
    filter_upwards [BatchedBandits.ae_forall_action_eq_const c ν] with ω hω
    simp [regret_eq_sum_gap, hω, hc]
  rw [integral_congr_ae this]
  simp

omit [Fintype α] in
/-- The Gaussian bandits with means in `[0, 1]` and variance `σ²` (LMLExplore's
`gaussianBandit`) are in the product class of the Gaussian laws `𝒩(m, σ²)`, `m ∈ [0, 1]`. -/
lemma gaussianBandit_mem [Finite α] (μ : α → ℝ) (σ2 : ℝ≥0) (hμ : ∀ a, μ a ∈ Set.Icc 0 1) :
    LMLExplore.Bandits.gaussianBandit μ σ2 ∈
      productClass (fun _ : α ↦ {Q | ∃ m ∈ Set.Icc (0 : ℝ) 1, Q = gaussianReal m σ2}) :=
  fun a ↦ ⟨μ a, hμ a, by rw [LMLExplore.Bandits.gaussianBandit_apply]⟩

/-- **Known case**: the minimax lower bound for Gaussian rewards [LS, Theorem 15.2], with the
constant `1 / 16` of LMLExplore's `exists_sqrt_le_integral_regret_gaussianBandit`: on the
Gaussian laws of variance `σ²` and means in `[0, 1]`, `R⋆(T) ≥ √(σ² (K - 1) T) / 16` for
`σ² (K - 1) ≤ T`. -/
lemma ofReal_le_minimaxRegret_gaussian (σ2 : ℝ≥0) (T : ℕ) (hK : 2 ≤ Fintype.card α)
    (hT : σ2 * (Fintype.card α - 1 : ℝ) ≤ T) :
    ENNReal.ofReal (√(σ2 * (Fintype.card α - 1) * T) / 16) ≤
      minimaxRegret
        (productClass (fun _ : α ↦ {Q | ∃ m ∈ Set.Icc (0 : ℝ) 1, Q = gaussianReal m σ2})) T := by
  refine le_iInf fun alg ↦ ?_
  obtain ⟨μ, hμ, hR⟩ :=
    LMLExplore.Bandits.exists_sqrt_le_integral_regret_gaussianBandit alg σ2 T hK hT
  refine le_iSup₂_of_le (LMLExplore.Bandits.gaussianBandit μ σ2) (gaussianBandit_mem μ σ2 hμ) ?_
  exact le_iSup_of_le inferInstance (ENNReal.ofReal_le_ofReal hR)

/-- **Exclusion**: the minimax regret is not identically `0`: it is positive on the Gaussian laws
of variance `1` with means in `[0, 1]`, for `K ≥ 2` arms and `T ≥ K - 1` (`T ≥ 1`). -/
lemma minimaxRegret_gaussian_ne_zero {T : ℕ} (hK : 2 ≤ Fintype.card α)
    (hT : (Fintype.card α - 1 : ℝ) ≤ T) :
    minimaxRegret
      (productClass (fun _ : α ↦ {Q | ∃ m ∈ Set.Icc (0 : ℝ) 1, Q = gaussianReal m 1})) T ≠ 0 := by
  have hle := ofReal_le_minimaxRegret_gaussian (α := α) 1 T hK (by simpa using hT)
  have hK1 : (1 : ℝ) ≤ Fintype.card α - 1 := by
    have : (2 : ℝ) ≤ Fintype.card α := by exact_mod_cast hK
    linarith
  have hpos : 0 < √((1 : ℝ≥0) * (Fintype.card α - 1) * T) / 16 := by
    refine div_pos (Real.sqrt_pos.2 ?_) (by norm_num)
    push_cast
    nlinarith
  exact ne_bot_of_le_ne_bot (by simpa using hpos) hle

end Minimax

section Classes

/-- The class `𝒞(a, b, σ̄, σ_p)` [INC-P001, Definition `def:class`]: the probability measures `ν`
on `ℝ` with mean `μ = ∫ x dν` in `[a, b]`, variance at most `σ̄²`, and
`E_ν e^{λ (X - μ)} ≤ e^{λ² σ_p² / 2}` for every `λ ∈ ℝ` (Mathlib's `HasSubgaussianMGF` with
parameter `σ_p²`, which includes the integrability of `e^{λ (X - μ)}`; it gives the mean a
meaning). The variance is `evariance`, in `[0, ∞]`. The paper takes `a < b` and
`0 < σ̄ ≤ σ_p`; the set is defined for all parameters, and the statements assume these
conditions. -/
def subGaussClass (a b σbar σp : ℝ) : Set (Measure ℝ) :=
  {ν | IsProbabilityMeasure ν ∧ (∫ x, x ∂ν) ∈ Set.Icc a b ∧
    evariance id ν ≤ ENNReal.ofReal (σbar ^ 2) ∧
    HasSubgaussianMGF (fun x ↦ x - ∫ y, y ∂ν) (σp ^ 2).toNNReal ν}

/-- Condition **(R1)** of a regular class with variance `σ̄` [INC-P001, Definition `def:regular`]:
`𝒞 ⊆ 𝒞(a, b, σ̄, σ_p)` for some `a < b` and `σ_p ≥ σ̄`; `0 < σ̄` is part of Definition `def:class`
of `𝒞(a, b, σ̄, σ_p)`. -/
def RegularR1 (C : Set (Measure ℝ)) (σbar : ℝ) : Prop :=
  0 < σbar ∧ ∃ a b σp : ℝ, a < b ∧ σbar ≤ σp ∧ C ⊆ subGaussClass a b σbar σp

/-- First case of (R2) [INC-P001, Definitions `def:regular` and `def:lowR2`(a)]: `𝒞` contains a
regular natural exponential family through `ν₀`, on both sides or on one side of `ν₀`. The family
is `θ ↦ ν₀.expFamily id θ`, the tilt `ν_θ ∝ e^{θ x} ν₀(dx)` (LMLExplore's `expFamily`, with the
statistic `id`), its natural parameter space `integrableExpSet id ν₀` contains a neighbourhood of
`0`, and `ν_θ ∈ 𝒞` for `θ ∈ (-β₀, β₀)`, or `θ ∈ (-β₀, 0]`, or `θ ∈ [0, β₀)`. The paper writes
the family from any base measure with `ν_{θ₀} = ν₀`; reparametrized by `θ - θ₀`, it is this one.
Since `β₀` can be shrunk, `ν_θ` is only used for `θ` in the natural parameter space. -/
def ContainsExpFamily (C : Set (Measure ℝ)) (ν₀ : Measure ℝ) : Prop :=
  0 ∈ interior (integrableExpSet id ν₀) ∧ ∃ β₀ > 0,
    (∀ θ ∈ Set.Ioo (-β₀) β₀, ν₀.expFamily id θ ∈ C) ∨
    (∀ θ ∈ Set.Ioc (-β₀) 0, ν₀.expFamily id θ ∈ C) ∨
    (∀ θ ∈ Set.Ico 0 β₀, ν₀.expFamily id θ ∈ C)

/-- Second case of (R2) [INC-P001, Definitions `def:regular` and `def:lowR2`(b)]: `𝒞` contains the
bounded perturbations of `ν₀`: for every bounded Borel `g` with `∫ g dν₀ = 0` there is `t_g > 0`
with `(1 + t g) ν₀ ∈ 𝒞` for every `|t| ≤ t_g`. The measure `(1 + t g) ν₀` is written
`ν₀.withDensity (fun x ↦ ENNReal.ofReal (1 + t g x))`; for `|t| ≤ t_g ≤ 1 / sup |g|` the density
is nonnegative and this is the paper's probability measure, and `t_g` can be shrunk to that. -/
def ContainsPerturbations (C : Set (Measure ℝ)) (ν₀ : Measure ℝ) : Prop :=
  ∀ g : ℝ → ℝ, Measurable g → (∃ G, ∀ x, |g x| ≤ G) → ∫ x, g x ∂ν₀ = 0 →
    ∃ tg > 0, ∀ t, |t| ≤ tg → ν₀.withDensity (fun x ↦ ENNReal.ofReal (1 + t * g x)) ∈ C

/-- Condition **(R2)** of a regular class with variance `σ̄` [INC-P001, Definitions `def:regular`
and `def:lowR2`]: for every `σ₀ < σ̄` there is a law `ν₀ ∈ 𝒞` with a finite mean and variance at
least `σ₀²` such that `𝒞` contains an exponential family through `ν₀` (on both sides or on one
side) or the bounded perturbations of `ν₀`. The standard deviation `σ₀` ranges over `(0, σ̄)`:
`σ₀ ≤ 0` asks nothing more than any `σ₀ ∈ (0, σ̄)`. The variance is `evariance`, in `[0, ∞]`. -/
def RegularR2 (C : Set (Measure ℝ)) (σbar : ℝ) : Prop :=
  ∀ σ₀ : ℝ, 0 < σ₀ → σ₀ < σbar → ∃ ν₀ ∈ C, IsProbabilityMeasure ν₀ ∧ Integrable id ν₀ ∧
    ENNReal.ofReal (σ₀ ^ 2) ≤ evariance id ν₀ ∧
    (ContainsExpFamily C ν₀ ∨ ContainsPerturbations C ν₀)

/-- A **regular class with variance `σ̄`** [INC-P001, Definition `def:regular`]: (R1) and (R2). -/
def IsRegular (C : Set (Measure ℝ)) (σbar : ℝ) : Prop := RegularR1 C σbar ∧ RegularR2 C σbar

/-- The Gaussian law `𝒩(μ, v)` is `v`-sub-Gaussian around its mean. -/
lemma hasSubgaussianMGF_gaussianReal (μ : ℝ) (v : ℝ≥0) :
    HasSubgaussianMGF (fun x ↦ x - ∫ y, y ∂gaussianReal μ v) v (gaussianReal μ v) := by
  rw [integral_id_gaussianReal]
  refine ⟨fun t ↦ ?_, fun t ↦ ?_⟩
  · simp_rw [mul_sub, Real.exp_sub]
    exact (integrable_exp_mul_gaussianReal t).div_const _
  · have hX : HasLaw (fun x ↦ x - μ) (gaussianReal 0 v) (gaussianReal μ v) := by
      refine ⟨by fun_prop, ?_⟩
      rw [gaussianReal_map_sub_const]
      simp
    rw [mgf_gaussianReal hX]
    simp

/-- **Witness**: a Gaussian law `𝒩(μ, v)` with `μ ∈ [a, b]` and `v ≤ σ̄²` lies in
`𝒞(a, b, σ̄, σ̄)`. -/
lemma gaussianReal_mem_subGaussClass {a b σbar μ : ℝ} {v : ℝ≥0} (hμ : μ ∈ Set.Icc a b)
    (hv : (v : ℝ) ≤ σbar ^ 2) : gaussianReal μ v ∈ subGaussClass a b σbar σbar := by
  refine ⟨inferInstance, by rwa [integral_id_gaussianReal], ?_, ?_⟩
  · rw [← (memLp_id_gaussianReal 2).ofReal_variance_eq, variance_id_gaussianReal]
    exact ENNReal.ofReal_le_ofReal hv
  · refine (hasSubgaussianMGF_gaussianReal μ v).mono ?_
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (sq_nonneg _)]
    exact hv

/-- **Known case**: the laws on `[0, 1]` lie in `𝒞(0, 1, 1/2, 1/2)` (Popoviciu's inequality for
the variance, Hoeffding's lemma for the sub-Gaussian bound), as in the proof of the upper bounds of
[INC-P001, Corollary `cor:examples`]. -/
lemma unitLaws_subset_subGaussClass :
    BatchedBandits.unitLaws ⊆ subGaussClass 0 1 (1 / 2) (1 / 2) := by
  rintro Q ⟨hQ, hQ01⟩
  have hint : Integrable id Q := Integrable.of_mem_Icc 0 1 aemeasurable_id hQ01
  refine ⟨hQ, ⟨integral_nonneg_of_ae (hQ01.mono fun x hx ↦ hx.1), ?_⟩, ?_, ?_⟩
  · calc ∫ x, x ∂Q ≤ ∫ _, (1 : ℝ) ∂Q := integral_mono_ae hint (integrable_const 1)
          (hQ01.mono fun x hx ↦ hx.2)
      _ = 1 := by simp
  · have hmem : MemLp id 2 Q := memLp_of_bounded (a := 0) (b := 1) hQ01
      aestronglyMeasurable_id 2
    rw [← hmem.ofReal_variance_eq]
    refine ENNReal.ofReal_le_ofReal ((variance_le_sq_of_bounded hQ01 aemeasurable_id).trans ?_)
    norm_num
  · have h := hasSubgaussianMGF_of_mem_Icc (X := id) aemeasurable_id hQ01
    refine h.mono (le_of_eq ?_)
    rw [← NNReal.coe_inj, Real.coe_toNNReal _ (sq_nonneg _)]
    simp [nnnorm_one]

/-- **Exclusion**: a law whose mean is outside `[a, b]` is not in `𝒞(a, b, σ̄, σ_p)`. -/
lemma dirac_not_mem_subGaussClass {a b σbar σp x : ℝ} (hx : b < x) :
    Measure.dirac x ∉ subGaussClass a b σbar σp := by
  rintro ⟨-, ⟨-, hb⟩, -⟩
  simp at hb
  linarith

/-- **Known case** of (R1): the class `𝒞(a, b, σ̄, σ_p)` itself satisfies (R1). -/
lemma regularR1_subGaussClass {a b σbar σp : ℝ} (hab : a < b) (hσ : 0 < σbar)
    (hσp : σbar ≤ σp) : RegularR1 (subGaussClass a b σbar σp) σbar :=
  ⟨hσ, a, b, σp, hab, hσp, subset_rfl⟩

/-- **Exclusion** of (R1): a class with unbounded means, here all the Dirac laws, is in no
`𝒞(a, b, σ̄, σ_p)`. -/
lemma not_regularR1_dirac (σbar : ℝ) : ¬ RegularR1 (Set.range Measure.dirac) σbar := by
  rintro ⟨-, a, b, σp, -, -, hC⟩
  exact dirac_not_mem_subGaussClass (a := a) (σbar := σbar) (σp := σp) (lt_add_one b)
    (hC ⟨b + 1, rfl⟩)

/-- **Witness** of the second case of (R2): the class of all measures contains the bounded
perturbations of every law. -/
lemma containsPerturbations_univ (ν₀ : Measure ℝ) : ContainsPerturbations Set.univ ν₀ :=
  fun _ _ _ _ ↦ ⟨1, one_pos, fun _ _ ↦ Set.mem_univ _⟩

/-- The Dirac laws have variance `0`. -/
lemma evariance_dirac (x : ℝ) : evariance id (Measure.dirac x) = 0 := by
  have hmem : MemLp id 2 (Measure.dirac x) :=
    memLp_of_bounded (a := x) (b := x) (by simp) aestronglyMeasurable_id 2
  rw [← hmem.ofReal_variance_eq, variance_dirac, ENNReal.ofReal_zero]

/-- **Exclusion** of (R2): the Dirac laws with means in `[a, b]` satisfy (R1) for every `σ̄ > 0`
(their variance is `0`), but not (R2): they have no law of positive variance. -/
lemma not_regularR2_dirac {a b σbar : ℝ} (hσ : 0 < σbar) :
    ¬ RegularR2 (Measure.dirac '' Set.Icc a b) σbar := by
  intro h
  obtain ⟨_, ⟨x, -, rfl⟩, -, -, hvar, -⟩ := h (σbar / 2) (by positivity) (by linarith)
  rw [evariance_dirac, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hvar
  nlinarith

/-- **Witness**: the Gaussian laws `𝒩(μ, v)` with `μ ∈ [a, b]` and `v ≤ σ̄²` form a regular class
with variance `σ̄` (an example of [INC-P001, Definition `def:regular`]; the exponential family
through `𝒩((a + b)/2, σ̄²)` is `𝒩((a + b)/2 + σ̄² θ, σ̄²)`, on both sides). -/
lemma isRegular_gaussian {a b σbar : ℝ} (hab : a < b) (hσ : 0 < σbar) :
    IsRegular {ν | ∃ μ ∈ Set.Icc a b, ∃ v : ℝ≥0, (v : ℝ) ≤ σbar ^ 2 ∧ ν = gaussianReal μ v}
      σbar := by
  refine ⟨⟨hσ, a, b, σbar, hab, le_rfl, ?_⟩, fun σ₀ hσ₀ hσ₀' ↦ ?_⟩
  · rintro _ ⟨μ, hμ, v, hv, rfl⟩
    exact gaussianReal_mem_subGaussClass hμ hv
  set v : ℝ≥0 := (σbar ^ 2).toNNReal with hv
  have hvσ : (v : ℝ) = σbar ^ 2 := Real.coe_toNNReal _ (sq_nonneg _)
  have hv0 : (0 : ℝ) < v := by rw [hvσ]; positivity
  refine ⟨gaussianReal ((a + b) / 2) v, ⟨(a + b) / 2, ⟨by linarith, by linarith⟩, v, hvσ.le, rfl⟩,
    inferInstance, (memLp_id_gaussianReal 1).integrable le_rfl, ?_, Or.inl ⟨by simp, ?_⟩⟩
  · rw [← (memLp_id_gaussianReal 2).ofReal_variance_eq, variance_id_gaussianReal, hvσ]
    exact ENNReal.ofReal_le_ofReal (by nlinarith)
  · refine ⟨(b - a) / (2 * v), div_pos (by linarith) (by positivity), Or.inl fun θ hθ ↦ ?_⟩
    rw [Measure.expFamily_def]
    simp only [id]
    rw [TauCeti.Probability.gaussianReal_tilted_mul]
    have h1 : |(v : ℝ) * θ| ≤ (b - a) / 2 := by
      rw [abs_mul, abs_of_pos hv0]
      have := abs_lt.2 ⟨hθ.1, hθ.2⟩
      rw [lt_div_iff₀ (by positivity)] at this
      nlinarith
    rw [abs_le] at h1
    exact ⟨(a + b) / 2 + v * θ, ⟨by linarith, by linarith⟩, v, hvσ.le, rfl⟩

/-- A law on `[0, 1]` has all its exponential moments. -/
lemma integrable_exp_mul_of_mem_unitLaws {Q : Measure ℝ} (hQ : Q ∈ BatchedBandits.unitLaws)
    (t : ℝ) : Integrable (fun x ↦ Real.exp (t * x)) Q := by
  have := hQ.1
  refine Integrable.of_bound (C := Real.exp |t|) (by fun_prop) (hQ.2.mono fun x hx ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg t) (abs_le.2 ⟨by linarith [hx.1], hx.2⟩)

/-- **Known case**: the laws on `[0, 1]` form a regular class with variance `1/2` (an example of
[INC-P001, Definition `def:regular`]): (R1) by `unitLaws_subset_subGaussClass`, and (R2) with
`ν₀ = Ber(1/2)`, of variance `1/4`, whose whole exponential family stays on `[0, 1]`. -/
lemma isRegular_unitLaws : IsRegular BatchedBandits.unitLaws (1 / 2) := by
  refine ⟨⟨by norm_num, 0, 1, 1 / 2, zero_lt_one, le_rfl, unitLaws_subset_subGaussClass⟩,
    fun σ₀ hσ₀ hσ₀' ↦ ?_⟩
  set p : I := ⟨1 / 2, by norm_num, by norm_num⟩
  have hν₀ := BatchedBandits.bernoulliMeasure_mem_unitLaws p
  have hint : ∀ t, t ∈ integrableExpSet id (bernoulliMeasure (1 : ℝ) 0 p) := fun t ↦
    integrable_exp_mul_of_mem_unitLaws hν₀ t
  refine ⟨_, hν₀, hν₀.1, Integrable.of_mem_Icc 0 1 aemeasurable_id hν₀.2, ?_,
    Or.inl ⟨?_, 1, one_pos, Or.inl fun θ _ ↦ ?_⟩⟩
  · have hmem : MemLp id 2 (bernoulliMeasure (1 : ℝ) 0 p) :=
      memLp_of_bounded (a := 0) (b := 1) hν₀.2 aestronglyMeasurable_id 2
    rw [← hmem.ofReal_variance_eq, TauCeti.Probability.variance_id_bernoulliMeasure]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [p]
    nlinarith
  · have : integrableExpSet id (bernoulliMeasure (1 : ℝ) 0 p) = Set.univ :=
      Set.eq_univ_of_forall hint
    simp [this]
  · have := hν₀.1
    have hac := Measure.expFamily_absolutelyContinuous (bernoulliMeasure (1 : ℝ) 0 p) id θ
    exact ⟨Measure.isProbabilityMeasure_expFamily (hint θ), hac.ae_le hν₀.2⟩

end Classes

end Incognita.StochasticBandits
