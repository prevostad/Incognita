/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.StochasticBandits.LimitGame
public import Incognita.StochasticBandits.Minimax
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-! # P001: drafts for the second statements pull request (not frozen, not reviewed)

Drafts of what the second statements pull request of P001 (`papers/P001-minimax-constant`) adds,
written by the first one to check that the planned shapes elaborate. Nothing here is a frozen
statement: the statements below are drafts with `sorry`, in the namespace
`Incognita.Exploration.P001`, and the definitions are to be moved to `Incognita/` with their
checks. `blueprint.md` lists the planned names.

* `def:kappa`: `uStar`, `aStar`, `kappa`, `lambdaK`.
* `prop:four`(c): the translation `translate c Q` (the image of `ℓ_{-c 1} · Q` by
  `Φ_c(x, a) = (x + c a, a)`) and the relabelling `relabel σ Q` (the image of `Q` by
  `(x, a) ↦ ((x_{σ k})_k, (a_{σ k})_k)`), [INC-P001, Lemma `lem:g-act`].
* the planned statements of `thm:main`, `cor:examples`, `prop:four`, `thm:bounds`, `cor:four-c`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal NNReal unitInterval

namespace Incognita.Exploration.P001

open Incognita.StochasticBandits Incognita.StochasticBandits.LimitGame

/-! ### The constants of `def:kappa` -/

/-- `u⋆ ≈ 1.256431`, the positive root of `e^u = 1 + 2u`. -/
noncomputable def uStar : ℝ := sSup {u : ℝ | 0 < u ∧ Real.exp u = 1 + 2 * u}

/-- `a⋆ = √(2 u⋆) ≈ 1.585201`. -/
noncomputable def aStar : ℝ := √(2 * uStar)

/-- `κ = 2 a⋆ / (1 + a⋆²) ≈ 0.902512`. -/
noncomputable def kappa : ℝ := 2 * aStar / (1 + aStar ^ 2)

/-- `λ_K = exp(-K h(1/K) / (K - 1))`, with `h` the binary entropy (Mathlib's `Real.binEntropy`). -/
noncomputable def lambdaK (K : ℕ) : ℝ := Real.exp (-(K * Real.binEntropy (1 / K)) / (K - 1))

/-- `e^u = 1 + 2u` has at most one positive root (strict convexity of `exp`, and the root `0`). -/
lemma eq_of_exp_eq {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (hu' : Real.exp u = 1 + 2 * u)
    (hv' : Real.exp v = 1 + 2 * v) : u = v := by
  by_contra hne
  wlog huv : u < v generalizing u v
  · exact this hv hu hv' hu' (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 huv) (Ne.symm hne))
  have hs : 0 < u / v := div_pos hu hv
  have hs1 : u / v < 1 := (div_lt_one hv).2 huv
  have h := strictConvexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ v) hv.ne (sub_pos.2 hs1) hs
    (by ring)
  have hcomb : (1 - u / v) • (0 : ℝ) + (u / v) • v = u := by
    simp only [smul_eq_mul, mul_zero, zero_add]
    field_simp
  rw [hcomb, hu', hv', Real.exp_zero, smul_eq_mul, smul_eq_mul] at h
  have : (1 - u / v) * 1 + u / v * (1 + 2 * v) = 1 + 2 * u := by
    field_simp
    ring
  linarith

/-- The positive root of `e^u = 1 + 2u` exists, in `(1, 2)`. -/
lemma exists_root : ∃ r ∈ Set.Ioo (1 : ℝ) 2, Real.exp r = 1 + 2 * r := by
  have he := Real.exp_one_lt_d9
  have he' := Real.exp_one_gt_d9
  have h1 : Real.exp 1 - (1 + 2 * 1) < 0 := by linarith
  have h2 : 0 < Real.exp 2 - (1 + 2 * 2) := by
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith
  have hc : Continuous fun u : ℝ ↦ Real.exp u - (1 + 2 * u) := by fun_prop
  obtain ⟨r, hr, hr0⟩ := intermediate_value_Ioo (by norm_num : (1 : ℝ) ≤ 2) hc.continuousOn
    (show (0 : ℝ) ∈ Set.Ioo (Real.exp 1 - (1 + 2 * 1)) (Real.exp 2 - (1 + 2 * 2)) from ⟨h1, h2⟩)
  exact ⟨r, hr, by simp only at hr0; linarith⟩

/-- `u⋆` is the positive root of `e^u = 1 + 2u`. -/
lemma uStar_spec : uStar ∈ Set.Ioo (1 : ℝ) 2 ∧ Real.exp uStar = 1 + 2 * uStar := by
  obtain ⟨r, hr, hr'⟩ := exists_root
  have hS : {u : ℝ | 0 < u ∧ Real.exp u = 1 + 2 * u} = {r} := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    refine ⟨fun h ↦ eq_of_exp_eq h.1 (by linarith [hr.1]) h.2 hr', ?_⟩
    rintro rfl
    exact ⟨by linarith [hr.1], hr'⟩
  rw [uStar, hS, csSup_singleton]
  exact ⟨hr, hr'⟩

/-- `λ_2 = 1/4`. -/
lemma lambdaK_two : lambdaK 2 = 1 / 4 := by
  have h : -((2 : ℕ) * Real.binEntropy (1 / (2 : ℕ))) / ((2 : ℕ) - 1 : ℝ) =
      Real.log ((2 : ℝ) ^ 2)⁻¹ := by
    rw [Real.log_inv, Real.log_pow, Nat.cast_ofNat, one_div, Real.binEntropy_two_inv]
    norm_num
  rw [lambdaK, h, Real.exp_log (by norm_num)]
  norm_num

/-! ### Translations and relabellings of limit policies -/

variable (α : Type*) [Fintype α] [DecidableEq α]

/-- `Φ_c(x, a) = (x + c a, a)`. -/
def shiftMap (c : ℝ) (ω : Omega α) : Omega α := (ω.1 + c • ω.2, ω.2)

/-- `T_c Q`, the image of `ℓ_{-c 1} · Q` by `Φ_c`: `Q` run on the observations shifted by `-c`
per unit of time [INC-P001, Lemma `lem:g-act`]. -/
noncomputable def translate (c : ℝ) (Q : Measure (Omega α)) : Measure (Omega α) :=
  (Q.withDensity fun ω ↦ ENNReal.ofReal (likelihood α (fun _ ↦ -c) ω)).map (shiftMap α c)

/-- `(x, a) ↦ ((x_{σ k})_k, (a_{σ k})_k)`. -/
def permuteMap (perm : Equiv.Perm α) (ω : Omega α) : Omega α :=
  (⟨fun t k ↦ ω.1 t (perm k), by fun_prop⟩, ⟨fun t k ↦ ω.2 t (perm k), by fun_prop⟩)

/-- `P_σ Q`, the image of `Q` by the relabelling of the arms [INC-P001, Lemma `lem:g-act`]. -/
noncomputable def relabel (perm : Equiv.Perm α) (Q : Measure (Omega α)) : Measure (Omega α) :=
  Q.map (permuteMap α perm)

/-! ### Planned statements (drafts) -/

variable {α} [Nontrivial α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The box `[-M, M]^α`. -/
def box (M : ℝ) : Set (α → ℝ) := Set.univ.pi fun _ ↦ Set.Icc (-M) M

/-- Draft of `thm:main`. -/
theorem tendsto_minimaxRegret {C : Set (Measure ℝ)} {σbar : ℝ} (hC : IsRegular C σbar) :
    (∀ c < ENNReal.ofReal σbar * value α, ∀ᶠ T : ℕ in atTop,
      c * ENNReal.ofReal √T ≤ minimaxRegret (productClass fun _ : α ↦ C) T) ∧
    (∀ c > ENNReal.ofReal σbar * value α, ∀ᶠ T : ℕ in atTop,
      minimaxRegret (productClass fun _ : α ↦ C) T ≤ c * ENNReal.ofReal √T) := by
  sorry

/-- Draft of `thm:main`(i). -/
theorem lower_bound {C : Set (Measure ℝ)} {σbar : ℝ} (hσ : 0 < σbar) (hC : RegularR2 C σbar) :
    ∀ c < ENNReal.ofReal σbar * value α, ∀ᶠ T : ℕ in atTop,
      c * ENNReal.ofReal √T ≤ minimaxRegret (productClass fun _ : α ↦ C) T := by
  sorry

/-- Draft of `thm:main`(ii), the bound on `R⋆`. -/
theorem upper_bound {C : Set (Measure ℝ)} {σbar : ℝ} (hC : RegularR1 C σbar) :
    ∀ c > ENNReal.ofReal σbar * value α, ∀ᶠ T : ℕ in atTop,
      minimaxRegret (productClass fun _ : α ↦ C) T ≤ c * ENNReal.ofReal √T := by
  sorry

/-- Draft of `cor:examples`, Bernoulli laws of mean at most `1/2`. -/
theorem examples_bernoulli_half :
    let C := Set.range fun p : {p : I // (p : ℝ) ≤ 1 / 2} ↦ bernoulliMeasure (1 : ℝ) 0 p.1
    (∀ c < ENNReal.ofReal (1 / 2) * value α, ∀ᶠ T : ℕ in atTop,
      c * ENNReal.ofReal √T ≤ minimaxRegret (productClass fun _ : α ↦ C) T) ∧
    (∀ c > ENNReal.ofReal (1 / 2) * value α, ∀ᶠ T : ℕ in atTop,
      minimaxRegret (productClass fun _ : α ↦ C) T ≤ c * ENNReal.ofReal √T) := by
  sorry

/-- Draft of `cor:examples`, the non-asymptotic Gaussian bound. -/
theorem examples_gaussian_box {a b σbar : ℝ} (hab : a < b) (hσ : 0 < σbar) (M : ℝ) (T : ℕ)
    (hT : (2 * σbar * M / (b - a)) ^ 2 ≤ T) :
    ENNReal.ofReal (σbar * √T) * valueOn α (box M) ≤
      minimaxRegret (productClass fun _ : α ↦
        {ν | ∃ μ ∈ Set.Icc a b, ∃ v : ℝ≥0, (v : ℝ) ≤ σbar ^ 2 ∧ ν = gaussianReal μ v}) T := by
  sorry

/-- Draft of `prop:four`(a). -/
theorem four_minimax :
    value α = ⨆ (prior : Measure (α → ℝ)) (_ : IsProbabilityMeasure prior)
      (_ : ∃ s : Finset (α → ℝ), prior (↑s)ᶜ = 0), bayesValue α prior := by
  sorry

/-- Draft of `prop:four`(b), without the batched value. -/
theorem four_local :
    value α = localValue α ∧
      Tendsto (fun M : ℝ ↦ valueOn α (box M)) atTop (nhds (value α)) := by
  sorry

/-- Draft of `prop:four`(c), translations. -/
theorem four_translate {H : Set (α → ℝ)} (hH : IsCompact H) (c : ℝ) :
    valueOn α ((fun h ↦ h + fun _ ↦ c) '' H) = valueOn α H := by
  sorry

/-- Draft of `prop:four`(c), an invariant minimax policy. -/
theorem four_invariant :
    ∃ Q, IsLimitPolicy α Q ∧ ⨆ h, risk α Q h = value α ∧
      (∀ perm : Equiv.Perm α, relabel α perm Q = Q) ∧ ∀ c : ℝ, translate α c Q = Q := by
  sorry

/-- Draft of `prop:four`(c), monotonicity in `K`. -/
theorem four_mono : value α ≤ value (Option α) := by
  sorry

/-- Draft of `thm:bounds`. -/
theorem bounds :
    ENNReal.ofReal (kappa * lambdaK (Fintype.card α) * √(Fintype.card α - 1)) ≤ value α ∧
      value α ≤ ENNReal.ofReal (2 * √2 * √(Fintype.card α)) := by
  sorry

omit [DecidableEq α] in
/-- Draft of `thm:bounds`, the Gaussian non-asymptotic bound. -/
theorem bounds_gaussian (T : ℕ) (hT : 2 * uStar * (Fintype.card α - 1) ≤ T) :
    ENNReal.ofReal (kappa * lambdaK (Fintype.card α) * √((Fintype.card α - 1) * T)) ≤
      minimaxRegret (productClass fun _ : α ↦
        {ν | ∃ μ ∈ Set.Icc (0 : ℝ) 1, ν = gaussianReal μ 1}) T := by
  sorry

/-- Draft of `cor:four-c`. -/
theorem local_gaussian {M : ℝ} (hM : 0 < M) :
    (∀ c < valueOn α (box M), ∀ᶠ T : ℕ in atTop,
      c * ENNReal.ofReal √T ≤ minimaxRegret (productClass fun _ : α ↦
        {ν | ∃ m ∈ Set.Icc (-M / √T) (M / √T), ν = gaussianReal m 1}) T) ∧
    (∀ c > valueOn α (box M), ∀ᶠ T : ℕ in atTop,
      minimaxRegret (productClass fun _ : α ↦
        {ν | ∃ m ∈ Set.Icc (-M / √T) (M / √T), ν = gaussianReal m 1}) T ≤
          c * ENNReal.ofReal √T) := by
  sorry

end Incognita.Exploration.P001
