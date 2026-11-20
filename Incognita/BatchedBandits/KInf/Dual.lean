/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.KInf.Shift
public import Incognita.BatchedBandits.LogInequalities

/-! # The primal and dual formulas of `𝒦_inf`

[INC-P000, Lemma `lem:primal`], both directions: for a law `P` on `[0, 1]` and a level
`μ ∈ [0, 1)`, the primal `𝒦_inf(P, μ) = dInf unitLaws P μ` equals
`sup_{λ ∈ [0, 1/(1-μ))} E_P[log (1 - λ (X - μ))]` ([HT10, Theorem 8], the paper's cited node
`cite:honda2010asymptotically-primal`). With `φ(λ) = E_P[log (1 - λ (X - μ))]`,
`g_λ(x) = 1 / (1 - λ (x - μ))` and `D_λ = E_P[(X - μ) g_λ(X)]`:

* `dInf_unitLaws_eq_iSup_dual`: the equality of the primal and dual formulas.
* `exists_dInf_sub_lt_dual`: the direction "primal ≤ dual", every `ε > 0` has some
  `λ ∈ [0, 1/(1-μ))` with `φ(λ) > 𝒦_inf(P, μ) - ε` (an `ε`-optimal `λ` of the dual formula, the
  form used by the deviation events `ℒ` and `KC`).
* `ofReal_dual_le_dInf`: the direction "dual ≤ primal", `φ(λ) ≤ 𝒦_inf(P, μ)` for every
  `λ ∈ [0, 1/(1-μ))` (the variational formula of the relative entropy, TauCeti's
  `ofReal_integral_sub_integral_indicator_exp_sub_one_le_klDiv`, with the function
  `log (1 - λ (x - μ))` on `[0, 1]`).
* `exists_unitLaws_integral_id_eq_klDiv_le`: for `λ ∈ [0, 1/(1-μ))` with `D_λ ≤ 0`, the law
  `Q = g_λ P + (-λ D_λ) δ_1` on `[0, 1]` has mean `μ + D_λ (1 - λ(1 - μ))` and
  `KL(P ‖ Q) ≤ φ(λ)` (since `dP/dQ ≤ 1/g_λ`).
* `dual_variation`: `-h D_λ - 2(h/c₀)² ≤ φ(λ + h) - φ(λ) ≤ -h D_λ` for `|h| ≤ c₀/2`,
  `c₀ = 1 - λ(1 - μ)` (from `u - 2u² ≤ log (1 + u) ≤ u`, `sub_two_mul_sq_le_log_one_add` of
  `LogInequalities`).
* `exists_isMaxOn_dual`: a maximiser of `φ` on `[0, b]` has `D_λ ≤ 0`, and `D_λ = 0` inside.
* `one_sub_mul_sub_bounds`, `abs_log_one_sub_mul_sub_le`, `integrable_log_one_sub_mul_sub`,
  `integrable_sub_div_one_sub_mul_sub`: the bounds `c₀ ≤ 1 - λ(x - μ) ≤ 1 + λμ` on `[0, 1]` and
  the integrability of the integrands of `φ` and `D_λ`.

The proof of "primal ≤ dual" follows the construction of the minimiser in the proof of
[HT10, Theorem 8], the law `g_λ P` (with an atom at `1` when the maximum is at the boundary), with
the first-order conditions obtained from the elementary bounds of `dual_variation` instead of
derivatives, and the mean raised above `μ` by a small mixture with `δ_1`
(`Incognita.klDiv_smul_add_smul_le_add`). The traces of the deviation events at the primal level
are in `Incognita.BatchedBandits.HY.Events.XOne`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory LMLExplore LMLExplore.Bandits
open Learning
open scoped ENNReal NNReal

namespace Incognita.BatchedBandits

variable {P : Measure ℝ}

/-- The denominator of the dual formula on `[0, 1]`: for `λ ≥ 0` and `x ∈ [0, 1]`,
`1 - λ(1 - μ) ≤ 1 - λ(x - μ) ≤ 1 + λμ`. -/
lemma one_sub_mul_sub_bounds {lam μ x : ℝ} (hl0 : 0 ≤ lam) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    1 - lam * (1 - μ) ≤ 1 - lam * (x - μ) ∧ 1 - lam * (x - μ) ≤ 1 + lam * μ := by
  constructor <;> nlinarith [hx.1, hx.2]

/-- The integrand of the dual formula is bounded on `[0, 1]`: for `λ ≥ 0`, `x ∈ [0, 1]` and
`0 < c ≤ 1 - λ(x - μ)`, `|log (1 - λ(x - μ))| ≤ max(-log c, log (1 + λμ))`. -/
lemma abs_log_one_sub_mul_sub_le {lam μ x c : ℝ} (hl0 : 0 ≤ lam) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hc : 0 < c) (hcx : c ≤ 1 - lam * (x - μ)) :
    |Real.log (1 - lam * (x - μ))| ≤ max (-Real.log c) (Real.log (1 + lam * μ)) := by
  rw [abs_le]
  constructor
  · have := Real.log_le_log hc hcx
    linarith [le_max_left (-Real.log c) (Real.log (1 + lam * μ))]
  · exact (Real.log_le_log (hc.trans_le hcx) (one_sub_mul_sub_bounds hl0 hx).2).trans
      (le_max_right _ _)

/-- The integrand `log (1 - λ (x - μ))` of the dual formula is integrable for a law on `[0, 1]`,
`λ ≥ 0` and `λ(1 - μ) < 1`. -/
lemma integrable_log_one_sub_mul_sub (hP : P ∈ unitLaws) {lam μ : ℝ} (hl0 : 0 ≤ lam)
    (hl1 : lam * (1 - μ) < 1) : Integrable (fun x ↦ Real.log (1 - lam * (x - μ))) P :=
  integrable_of_abs_le_of_mem_unitLaws hP (by fun_prop) _ fun _ hx ↦
    abs_log_one_sub_mul_sub_le hl0 hx (by linarith) (one_sub_mul_sub_bounds hl0 hx).1

/-- The integrand `(x - μ) / (1 - λ (x - μ))` of `D_λ` is integrable for a law on `[0, 1]`,
`λ ≥ 0` and `λ(1 - μ) < 1` (every level `μ`). -/
lemma integrable_sub_div_one_sub_mul_sub (hP : P ∈ unitLaws) {lam μ : ℝ} (hl0 : 0 ≤ lam)
    (hl1 : lam * (1 - μ) < 1) : Integrable (fun x ↦ (x - μ) / (1 - lam * (x - μ))) P := by
  have hc₀0 : 0 < 1 - lam * (1 - μ) := by linarith
  refine integrable_of_abs_le_of_mem_unitLaws hP (by fun_prop)
    ((1 + |μ|) / (1 - lam * (1 - μ))) fun x hx ↦ ?_
  have h1 := (one_sub_mul_sub_bounds (μ := μ) hl0 hx).1
  rw [abs_div, abs_of_pos (hc₀0.trans_le h1)]
  have : |x - μ| ≤ 1 + |μ| :=
    (abs_sub _ _).trans (by rw [abs_of_nonneg hx.1]; linarith [hx.2])
  exact div_le_div₀ (by positivity) this hc₀0 h1

/-- [INC-P000, proof of Lemma `lem:primal`, the competitor] (the minimiser of the proof of
[HT10, Theorem 8]) For a law `P` on `[0, 1]`, a level `μ` (the paper's `μ ∈ [0, 1)` is not
needed) and `λ ≥ 0` with `λ(1 - μ) < 1` and `D_λ = E_P[(X - μ)/(1 - λ (X - μ))] ≤ 0`, there is
a law `Q` on `[0, 1]` with mean `μ + D_λ (1 - λ(1 - μ))` and
`KL(P ‖ Q) ≤ E_P[log (1 - λ (X - μ))]`: the law `Q = g_λ P + (-λ D_λ) δ_1`,
`g_λ(x) = 1/(1 - λ(x - μ))` (a probability since `E_P[g_λ] = 1 + λ D_λ`), for which
`dP/dQ ≤ 1/g_λ`. -/
lemma exists_unitLaws_integral_id_eq_klDiv_le (hP : P ∈ unitLaws) {μ lam : ℝ} (hl0 : 0 ≤ lam)
    (hl1 : lam * (1 - μ) < 1)
    (hD : ∫ x, (x - μ) / (1 - lam * (x - μ)) ∂P ≤ 0) :
    ∃ Q ∈ unitLaws, Q[id] = μ + (∫ x, (x - μ) / (1 - lam * (x - μ)) ∂P) * (1 - lam * (1 - μ)) ∧
      klDiv P Q ≤ ENNReal.ofReal (∫ x, Real.log (1 - lam * (x - μ)) ∂P) := by
  have := hP.1
  set D := ∫ x, (x - μ) / (1 - lam * (x - μ)) ∂P with hDdef
  set c₀ := 1 - lam * (1 - μ) with hc₀
  have hc₀0 : 0 < c₀ := by linarith
  -- the denominator on `[0, 1]`
  have hden : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      c₀ ≤ 1 - lam * (x - μ) ∧ 1 - lam * (x - μ) ≤ 1 + lam * μ := fun _ hx ↦
    one_sub_mul_sub_bounds hl0 hx
  set g : ℝ → ℝ := fun x ↦ 1 / (1 - lam * (x - μ)) with hg
  have hgm : Measurable g := by
    simp only [hg]
    fun_prop
  have hg0 : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < g x := fun x hx ↦
    one_div_pos.mpr (hc₀0.trans_le (hden x hx).1)
  have hgle : ∀ x ∈ Set.Icc (0 : ℝ) 1, g x ≤ 1 / c₀ := fun x hx ↦
    one_div_le_one_div_of_le hc₀0 (hden x hx).1
  -- integrability of the bounded functions
  have hgi : Integrable g P := integrable_of_abs_le_of_mem_unitLaws hP hgm (1 / c₀) fun x hx ↦ by
    rw [abs_of_pos (hg0 x hx)]; exact hgle x hx
  have hDi : Integrable (fun x ↦ (x - μ) / (1 - lam * (x - μ))) P :=
    integrable_sub_div_one_sub_mul_sub hP hl0 hl1
  -- `E_P[g] = 1 + λ D`
  have hgid : ∀ x ∈ Set.Icc (0 : ℝ) 1, g x = 1 + lam * ((x - μ) / (1 - lam * (x - μ))) := by
    intro x hx
    have hpos := hc₀0.trans_le (hden x hx).1
    simp only [hg]
    field_simp
    ring
  have hEg : ∫ x, g x ∂P = 1 + lam * D := by
    rw [integral_congr_ae (hP.2.mono fun x hx ↦ hgid x hx), integral_add (integrable_const _)
      (hDi.const_mul lam), integral_const, integral_const_mul, probReal_univ, smul_eq_mul, mul_one]
  have hEg0 : 0 < 1 + lam * D := by
    rw [← hEg]
    refine integral_pos_iff_support_of_nonneg_ae (hP.2.mono fun x hx ↦ (hg0 x hx).le) hgi |>.mpr ?_
    have : P (Function.support g) = 1 := by
      refine (prob_compl_eq_zero_iff ?_).mp ?_
      · exact measurableSet_support hgm
      · refine measure_mono_null (fun x hx ↦ ?_) (ae_iff.mp hP.2)
        simp only [Set.mem_compl_iff, Function.mem_support, not_not] at hx
        intro hx'
        exact (hg0 x hx').ne' hx
    rw [this]
    exact zero_lt_one
  -- the measure `Q = g P + w δ_1`
  set fN : ℝ → ℝ≥0 := fun x ↦ (g x).toNNReal with hfN
  have hfNm : Measurable fN := hgm.real_toNNReal
  set R := P.withDensity (fun x ↦ (fN x : ℝ≥0∞)) with hR
  set w := -(lam * D) with hw
  have hw0 : 0 ≤ w := by
    have := mul_nonpos_of_nonneg_of_nonpos hl0 hD
    rw [hw]
    linarith
  set Q := R + ENNReal.ofReal w • Measure.dirac (1 : ℝ) with hQ
  have hRuniv : R Set.univ = ENNReal.ofReal (1 + lam * D) := by
    rw [hR, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, ← hEg,
      ofReal_integral_eq_lintegral_ofReal hgi (hP.2.mono fun x hx ↦ (hg0 x hx).le)]
    -- `ENNReal.ofReal r` is `↑r.toNNReal` by definition, and `fN x = (g x).toNNReal`
    simp only [hfN, ENNReal.ofReal]
  have hQuniv : Q Set.univ = 1 := by
    rw [hQ, add_apply, smul_apply, hRuniv, measure_univ, smul_eq_mul, mul_one,
      ← ENNReal.ofReal_add hEg0.le hw0, hw]
    simp
  have hQprob : IsProbabilityMeasure Q := ⟨hQuniv⟩
  have hRfin : IsFiniteMeasure R := ⟨by rw [hRuniv]; exact ENNReal.ofReal_lt_top⟩
  have hQunit : Q ∈ unitLaws := by
    refine ⟨hQprob, ?_⟩
    rw [hQ, ae_add_measure_iff]
    exact ⟨(withDensity_absolutelyContinuous P _).ae_le hP.2, Measure.ae_smul_measure
      ((ae_dirac_iff measurableSet_Icc).2 ⟨zero_le_one, le_rfl⟩) _⟩
  refine ⟨Q, hQunit, ?_, ?_⟩
  · -- the mean
    have hRi : Integrable id R := by
      refine Integrable.of_bound measurable_id.aestronglyMeasurable 1
        ((withDensity_absolutelyContinuous P _).ae_le (hP.2.mono fun x hx ↦ ?_))
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨show -1 ≤ x by linarith [hx.1], hx.2⟩
    have hdi : Integrable id (ENNReal.ofReal w • Measure.dirac (1 : ℝ)) :=
      (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
    rw [hQ, integral_add_measure hRi hdi, integral_smul_measure, integral_dirac,
      ENNReal.toReal_ofReal hw0, hR, integral_withDensity_eq_integral_smul hfNm]
    have hpt : ∀ᵐ x ∂P, fN x • id x = (x - μ) / (1 - lam * (x - μ)) + μ * g x := by
      filter_upwards [hP.2] with x hx
      rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (hg0 x hx).le]
      simp only [hg, id]
      ring
    rw [integral_congr_ae hpt, integral_add hDi (hgi.const_mul μ), integral_const_mul, hEg]
    simp only [smul_eq_mul, id, mul_one, hw, hc₀, ← hDdef]
    ring
  · -- the relative entropy
    have hfN0 : ∀ᵐ x ∂P, fN x ≠ 0 := by
      filter_upwards [hP.2] with x hx
      simp only [hfN, ne_eq, Real.toNNReal_eq_zero, not_le]
      exact hg0 x hx
    have hRQ : R ≤ Q := Measure.le_add_right le_rfl
    have hPQ : P ≪ Q := (withDensity_absolutelyContinuous' hfNm.coe_nnreal_ennreal.aemeasurable
      (hfN0.mono fun x hx ↦ ENNReal.coe_ne_zero.mpr hx)).trans
      (Measure.absolutelyContinuous_of_le hRQ)
    -- `dP/dQ ≤ 1 / g`, so `llr P Q ≤ -log g = log (1 - λ (x - μ))`
    have hllr : ∀ᵐ x ∂P, llr P Q x ≤ Real.log (1 - lam * (x - μ)) := by
      filter_upwards [ae_llr_le_neg_log_of_withDensity_le hfNm hfN0 hRQ, hP.2] with x hx hxI
      rw [hfN, Real.coe_toNNReal _ (hg0 x hxI).le, hg] at hx
      simpa only [one_div, Real.log_inv, neg_neg] using hx
    have hlogi : Integrable (fun x ↦ Real.log (1 - lam * (x - μ))) P :=
      integrable_log_one_sub_mul_sub hP hl0 hl1
    have hintQ : Integrable (llr P Q) P := TauCeti.integrable_llr_of_ae_le hPQ hlogi hllr
    rw [klDiv_of_ac_of_integrable hPQ hintQ]
    simp only [probReal_univ, add_sub_cancel_right]
    exact ENNReal.ofReal_le_ofReal (integral_mono_ae hintQ hlogi hllr)

/-- [INC-P000, proof of Lemma `lem:primal`, the variation of the dual function] For a law `P` on
`[0, 1]`, `μ ∈ [0, 1)`, `λ ≥ 0` with `c₀ = 1 - λ(1 - μ) > 0`, and `h` with `λ + h ≥ 0` and
`|h| ≤ c₀/2`, the dual function `φ(λ) = E_P[log (1 - λ (X - μ))]` satisfies
`-h D_λ - 2 (h/c₀)² ≤ φ(λ + h) - φ(λ) ≤ -h D_λ`, `D_λ = E_P[(X - μ)/(1 - λ(X - μ))]`. -/
lemma dual_variation (hP : P ∈ unitLaws) {μ lam h : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ < 1)
    (hl0 : 0 ≤ lam) (hl1 : lam * (1 - μ) < 1) (hh : |h| ≤ (1 - lam * (1 - μ)) / 2) :
    -h * (∫ x, (x - μ) / (1 - lam * (x - μ)) ∂P) - 2 * (h / (1 - lam * (1 - μ))) ^ 2 ≤
        (∫ x, Real.log (1 - (lam + h) * (x - μ)) ∂P) - ∫ x, Real.log (1 - lam * (x - μ)) ∂P ∧
      (∫ x, Real.log (1 - (lam + h) * (x - μ)) ∂P) - ∫ x, Real.log (1 - lam * (x - μ)) ∂P ≤
        -h * (∫ x, (x - μ) / (1 - lam * (x - μ)) ∂P) := by
  -- With `u = -h (x - μ)/(1 - λ(x - μ))`, `1 - (λ + h)(x - μ) = (1 - λ(x - μ))(1 + u)`,
  -- `|u| ≤ |h|/c₀ ≤ 1/2` and `u - 2u² ≤ log (1 + u) ≤ u`.
  have := hP.1
  set c₀ := 1 - lam * (1 - μ) with hc₀
  have hc₀0 : 0 < c₀ := by linarith
  have hden : ∀ x ∈ Set.Icc (0 : ℝ) 1, c₀ ≤ 1 - lam * (x - μ) ∧
      1 - lam * (x - μ) ≤ 1 + lam * μ := fun _ hx ↦ one_sub_mul_sub_bounds hl0 hx
  set u : ℝ → ℝ := fun x ↦ -h * ((x - μ) / (1 - lam * (x - μ))) with hu
  have hub : ∀ x ∈ Set.Icc (0 : ℝ) 1, |u x| ≤ |h| / c₀ := by
    intro x hx
    have hpos := hc₀0.trans_le (hden x hx).1
    simp only [hu, abs_mul, abs_neg, abs_div, abs_of_pos hpos]
    have hxμ : |x - μ| ≤ 1 := abs_le.mpr ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩
    rw [mul_div_assoc']
    refine div_le_div₀ (abs_nonneg h) (by nlinarith [abs_nonneg h]) hc₀0 (hden x hx).1
  have hhc : |h| / c₀ ≤ 1 / 2 := by
    rw [div_le_iff₀ hc₀0]
    linarith
  have hfac : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      Real.log (1 - (lam + h) * (x - μ)) = Real.log (1 - lam * (x - μ)) + Real.log (1 + u x) := by
    intro x hx
    have hpos := hc₀0.trans_le (hden x hx).1
    have h1u : 0 < 1 + u x := by
      have := (abs_le.mp ((hub x hx).trans hhc)).1
      linarith
    rw [← Real.log_mul hpos.ne' h1u.ne']
    congr 1
    simp only [hu]
    field_simp
    ring
  -- integrability
  have hi0 : Integrable (fun x ↦ Real.log (1 - lam * (x - μ))) P :=
    integrable_log_one_sub_mul_sub hP hl0 hl1
  have hui : Integrable u P := integrable_of_abs_le_of_mem_unitLaws hP (by simp only [hu]; fun_prop)
    _ hub
  have hu2i : Integrable (fun x ↦ u x - 2 * u x ^ 2) P :=
    integrable_of_abs_le_of_mem_unitLaws hP (by simp only [hu]; fun_prop) 1
      fun x hx ↦ by
        obtain ⟨ha, hb⟩ := abs_le.mp ((hub x hx).trans hhc)
        rw [abs_le]
        constructor <;> nlinarith
  have hsqb : ∀ x ∈ Set.Icc (0 : ℝ) 1, u x ^ 2 ≤ (h / c₀) ^ 2 := by
    intro x hx
    calc u x ^ 2 = |u x| ^ 2 := (sq_abs _).symm
      _ ≤ (|h| / c₀) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hub x hx) 2
      _ = (h / c₀) ^ 2 := by rw [div_pow, sq_abs, div_pow]
  have hsqi : Integrable (fun x ↦ u x ^ 2) P :=
    integrable_of_abs_le_of_mem_unitLaws hP (by simp only [hu]; fun_prop) ((h / c₀) ^ 2)
      fun x hx ↦ by rw [abs_of_nonneg (sq_nonneg _)]; exact hsqb x hx
  have hl1i : Integrable (fun x ↦ Real.log (1 + u x)) P := by
    refine integrable_of_abs_le_of_mem_unitLaws hP (by simp only [hu]; fun_prop)
      (max (-Real.log (1 / 2)) (Real.log (3 / 2))) fun x hx ↦ ?_
    have h1 := abs_le.mp ((hub x hx).trans hhc)
    rw [abs_le]
    constructor
    · have := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) (show 1 / 2 ≤ 1 + u x by linarith)
      linarith [le_max_left (-Real.log (1 / 2)) (Real.log (3 / 2))]
    · exact (Real.log_le_log (by linarith) (show 1 + u x ≤ 3 / 2 by linarith)).trans
        (le_max_right _ _)
  have hdiff : (∫ x, Real.log (1 - (lam + h) * (x - μ)) ∂P) - ∫ x, Real.log (1 - lam * (x - μ)) ∂P
      = ∫ x, Real.log (1 + u x) ∂P := by
    rw [integral_congr_ae (hP.2.mono fun x hx ↦ hfac x hx), integral_add hi0 hl1i]
    ring
  have hint_u : ∫ x, u x ∂P = -h * ∫ x, (x - μ) / (1 - lam * (x - μ)) ∂P := by
    simp only [hu]
    rw [integral_const_mul]
  rw [hdiff, ← hint_u]
  constructor
  · -- the lower bound
    have hmono : ∫ x, (u x - 2 * u x ^ 2) ∂P ≤ ∫ x, Real.log (1 + u x) ∂P :=
      integral_mono_ae hu2i hl1i (hP.2.mono fun x hx ↦ sub_two_mul_sq_le_log_one_add
        (by have := (abs_le.mp ((hub x hx).trans hhc)).1; linarith))
    have hsq : ∫ x, u x ^ 2 ∂P ≤ (h / c₀) ^ 2 := by
      calc ∫ x, u x ^ 2 ∂P ≤ ∫ _x, (h / c₀) ^ 2 ∂P := integral_mono_ae hsqi
            (integrable_const _) (hP.2.mono fun x hx ↦ hsqb x hx)
        _ = (h / c₀) ^ 2 := by simp
    have hsplit : ∫ x, (u x - 2 * u x ^ 2) ∂P = ∫ x, u x ∂P - 2 * ∫ x, u x ^ 2 ∂P := by
      rw [integral_sub hui (hsqi.const_mul 2), integral_const_mul (2 : ℝ) (fun x ↦ u x ^ 2)]
    linarith
  · -- the upper bound
    exact integral_mono_ae hl1i hui (hP.2.mono fun x hx ↦ by
      have h1u : 0 < 1 + u x := by
        have := (abs_le.mp ((hub x hx).trans hhc)).1
        linarith
      have := Real.log_le_sub_one_of_pos h1u
      linarith)

/-- [INC-P000, proof of Lemma `lem:primal`, the maximiser] For a law `P` on `[0, 1]` with mean
`≤ μ`, `μ ∈ [0, 1)` and `b ≥ 0` with `b(1 - μ) < 1`, the dual function `φ` has a maximiser `λ` on
`[0, b]`, with `D_λ ≤ 0`, and `D_λ = 0` if `λ < b` (first-order conditions, from
`dual_variation`; at `λ = 0`, `D_0 = m(P) - μ ≤ 0`). -/
lemma exists_isMaxOn_dual (hP : P ∈ unitLaws) {μ b : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ < 1) (hb0 : 0 ≤ b)
    (hb1 : b * (1 - μ) < 1) (hmean : P[id] ≤ μ) :
    ∃ lam ∈ Set.Icc 0 b, (∀ l ∈ Set.Icc 0 b, ∫ x, Real.log (1 - l * (x - μ)) ∂P ≤
        ∫ x, Real.log (1 - lam * (x - μ)) ∂P) ∧
      ∫ x, (x - μ) / (1 - lam * (x - μ)) ∂P ≤ 0 ∧
      (lam < b → ∫ x, (x - μ) / (1 - lam * (x - μ)) ∂P = 0) := by
  have := hP.1
  set cb := 1 - b * (1 - μ) with hcb
  have hcb0 : 0 < cb := by linarith
  have hden : ∀ l ∈ Set.Icc 0 b, ∀ x ∈ Set.Icc (0 : ℝ) 1, cb ≤ 1 - l * (x - μ) ∧
      1 - l * (x - μ) ≤ 1 + b * μ := by
    intro l hl x hx
    constructor <;> nlinarith [hl.1, hl.2, hx.1, hx.2]
  -- continuity of `φ` on `[0, b]`
  have hcont : ContinuousOn (fun l ↦ ∫ x, Real.log (1 - l * (x - μ)) ∂P) (Set.Icc 0 b) := by
    refine continuousOn_of_dominated (bound := fun _ ↦ max (-Real.log cb) (Real.log (1 + b * μ)))
      (fun l _ ↦ Measurable.aestronglyMeasurable
        (by fun_prop : Measurable fun x : ℝ ↦ Real.log (1 - l * (x - μ))))
      (fun l hl ↦ hP.2.mono fun x hx ↦ ?_) (integrable_const _)
      (hP.2.mono fun x hx ↦ ?_)
    · obtain ⟨h1, h2⟩ := hden l hl x hx
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · have := Real.log_le_log hcb0 h1
        linarith [le_max_left (-Real.log cb) (Real.log (1 + b * μ))]
      · exact (Real.log_le_log (hcb0.trans_le h1) h2).trans (le_max_right _ _)
    · refine ContinuousOn.log (by fun_prop) fun l hl ↦ ?_
      exact (hcb0.trans_le (hden l hl x hx).1).ne'
  obtain ⟨lam, hlam, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr hb0) hcont
  refine ⟨lam, hlam, fun l hl ↦ hmax hl, ?_⟩
  set D := ∫ x, (x - μ) / (1 - lam * (x - μ)) ∂P with hD
  set c₀ := 1 - lam * (1 - μ) with hc₀
  have hl1 : lam * (1 - μ) < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right hlam.2
    (by linarith)) hb1
  have hc₀0 : 0 < c₀ := by linarith
  have hφ : ∀ h, lam + h ∈ Set.Icc 0 b →
      (∫ x, Real.log (1 - (lam + h) * (x - μ)) ∂P) ≤ ∫ x, Real.log (1 - lam * (x - μ)) ∂P :=
    fun h hh ↦ hmax hh
  -- `D ≤ 0`
  have hDle : D ≤ 0 := by
    rcases hlam.1.lt_or_eq with hpos | h0
    · by_contra hDpos
      have hDpos := not_le.mp hDpos
      set m := min lam (min (c₀ / 2) (D * c₀ ^ 2 / 4)) with hm
      have hm0 : 0 < m := lt_min hpos (lt_min (by positivity) (by positivity))
      have hmc : m ≤ c₀ / 2 := (min_le_right _ _).trans (min_le_left _ _)
      have hmD : m ≤ D * c₀ ^ 2 / 4 := (min_le_right _ _).trans (min_le_right _ _)
      obtain ⟨hlow, -⟩ := dual_variation hP hμ0 hμ1 hlam.1 hl1 (h := -m)
        (by rw [abs_neg, abs_of_pos hm0]; exact hmc)
      have hmem : lam + -m ∈ Set.Icc 0 b :=
        ⟨by linarith [min_le_left lam (min (c₀ / 2) (D * c₀ ^ 2 / 4))], by linarith [hlam.2]⟩
      have hle := hφ (-m) hmem
      have hsq : 2 * (-m / c₀) ^ 2 ≤ m * D / 2 := by
        rw [div_pow, neg_sq, mul_div_assoc']
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        have := mul_le_mul_of_nonneg_left hmD hm0.le
        nlinarith
      nlinarith
    · -- at `λ = 0`, `D_0 = m(P) - μ`
      rw [hD, ← h0]
      simp only [zero_mul, sub_zero, div_one]
      have hid : Integrable (fun x : ℝ ↦ x) P := integrable_id_of_mem_unitLaws hP
      rw [integral_sub hid (integrable_const _), integral_const, probReal_univ, one_smul]
      have : ∫ x, x ∂P = P[id] := rfl
      linarith
  refine ⟨hDle, fun hlb ↦ le_antisymm hDle ?_⟩
  -- `λ < b`: `D ≥ 0`
  by_contra hneg
  have hneg := not_le.mp hneg
  set m := min (b - lam) (min (c₀ / 2) (-D * c₀ ^ 2 / 4)) with hm
  have hnegD : 0 < -D := neg_pos.mpr hneg
  have hpos3 : 0 < -D * c₀ ^ 2 / 4 := by positivity
  have hm0 : 0 < m := lt_min (by linarith) (lt_min (by positivity) hpos3)
  have hmc : m ≤ c₀ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hmD : m ≤ -D * c₀ ^ 2 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨hlow, -⟩ := dual_variation hP hμ0 hμ1 hlam.1 hl1 (h := m)
    (by rw [abs_of_pos hm0]; exact hmc)
  have hmem : lam + m ∈ Set.Icc 0 b :=
    ⟨by linarith [hlam.1], by linarith [min_le_left (b - lam) (min (c₀ / 2) (-D * c₀ ^ 2 / 4))]⟩
  have hle := hφ m hmem
  have hsq : 2 * (m / c₀) ^ 2 ≤ m * (-D) / 2 := by
    rw [div_pow, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    have := mul_le_mul_of_nonneg_left hmD hm0.le
    nlinarith
  nlinarith

/-- [INC-P000, Lemma `lem:primal`, the direction "primal ≤ dual"] (one direction of
[HT10, Theorem 8], the paper's cited node `cite:honda2010asymptotically-primal`) For a law `P` on
`[0, 1]` and `μ ∈ [0, 1)`, every `ε > 0` has some `λ ∈ [0, 1/(1-μ))` with
`E_P[log (1 - λ (X - μ))] > 𝒦_inf(P, μ) - ε`: the primal `𝒦_inf` of the frozen statements is at
most the dual supremum. The other direction is `ofReal_dual_le_dInf`. -/
theorem exists_dInf_sub_lt_dual (hP : P ∈ unitLaws) {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ < 1) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ lam, 0 ≤ lam ∧ lam * (1 - μ) < 1 ∧
      (dInf unitLaws P μ).toReal - ε < ∫ x, Real.log (1 - lam * (x - μ)) ∂P := by
  -- For `m(P) > μ`, `𝒦_inf = 0` and `λ = 0`. Otherwise, take the maximiser `λ` of the dual
  -- function on `[0, b]`, `1 - b(1 - μ) = s` small (`exists_isMaxOn_dual`), the law `Q` of
  -- `exists_unitLaws_integral_id_eq_klDiv_le` (mean `≥ μ - s`, `KL(P ‖ Q) ≤ φ(λ)`) and its mixture
  -- with `δ_1` of weight `2s/(1 - μ)`, whose mean is `> μ` (`klDiv_smul_add_smul_le_add`).
  have := hP.1
  have h1μ : 0 < 1 - μ := by linarith
  have hφ0 : ∫ x, Real.log (1 - 0 * (x - μ)) ∂P = 0 := by simp
  by_cases hm : μ < P[id]
  · refine ⟨0, le_rfl, by linarith, ?_⟩
    rw [dInf_unitLaws_eq_zero_of_lt_integral hP hm, hφ0, ENNReal.toReal_zero]
    linarith
  have hm := not_lt.mp hm
  -- the level `s` and the bound `b`
  set s := min ((1 - μ) / 4) (ε * (1 - μ) / 8) with hs
  have hs0 : 0 < s := lt_min (by positivity) (by positivity)
  have hs4 : s ≤ (1 - μ) / 4 := min_le_left _ _
  have hsε : s ≤ ε * (1 - μ) / 8 := min_le_right _ _
  set b := (1 - s) / (1 - μ) with hb
  have hbs : b * (1 - μ) = 1 - s := by rw [hb, div_mul_cancel₀ _ h1μ.ne']
  have hb0 : 0 ≤ b := div_nonneg (by linarith) h1μ.le
  have hb1 : b * (1 - μ) < 1 := by rw [hbs]; linarith
  obtain ⟨lam, hlam, hmax, hDle, hDeq⟩ := exists_isMaxOn_dual hP hμ0 hμ1 hb0 hb1 hm
  have hl1 : lam * (1 - μ) < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right hlam.2 h1μ.le) hb1
  set D := ∫ x, (x - μ) / (1 - lam * (x - μ)) ∂P with hD
  set φ := ∫ x, Real.log (1 - lam * (x - μ)) ∂P with hφ
  have hφpos : 0 ≤ φ := by
    have := hmax 0 ⟨le_rfl, hb0⟩
    rw [hφ0] at this
    exact this
  obtain ⟨Q, hQ, hQmean, hQkl⟩ :=
    exists_unitLaws_integral_id_eq_klDiv_le hP hlam.1 hl1 hDle
  have := hQ.1
  -- `μ - s ≤ m(Q) ≤ μ`
  have hDge : -μ ≤ D := by
    have hi : Integrable (fun x ↦ (x - μ) / (1 - lam * (x - μ))) P :=
      integrable_sub_div_one_sub_mul_sub hP hlam.1 hl1
    calc -μ = ∫ _x, -μ ∂P := by simp
      _ ≤ D := integral_mono_ae (integrable_const _) hi (hP.2.mono fun x hx ↦ by
          by_cases hxμ : x < μ
          · have hpos : 1 ≤ 1 - lam * (x - μ) := by nlinarith [hlam.1]
            rw [le_div_iff₀ (by linarith)]
            nlinarith [hx.1]
          · exact (neg_nonpos.mpr hμ0).trans (div_nonneg (by linarith) (by nlinarith [hx.2])))
  have hmQ : μ - s ≤ Q[id] ∧ Q[id] ≤ μ := by
    rw [hQmean, ← hD]
    have hc : 0 < 1 - lam * (1 - μ) := by linarith
    constructor
    · rcases hlam.2.lt_or_eq with hlt | heq
      · rw [hDeq hlt]
        linarith
      · have hfac : 1 - lam * (1 - μ) = s := by rw [heq, hbs]; ring
        rw [hfac]
        nlinarith
    · nlinarith
  -- the mixture with `δ_1`
  set v := 2 * s / (1 - μ) with hv
  have hv0 : 0 ≤ v := by positivity
  have hv2 : v ≤ 1 / 2 := by
    rw [hv, div_le_iff₀ h1μ]
    linarith
  set vN : ℝ≥0 := ⟨v, hv0⟩ with hvN
  -- the coercion of `vN` to `ℝ`, by definition of `vN`
  have hvr : (vN : ℝ) = v := rfl
  have hvN1 : vN < 1 := by
    rw [← NNReal.coe_lt_coe, NNReal.coe_one, hvr]
    linarith
  have hQ' := smul_add_smul_dirac_one_mem_unitLaws hQ hvN1.le
  have hmean' : μ < ((1 - vN) • Q + vN • Measure.dirac (1 : ℝ))[id] := by
    rw [integral_id_smul_add_smul_dirac_one hQ hvN1.le, hvr]
    have h1 : v * (1 - μ) = 2 * s := by rw [hv, div_mul_cancel₀ _ h1μ.ne']
    nlinarith [hmQ.1, hmQ.2]
  have hkl := klDiv_smul_add_smul_le_add (μ := P) (ν := Q) (Measure.dirac (1 : ℝ)) hvN1
  have hlog : -Real.log ((1 - vN : ℝ≥0) : ℝ) ≤ 2 * v := by
    rw [NNReal.coe_sub hvN1.le, NNReal.coe_one, hvr]
    have hpos : 0 < 1 - v := by linarith
    rw [← Real.log_inv]
    have := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
    have h2 : (1 - v)⁻¹ - 1 ≤ 2 * v := by
      rw [inv_eq_one_div, div_sub_one hpos.ne', div_le_iff₀ hpos]
      nlinarith
    linarith
  have hdInf : dInf unitLaws P μ ≤ ENNReal.ofReal φ + ENNReal.ofReal (2 * v) :=
    calc dInf unitLaws P μ ≤ klDiv P ((1 - vN) • Q + vN • Measure.dirac (1 : ℝ)) :=
          dInf_le hQ' hmean'
      _ ≤ klDiv P Q + ENNReal.ofReal (-Real.log ((1 - vN : ℝ≥0) : ℝ)) := hkl
      _ ≤ ENNReal.ofReal φ + ENNReal.ofReal (2 * v) := by
          gcongr
  have hfin : ENNReal.ofReal φ + ENNReal.ofReal (2 * v) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  have hreal := ENNReal.toReal_mono hfin hdInf
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hφpos, ENNReal.toReal_ofReal (by positivity)] at hreal
  refine ⟨lam, hlam.1, hl1, ?_⟩
  have h2v : 2 * v ≤ ε / 2 := by
    rw [hv, mul_div_assoc', div_le_iff₀ h1μ]
    linarith
  linarith

/-- [INC-P000, Lemma `lem:primal`, the direction "dual ≤ primal"] For a law `P` on `[0, 1]`, every
level `μ` (the paper's `μ ∈ [0, 1)` is not needed) and `λ ≥ 0` with `λ(1 - μ) < 1`,
`E_P[log (1 - λ (X - μ))] ≤ 𝒦_inf(P, μ)`. -/
lemma ofReal_dual_le_dInf (hP : P ∈ unitLaws) {μ lam : ℝ} (hl0 : 0 ≤ lam)
    (hl1 : lam * (1 - μ) < 1) :
    ENNReal.ofReal (∫ x, Real.log (1 - lam * (x - μ)) ∂P) ≤ dInf unitLaws P μ := by
  have := hP.1
  set c₀ := 1 - lam * (1 - μ) with hc₀
  have hc₀0 : 0 < c₀ := by linarith
  have hden : ∀ x ∈ Set.Icc (0 : ℝ) 1, c₀ ≤ 1 - lam * (x - μ) ∧
      1 - lam * (x - μ) ≤ 1 + lam * μ := fun _ hx ↦ one_sub_mul_sub_bounds hl0 hx
  set f : ℝ → ℝ := fun x ↦ Real.log (1 - lam * (x - μ)) with hf
  have hfi : ∀ Q ∈ unitLaws, Integrable f Q := fun _ hQ ↦
    integrable_log_one_sub_mul_sub hQ hl0 hl1
  -- For every law `Q` on `[0, 1]` with mean `> μ`, the variational formula of `KL(P ‖ Q)` with the
  -- function `f = log (1 - λ (x - μ))` on `[0, 1]` gives `KL(P ‖ Q) ≥ E_P[f] - E_Q[e^f - 1]`, and
  -- `E_Q[e^f - 1] = -λ (m(Q) - μ) ≤ 0`.
  refine le_dInf_iff.mpr fun Q hQ hQm ↦ ?_
  have := hQ.1
  set s := Set.Icc (0 : ℝ) 1 with hs
  -- `e^f = 1 - λ (x - μ)` on `[0, 1]`
  have hexp : ∀ x ∈ s, Real.exp (f x) = 1 - lam * (x - μ) := fun x hx ↦
    Real.exp_log (hc₀0.trans_le (hden x hx).1)
  have hind : ∀ᵐ x ∂Q, s.indicator (fun x ↦ Real.exp (f x)) x = 1 - lam * (x - μ) := by
    filter_upwards [hQ.2] with x hx
    rw [Set.indicator_of_mem hx, hexp x hx]
  have hlin : Integrable (fun x ↦ 1 - lam * (x - μ)) Q :=
    integrable_of_abs_le_of_mem_unitLaws hQ (by fun_prop) (1 + lam * μ) fun x hx ↦ by
      obtain ⟨h1, h2⟩ := hden x hx
      rw [abs_of_pos (hc₀0.trans_le h1)]
      exact h2
  have hie : Integrable (s.indicator fun x ↦ Real.exp (f x)) Q :=
    hlin.congr (hind.mono fun x hx ↦ hx.symm)
  have hDV := TauCeti.ofReal_integral_sub_integral_indicator_exp_sub_one_le_klDiv
    (μ := P) (ν := Q) (s := s) hP.2 (hfi P hP) hie
  -- the correction term is `-λ (m(Q) - μ) ≤ 0`
  have hcorr : ∫ x, (s.indicator (fun x ↦ Real.exp (f x)) x - 1) ∂Q = -(lam * (Q[id] - μ)) := by
    rw [integral_congr_ae (hind.mono fun x hx ↦ by rw [hx])]
    have hid : Integrable (fun x : ℝ ↦ x) Q := integrable_id_of_mem_unitLaws hQ
    have : (fun x : ℝ ↦ 1 - lam * (x - μ) - 1) = fun x ↦ -(lam * x) + lam * μ := by
      funext x; ring
    have h1 : Integrable (fun x : ℝ ↦ -(lam * x)) Q := (hid.const_mul lam).neg
    rw [this, integral_add h1 (integrable_const _), integral_neg,
      integral_const_mul, integral_const, probReal_univ, one_smul]
    -- `Q[id]` is `∫ x, id x ∂Q`
    simp only [id]
    ring
  rw [hcorr] at hDV
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hDV
  have : 0 ≤ lam * (Q[id] - μ) := mul_nonneg hl0 (by linarith)
  simp only [hf]
  linarith

/-- [INC-P000, Lemma `lem:primal`] ([HT10, Theorem 8]) For a law `P` on `[0, 1]` and a level
`μ < 1`, the primal `𝒦_inf(P, μ)` equals the dual formula
`sup_{λ ≥ 0, λ(1 - μ) < 1} E_P[log (1 - λ (X - μ))]` (the paper's `μ ≥ 0` is not needed: below
`0`, both sides are `0`). -/
lemma dInf_unitLaws_eq_iSup_dual (hP : P ∈ unitLaws) {μ : ℝ} (hμ1 : μ < 1) :
    dInf unitLaws P μ = ⨆ lam ∈ {lam : ℝ | 0 ≤ lam ∧ lam * (1 - μ) < 1},
      ENNReal.ofReal (∫ x, Real.log (1 - lam * (x - μ)) ∂P) := by
  refine le_antisymm ?_ (iSup₂_le fun lam hlam ↦ ofReal_dual_le_dInf hP hlam.1 hlam.2)
  rcases lt_or_ge μ 0 with hμ0 | hμ0
  · have := hP.1
    rw [dInf_unitLaws_eq_zero_of_lt_integral hP
      (hμ0.trans_le (integral_id_mem_Icc_of_mem_unitLaws hP).1)]
    exact zero_le
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
  obtain ⟨lam, hl0, hl1, hlam⟩ := exists_dInf_sub_lt_dual hP hμ0 hμ1 (ε := ε) (by exact_mod_cast hε)
  calc dInf unitLaws P μ = ENNReal.ofReal (dInf unitLaws P μ).toReal :=
        (ENNReal.ofReal_toReal (dInf_unitLaws_ne_top hP hμ1)).symm
    _ ≤ ENNReal.ofReal ((∫ x, Real.log (1 - lam * (x - μ)) ∂P) + ε) :=
        ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ ENNReal.ofReal (∫ x, Real.log (1 - lam * (x - μ)) ∂P) + ENNReal.ofReal ε :=
        ENNReal.ofReal_add_le
    _ ≤ _ := by
        rw [ENNReal.ofReal_coe_nnreal]
        gcongr
        exact le_iSup₂ (f := fun lam (_ : lam ∈ {lam : ℝ | 0 ≤ lam ∧ lam * (1 - μ) < 1}) ↦
          ENNReal.ofReal (∫ x, Real.log (1 - lam * (x - μ)) ∂P)) lam ⟨hl0, hl1⟩

end Incognita.BatchedBandits
