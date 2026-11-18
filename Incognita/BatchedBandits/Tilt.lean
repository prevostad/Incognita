/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Probability.Moments.Basic

/-! # A good tilt exists

[INC-P000, Lemma `lem:theta`]. For a random variable `Y ∈ [0, 1]` of mean `m` (the reward of an
arm, law `ν`) and a level `m⋆` with `m < m⋆ < 1`, the moments of [INC-P000, Definition
`def:empkinf`] are `Φ_ν(θ, q) = E[e^(θ(Y - q))]` and `Ψ_ν(θ, q) = E[(1 - Y) e^(θ(Y - q))]`.

* `exists_tilt`: (i), some `θ > 0` has `Φ_ν(θ, m⋆) < 1` and `Ψ_ν(θ, m⋆) < 1 - m⋆`. If `Y ≤ m⋆`
  almost surely, any large `θ` works (dominated convergence); otherwise the minimiser of
  `θ ↦ Φ_ν(θ, m⋆)` on `[0, θ_max]` is interior, its derivative `E[(Y - m⋆) e^(θ(Y-m⋆))]` vanishes,
  and `Ψ_ν(θ, m⋆) = (1 - m⋆) Φ_ν(θ, m⋆)`.
* `tilt_shift`: (ii), with `c_θ = (1/2) min(log (1/Φ⋆), log ((1 - m⋆)/Ψ⋆))` and
  `ε_θ = min(c_θ / (6θ), (1 - m⋆)(1 - e^(-c_θ/2)))`, every `ε ∈ (0, ε_θ]` has
  `e^(c_θ) Φ_ν(θ, m⋆ - 3ε) ≤ 1` and `e^(c_θ) Ψ_ν(θ, m⋆ - 3ε) ≤ 1 - (m⋆ + ε)`; `c_θ > 0` and
  `ε_θ > 0` (`tilt_const_pos`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open Real (exp)

open scoped Topology

namespace Incognita.BatchedBandits

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {Y : Ω → ℝ}

/-- [INC-P000, Lemma `lem:theta`(i)] For `Y ∈ [0, 1]` almost surely with mean `m < m⋆ < 1`, some
`θ > 0` has `E[e^(θ(Y - m⋆))] < 1` and `E[(1 - Y) e^(θ(Y - m⋆))] < 1 - m⋆`. -/
lemma exists_tilt (hYm : Measurable Y) (hb : ∀ᵐ ω ∂P, Y ω ∈ Icc (0 : ℝ) 1) {m ms : ℝ}
    (hmean : P[Y] = m) (hm : m < ms) (hms : ms < 1) :
    ∃ θ, 0 < θ ∧ ∫ ω, exp (θ * (Y ω - ms)) ∂P < 1 ∧
      ∫ ω, (1 - Y ω) * exp (θ * (Y ω - ms)) ∂P < 1 - ms := by
  have hm0 : 0 ≤ m := by
    rw [← hmean]
    exact integral_nonneg_of_ae (by filter_upwards [hb] with ω hω using hω.1)
  set Z : Ω → ℝ := fun ω ↦ Y ω - ms with hZ
  have hZm : Measurable Z := hYm.sub_const ms
  have hZb : ∀ᵐ ω ∂P, Z ω ∈ Icc (-1 : ℝ) 1 := by
    filter_upwards [hb] with ω hω
    simp only [hZ, mem_Icc]
    constructor <;> linarith [hω.1, hω.2]
  have hYi : Integrable Y P := Integrable.of_mem_Icc 0 1 hYm.aemeasurable hb
  have hZi : Integrable Z P := Integrable.of_mem_Icc (-1) 1 hZm.aemeasurable hZb
  have hint : ∀ t, Integrable (fun ω ↦ exp (t * Z ω)) P := fun t ↦
    integrable_exp_mul_of_mem_Icc hZm.aemeasurable hZb
  have hint2 : ∀ t, Integrable (fun ω ↦ Z ω * exp (t * Z ω)) P := by
    intro t
    refine Integrable.mono' (hint t) (by fun_prop : Measurable fun ω ↦
      Z ω * exp (t * Z ω)).aestronglyMeasurable ?_
    filter_upwards [hZb] with ω hω
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
    have : |Z ω| ≤ 1 := abs_le.mpr ⟨hω.1, hω.2⟩
    nlinarith [Real.exp_pos (t * Z ω)]
  have hexpset : ∀ t, t ∈ interior (integrableExpSet Z P) := by
    intro t
    have : integrableExpSet Z P = univ := eq_univ_of_forall hint
    rw [this, interior_univ]
    exact mem_univ t
  have hderiv : ∀ t, HasDerivAt (mgf Z P) (∫ ω, Z ω * exp (t * Z ω) ∂P) t :=
    fun t ↦ hasDerivAt_mgf (hexpset t)
  have hEZ : ∫ ω, Z ω ∂P = m - ms := by
    simp only [hZ]
    rw [integral_sub hYi (integrable_const ms), hmean]
    simp
  -- `Ψ(θ) = (1 - m⋆) φ(θ) - E[Z e^(θ Z)]`
  have hΨ : ∀ θ, ∫ ω, (1 - Y ω) * exp (θ * (Y ω - ms)) ∂P =
      (1 - ms) * mgf Z P θ - ∫ ω, Z ω * exp (θ * Z ω) ∂P := by
    intro θ
    have hfun : (fun ω ↦ (1 - Y ω) * exp (θ * (Y ω - ms))) =
        fun ω ↦ (1 - ms) * exp (θ * Z ω) - Z ω * exp (θ * Z ω) := by
      funext ω
      simp only [hZ]
      ring
    rw [hfun, integral_sub ((hint θ).const_mul _) (hint2 θ), integral_const_mul]
    rfl
  have h1ms : 0 < 1 - ms := by linarith
  by_cases hpos : P {ω | 0 < Z ω} = 0
  · -- Case 1: `Z ≤ 0` almost surely; let `θ → ∞`
    have hZle : ∀ᵐ ω ∂P, Z ω ≤ 0 := by
      rw [ae_iff]
      simpa only [not_le] using hpos
    set p0 := P.real {ω | Z ω = 0} with hp0
    have hmeas0 : MeasurableSet {ω | Z ω = 0} := hZm (measurableSet_singleton 0)
    -- `p0 < 1`, since `E Z ≥ -P(Z ≠ 0)`
    have hp0lt : p0 < 1 := by
      have hlow : ∀ᵐ ω ∂P, ({ω | Z ω = 0} : Set Ω).indicator (fun _ ↦ (1 : ℝ)) ω - 1 ≤
          Z ω := by
        filter_upwards [hZb] with ω hω
        by_cases h0 : Z ω = 0
        · rw [Set.indicator_of_mem (show ω ∈ {ω | Z ω = 0} from h0), h0]
          norm_num
        · rw [Set.indicator_of_notMem (show ω ∉ {ω | Z ω = 0} from h0)]
          linarith [hω.1]
      have hI : ∫ ω, (({ω | Z ω = 0} : Set Ω).indicator (fun _ ↦ (1 : ℝ)) ω - 1) ∂P ≤
          ∫ ω, Z ω ∂P :=
        integral_mono_ae (((integrable_const 1).indicator hmeas0).sub (integrable_const 1))
          hZi hlow
      rw [integral_sub ((integrable_const 1).indicator hmeas0) (integrable_const 1),
        integral_indicator hmeas0, setIntegral_const, hEZ] at hI
      simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at hI
      linarith
    -- dominated convergence
    have hlim : ∀ᵐ ω ∂P, Tendsto (fun θ : ℝ ↦ exp (θ * Z ω)) atTop
        (𝓝 (({ω | Z ω = 0} : Set Ω).indicator (fun _ ↦ (1 : ℝ)) ω)) := by
      filter_upwards [hZle] with ω hω
      rcases hω.lt_or_eq with hlt | h0
      · rw [Set.indicator_of_notMem (show ω ∉ {ω | Z ω = 0} from hlt.ne)]
        exact Real.tendsto_exp_atBot.comp (tendsto_id.atTop_mul_const_of_neg hlt)
      · rw [Set.indicator_of_mem (show ω ∈ {ω | Z ω = 0} from h0), h0]
        simp
    have hφ : Tendsto (mgf Z P) atTop (𝓝 p0) := by
      have := tendsto_integral_filter_of_dominated_convergence (fun _ ↦ (1 : ℝ))
        (Eventually.of_forall fun θ ↦ (hint θ).aestronglyMeasurable)
        ((eventually_ge_atTop 0).mono fun θ hθ ↦ by
          filter_upwards [hZle] with ω hω
          rw [Real.norm_of_nonneg (Real.exp_pos _).le]
          exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hθ hω))
        (integrable_const 1) hlim
      rw [integral_indicator hmeas0, setIntegral_const, smul_eq_mul, mul_one] at this
      exact this
    have hlim' : ∀ᵐ ω ∂P, Tendsto (fun θ : ℝ ↦ (1 - Y ω) * exp (θ * (Y ω - ms))) atTop
        (𝓝 ((1 - ms) * ({ω | Z ω = 0} : Set Ω).indicator (fun _ ↦ (1 : ℝ)) ω)) := by
      filter_upwards [hlim] with ω hω
      have hYZ : (1 - Y ω) * ({ω | Z ω = 0} : Set Ω).indicator (fun _ ↦ (1 : ℝ)) ω =
          (1 - ms) * ({ω | Z ω = 0} : Set Ω).indicator (fun _ ↦ (1 : ℝ)) ω := by
        by_cases h0 : Z ω = 0
        · have : Y ω = ms := by simp only [hZ] at h0; linarith
          rw [this]
        · rw [Set.indicator_of_notMem (show ω ∉ {ω | Z ω = 0} from h0), mul_zero, mul_zero]
      rw [← hYZ]
      exact hω.const_mul _
    have hψ : Tendsto (fun θ : ℝ ↦ ∫ ω, (1 - Y ω) * exp (θ * (Y ω - ms)) ∂P) atTop
        (𝓝 ((1 - ms) * p0)) := by
      have := tendsto_integral_filter_of_dominated_convergence (fun _ ↦ (1 : ℝ))
        (Eventually.of_forall fun θ ↦ (by fun_prop : Measurable fun ω ↦
          (1 - Y ω) * exp (θ * (Y ω - ms))).aestronglyMeasurable)
        ((eventually_ge_atTop 0).mono fun θ hθ ↦ by
          filter_upwards [hZle, hb] with ω hω hω'
          rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs,
            abs_of_nonneg (by linarith [hω'.2])]
          have : exp (θ * (Y ω - ms)) ≤ 1 :=
            Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hθ hω)
          nlinarith [hω'.1, Real.exp_pos (θ * (Y ω - ms))])
        (integrable_const 1) hlim'
      rwa [integral_const_mul, integral_indicator hmeas0, setIntegral_const, smul_eq_mul,
        mul_one] at this
    have h1 := (tendsto_order.1 hφ).2 1 hp0lt
    have h2 := (tendsto_order.1 hψ).2 (1 - ms) (by nlinarith)
    obtain ⟨θ, hθ0, hθ1, hθ2⟩ := ((eventually_gt_atTop 0).and (h1.and h2)).exists
    exact ⟨θ, hθ0, hθ1, hθ2⟩
  · -- Case 2: some mass above `m⋆`
    obtain ⟨z0, hz0, hpz⟩ : ∃ z0 : ℝ, 0 < z0 ∧ P {ω | z0 ≤ Z ω} ≠ 0 := by
      by_contra hcon
      simp only [not_exists, not_and, not_not] at hcon
      apply hpos
      have hsub : {ω | 0 < Z ω} ⊆ ⋃ n : ℕ, {ω | 1 / ((n : ℝ) + 1) ≤ Z ω} := by
        intro ω hω
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < Z ω from hω)
        exact mem_iUnion.mpr ⟨n, hn.le⟩
      exact measure_mono_null hsub (measure_iUnion_null fun n ↦ hcon _ (by positivity))
    set p := P.real {ω | z0 ≤ Z ω} with hp
    have hp0 : 0 < p := ENNReal.toReal_pos hpz (measure_ne_top _ _)
    have hmeasz : MeasurableSet {ω | z0 ≤ Z ω} := measurableSet_le measurable_const hZm
    set θs := (ms - m) / 2 with hθs
    have hθs0 : 0 < θs := by rw [hθs]; linarith
    have hθs1 : θs ≤ 1 / 2 := by
      have : m ≥ -1 := by
        have := integral_nonneg_of_ae (μ := P) (f := Y) (by
          filter_upwards [hb] with ω hω using hω.1)
        rw [hmean] at this
        linarith
      rw [hθs]
      linarith
    -- `φ(θs) ≤ 1 - θs² < 1`
    have hφs : mgf Z P θs < 1 := by
      have hpt : ∀ᵐ ω ∂P, exp (θs * Z ω) ≤ 1 + θs * Z ω + θs ^ 2 := by
        filter_upwards [hZb] with ω hω
        have hx : |θs * Z ω| ≤ 1 := by
          rw [abs_mul, abs_of_pos hθs0]
          have : |Z ω| ≤ 1 := abs_le.mpr ⟨hω.1, hω.2⟩
          nlinarith
        have h := Real.abs_exp_sub_one_sub_id_le hx
        have hsq : (θs * Z ω) ^ 2 ≤ θs ^ 2 := by
          have : |Z ω| ≤ 1 := abs_le.mpr ⟨hω.1, hω.2⟩
          rw [mul_pow]
          have : Z ω ^ 2 ≤ 1 := by
            rw [← sq_abs]
            nlinarith [abs_nonneg (Z ω)]
          nlinarith
        have := (abs_le.mp h).2
        linarith
      have hI : ∫ ω, exp (θs * Z ω) ∂P ≤ ∫ ω, (1 + θs * Z ω + θs ^ 2) ∂P :=
        integral_mono_ae (hint θs) (((integrable_const 1).add
          (hZi.const_mul θs)).add (integrable_const (θs ^ 2))) hpt
      rw [integral_add (f := fun ω ↦ 1 + θs * Z ω) ((integrable_const 1).add
        (hZi.const_mul θs)) (integrable_const _), integral_add (f := fun _ ↦ (1 : ℝ))
        (g := fun ω ↦ θs * Z ω) (integrable_const 1) (hZi.const_mul θs), integral_const_mul,
        hEZ] at hI
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hI
      change mgf Z P θs ≤ _ at hI
      have : θs * (m - ms) = -2 * θs ^ 2 := by rw [hθs]; ring
      nlinarith
    -- `φ(θmax) ≥ 1`
    set θm := max 1 (Real.log (1 / p) / z0) with hθm
    have hθm1 : 1 ≤ θm := le_max_left _ _
    have hφm : 1 ≤ mgf Z P θm := by
      have hpt : ∀ᵐ ω ∂P, ({ω | z0 ≤ Z ω} : Set Ω).indicator (fun _ ↦ exp (θm * z0)) ω ≤
          exp (θm * Z ω) := by
        refine Eventually.of_forall fun ω ↦ ?_
        by_cases h : z0 ≤ Z ω
        · rw [Set.indicator_of_mem (show ω ∈ {ω | z0 ≤ Z ω} from h)]
          exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h (by linarith))
        · rw [Set.indicator_of_notMem (show ω ∉ {ω | z0 ≤ Z ω} from h)]
          exact (Real.exp_pos _).le
      have hI := integral_mono_ae ((integrable_const _).indicator hmeasz) (hint θm) hpt
      rw [integral_indicator hmeasz, setIntegral_const, smul_eq_mul] at hI
      change _ ≤ mgf Z P θm at hI
      have hlog : Real.log (1 / p) ≤ θm * z0 := by
        rw [← div_le_iff₀ hz0]
        exact le_max_right _ _
      have : 1 / p ≤ exp (θm * z0) := by
        calc 1 / p = exp (Real.log (1 / p)) := (Real.exp_log (by positivity)).symm
          _ ≤ _ := Real.exp_le_exp.mpr hlog
      have : 1 ≤ p * exp (θm * z0) := by
        rw [div_le_iff₀ hp0] at this
        linarith
      have hpr : P.real {ω | z0 ≤ Z ω} = p := rfl
      rw [measureReal_def] at hpr
      calc 1 ≤ p * exp (θm * z0) := this
        _ = _ := by rw [hp, measureReal_def]
        _ ≤ _ := hI
    -- an interior minimiser
    have hcont : ContinuousOn (mgf Z P) (Icc 0 θm) :=
      (continuous_mgf hint).continuousOn
    obtain ⟨θ, hθmem, hθmin⟩ := isCompact_Icc.exists_isMinOn
      (nonempty_Icc.mpr (by linarith)) hcont
    have hθsmem : θs ∈ Icc 0 θm := ⟨hθs0.le, by linarith⟩
    have hφθ : mgf Z P θ < 1 := (hθmin hθsmem).trans_lt hφs
    have hθ0 : θ ≠ 0 := by
      rintro rfl
      rw [mgf_zero] at hφθ
      simp at hφθ
    have hθm' : θ ≠ θm := by
      rintro rfl
      linarith
    have hθIoo : θ ∈ Ioo 0 θm :=
      ⟨lt_of_le_of_ne hθmem.1 (Ne.symm hθ0), lt_of_le_of_ne hθmem.2 hθm'⟩
    have hloc : IsLocalMin (mgf Z P) θ :=
      hθmin.isLocalMin (Icc_mem_nhds hθIoo.1 hθIoo.2)
    have hzero := hloc.hasDerivAt_eq_zero (hderiv θ)
    refine ⟨θ, hθIoo.1, hφθ, ?_⟩
    rw [hΨ θ, hzero, sub_zero]
    nlinarith

/-- [INC-P000, Lemma `lem:theta`(ii), the constants] If `0 < Φ⋆ < 1` and `0 < Ψ⋆ < 1 - m⋆`, then
`c_θ = (1/2) min(log (1/Φ⋆), log ((1 - m⋆)/Ψ⋆)) > 0` and, for `θ > 0`,
`ε_θ = min(c_θ / (6θ), (1 - m⋆)(1 - e^(-c_θ/2))) > 0`. -/
lemma tilt_const_pos {Φs Ψs ms θ : ℝ} (hΦ0 : 0 < Φs) (hΦ1 : Φs < 1) (hΨ0 : 0 < Ψs)
    (hΨ1 : Ψs < 1 - ms) (hθ : 0 < θ) :
    0 < (1 / 2) * min (Real.log (1 / Φs)) (Real.log ((1 - ms) / Ψs)) ∧
      0 < min ((1 / 2) * min (Real.log (1 / Φs)) (Real.log ((1 - ms) / Ψs)) / (6 * θ))
        ((1 - ms) * (1 - exp (-((1 / 2) * min (Real.log (1 / Φs))
          (Real.log ((1 - ms) / Ψs)) / 2)))) := by
  have h1 : 0 < Real.log (1 / Φs) := Real.log_pos (by rw [lt_div_iff₀ hΦ0]; linarith)
  have h2 : 0 < Real.log ((1 - ms) / Ψs) := Real.log_pos (by rw [lt_div_iff₀ hΨ0]; linarith)
  have hc : 0 < (1 / 2) * min (Real.log (1 / Φs)) (Real.log ((1 - ms) / Ψs)) :=
    mul_pos (by norm_num) (lt_min h1 h2)
  refine ⟨hc, lt_min (by positivity) (mul_pos (by linarith) ?_)⟩
  rw [sub_pos, Real.exp_lt_one_iff]
  linarith

omit [IsProbabilityMeasure P] in
/-- [INC-P000, Lemma `lem:theta`(ii)] For a tilt `θ > 0` with
`0 < Φ⋆ = E[e^(θ(Y - m⋆))] < 1` and `0 < Ψ⋆ = E[(1 - Y) e^(θ(Y - m⋆))] < 1 - m⋆`, and with
`c_θ`, `ε_θ` as in `tilt_const_pos`, every `ε ≤ ε_θ` has
`e^(c_θ) Φ_ν(θ, m⋆ - 3ε) ≤ 1` and `e^(c_θ) Ψ_ν(θ, m⋆ - 3ε) ≤ 1 - (m⋆ + ε)`: shifting the level
multiplies both moments by `e^(3θε) ≤ e^(c_θ/2)`. Neither `Y ∈ [0, 1]` nor `ε > 0` is used
(only `ε ≤ ε_θ`). -/
lemma tilt_shift {ms θ : ℝ} (hθ : 0 < θ) (hΦ0 : 0 < ∫ ω, exp (θ * (Y ω - ms)) ∂P)
    (hΦ1 : ∫ ω, exp (θ * (Y ω - ms)) ∂P < 1)
    (hΨ0 : 0 < ∫ ω, (1 - Y ω) * exp (θ * (Y ω - ms)) ∂P)
    (hΨ1 : ∫ ω, (1 - Y ω) * exp (θ * (Y ω - ms)) ∂P < 1 - ms) {ε : ℝ}
    (hεθ : ε ≤ min ((1 / 2) * min (Real.log (1 / ∫ ω, exp (θ * (Y ω - ms)) ∂P))
        (Real.log ((1 - ms) / ∫ ω, (1 - Y ω) * exp (θ * (Y ω - ms)) ∂P)) / (6 * θ))
      ((1 - ms) * (1 - exp (-((1 / 2) * min (Real.log (1 / ∫ ω, exp (θ * (Y ω - ms)) ∂P))
        (Real.log ((1 - ms) / ∫ ω, (1 - Y ω) * exp (θ * (Y ω - ms)) ∂P)) / 2))))) :
    exp ((1 / 2) * min (Real.log (1 / ∫ ω, exp (θ * (Y ω - ms)) ∂P))
        (Real.log ((1 - ms) / ∫ ω, (1 - Y ω) * exp (θ * (Y ω - ms)) ∂P))) *
        ∫ ω, exp (θ * (Y ω - (ms - 3 * ε))) ∂P ≤ 1 ∧
      exp ((1 / 2) * min (Real.log (1 / ∫ ω, exp (θ * (Y ω - ms)) ∂P))
        (Real.log ((1 - ms) / ∫ ω, (1 - Y ω) * exp (θ * (Y ω - ms)) ∂P))) *
        ∫ ω, (1 - Y ω) * exp (θ * (Y ω - (ms - 3 * ε))) ∂P ≤ 1 - (ms + ε) := by
  set Φs := ∫ ω, exp (θ * (Y ω - ms)) ∂P with hΦs
  set Ψs := ∫ ω, (1 - Y ω) * exp (θ * (Y ω - ms)) ∂P with hΨs
  set c := (1 / 2) * min (Real.log (1 / Φs)) (Real.log ((1 - ms) / Ψs)) with hc
  have h1ms : 0 < 1 - ms := hΨ0.trans hΨ1
  -- shifting the level multiplies the moments by `e^(3θε)`
  have hshΦ : ∫ ω, exp (θ * (Y ω - (ms - 3 * ε))) ∂P = exp (3 * θ * ε) * Φs := by
    rw [hΦs, ← integral_const_mul]
    congr 1
    funext ω
    rw [← Real.exp_add]
    ring_nf
  have hshΨ : ∫ ω, (1 - Y ω) * exp (θ * (Y ω - (ms - 3 * ε))) ∂P = exp (3 * θ * ε) * Ψs := by
    rw [hΨs, ← integral_const_mul]
    congr 1
    funext ω
    rw [show θ * (Y ω - (ms - 3 * ε)) = 3 * θ * ε + θ * (Y ω - ms) by ring, Real.exp_add]
    ring
  have hcpos := (tilt_const_pos hΦ0 hΦ1 hΨ0 hΨ1 hθ).1
  -- `Φ⋆ ≤ e^(-2c)` and `Ψ⋆ ≤ (1 - m⋆) e^(-2c)`
  have hΦc : Φs ≤ exp (-(2 * c)) := by
    have hmin := min_le_left (Real.log (1 / Φs)) (Real.log ((1 - ms) / Ψs))
    have : 2 * c ≤ Real.log (1 / Φs) := by
      rw [hc]
      linarith
    rw [Real.log_div (by norm_num) hΦ0.ne', Real.log_one, zero_sub] at this
    calc Φs = exp (Real.log Φs) := (Real.exp_log hΦ0).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hΨc : Ψs ≤ (1 - ms) * exp (-(2 * c)) := by
    have hmin := min_le_right (Real.log (1 / Φs)) (Real.log ((1 - ms) / Ψs))
    have : 2 * c ≤ Real.log ((1 - ms) / Ψs) := by
      rw [hc]
      linarith
    rw [Real.log_div h1ms.ne' hΨ0.ne'] at this
    calc Ψs = exp (Real.log Ψs) := (Real.exp_log hΨ0).symm
      _ ≤ exp (Real.log (1 - ms) - 2 * c) := Real.exp_le_exp.mpr (by linarith)
      _ = (1 - ms) * exp (-(2 * c)) := by
          rw [sub_eq_add_neg, Real.exp_add, Real.exp_log h1ms]
  -- `3 θ ε ≤ c / 2`
  have hθε : 3 * θ * ε ≤ c / 2 := by
    have := hεθ.trans (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hexp : exp c * exp (3 * θ * ε) * exp (-(2 * c)) ≤ exp (-(c / 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  constructor
  · rw [hshΦ]
    calc exp c * (exp (3 * θ * ε) * Φs) ≤ exp c * (exp (3 * θ * ε) * exp (-(2 * c))) := by
          gcongr
      _ = exp c * exp (3 * θ * ε) * exp (-(2 * c)) := by ring
      _ ≤ exp (-(c / 2)) := hexp
      _ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  · rw [hshΨ]
    have hε2 := hεθ.trans (min_le_right _ _)
    calc exp c * (exp (3 * θ * ε) * Ψs)
        ≤ exp c * (exp (3 * θ * ε) * ((1 - ms) * exp (-(2 * c)))) := by gcongr
      _ = (1 - ms) * (exp c * exp (3 * θ * ε) * exp (-(2 * c))) := by ring
      _ ≤ (1 - ms) * exp (-(c / 2)) := mul_le_mul_of_nonneg_left hexp h1ms.le
      _ ≤ 1 - (ms + ε) := by
          have : -(c / 2) = -(1 / 2 * min (Real.log (1 / Φs))
              (Real.log ((1 - ms) / Ψs)) / 2) := by rw [hc]
          rw [this]
          linarith

end Incognita.BatchedBandits
