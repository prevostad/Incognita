/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.KInf.Shift
public import Incognita.BatchedBandits.LogInequalities
public import Incognita.P006.KInf

/-! # The constants of HY's upper bound

The arithmetic of [INC-P000, Lemmas `lem:constA` and `lem:constC`, Definition `def:constC`]: the
constants of the proofs of Propositions `prop:dyA` and `prop:fixedC`, for an instance of `𝒫`, a
sub-optimal arm `a` and `d_a = 𝒦_inf(ν_a, m⋆)`.

* `mul_div_two_mul_sq_bounds`: Lemma `lem:constC`(a), what "`ℓ` large" guarantees for the count
  threshold `u = (1 + η) L_ℓ / (2ε²)`.
* `div_six_mul_bounds`: the exponent `δ = η / (6(1 + 2η))` of Lemma `lem:constC`(c), (d).
* `le_inv_pow_max_ceil_log_div_log`: the integer `M_ε` of Definition `def:constC`.
* `div_two_le_and_one_add_div_le`, `dInf_sub_shift_bounds_of_gap_pos`: Lemma `lem:constC`(b), the
  bounds on `D'_ε = 𝒦_inf(ν_a, m⋆ - 2ε) - ε`.
* `dInf_shift_bounds_of_gap_pos`: Lemma `lem:constA`(d), the bounds on
  `D_ε = 𝒦_inf(ν_a, m⋆ - 2ε) - ε` and `K⁺_ε = 𝒦_inf(ν_a, m⋆ + ε) + 2ε`.

The two `dInf` bounds rest on Lemma `lem:kinf`(v) (`dInf_unitLaws_sub_le_of_le`,
`dInf_unitLaws_le_add`) and on `d_a ≥ 2 Δ_a²`, `Δ_a` the gap
(`Incognita.P006.kinf_bounds_of_gap_pos`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory LMLExplore LMLExplore.Bandits
open scoped ENNReal NNReal

namespace Incognita.BatchedBandits

/-- [INC-P000, Lemma `lem:constC`(a), "what `ℓ` large guarantees"] Let `δ ∈ (0, 1/2]`, `η > 0`,
`ε ∈ (0, 1)`, `κ > 0` (the paper's `κ(m⋆ + ε)`), `w₀ ≥ 0`, an integer `M` with
`(1 - δ)^(-M) ≥ (1 + 2η) κ / (2ε²)` (the paper's `M_ε`) and `(1 + η) ≤ (1 + 2η)(1 - 2δ)` (from
Lemma `lem:constC`(c)), and `y = L_ℓ` with `y ≥ 4/δ²`, `y ≥ (2/δ) log ((1 + η)/(2ε²))`,
`y ≥ w₀ κ / δ` and `y ≥ 2 w₀`. With the count threshold `u = (1 + η) y / (2ε²)`:
`1 ≤ u ≤ e^((1-δ) y)` (`= t_ℓ^(1-δ)`), `(1 - δ) y - log u ≥ (1 - 2δ) y > 0`,
`(1 - δ)^(-M) (1 - 2δ) y / κ ≥ u`, `w₀ κ ≤ δ y` and `w₀ ≤ ε u`. -/
lemma mul_div_two_mul_sq_bounds {δ η ε κ w₀ y : ℝ} {M : ℕ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hη : 0 < η) (hε0 : 0 < ε) (hε1 : ε < 1) (hκ : 0 < κ) (hw₀ : 0 ≤ w₀)
    (hM : (1 + 2 * η) * κ / (2 * ε ^ 2) ≤ ((1 - δ)⁻¹) ^ M)
    (hηδ : 1 + η ≤ (1 + 2 * η) * (1 - 2 * δ))
    (hy1 : 4 / δ ^ 2 ≤ y) (hy2 : 2 / δ * Real.log ((1 + η) / (2 * ε ^ 2)) ≤ y)
    (hy3 : w₀ * κ / δ ≤ y) (hy4 : 2 * w₀ ≤ y) :
    1 ≤ (1 + η) * y / (2 * ε ^ 2) ∧ (1 + η) * y / (2 * ε ^ 2) ≤ Real.exp ((1 - δ) * y) ∧
    (1 - 2 * δ) * y ≤ (1 - δ) * y - Real.log ((1 + η) * y / (2 * ε ^ 2)) ∧ 0 < (1 - 2 * δ) * y ∧
    (1 + η) * y / (2 * ε ^ 2) ≤ ((1 - δ)⁻¹) ^ M * ((1 - 2 * δ) * y) / κ ∧
    w₀ * κ ≤ δ * y ∧ w₀ ≤ ε * ((1 + η) * y / (2 * ε ^ 2)) := by
  have hε2 : 0 < 2 * ε ^ 2 := by positivity
  have hε21 : 2 * ε ^ 2 < 2 := by nlinarith
  have hδ2 : 4 ≤ 4 / δ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hy0 : 4 ≤ y := hδ2.trans hy1
  have hypos : 0 < y := by linarith
  set c := (1 + η) / (2 * ε ^ 2) with hc
  have hc1 : 1 / 2 ≤ c := by
    rw [hc, le_div_iff₀ hε2]
    nlinarith
  have hc0 : 0 < c := by linarith
  have hu : (1 + η) * y / (2 * ε ^ 2) = c * y := by rw [hc]; ring
  rw [hu]
  -- `log u ≤ δ y`
  have hsqrt : Real.sqrt y ≤ δ / 2 * y := by
    have hs : 2 / δ ≤ Real.sqrt y := by
      rw [show 2 / δ = Real.sqrt ((2 / δ) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
      refine Real.sqrt_le_sqrt ?_
      rw [div_pow]
      linarith
    have hss : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hypos.le
    have hs0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
    have hone : 1 ≤ δ / 2 * Real.sqrt y := by
      have : δ / 2 * (2 / δ) = 1 := by field_simp
      rw [← this]
      exact mul_le_mul_of_nonneg_left hs (by positivity)
    calc Real.sqrt y = 1 * Real.sqrt y := (one_mul _).symm
      _ ≤ (δ / 2 * Real.sqrt y) * Real.sqrt y := mul_le_mul_of_nonneg_right hone hs0
      _ = δ / 2 * y := by rw [mul_assoc, hss]
  have hlogy : Real.log y ≤ δ / 2 * y := (log_le_sqrt hypos).trans hsqrt
  have hlogc : Real.log c ≤ δ / 2 * y := by
    have := hy2
    rw [div_mul_eq_mul_div, div_le_iff₀ hδ0] at this
    linarith
  have hlogu : Real.log (c * y) ≤ δ * y := by
    rw [Real.log_mul hc0.ne' hypos.ne']
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · calc c * y = Real.exp (Real.log (c * y)) := (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp ((1 - δ) * y) := Real.exp_le_exp.mpr (by nlinarith)
  · linarith
  · have : 0 < 1 - 2 * δ := by
      have : 0 < 1 + η := by linarith
      nlinarith
    positivity
  · have h12 : 0 < 1 - 2 * δ := by
      have : 0 < 1 + η := by linarith
      nlinarith
    have h2 : 0 ≤ (1 - 2 * δ) * y / κ := by positivity
    have heq : (1 + 2 * η) * κ / (2 * ε ^ 2) * ((1 - 2 * δ) * y / κ) =
        (1 + 2 * η) * (1 - 2 * δ) * y / (2 * ε ^ 2) := by
      field_simp
    have h1 : c * y ≤ (1 + 2 * η) * κ / (2 * ε ^ 2) * ((1 - 2 * δ) * y / κ) := by
      rw [heq, hc, div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hηδ hypos.le) hε2.le
    calc c * y ≤ (1 + 2 * η) * κ / (2 * ε ^ 2) * ((1 - 2 * δ) * y / κ) := h1
      _ ≤ ((1 - δ)⁻¹) ^ M * ((1 - 2 * δ) * y / κ) := mul_le_mul_of_nonneg_right hM h2
      _ = ((1 - δ)⁻¹) ^ M * ((1 - 2 * δ) * y) / κ := by ring
  · rw [div_le_iff₀ hδ0] at hy3
    linarith
  · have : ε * (c * y) = (1 + η) * y / (2 * ε) := by
      rw [hc]
      field_simp
    rw [this, le_div_iff₀ (by positivity)]
    nlinarith

/-- [INC-P000, Lemma `lem:constC`(c) exponent and (d)] For `η > 0` and `δ = η / (6(1 + 2η))`:
`0 < δ < 1/12`, `(1 - δ)(1 - 2δ) ≥ 1 - 3δ`, `(1 + 2η)(1 - 4δ) ≥ 1 + η`, and so
`(1 + 2η)(1 - 2δ) ≥ 1 + η`. -/
lemma div_six_mul_bounds {η : ℝ} (hη : 0 < η) :
    0 < η / (6 * (1 + 2 * η)) ∧ η / (6 * (1 + 2 * η)) < 1 / 12 ∧
    1 - 3 * (η / (6 * (1 + 2 * η))) ≤
      (1 - η / (6 * (1 + 2 * η))) * (1 - 2 * (η / (6 * (1 + 2 * η)))) ∧
    1 + η ≤ (1 + 2 * η) * (1 - 4 * (η / (6 * (1 + 2 * η)))) ∧
    1 + η ≤ (1 + 2 * η) * (1 - 2 * (η / (6 * (1 + 2 * η)))) := by
  set δ := η / (6 * (1 + 2 * η)) with hδ
  have hden : 0 < 6 * (1 + 2 * η) := by positivity
  have hδ0 : 0 < δ := by positivity
  have hδ12 : δ < 1 / 12 := by
    rw [hδ, div_lt_iff₀ hden]
    linarith
  have h4 : (1 + 2 * η) * (1 - 4 * δ) = 1 + 4 / 3 * η := by
    rw [hδ]
    field_simp
    ring
  refine ⟨hδ0, hδ12, by nlinarith, by rw [h4]; linarith, ?_⟩
  have : (1 + 2 * η) * (1 - 4 * δ) ≤ (1 + 2 * η) * (1 - 2 * δ) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  linarith

/-- [INC-P000, Definition `def:constC`, `M_ε`] For `δ ∈ (0, 1)` and `X > 0`, the integer
`M = max(1, ⌈log X / log (1/(1 - δ))⌉)` has `(1 - δ)^(-M) ≥ X` and `M ≥ 1`. -/
lemma le_inv_pow_max_ceil_log_div_log {δ X : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hX : 0 < X) :
    1 ≤ max 1 ⌈Real.log X / Real.log (1 / (1 - δ))⌉₊ ∧
      X ≤ ((1 - δ)⁻¹) ^ (max 1 ⌈Real.log X / Real.log (1 / (1 - δ))⌉₊) := by
  refine ⟨le_max_left _ _, ?_⟩
  set M := max 1 ⌈Real.log X / Real.log (1 / (1 - δ))⌉₊ with hM
  have h1δ : 0 < 1 - δ := by linarith
  have hq : 1 < (1 - δ)⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) h1δ, inv_one]
    linarith
  have hlogq : 0 < Real.log (1 / (1 - δ)) := by
    rw [one_div]
    exact Real.log_pos hq
  have hpos : 0 < ((1 - δ)⁻¹) ^ M := by positivity
  rw [← Real.log_le_log_iff hX hpos, Real.log_pow, ← one_div]
  have hceil : Real.log X / Real.log (1 / (1 - δ)) ≤ M :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
  rw [div_le_iff₀ hlogq] at hceil
  linarith

/-- [INC-P000, proof of Lemma `lem:constC`(b), the arithmetic] For `Δ, c > 0`, `ε ∈ (0, Δ/(4c)]`
and `D ≥ Δ - 2cε`: `D ≥ Δ/2` and `(1 + ε)/D ≤ 1/Δ + (2/Δ + 4c/Δ²) ε`. -/
lemma div_two_le_and_one_add_div_le {Δ c ε D : ℝ} (hΔ : 0 < Δ) (hc : 0 < c) (hε : 0 < ε)
    (hεΔ : ε ≤ Δ / (4 * c)) (hD : Δ - 2 * c * ε ≤ D) :
    Δ / 2 ≤ D ∧ (1 + ε) / D ≤ 1 / Δ + (2 / Δ + 4 * c / Δ ^ 2) * ε := by
  have h4c : 4 * c * ε ≤ Δ := by
    have := mul_le_mul_of_nonneg_left hεΔ (by linarith : 0 ≤ 4 * c)
    rwa [mul_div_cancel₀ _ (by positivity)] at this
  have hD2 : Δ / 2 ≤ D := by linarith
  refine ⟨hD2, ?_⟩
  have hDpos : 0 < D := by linarith
  have hlow : 0 < Δ - 2 * c * ε := by linarith
  refine (div_le_div_of_nonneg_left (by linarith) hlow hD).trans ?_
  rw [div_le_iff₀ hlow]
  -- with `s = c ε / Δ ≤ 1/4`
  set s := c * ε / Δ with hs
  have hs0 : 0 ≤ s := by positivity
  have hs4 : s ≤ 1 / 4 := by
    rw [hs, div_le_iff₀ hΔ]
    linarith
  have hexp : (1 / Δ + (2 / Δ + 4 * c / Δ ^ 2) * ε) * (Δ - 2 * c * ε) =
      1 + 2 * ε + 2 * s - 4 * ε * s - 8 * s ^ 2 := by
    rw [hs]
    field_simp
    ring
  rw [hexp]
  nlinarith [mul_nonneg hε.le (by linarith : (0 : ℝ) ≤ 1 - 4 * s),
    mul_nonneg hs0 (by linarith : (0 : ℝ) ≤ 1 - 4 * s)]

variable {α : Type*} [MeasurableSpace α] [Finite α] [MeasurableSingletonClass α]

/-- [INC-P000, Lemma `lem:constC`(b), and (d) first claim] For an instance `ν` of `𝒫` and a
sub-optimal arm `a`, let `Δ = 𝒦_inf(ν_a, m⋆)` (the paper's `d_a`), `c⋆ = (2 - m⋆)/(1 - m⋆)`
and `D'_ε = 𝒦_inf(ν_a, m⋆ - 2ε) - ε`. Then `Δ ≥ 2 Δ_a² > 0`, `Δ_a` the gap (the paper's
`d_a ≥ (m⋆ - m_a)²/8`), and for every `ε ∈ (0, 1]` with `ε ≤ Δ/(4c⋆)` (the paper's `ε ≤ ε̄`;
its `2ε ≤ m⋆` is not needed):
`D'_ε ≥ Δ - 2c⋆ε ≥ Δ/2 ≥ ε²/8` and `(1 + ε)/D'_ε ≤ 1/Δ + C₁ε`, `C₁ = 2/Δ + 4c⋆/Δ²`
(Lemma `lem:kinf`(v) for the law `ν_a`, `dInf_unitLaws_sub_le_of_le`). -/
lemma dInf_sub_shift_bounds_of_gap_pos {ν : Kernel α ℝ} (hν : ν ∈ unitBandits α) {a : α}
    (ha : 0 < Bandits.gap ν a) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hεΔ : ε ≤ (dInf unitLaws (ν a) (⨆ b, ∫ x, id x ∂(ν b))).toReal /
      (4 * ((2 - ⨆ b, ∫ x, id x ∂(ν b)) / (1 - ⨆ b, ∫ x, id x ∂(ν b))))) :
    2 * Bandits.gap ν a ^ 2 ≤ (dInf unitLaws (ν a) (⨆ b, ∫ x, id x ∂(ν b))).toReal ∧
    (dInf unitLaws (ν a) (⨆ b, ∫ x, id x ∂(ν b))).toReal -
        2 * ((2 - ⨆ b, ∫ x, id x ∂(ν b)) / (1 - ⨆ b, ∫ x, id x ∂(ν b))) * ε ≤
      (dInf unitLaws (ν a) ((⨆ b, ∫ x, id x ∂(ν b)) - 2 * ε)).toReal - ε ∧
    (dInf unitLaws (ν a) (⨆ b, ∫ x, id x ∂(ν b))).toReal / 2 ≤
      (dInf unitLaws (ν a) ((⨆ b, ∫ x, id x ∂(ν b)) - 2 * ε)).toReal - ε ∧
    ε ^ 2 / 8 ≤ (dInf unitLaws (ν a) (⨆ b, ∫ x, id x ∂(ν b))).toReal / 2 ∧
    (1 + ε) / ((dInf unitLaws (ν a) ((⨆ b, ∫ x, id x ∂(ν b)) - 2 * ε)).toReal - ε) ≤
      1 / (dInf unitLaws (ν a) (⨆ b, ∫ x, id x ∂(ν b))).toReal +
        (2 / (dInf unitLaws (ν a) (⨆ b, ∫ x, id x ∂(ν b))).toReal +
          4 * ((2 - ⨆ b, ∫ x, id x ∂(ν b)) / (1 - ⨆ b, ∫ x, id x ∂(ν b))) /
            (dInf unitLaws (ν a) (⨆ b, ∫ x, id x ∂(ν b))).toReal ^ 2) * ε := by
  set ms := ⨆ b, ∫ x, id x ∂(ν b) with hms
  obtain ⟨hpos, hlow, -, hfin⟩ := Incognita.P006.kinf_bounds_of_gap_pos hν ha
  set Δ := (dInf unitLaws (ν a) ms).toReal with hΔdef
  have hms1 : ms < 1 := hν.2
  have h1ms : 0 < 1 - ms := by linarith
  set cs := (2 - ms) / (1 - ms) with hcs
  have hcs1 : 1 ≤ cs := by rw [hcs, le_div_iff₀ h1ms]; linarith
  have hgap : 0 < 2 * Bandits.gap ν a ^ 2 := by positivity
  have hΔ : 2 * Bandits.gap ν a ^ 2 ≤ Δ := by
    rw [hΔdef, ← ENNReal.ofReal_le_iff_le_toReal hfin]
    exact hlow
  have hΔ0 : 0 < Δ := hgap.trans_le hΔ
  -- `𝒦_inf(ν_a, m⋆ - 2ε) ≥ Δ - 2ε/(1 - m⋆)`
  have hshift := dInf_unitLaws_sub_le_of_le (hν.1 a) (μ := ms) (ε := 2 * ε) (by linarith) hms1
  have hD : Δ - 2 * cs * ε ≤ (dInf unitLaws (ν a) (ms - 2 * ε)).toReal - ε := by
    have h2 : 2 * cs * ε = 2 * ε / (1 - ms) + 2 * ε := by
      rw [hcs]
      field_simp
      ring
    rw [h2]
    linarith
  obtain ⟨hD2, hbound⟩ := div_two_le_and_one_add_div_le hΔ0 (by linarith) hε hεΔ hD
  have h8 : ε ^ 2 / 8 ≤ Δ / 2 := by
    have h4 : 4 * cs * ε ≤ Δ := by
      have := mul_le_mul_of_nonneg_left hεΔ (by linarith : 0 ≤ 4 * cs)
      rwa [mul_div_cancel₀ _ (by positivity)] at this
    have : ε ^ 2 ≤ ε := by nlinarith
    nlinarith
  exact ⟨hΔ, hD, hD2, h8, hbound⟩

/-- [INC-P000, Lemma `lem:constA`(d)] For an instance `ν` of `𝒫` and a sub-optimal arm `a`, let
`Δ = 𝒦_inf(ν_a, m⋆)`, `c⋆ = (2 - m⋆)/(1 - m⋆)`, `D_ε = 𝒦_inf(ν_a, m⋆ - 2ε) - ε` and
`K⁺_ε = 𝒦_inf(ν_a, m⋆ + ε) + 2ε`. For a margin `ω ∈ (0, 1]` and `ε > 0` with
`2ε ≤ 1 - m⋆` and `ε ≤ ωΔ/(16c⋆)` (the paper's `ε ≤ min(ε̄, ε_ω)`; its `2ε ≤ m⋆` is not needed):
`D_ε ≥ Δ - 2c⋆ε ≥ 7Δ/8`, `1/D_ε ≤ 1/Δ + 3c⋆ε/Δ²`, `K⁺_ε ≤ Δ + 2c⋆ε` and `(1 + ω) D_ε ≥ K⁺_ε`
(Lemma `lem:kinf`(v) for the law `ν_a`, at `m⋆` with the shift `2ε` and at `m⋆ + ε` with the
shift `ε`). -/
lemma dInf_shift_bounds_of_gap_pos {ν : Kernel α ℝ} (hν : ν ∈ unitBandits α) {a : α}
    (ha : 0 < Bandits.gap ν a) {ω ε : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1) (hε : 0 < ε)
    (h2ε1 : 2 * ε ≤ 1 - ⨆ b, ∫ x, id x ∂(ν b))
    (hεω : ε ≤ ω * (dInf unitLaws (ν a) (⨆ b, ∫ x, id x ∂(ν b))).toReal /
      (16 * ((2 - ⨆ b, ∫ x, id x ∂(ν b)) / (1 - ⨆ b, ∫ x, id x ∂(ν b))))) :
    (dInf unitLaws (ν a) (⨆ b, ∫ x, id x ∂(ν b))).toReal -
        2 * ((2 - ⨆ b, ∫ x, id x ∂(ν b)) / (1 - ⨆ b, ∫ x, id x ∂(ν b))) * ε ≤
      (dInf unitLaws (ν a) ((⨆ b, ∫ x, id x ∂(ν b)) - 2 * ε)).toReal - ε ∧
    7 / 8 * (dInf unitLaws (ν a) (⨆ b, ∫ x, id x ∂(ν b))).toReal ≤
      (dInf unitLaws (ν a) ((⨆ b, ∫ x, id x ∂(ν b)) - 2 * ε)).toReal - ε ∧
    1 / ((dInf unitLaws (ν a) ((⨆ b, ∫ x, id x ∂(ν b)) - 2 * ε)).toReal - ε) ≤
      1 / (dInf unitLaws (ν a) (⨆ b, ∫ x, id x ∂(ν b))).toReal +
        3 * ((2 - ⨆ b, ∫ x, id x ∂(ν b)) / (1 - ⨆ b, ∫ x, id x ∂(ν b))) * ε /
          (dInf unitLaws (ν a) (⨆ b, ∫ x, id x ∂(ν b))).toReal ^ 2 ∧
    (dInf unitLaws (ν a) ((⨆ b, ∫ x, id x ∂(ν b)) + ε)).toReal + 2 * ε ≤
      (dInf unitLaws (ν a) (⨆ b, ∫ x, id x ∂(ν b))).toReal +
        2 * ((2 - ⨆ b, ∫ x, id x ∂(ν b)) / (1 - ⨆ b, ∫ x, id x ∂(ν b))) * ε ∧
    (dInf unitLaws (ν a) ((⨆ b, ∫ x, id x ∂(ν b)) + ε)).toReal + 2 * ε ≤
      (1 + ω) * ((dInf unitLaws (ν a) ((⨆ b, ∫ x, id x ∂(ν b)) - 2 * ε)).toReal - ε) := by
  set ms := ⨆ b, ∫ x, id x ∂(ν b) with hms
  obtain ⟨hpos, hlow, -, hfin⟩ := Incognita.P006.kinf_bounds_of_gap_pos hν ha
  set Δ := (dInf unitLaws (ν a) ms).toReal with hΔdef
  have hms1 : ms < 1 := hν.2
  have h1ms : 0 < 1 - ms := by linarith
  set cs := (2 - ms) / (1 - ms) with hcs
  have hcs1 : 1 ≤ cs := by rw [hcs, le_div_iff₀ h1ms]; linarith
  have hΔ0 : 0 < Δ := by
    have hgap : 0 < 2 * Bandits.gap ν a ^ 2 := by positivity
    refine hgap.trans_le ?_
    rw [hΔdef, ← ENNReal.ofReal_le_iff_le_toReal hfin]
    exact hlow
  have hε16 : 16 * cs * ε ≤ ω * Δ := by
    have := mul_le_mul_of_nonneg_left hεω (by linarith : 0 ≤ 16 * cs)
    rwa [mul_div_cancel₀ _ (by positivity)] at this
  -- the lower estimate
  have hshift := dInf_unitLaws_sub_le_of_le (hν.1 a) (μ := ms) (ε := 2 * ε) (by linarith) hms1
  have h2cs : 2 * cs * ε = 2 * ε / (1 - ms) + 2 * ε := by
    rw [hcs]
    field_simp
    ring
  have hD : Δ - 2 * cs * ε ≤ (dInf unitLaws (ν a) (ms - 2 * ε)).toReal - ε := by
    rw [h2cs]
    linarith
  set D := (dInf unitLaws (ν a) (ms - 2 * ε)).toReal - ε with hDdef
  have hD78 : 7 / 8 * Δ ≤ D := by nlinarith
  have hDpos : 0 < D := by linarith
  -- the upper estimate
  have hμ1 : ms + ε < 1 := by linarith
  have hup := dInf_unitLaws_le_add (hν.1 a) (μ := ms + ε) (ε := ε) hμ1
  rw [add_sub_cancel_right] at hup
  have hup' : (dInf unitLaws (ν a) (ms + ε)).toReal ≤ Δ + ε / (1 - (ms + ε)) := by
    have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin, ENNReal.ofReal_ne_top⟩) hup
    rwa [ENNReal.toReal_add hfin ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (div_nonneg hε.le (by linarith))] at h2
  have hhalf : ε / (1 - (ms + ε)) ≤ 2 * ε / (1 - ms) := by
    rw [div_le_div_iff₀ (by linarith) h1ms]
    nlinarith
  have hKp : (dInf unitLaws (ν a) (ms + ε)).toReal + 2 * ε ≤ Δ + 2 * cs * ε := by
    rw [h2cs]
    linarith
  refine ⟨hD, hD78, ?_, hKp, ?_⟩
  · -- `1/D ≤ 1/Δ + 3c⋆ε/Δ²`
    rw [div_add_div _ _ hΔ0.ne' (by positivity), div_le_div_iff₀ hDpos (by positivity)]
    have h1 : Δ - D ≤ 2 * cs * ε := by linarith
    have h2 : 0 ≤ cs * ε := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hD78 h2, mul_pos hΔ0 hΔ0]
  · -- `(1 + ω) D ≥ K⁺`
    have : (1 + ω) * (Δ - 2 * cs * ε) ≤ (1 + ω) * D := mul_le_mul_of_nonneg_left hD (by linarith)
    nlinarith

end Incognita.BatchedBandits
