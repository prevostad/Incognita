/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.KInf

/-! # Shifting the level of `𝒦_inf`

[INC-P000, Lemma `lem:kinf`(v)] for a law `P` on `[0, 1]` and the primal formula
`𝒦_inf(P, μ) = dInf unitLaws P μ`: for `0 < ε` and `μ < 1`,
`𝒦_inf(P, μ) ≤ 𝒦_inf(P, μ - ε) + ε / (1 - μ)`. A competitor `Q` at the level `μ - ε` (mean
`> μ - ε`) gives the competitor `(1 - v) Q + v δ_1` at the level `μ`, `v = ε / (1 - μ + ε)`, with
`KL(P ‖ ·) ≤ KL(P ‖ Q) + log (1 / (1 - v))` (`Incognita.klDiv_smul_add_smul_le_add`) and
`log (1 / (1 - v)) = log (1 + ε / (1 - μ)) ≤ ε / (1 - μ)`.

* `dInf_unitLaws_le_add`: Lemma `lem:kinf`(v), primal form.
* `dInf_unitLaws_ne_top`: `𝒦_inf(P, μ) < ∞` for every level `μ < 1`.
* `dInf_unitLaws_sub_le_of_le`: the consequences used in Lemmas `lem:constA`(d) and `lem:constC`(b):
  `𝒦_inf(P, μ - ε) ≥ 𝒦_inf(P, μ) - ε / (1 - μ)` in real numbers.

The paper's `0 < ε ≤ μ` only keeps the level `μ - ε` in `[0, 1)`, where its `𝒦_inf` is defined;
`dInf` is defined at every level (and is `0` below the mean of `P`), so `ε ≤ μ` is dropped.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory LMLExplore LMLExplore.Bandits
open scoped ENNReal NNReal

namespace Incognita.BatchedBandits

variable {P : Measure ℝ}

/-- [INC-P000, Lemma `lem:kinf`(v), primal form] For a law `P` on `[0, 1]`, every `ε` and `μ < 1`,
`𝒦_inf(P, μ) ≤ 𝒦_inf(P, μ - ε) + ε / (1 - μ)` (the paper's `0 < ε ≤ μ` is not needed: for
`ε ≤ 0` this is the monotonicity of `𝒦_inf(P, ·)`). -/
lemma dInf_unitLaws_le_add (hP : P ∈ unitLaws) {μ ε : ℝ} (hμ : μ < 1) :
    dInf unitLaws P μ ≤ dInf unitLaws P (μ - ε) + ENNReal.ofReal (ε / (1 - μ)) := by
  rcases le_or_gt ε 0 with hε | hε
  · exact (dInf_mono _ _ (by linarith)).trans le_self_add
  have := hP.1
  have h1μ : 0 < 1 - μ := by linarith
  rw [← tsub_le_iff_right]
  refine le_dInf_iff.mpr fun Q hQ hQm ↦ ?_
  have := hQ.1
  rw [tsub_le_iff_right]
  -- the mixture with `δ_1`
  set v : ℝ≥0 := ⟨ε / (1 - μ + ε), div_nonneg hε.le (by linarith)⟩ with hv
  -- the coercion of `v` to `ℝ`, by definition of `v`
  have hvr : (v : ℝ) = ε / (1 - μ + ε) := rfl
  have hv1 : v < 1 := by
    rw [← NNReal.coe_lt_coe, NNReal.coe_one, hvr, div_lt_one (by linarith)]
    linarith
  have hmean : μ < ((1 - v) • Q + v • Measure.dirac (1 : ℝ))[id] := by
    rw [integral_id_smul_add_smul_dirac_one hQ hv1.le, hvr]
    have hden : 0 < 1 - μ + ε := by linarith
    have : (1 - ε / (1 - μ + ε)) * (μ - ε) + ε / (1 - μ + ε) = μ := by
      field_simp
      ring
    have hpos : 0 < 1 - ε / (1 - μ + ε) := by
      rw [sub_pos, div_lt_one hden]
      linarith
    nlinarith
  have hkl := klDiv_smul_add_smul_le_add (μ := P) (ν := Q) (Measure.dirac (1 : ℝ)) hv1
  have hlog : -Real.log ((1 - v : ℝ≥0) : ℝ) ≤ ε / (1 - μ) := by
    rw [NNReal.coe_sub hv1.le, NNReal.coe_one, hvr]
    have hden : 0 < 1 - μ + ε := by linarith
    have h1 : 1 - ε / (1 - μ + ε) = (1 - μ) / (1 - μ + ε) := by
      field_simp
      ring
    rw [h1, ← Real.log_inv, inv_div]
    have h2 : (1 - μ + ε) / (1 - μ) = 1 + ε / (1 - μ) := by
      field_simp
    rw [h2]
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + ε / (1 - μ) by positivity)
    linarith
  calc dInf unitLaws P μ ≤ klDiv P ((1 - v) • Q + v • Measure.dirac (1 : ℝ)) :=
        dInf_le (smul_add_smul_dirac_one_mem_unitLaws hQ hv1.le) hmean
    _ ≤ klDiv P Q + ENNReal.ofReal (-Real.log ((1 - v : ℝ≥0) : ℝ)) := hkl
    _ ≤ klDiv P Q + ENNReal.ofReal (ε / (1 - μ)) := by
        gcongr

/-- `𝒦_inf(P, μ)` is finite for a law `P` on `[0, 1]` and a level `μ < 1`: below the mean of `P`,
`P` itself is a competitor; at or above it, `dInf_unitLaws_le_ofReal_log`. -/
lemma dInf_unitLaws_ne_top (hP : P ∈ unitLaws) {μ : ℝ} (hμ : μ < 1) :
    dInf unitLaws P μ ≠ ⊤ := by
  have := hP.1
  rcases le_or_gt P[id] μ with h | h
  · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (dInf_unitLaws_le_ofReal_log hP h hμ)
  · exact ne_top_of_le_ne_top (by simp [klDiv_self]) (dInf_le hP h)

/-- [INC-P000, Lemma `lem:kinf`(v), real form] For a law `P` on `[0, 1]`, `0 < ε` and `μ < 1`:
`𝒦_inf(P, μ).toReal - ε / (1 - μ) ≤ 𝒦_inf(P, μ - ε).toReal` (the form of the
proofs of Lemmas `lem:constA`(d), `lem:constC`(b): with `μ = m⋆`, `ε = 2ε'`,
`𝒦_inf(ν_a, m⋆ - 2ε') ≥ d_a - 2ε'/(1 - m⋆)`, `d_a = 𝒦_inf(ν_a, m⋆)`). -/
lemma dInf_unitLaws_sub_le_of_le (hP : P ∈ unitLaws) {μ ε : ℝ} (hε : 0 < ε) (hμ : μ < 1) :
    (dInf unitLaws P μ).toReal - ε / (1 - μ) ≤ (dInf unitLaws P (μ - ε)).toReal := by
  have hfin := dInf_unitLaws_ne_top hP (show μ - ε < 1 by linarith)
  have h := dInf_unitLaws_le_add hP (ε := ε) hμ
  have h1μ : 0 < 1 - μ := by linarith
  have hc : 0 ≤ ε / (1 - μ) := div_nonneg hε.le h1μ.le
  have hfin' : dInf unitLaws P (μ - ε) + ENNReal.ofReal (ε / (1 - μ)) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hfin, ENNReal.ofReal_ne_top⟩
  have h2 := ENNReal.toReal_mono hfin' h
  rw [ENNReal.toReal_add hfin ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hc] at h2
  linarith

end Incognita.BatchedBandits
