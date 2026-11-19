/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.Instances
public import Incognita.ForMathlib.InformationTheory.KullbackLeibler.Basic
public import LMLExplore.Bandits.LaiRobbins
public import LMLExplore.Identification.Task.RealLaws

/-! # `𝒦_inf` on the laws on `[0, 1]`

Values and bounds of `𝒦_inf(P, μ) = dInf unitLaws P μ`, the infimum of `KL(P ‖ Q)` over the laws
`Q` on `[0, 1]` with mean `> μ` [INC-P006, Proposition `prop:kinf`]. With `p = m(P)`:

* `dInf_unitLaws_eq_top_of_one_le`: `𝒦_inf(P, μ) = ∞` for `μ ≥ 1` (no law on `[0, 1]` has a mean
  above `1`);
* `dInf_unitLaws_eq_zero_of_lt_integral`: `𝒦_inf(P, μ) = 0` for `μ < p` (`Q = P`);
* `Relations.kInfUpper_unitIntervalLaws_le_dInf_unitLaws`: LMLExplore's transportation cost
  `K⁺(P, μ)` over the laws on `[0, 1]` is at most `𝒦_inf(P, μ)`;
* `klBer_le_dInf_unitLaws`: `kl(p, μ) ≤ 𝒦_inf(P, μ)` for `p ≤ μ`, from LMLExplore's lower bound
  `klBer_le_kInfUpper_of_subset_unitIntervalLaws` on `K⁺`;
* `dInf_unitLaws_le_ofReal_log`: `𝒦_inf(P, μ) ≤ log ((1 - p) / (1 - μ))` for `p ≤ μ < 1`, through
  the mixtures `(1 - u) P + u δ_1`, `u ∈ (u₀, 1)` with `u₀ = (μ - p) / (1 - p)`, whose density bound
  gives `KL(P ‖ ·) ≤ log (1 / (1 - u))` (`Incognita.klDiv_le_ofReal_neg_log_smul_add_smul`);
* `dInf_unitLaws_bernoulliMeasure`: `𝒦_inf(Ber(p), μ) = kl(p, μ)` for `p ≤ μ < 1` (the Bernoulli
  laws are competitors: LMLExplore's `dInf_range_bernoulliMeasure`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology LMLExplore
  LMLExplore.Bandits
open scoped ENNReal NNReal unitInterval

namespace Incognita.BatchedBandits

variable {P : Measure ℝ} {μ : ℝ}

/-- `dInf` is antitone in the class of laws. -/
lemma dInf_anti {M M' : Set (Measure ℝ)} (h : M ⊆ M') (P : Measure ℝ) (m : ℝ) :
    dInf M' P m ≤ dInf M P m :=
  le_dInf_iff.2 fun _ hQ hm ↦ dInf_le (h hQ) hm

/-- [INC-P006, Proposition `prop:kinf`(i)] `𝒦_inf(P, μ) = ∞` for `μ ≥ 1`: no law on `[0, 1]` has a
mean above `1`. No hypothesis on `P`. -/
lemma dInf_unitLaws_eq_top_of_one_le (P : Measure ℝ) (hμ : 1 ≤ μ) : dInf unitLaws P μ = ∞ :=
  top_le_iff.1 <| le_dInf_iff.2 fun _ hQ hm ↦
    absurd (hμ.trans_lt hm) (not_lt.2 (integral_id_mem_Icc_of_mem_unitLaws hQ).2)

/-- [INC-P006, Proposition `prop:kinf`(ii)] `𝒦_inf(P, μ) = 0` for `μ` below the mean of `P`: `P`
itself is a competitor. -/
lemma dInf_unitLaws_eq_zero_of_lt_integral (hP : P ∈ unitLaws) (hμ : μ < P[id]) :
    dInf unitLaws P μ = 0 := by
  have := hP.1
  exact nonpos_iff_eq_zero.1 ((dInf_le hP hμ).trans_eq (klDiv_self P))

/-- LMLExplore's transportation cost `K⁺(P, μ)` over the laws on `[0, 1]` (competitors of mean
`≥ μ`) is at most `𝒦_inf(P, μ) = dInf unitLaws P μ` (competitors of mean `> μ`). -/
lemma Relations.kInfUpper_unitIntervalLaws_le_dInf_unitLaws (P : ProbabilityMeasure ℝ) (μ : ℝ) :
    Identification.kInfUpper ProbabilityMeasure.toMeasure Identification.unitIntervalLaws
        (fun Q ↦ (Q : Measure ℝ)[id]) P μ ≤
      dInf unitLaws (P : Measure ℝ) μ :=
  le_dInf_iff.2 fun Q hQ hm ↦
    Identification.kInfUpper_le (κ := ProbabilityMeasure.toMeasure)
      (m := fun Q ↦ (Q : Measure ℝ)[id]) (y := (⟨Q, hQ.1⟩ : ProbabilityMeasure ℝ))
      (Identification.mem_unitIntervalLaws_iff.2 hQ.2) hm.le

/-- [INC-P006, Proposition `prop:kinf`(iii), lower bound] `kl(p, μ) ≤ 𝒦_inf(P, μ)` for
`p = m(P) ≤ μ`: LMLExplore's bound `kl(p, μ) ≤ K⁺(P, μ)` and `K⁺ ≤ 𝒦_inf`. -/
lemma klBer_le_dInf_unitLaws (hP : P ∈ unitLaws) (hpμ : P[id] ≤ μ) :
    klBer P[id] μ ≤ dInf unitLaws P μ :=
  (Identification.klBer_le_kInfUpper_of_subset_unitIntervalLaws (P := ⟨P, hP.1⟩) subset_rfl
    (Identification.mem_unitIntervalLaws_iff.2 hP.2) hpμ).trans
    (Relations.kInfUpper_unitIntervalLaws_le_dInf_unitLaws ⟨P, hP.1⟩ μ)

/-- [INC-P006, Proposition `prop:kinf`(iii), upper bound] For `p = m(P) ≤ μ < 1`,
`𝒦_inf(P, μ) ≤ log ((1 - p) / (1 - μ))`. -/
lemma dInf_unitLaws_le_ofReal_log (hP : P ∈ unitLaws) (hpμ : P[id] ≤ μ) (hμ : μ < 1) :
    dInf unitLaws P μ ≤ ENNReal.ofReal (Real.log ((1 - P[id]) / (1 - μ))) := by
  -- For `u ∈ (u₀, 1)`, `u₀ = (μ - p) / (1 - p)`, the mixture `(1 - u) P + u δ_1` is a competitor
  -- with `KL(P ‖ ·) ≤ log (1 / (1 - u))`; let `u ↓ u₀`.
  have := hP.1
  set p := P[id] with hp
  have hp1 : p < 1 := hpμ.trans_lt hμ
  have hp1' : 0 < 1 - p := sub_pos.2 hp1
  set u₀ := (μ - p) / (1 - p) with hu₀
  have hu₀1 : u₀ < 1 := by rw [hu₀, div_lt_one hp1']; linarith
  -- the bound at each `u ∈ (u₀, 1)`
  have hbound : ∀ u ∈ Set.Ioo u₀ 1,
      dInf unitLaws P μ ≤ ENNReal.ofReal (Real.log (1 - u)⁻¹) := by
    intro u hu
    have hu0 : 0 ≤ u := (div_nonneg (sub_nonneg.2 hpμ) hp1'.le).trans hu.1.le
    set v : ℝ≥0 := ⟨u, hu0⟩
    have hv1 : v < 1 := by
      rw [← NNReal.coe_lt_coe]
      exact hu.2
    have hmean : μ < ((1 - v) • P + v • Measure.dirac (1 : ℝ))[id] := by
      rw [integral_id_smul_add_smul_dirac_one hP hv1.le]
      change μ < (1 - u) * p + u
      have := (div_lt_iff₀ hp1').1 hu.1
      linarith
    calc dInf unitLaws P μ ≤ klDiv P ((1 - v) • P + v • Measure.dirac (1 : ℝ)) :=
          dInf_le (smul_add_smul_dirac_one_mem_unitLaws hP hv1.le) hmean
      _ ≤ ENNReal.ofReal (-Real.log ((1 - v : ℝ≥0) : ℝ)) :=
          Incognita.klDiv_le_ofReal_neg_log_smul_add_smul _ hv1
      _ = ENNReal.ofReal (Real.log (1 - u)⁻¹) := by
          rw [NNReal.coe_sub hv1.le, Real.log_inv]
          rfl
  -- the limit `u ↓ u₀`
  have hlim : Tendsto (fun u ↦ ENNReal.ofReal (Real.log (1 - u)⁻¹)) (𝓝[>] u₀)
      (𝓝 (ENNReal.ofReal (Real.log ((1 - p) / (1 - μ))))) := by
    have hval : (1 - u₀)⁻¹ = (1 - p) / (1 - μ) := by
      rw [hu₀, one_sub_div hp1'.ne', inv_div]
      ring_nf
    rw [← hval]
    have hc : ContinuousAt (fun u ↦ Real.log (1 - u)⁻¹) u₀ :=
      ((continuous_const.sub continuous_id).continuousAt.inv₀ (sub_pos.2 hu₀1).ne').log
        (inv_pos.2 (sub_pos.2 hu₀1)).ne'
    exact ((ENNReal.continuous_ofReal.tendsto _).comp hc.tendsto).mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT hu₀1] with u hu
  exact hbound u hu

/-- [INC-P006, Proposition `prop:kinf`(iv)] `𝒦_inf(Ber(p), μ) = kl(p, μ)` for `p ≤ μ < 1`: the lower
bound is `klBer_le_dInf_unitLaws`, and the Bernoulli laws are competitors
(LMLExplore's `dInf_range_bernoulliMeasure`). -/
lemma dInf_unitLaws_bernoulliMeasure {p : I} (hpμ : (p : ℝ) ≤ μ) (hμ : μ < 1) :
    dInf unitLaws Ber((1 : ℝ), 0, p) μ = klBer p μ := by
  have hmean : Ber((1 : ℝ), 0, p)[id] = (p : ℝ) :=
    TauCeti.Probability.integral_id_bernoulliMeasure _
  refine le_antisymm ?_ ?_
  · rw [← dInf_range_bernoulliMeasure hpμ hμ]
    exact dInf_anti (Set.range_subset_iff.2 bernoulliMeasure_mem_unitLaws) _ _
  · simpa [hmean] using
      klBer_le_dInf_unitLaws (bernoulliMeasure_mem_unitLaws p) (hmean.trans_le hpμ)

end Incognita.BatchedBandits
