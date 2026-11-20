/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.HY.Events
public import Incognita.BatchedBandits.HY.Ranks

/-! # The batches lost on the failure event when `x > 1`

[INC-P000, Lemmas `lem:probasA` and `lem:sumsA`(b)] for the failure event `ℱ` of
Definition `def:evA` read on the run, in the form that the inequality (eq:DA) of
`hyAlg_ae_pullCount_le_max_add` uses: `ℱ^c` is the conjunction of the traces of `𝒜` at two batch
ends, of `𝒱^c` and of `Π^c` at the test.

* `measure_not_accurate_and_not_rejected_le`: the probability of the trace of `ℱ` is at most the
  sum of the bounds of Lemma `lem:probasA`(a)–(b) for its four pieces, for every learner.
* `sum_batch_mul_measure_not_accurate_and_not_rejected_le`: the whole batches charged to `ℱ` cost a
  finite amount, `∑_ℓ B_(ℓ+4) P(ℱ_ℓ) ≤ (c / 2) e^S + C σ_(4β)(η)` (the last sum of the paper's
  (eq:main2A), Lemma `lem:sumsA`(b)), under (R3) and the growth `L_(ℓ+4) ≤ x₊³ L_(ℓ+1)` of
  Lemma `lem:ranksA`.

Indices: as in `hyAlg_ae_pullCount_le_max_add`, the test at `t_(ℓ+3)` is the paper's test at
`t_ℓ`, the previous one is at `t_(ℓ+2)`, and the batch lost on `ℱ` has length
`B_(ℓ+4) = t_(ℓ+4) - t_(ℓ+3)`.
-/

@[expose] public section

open Learning Finset MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace Incognita.BatchedBandits

variable {α : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- [INC-P000, Lemma `lem:probasA`(a)–(b), for the failure event `ℱ` on the run] For every learner
on an instance `ν` of `𝒫`, every grid and net exponent `β`, a test at `t_(ℓ+3)`, an accuracy
`ε > 0` with `m⋆ + ε < 1`, an optimal arm `a'`, a level `m₂` with `m₂ + ε ≥ 0` and the gain
condition `2η (m₂ + ε) ≤ m⋆ - (m₂ + ε)` (`η ≥ 0`), tilts `θ_c ≥ 0` of the sub-optimal arms with the
moment conditions of Lemma `lem:pair` at the level `m⋆ + ε` and the mean level `m⋆ - 3ε`
(Lemma `lem:constA`(c)), and `z > 0`: the probability that the trace of `ℱ^c` fails (some
well-sampled arm has an inaccurate mean at `t_(ℓ+2)` or `t_(ℓ+3)`, or `a'` is wrongly rejected, or
some rejected sub-optimal arm has a mean that climbs) is at most
`K p_𝒜(U_(ℓ+2)) + K p_𝒜(U_(ℓ+3)) + C(m₂ + ε) U³ e^(-(1+2η)z) + K C(m⋆ + ε) U⁴ e^(-(1+2η)z)`, with
`p_𝒜(U) = 2 e^(-ε² U) / (1 - e^(-2ε²))`, `U = U_(ℓ+3)` and `C(r) = (4 + 2κ(r)) e^(2(1+2η))`. -/
lemma measure_not_accurate_and_not_rejected_le {alg : Algorithm Unit α ℝ} {ν : Kernel α ℝ}
    [IsMarkovKernel ν] (hν : ν ∈ unitBandits α) {K : ℕ} (g : Grid K) (β : ℝ) (ℓ : ℕ)
    {ε m₂ z η : ℝ} (a' : α)
    (θc : α → ℝ) (hε : 0 < ε) (hz : 0 < z) (hη : 0 ≤ η)
    (ha' : (∫ y, id y ∂(ν a')) = ⨆ b, ∫ y, id y ∂(ν b))
    (hmε : (⨆ b, ∫ y, id y ∂(ν b)) + ε < 1) (hm₂0 : 0 ≤ m₂ + ε)
    (hηr : 2 * η * (m₂ + ε) ≤ (⨆ b, ∫ y, id y ∂(ν b)) - (m₂ + ε))
    (hθ : ∀ c, (∫ y, id y ∂(ν c)) < ⨆ b, ∫ y, id y ∂(ν b) → 0 ≤ θc c)
    (hΦ : ∀ c, (∫ y, id y ∂(ν c)) < ⨆ b, ∫ y, id y ∂(ν b) →
      Real.exp (2 * η * Real.log (1 / (1 - ((⨆ b, ∫ y, id y ∂(ν b)) + ε)))) *
        ∫ y, Real.exp (θc c * (y - ((⨆ b, ∫ y, id y ∂(ν b)) - 3 * ε))) ∂(ν c) ≤ 1)
    (hΨ : ∀ c, (∫ y, id y ∂(ν c)) < ⨆ b, ∫ y, id y ∂(ν b) →
      Real.exp (2 * η * Real.log (1 / (1 - ((⨆ b, ∫ y, id y ∂(ν b)) + ε)))) *
        ∫ y, (1 - y) * Real.exp (θc c * (y - ((⨆ b, ∫ y, id y ∂(ν b)) - 3 * ε))) ∂(ν c) ≤
          1 - ((⨆ b, ∫ y, id y ∂(ν b)) + ε)) :
    trajMeasure alg (Environment.bandit ν) {ω | ¬ ((∀ j, ℓ + 2 ≤ j → j ≤ ℓ + 3 → ∀ c,
        g.netSize β j ≤ 2 * pullCount IT.action c (g.t j) ω →
        |HY.pseudoMean 0 (history IT.obs IT.action IT.feedback (g.t j) ω) (g.t j) c -
          ∫ y, id y ∂(ν c)| ≤ ε) ∧
      ¬ (2 * pullCount IT.action a' (g.t (ℓ + 3)) ω < g.netSize β (ℓ + 3) ∧
        ENNReal.ofReal z ≤ (pullCount IT.action a' (g.t (ℓ + 2)) ω : ℝ≥0∞) *
          HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback (g.t (ℓ + 2)) ω)
            (g.t (ℓ + 2)) a' (m₂ + ε)) ∧
      (∀ c, (∫ y, id y ∂(ν c)) < ⨆ b, ∫ y, id y ∂(ν b) →
        ¬ (2 * pullCount IT.action c (g.t (ℓ + 3)) ω < g.netSize β (ℓ + 3) ∧
          ENNReal.ofReal z ≤ (pullCount IT.action c (g.t (ℓ + 2)) ω : ℝ≥0∞) *
            HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback (g.t (ℓ + 2)) ω)
              (g.t (ℓ + 2)) c ((⨆ b, ∫ y, id y ∂(ν b)) + ε) ∧
          (⨆ b, ∫ y, id y ∂(ν b)) - 3 * ε ≤
            HY.pseudoMean 0 (history IT.obs IT.action IT.feedback (g.t (ℓ + 3)) ω)
              (g.t (ℓ + 3)) c)))} ≤
      Fintype.card α * ENNReal.ofReal (2 * Real.exp (-(ε ^ 2 * g.netSize β (ℓ + 2))) /
          (1 - Real.exp (-(2 * ε ^ 2)))) +
        Fintype.card α * ENNReal.ofReal (2 * Real.exp (-(ε ^ 2 * g.netSize β (ℓ + 3))) /
          (1 - Real.exp (-(2 * ε ^ 2)))) +
        ENNReal.ofReal ((4 + 2 * Real.log (1 / (1 - (m₂ + ε)))) * Real.exp (2 * (1 + 2 * η)) *
          g.netSize β (ℓ + 3) ^ 3 * Real.exp (-(1 + 2 * η) * z)) +
        Fintype.card α * ENNReal.ofReal ((4 + 2 * Real.log (1 / (1 - ((⨆ b, ∫ y, id y ∂(ν b)) +
          ε)))) * Real.exp (2 * (1 + 2 * η)) * g.netSize β (ℓ + 3) ^ 4 *
            Real.exp (-(1 + 2 * η) * z)) := by
  set ms := ⨆ b, ∫ y, id y ∂(ν b) with hms
  set μ := trajMeasure alg (Environment.bandit ν)
  -- the four pieces of `ℱ`
  set SA : ℕ → Set (ℕ → Round Unit α ℝ) := fun j ↦ {ω | ∃ c, g.netSize β j ≤
    2 * pullCount IT.action c (g.t j) ω ∧
    ε < |HY.pseudoMean 0 (history IT.obs IT.action IT.feedback (g.t j) ω) (g.t j) c -
      ∫ y, id y ∂(ν c)|} with hSA
  set SV : Set (ℕ → Round Unit α ℝ) := {ω |
    2 * pullCount IT.action a' (g.t (ℓ + 3)) ω < g.netSize β (ℓ + 3) ∧
    ENNReal.ofReal z ≤ (pullCount IT.action a' (g.t (ℓ + 2)) ω : ℝ≥0∞) *
      HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback (g.t (ℓ + 2)) ω)
        (g.t (ℓ + 2)) a' (m₂ + ε)} with hSV
  set SP : α → Set (ℕ → Round Unit α ℝ) := fun c ↦ {ω | 2 * pullCount IT.action c (g.t (ℓ + 3)) ω <
      g.netSize β (ℓ + 3) ∧
    ENNReal.ofReal z ≤ (pullCount IT.action c (g.t (ℓ + 2)) ω : ℝ≥0∞) *
      HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback (g.t (ℓ + 2)) ω)
        (g.t (ℓ + 2)) c (ms + ε) ∧
    ms - 3 * ε ≤ HY.pseudoMean 0 (history IT.obs IT.action IT.feedback (g.t (ℓ + 3)) ω)
      (g.t (ℓ + 3)) c} with hSP
  set sub := Finset.univ.filter fun c ↦ (∫ y, id y ∂(ν c)) < ms
  refine (measure_mono (t := SA (ℓ + 2) ∪ SA (ℓ + 3) ∪ SV ∪ ⋃ c ∈ sub, SP c) ?_).trans ?_
  · intro ω hω
    rw [Set.mem_ofPred_eq] at hω
    by_contra hne
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hne
    obtain ⟨⟨⟨h2, h3⟩, hV⟩, hP⟩ := hne
    refine hω ⟨fun j hj1 hj2 c hc ↦ ?_, hV, fun c hc hPc ↦ hP c ?_ hPc⟩
    · rcases (show j = ℓ + 2 ∨ j = ℓ + 3 by omega) with rfl | rfl
      · exact not_lt.mp fun hlt ↦ h2 ⟨c, hc, hlt⟩
      · exact not_lt.mp fun hlt ↦ h3 ⟨c, hc, hlt⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩
  -- the bounds of Lemma `lem:probasA`(a)–(b) for each piece
  have hst : g.t (ℓ + 2) ≤ g.t (ℓ + 3) := g.strictMono.monotone (by omega)
  have hA : ∀ j, μ (SA j) ≤ Fintype.card α * ENNReal.ofReal
      (2 * Real.exp (-(ε ^ 2 * g.netSize β j)) / (1 - Real.exp (-(2 * ε ^ 2)))) :=
    fun j ↦ measure_exists_wellSampled_abs_sub_gt_le hν (g.t j) (g.one_le_netSize β j) hε
  have hr0 : 0 ≤ 2 * η * (m₂ + ε) := mul_nonneg (mul_nonneg zero_le_two hη) hm₂0
  have hV := measure_lt_mul_pseudoKinf_le (alg := alg) hν hst a' hm₂0 (by linarith)
    hη (by rw [ha']; exact hηr) hz (g.netSize β (ℓ + 3))
  have hms0 : 0 ≤ ms + ε := by
    have := (integral_id_mem_Icc_of_mem_unitLaws (hν.1 a')).1
    rw [ha'] at this
    linarith
  have hP : μ (⋃ c ∈ sub, SP c) ≤ Fintype.card α * ENNReal.ofReal
      ((4 + 2 * Real.log (1 / (1 - (ms + ε)))) * Real.exp (2 * (1 + 2 * η)) *
        g.netSize β (ℓ + 3) ^ 4 * Real.exp (-(1 + 2 * η) * z)) := by
    set X := (4 + 2 * Real.log (1 / (1 - (ms + ε)))) * Real.exp (2 * (1 + 2 * η)) *
        (g.netSize β (ℓ + 3) : ℝ) ^ 4 * Real.exp (-(1 + 2 * η) * z)
    have hle : ∀ c ∈ sub, μ (SP c) ≤ ENNReal.ofReal X := fun c hc ↦ by
      have hc' := (Finset.mem_filter.mp hc).2
      exact measure_lt_mul_pseudoKinf_and_le_le hν hst c hms0 hmε (hθ c hc') hη (hΦ c hc')
        (hΨ c hc') hz _
    calc μ (⋃ c ∈ sub, SP c) ≤ ∑ c ∈ sub, μ (SP c) := measure_biUnion_finset_le sub SP
      _ ≤ ∑ c ∈ sub, ENNReal.ofReal X := Finset.sum_le_sum hle
      _ = sub.card * ENNReal.ofReal X := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := by gcongr; exact_mod_cast Finset.card_le_univ sub
  calc μ (SA (ℓ + 2) ∪ SA (ℓ + 3) ∪ SV ∪ ⋃ c ∈ sub, SP c)
      ≤ μ (SA (ℓ + 2)) + μ (SA (ℓ + 3)) + μ SV + μ (⋃ c ∈ sub, SP c) := by
        calc _ ≤ μ (SA (ℓ + 2) ∪ SA (ℓ + 3) ∪ SV) + μ (⋃ c ∈ sub, SP c) := measure_union_le _ _
          _ ≤ μ (SA (ℓ + 2) ∪ SA (ℓ + 3)) + μ SV + μ (⋃ c ∈ sub, SP c) := by
            gcongr; exact measure_union_le _ _
          _ ≤ _ := by gcongr; exact measure_union_le _ _
    _ ≤ _ := by gcongr <;> exact hA _

/-- [INC-P000, Lemma `lem:sumsA`(b), for the failure event on the run] For every learner on an
instance `ν` of `𝒫`, every grid and net exponent `β ≥ 1`, an accuracy `ε > 0`, a gain `η > 0` and
the other constants of `measure_not_accurate_and_not_rejected_le`, levels `z_ℓ > 0` with (R3)
`(1 + 2η) z_ℓ ≥ (1 + η) L_(ℓ+4)` (so that `e^(-(1+2η) z_ℓ) ≤ t_(ℓ+4)^(-(1+η))`), the growth
`L_(ℓ+4) ≤ x₊³ L_(ℓ+1)` (Lemma `lem:ranksA`) on `[k₀, L)`, and `S ≥ 2 x₊³ y - ε² y^β` for every
`y ≥ 0` (the paper's `S'_ε`): the whole batches charged to the failure event cost
`∑_(k₀ ≤ ℓ < L) B_(ℓ+4) P(ℱ_ℓ) ≤ (c / 2) e^S + C σ_(4β)(η)`, with `c = 4K / (1 - e^(-2ε²))`
(the paper's `2 c_𝒜(ε)`) and `C = (1 + K) C(m⋆ + ε)`, `C(r) = (4 + 2κ(r)) e^(2(1+2η))` (the paper's
`(1 + K) C_η`). The batch `B_(ℓ+4) = t_(ℓ+4) - t_(ℓ+3)` follows the test at `t_(ℓ+3)`, as in
`hyAlg_ae_pullCount_le_max_add`. -/
lemma sum_batch_mul_measure_not_accurate_and_not_rejected_le {alg : Algorithm Unit α ℝ}
    {ν : Kernel α ℝ} [IsMarkovKernel ν] (hν : ν ∈ unitBandits α) {K : ℕ} (g : Grid K) {β : ℝ}
    (hβ : 1 ≤ β) {ε m₂ η xp S : ℝ} (z : ℕ → ℝ) (a' : α) (θc : α → ℝ) (hε : 0 < ε) (hη : 0 < η)
    (ha' : (∫ y, id y ∂(ν a')) = ⨆ b, ∫ y, id y ∂(ν b))
    (hmε : (⨆ b, ∫ y, id y ∂(ν b)) + ε < 1) (hm₂0 : 0 ≤ m₂ + ε)
    (hηr : 2 * η * (m₂ + ε) ≤ (⨆ b, ∫ y, id y ∂(ν b)) - (m₂ + ε))
    (hθ : ∀ c, (∫ y, id y ∂(ν c)) < ⨆ b, ∫ y, id y ∂(ν b) → 0 ≤ θc c)
    (hΦ : ∀ c, (∫ y, id y ∂(ν c)) < ⨆ b, ∫ y, id y ∂(ν b) →
      Real.exp (2 * η * Real.log (1 / (1 - ((⨆ b, ∫ y, id y ∂(ν b)) + ε)))) *
        ∫ y, Real.exp (θc c * (y - ((⨆ b, ∫ y, id y ∂(ν b)) - 3 * ε))) ∂(ν c) ≤ 1)
    (hΨ : ∀ c, (∫ y, id y ∂(ν c)) < ⨆ b, ∫ y, id y ∂(ν b) →
      Real.exp (2 * η * Real.log (1 / (1 - ((⨆ b, ∫ y, id y ∂(ν b)) + ε)))) *
        ∫ y, (1 - y) * Real.exp (θc c * (y - ((⨆ b, ∫ y, id y ∂(ν b)) - 3 * ε))) ∂(ν c) ≤
          1 - ((⨆ b, ∫ y, id y ∂(ν b)) + ε))
    {k₀ L : ℕ} (hz : ∀ ℓ ∈ Finset.Ico k₀ L, 0 < z ℓ)
    (hR3 : ∀ ℓ ∈ Finset.Ico k₀ L, (1 + η) * g.logEnd (ℓ + 4) ≤ (1 + 2 * η) * z ℓ)
    (hxp : ∀ ℓ ∈ Finset.Ico k₀ L, g.logEnd (ℓ + 4) ≤ xp ^ 3 * g.logEnd (ℓ + 1))
    (hS : ∀ y : ℝ, 0 ≤ y → 2 * xp ^ 3 * y - ε ^ 2 * y ^ β ≤ S) :
    ∑ ℓ ∈ Finset.Ico k₀ L, ((g.t (ℓ + 4) : ℝ) - g.t (ℓ + 3)) *
      (trajMeasure alg (Environment.bandit ν) {ω | ¬ ((∀ j, ℓ + 2 ≤ j → j ≤ ℓ + 3 → ∀ c,
          g.netSize β j ≤ 2 * pullCount IT.action c (g.t j) ω →
          |HY.pseudoMean 0 (history IT.obs IT.action IT.feedback (g.t j) ω) (g.t j) c -
            ∫ y, id y ∂(ν c)| ≤ ε) ∧
        ¬ (2 * pullCount IT.action a' (g.t (ℓ + 3)) ω < g.netSize β (ℓ + 3) ∧
          ENNReal.ofReal (z ℓ) ≤ (pullCount IT.action a' (g.t (ℓ + 2)) ω : ℝ≥0∞) *
            HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback (g.t (ℓ + 2)) ω)
              (g.t (ℓ + 2)) a' (m₂ + ε)) ∧
        (∀ c, (∫ y, id y ∂(ν c)) < ⨆ b, ∫ y, id y ∂(ν b) →
          ¬ (2 * pullCount IT.action c (g.t (ℓ + 3)) ω < g.netSize β (ℓ + 3) ∧
            ENNReal.ofReal (z ℓ) ≤ (pullCount IT.action c (g.t (ℓ + 2)) ω : ℝ≥0∞) *
              HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback (g.t (ℓ + 2)) ω)
                (g.t (ℓ + 2)) c ((⨆ b, ∫ y, id y ∂(ν b)) + ε) ∧
            (⨆ b, ∫ y, id y ∂(ν b)) - 3 * ε ≤
              HY.pseudoMean 0 (history IT.obs IT.action IT.feedback (g.t (ℓ + 3)) ω)
                (g.t (ℓ + 3)) c)))}).toReal ≤
      4 * Fintype.card α / (1 - Real.exp (-(2 * ε ^ 2))) / 2 * Real.exp S +
        (1 + Fintype.card α) * ((4 + 2 * Real.log (1 / (1 - ((⨆ b, ∫ y, id y ∂(ν b)) + ε)))) *
          Real.exp (2 * (1 + 2 * η))) *
          (2 / η * Real.exp (η / 2) * (2 * (4 * β) / (Real.exp 1 * η)) ^ (4 * β)) := by
  set ms := ⨆ b, ∫ y, id y ∂(ν b) with hms
  set D := 1 - Real.exp (-(2 * ε ^ 2)) with hD
  have hD0 : 0 < D := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith))
  set κ := Real.log (1 / (1 - (ms + ε))) with hκ
  set Cη := (4 + 2 * κ) * Real.exp (2 * (1 + 2 * η)) with hCη
  have hr0 : 0 ≤ 2 * η * (m₂ + ε) := mul_nonneg (mul_nonneg zero_le_two hη.le) hm₂0
  have hκ₂0 : 0 ≤ Real.log (1 / (1 - (m₂ + ε))) :=
    Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
  have hκ₂ : Real.log (1 / (1 - (m₂ + ε))) ≤ κ :=
    Real.log_le_log (one_div_pos.mpr (by linarith)) (one_div_le_one_div_of_le (by linarith)
      (by linarith))
  have hCη0 : 0 ≤ Cη := mul_nonneg (by linarith) (Real.exp_pos _).le
  set c := 4 * (Fintype.card α : ℝ) / D with hc
  have hc0 : 0 ≤ c := div_nonneg (by positivity) hD0.le
  set C := (1 + (Fintype.card α : ℝ)) * Cη with hC
  have hC0 : 0 ≤ C := mul_nonneg (by positivity) hCη0
  have hxp' : ∀ i ∈ Finset.Ico (k₀ + 3) (L + 3), g.logEnd (i + 1) ≤ xp ^ 3 * g.logEnd (i - 2) := by
    intro i hi
    obtain ⟨ℓ, rfl⟩ : ∃ ℓ, i = ℓ + 3 := ⟨i - 3, by simp only [Finset.mem_Ico] at hi; omega⟩
    have hℓ : ℓ ∈ Finset.Ico k₀ L := by simp only [Finset.mem_Ico] at hi ⊢; omega
    simpa only [show ℓ + 3 - 2 = ℓ + 1 by omega] using hxp ℓ hℓ
  have key := g.sum_batch_mul_le hβ hη hC0 hc0 (k₀ := k₀ + 3) (L := L + 3)
    (a := fun i ↦ c * Real.exp (-(ε ^ 2 * g.logEnd (i - 2) ^ β)))
    (v := fun i ↦ C * (g.netSize β i : ℝ) ^ 4 * (g.t (i + 1) : ℝ) ^ (-(1 + η)))
    (by omega) (fun _ _ ↦ le_rfl) (fun _ _ ↦ le_rfl) hxp' hS
  have hre := Finset.sum_Ico_add' (fun i ↦ ((g.t (i + 1) : ℝ) - g.t i) *
    (c * Real.exp (-(ε ^ 2 * g.logEnd (i - 2) ^ β)) +
      C * (g.netSize β i : ℝ) ^ 4 * (g.t (i + 1) : ℝ) ^ (-(1 + η)))) k₀ L 3
  refine le_trans ?_ (hre.trans_le key)
  refine Finset.sum_le_sum fun ℓ hℓ ↦ ?_
  have hB : 0 ≤ (g.t (ℓ + 4) : ℝ) - g.t (ℓ + 3) :=
    sub_nonneg.mpr (by exact_mod_cast (g.strictMono (show ℓ + 3 < ℓ + 4 by omega)).le)
  refine mul_le_mul_of_nonneg_left ?_ hB
  -- the bound of `measure_not_accurate_and_not_rejected_le`, term by term
  have hM := measure_not_accurate_and_not_rejected_le (alg := alg) hν g β ℓ a' θc hε (hz ℓ hℓ)
    hη.le ha' hmε hm₂0 hηr hθ hΦ hΨ
  set U := (g.netSize β (ℓ + 3) : ℝ) with hU
  have hU1 : 1 ≤ U := by rw [hU]; exact_mod_cast g.one_le_netSize β (ℓ + 3)
  set E := Real.exp (-(ε ^ 2 * g.logEnd (ℓ + 1) ^ β)) with hE
  set X := Real.exp (-(1 + 2 * η) * z ℓ) with hX
  set T := (g.t (ℓ + 4) : ℝ) ^ (-(1 + η)) with hT
  have ht0 : (0 : ℝ) < g.t (ℓ + 4) := by
    exact_mod_cast (show 0 < g.t (ℓ + 4) by have := g.two_le_t (show 1 ≤ ℓ + 4 by omega); omega)
  have hXT : X ≤ T := by
    rw [hX, hT, Real.rpow_def_of_pos ht0, Real.exp_le_exp]
    have := hR3 ℓ hℓ
    unfold Grid.logEnd at this
    linarith
  -- the means: `U_(ℓ+2) ≥ L_(ℓ+1)^β` and `U_(ℓ+3) ≥ L_(ℓ+2)^β ≥ L_(ℓ+1)^β`
  have hUj : ∀ j, ℓ + 2 ≤ j → g.logEnd (ℓ + 1) ^ β ≤ g.netSize β j := by
    intro j hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [g.netSize_succ β (by omega)]
    refine le_trans ?_ (Nat.le_ceil _)
    exact Real.rpow_le_rpow (g.logEnd_nonneg _) (g.logEnd_monotone (by omega)) (by linarith)
  have hEj : ∀ j, ℓ + 2 ≤ j → Real.exp (-(ε ^ 2 * g.netSize β j)) ≤ E := fun j hj ↦ by
    rw [hE, Real.exp_le_exp, neg_le_neg_iff]
    exact mul_le_mul_of_nonneg_left (hUj j hj) (sq_nonneg _)
  have e : ∀ x : ℝ, (Fintype.card α : ℝ≥0∞) * ENNReal.ofReal x =
      ENNReal.ofReal (Fintype.card α * x) := fun x ↦ by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  have hA0 : ∀ j, 0 ≤ (Fintype.card α : ℝ) * (2 * Real.exp (-(ε ^ 2 * g.netSize β j)) / D) :=
    fun j ↦ mul_nonneg (Nat.cast_nonneg _) (div_nonneg (by positivity) hD0.le)
  have hV0 : 0 ≤ (4 + 2 * Real.log (1 / (1 - (m₂ + ε)))) * Real.exp (2 * (1 + 2 * η)) * U ^ 3 * X :=
    by positivity
  have hP0 : 0 ≤ (Fintype.card α : ℝ) * (Cη * U ^ 4 * X) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg hCη0 (by positivity)) (by positivity))
  have hsum0 : 0 ≤ c * E + C * U ^ 4 * T :=
    add_nonneg (mul_nonneg hc0 (Real.exp_pos _).le)
      (mul_nonneg (mul_nonneg hC0 (by positivity)) (Real.rpow_nonneg ht0.le _))
  refine ENNReal.toReal_le_of_le_ofReal ?_ (hM.trans ?_)
  · simpa only [show ℓ + 3 - 2 = ℓ + 1 by omega] using hsum0
  rw [e, e, e, ← ENNReal.ofReal_add (hA0 _) (hA0 _),
    ← ENNReal.ofReal_add (add_nonneg (hA0 _) (hA0 _)) hV0,
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg (hA0 _) (hA0 _)) hV0) hP0]
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [show ℓ + 3 - 2 = ℓ + 1 by omega]
  -- the real inequality
  have h2 := hEj (ℓ + 2) le_rfl
  have h3 := hEj (ℓ + 3) (by omega)
  have hA : (Fintype.card α : ℝ) * (2 * Real.exp (-(ε ^ 2 * g.netSize β (ℓ + 2))) / D) +
      (Fintype.card α : ℝ) * (2 * Real.exp (-(ε ^ 2 * g.netSize β (ℓ + 3))) / D) ≤ c * E := by
    have hK0 : (0 : ℝ) ≤ 2 * Fintype.card α / D := div_nonneg (by positivity) hD0.le
    calc _ = 2 * Fintype.card α / D * (Real.exp (-(ε ^ 2 * g.netSize β (ℓ + 2))) +
          Real.exp (-(ε ^ 2 * g.netSize β (ℓ + 3)))) := by ring
      _ ≤ 2 * Fintype.card α / D * (E + E) := by gcongr
      _ = c * E := by rw [hc]; ring
  have hU34 : U ^ 3 ≤ U ^ 4 := pow_le_pow_right₀ hU1 (by norm_num)
  have hV : (4 + 2 * Real.log (1 / (1 - (m₂ + ε)))) * Real.exp (2 * (1 + 2 * η)) * U ^ 3 * X ≤
      Cη * U ^ 4 * T := by
    have hC₂ : (4 + 2 * Real.log (1 / (1 - (m₂ + ε)))) * Real.exp (2 * (1 + 2 * η)) ≤ Cη :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    exact mul_le_mul (mul_le_mul hC₂ hU34 (by positivity) hCη0) hXT (by positivity)
      (mul_nonneg hCη0 (by positivity))
  have hP : (Fintype.card α : ℝ) * (Cη * U ^ 4 * X) ≤ (Fintype.card α : ℝ) * (Cη * U ^ 4 * T) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hXT
      (mul_nonneg hCη0 (by positivity))) (Nat.cast_nonneg _)
  have hCT : Cη * U ^ 4 * T + (Fintype.card α : ℝ) * (Cη * U ^ 4 * T) = C * U ^ 4 * T := by
    rw [hC]; ring
  linarith

end Incognita.BatchedBandits
