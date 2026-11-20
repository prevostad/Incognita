/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.HY.GoodBatch

/-! # The decomposition of the counts of HY when `x > 1`, along a run

[INC-P000, Lemmas `lem:goodA` and `lem:decompA`(a)], along almost every run of HY, with the events
of Definition `def:evA` read on the run (their traces at the counts of the run; each trace is
implied by the paper's event on the stacks, since the empirical law of `c` at `t_j` is
`ν̂_(c, N_c(t_j))`).

* `hyAlg_ae_pullCount_le_max_of_good`: Lemma `lem:goodA` with its Step 1. On the trace of the good
  event `𝒢` (accurate means at three batch ends, no optimal arm wrongly rejected, no rejected
  sub-optimal arm whose mean climbs, the empirical divergence of `a` neither low nor high), the
  sub-optimal arm `a` follows its plan `K + (1 + ω) y log t / D` during the next batch. Step 1
  (the leader is optimal, the test levels are accurate, the counts of `a` are above the count
  threshold) comes from `hyAlg_ae_integral_leader_eq_iSup` and
  `hyAlg_ae_logEnd_div_log_le_pullCount`; Steps 2–4 are
  `hyAlg_ae_le_mul_testKinf_and_pullCount_le_max`.
* `hyAlg_ae_pullCount_le_max_add`: the inequality (eq:DA) of Lemma `lem:decompA`(a), `N_a(t)` is at
  most the largest of the past count, the plan and a net `2 U` charged to the failure of `𝒢`, plus
  the whole batch charged to the failure event `ℱ` (Cases 1–3 of the paper's proof).

Indices: the paper's test at `t_ℓ` (`ℓ ≥ 5`) is the Lean test at `t_(ℓ+3)`, and the paper's batch
`ℓ + 1` is the Lean batch of rounds `[t_(ℓ+3), t_(ℓ+4))`; the earlier batch ends are `t_(ℓ+2)`
(the previous test) and `t_(ℓ+1)`.
-/

@[expose] public section

open Learning Finset MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace Incognita.BatchedBandits

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α]

/-- [INC-P000, Lemma `lem:goodA`, along a run, with Step 1] Along almost every run of HY (`w₀ ≥ 0`,
on a grid for `K ≥ 2` arms) on an instance `ν` of `𝒫`, for the test at `t_(ℓ+3)` (the paper's
`t_ℓ`; `ℓ ≥ 1`), let the batches of Lean indices `ℓ, …, ℓ + 3` satisfy (R2) (the hypotheses of
`hyAlg_ae_pullCount_le_max_target_and_netSize_le_sub`, with `ω ≥ 0`), `γ_(ℓ+3) ≥ 0`, and let:
* `a'` be an optimal arm, `a` a sub-optimal arm, `m₂` a bound of the sub-optimal means, and
  `ε > 0` with the conditions of Lemma `lem:constA`(a) (`m⋆ + ε < 1`, `m₂ + ε < m⋆ - 2ε`,
  `m_c + ε < m⋆ - 3ε` for every sub-optimal `c`);
* `2 w₀ ≤ ε U_(ℓ+3)`, and a level `z` with
  `z + w₀ κ(m⋆ + ε) ≤ h̄_(ℓ+2) = (1 - γ_(ℓ+2)) y_(ℓ+1) L_(ℓ+2)` (the paper's `z_ℓ`);
* (T1) `κ_ε L_j^(β-1) ≥ 1` for `j = ℓ + 1, ℓ + 2`, with `κ_ε = κ(m⋆ + ε)`, and a count threshold
  `u ≤ L_(ℓ+1) / κ_ε` (the paper's `u_ℓ(ε)`) with (T3) `w₀ κ_ε ≤ ε u`;
* `D > 0` (the paper's `D_ε`) and `K⁺ ≥ 0` (the paper's `𝒦_inf(ν_a, m⋆ + ε)`) with the margin
  `K⁺ + 2ε ≤ (1 + ω_(ℓ+2)) D`, (T2) `D L_(ℓ+2)^(β-1) ≥ 2 x₊³` and (R1) `x_(ℓ+2), x_(ℓ+3) ≤ x₊`.
The trace of the good event `𝒢` on the run:
* `𝒜` at `t_(ℓ+1)`, `t_(ℓ+2)`, `t_(ℓ+3)`: every well-sampled arm has an empirical mean within `ε`
  of its mean;
* not `𝒱` and not `Π` at the test `t_(ℓ+3)` (as in `hyAlg_ae_integral_leader_eq_iSup`);
* not `ℒ`: not (`N_a(t_(ℓ+3)) ≥ u` and `𝒦_inf(ν̂_a(t_(ℓ+3)), m⋆ - 2ε) < D`);
* not `𝒰`: not (`N_a(t_(ℓ+2)) ≥ u` and `𝒦_inf(ν̂_a(t_(ℓ+2)), m⋆ + ε) > K⁺ + ε`).
Then every round `t ∈ [t_(ℓ+3), t_(ℓ+4)]` has
`N_a(t) ≤ max(N_a(t_(ℓ+3)), K + (1 + ω_(ℓ+3)) y_(ℓ+3) log t / D)`.

The paper's `𝒢_ℓ` also contains `𝒱_(ℓ-1)^c` and `Π_(ℓ-1)^c`; they only serve the claim that the
previous leader is optimal, which the bound does not use, and are not assumed. -/
lemma hyAlg_ae_pullCount_le_max_of_good (w₀ β : ℝ) (hw₀ : 0 ≤ w₀) (ωs θ γ : ℕ → ℝ)
    (g : Grid (Fintype.card α)) (hK : 2 ≤ Fintype.card α) {ν : Kernel α ℝ} [IsMarkovKernel ν]
    (hν : ν ∈ unitBandits α) :
    ∀ᵐ ω ∂(trajMeasure (hyAlg w₀ β ωs θ γ g : Algorithm Unit α ℝ) (Environment.bandit ν)),
      ∀ ℓ, ℓ ≠ 0 →
      (∀ j, ℓ ≤ j → j ≤ ℓ + 3 → 0 ≤ θ j ∧ 0 ≤ ωs j ∧ 2 ≤ g.imedEnd θ j ∧
        (2 * (Fintype.card α - 1 : ℕ) * g.netSize β (j + 1) : ℝ) ≤
          g.imedEnd θ j * Real.log (g.imedEnd θ j) ∧
        Fintype.card α * (g.netSize β (j + 1) + Fintype.card α) ≤ g.t (j + 1) - g.imedEnd θ j) →
      0 ≤ γ (ℓ + 3) →
      ∀ (ε m₂ z D Kp xp u : ℝ) (a' a : α), 0 < ε → 0 < D → 0 ≤ Kp →
      (∫ y, id y ∂(ν a')) = ⨆ b, ∫ y, id y ∂(ν b) →
      (∫ y, id y ∂(ν a)) < ⨆ b, ∫ y, id y ∂(ν b) →
      (∀ c, (∫ y, id y ∂(ν c)) < ⨆ b, ∫ y, id y ∂(ν b) → (∫ y, id y ∂(ν c)) ≤ m₂) →
      (⨆ b, ∫ y, id y ∂(ν b)) + ε < 1 →
      m₂ + ε < (⨆ b, ∫ y, id y ∂(ν b)) - 2 * ε →
      (∀ c, (∫ y, id y ∂(ν c)) < ⨆ b, ∫ y, id y ∂(ν b) →
        (∫ y, id y ∂(ν c)) + ε < (⨆ b, ∫ y, id y ∂(ν b)) - 3 * ε) →
      2 * w₀ ≤ ε * g.netSize β (ℓ + 3) →
      z + w₀ * Real.log (1 / (1 - ((⨆ b, ∫ y, id y ∂(ν b)) + ε))) ≤
        (1 - γ (ℓ + 2)) * g.ratio (ℓ + 1) ^ 2 * g.logEnd (ℓ + 2) →
      1 ≤ Real.log (1 / (1 - ((⨆ b, ∫ y, id y ∂(ν b)) + ε))) * g.logEnd (ℓ + 1) ^ (β - 1) →
      1 ≤ Real.log (1 / (1 - ((⨆ b, ∫ y, id y ∂(ν b)) + ε))) * g.logEnd (ℓ + 2) ^ (β - 1) →
      u ≤ g.logEnd (ℓ + 1) / Real.log (1 / (1 - ((⨆ b, ∫ y, id y ∂(ν b)) + ε))) →
      w₀ * Real.log (1 / (1 - ((⨆ b, ∫ y, id y ∂(ν b)) + ε))) ≤ ε * u →
      Kp + 2 * ε ≤ (1 + ωs (ℓ + 2)) * D →
      2 * xp ^ 3 ≤ D * g.logEnd (ℓ + 2) ^ (β - 1) → g.ratio (ℓ + 2) ≤ xp →
      g.ratio (ℓ + 3) ≤ xp →
      (∀ j, ℓ + 1 ≤ j → j ≤ ℓ + 3 → ∀ c, g.netSize β j ≤ 2 * pullCount IT.action c (g.t j) ω →
        |HY.pseudoMean 0 (history IT.obs IT.action IT.feedback (g.t j) ω) (g.t j) c -
          ∫ y, id y ∂(ν c)| ≤ ε) →
      ¬ (2 * pullCount IT.action a' (g.t (ℓ + 3)) ω < g.netSize β (ℓ + 3) ∧
        ENNReal.ofReal z ≤ (pullCount IT.action a' (g.t (ℓ + 2)) ω : ℝ≥0∞) *
          HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback (g.t (ℓ + 2)) ω) (g.t (ℓ + 2)) a'
            (m₂ + ε)) →
      (∀ c, (∫ y, id y ∂(ν c)) < ⨆ b, ∫ y, id y ∂(ν b) →
        ¬ (2 * pullCount IT.action c (g.t (ℓ + 3)) ω < g.netSize β (ℓ + 3) ∧
          ENNReal.ofReal z ≤ (pullCount IT.action c (g.t (ℓ + 2)) ω : ℝ≥0∞) *
            HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback (g.t (ℓ + 2)) ω) (g.t (ℓ + 2)) c
              ((⨆ b, ∫ y, id y ∂(ν b)) + ε) ∧
          (⨆ b, ∫ y, id y ∂(ν b)) - 3 * ε ≤
            HY.pseudoMean 0 (history IT.obs IT.action IT.feedback (g.t (ℓ + 3)) ω) (g.t (ℓ + 3))
              c)) →
      ¬ (u ≤ pullCount IT.action a (g.t (ℓ + 3)) ω ∧
        HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback (g.t (ℓ + 3)) ω) (g.t (ℓ + 3)) a
          ((⨆ b, ∫ y, id y ∂(ν b)) - 2 * ε) < ENNReal.ofReal D) →
      ¬ (u ≤ pullCount IT.action a (g.t (ℓ + 2)) ω ∧
        ENNReal.ofReal (Kp + ε) <
          HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback (g.t (ℓ + 2)) ω) (g.t (ℓ + 2)) a
            ((⨆ b, ∫ y, id y ∂(ν b)) + ε)) →
      ∀ t, g.t (ℓ + 3) ≤ t → t ≤ g.t (ℓ + 4) →
        (pullCount IT.action a t ω : ℝ) ≤ max (pullCount IT.action a (g.t (ℓ + 3)) ω : ℝ)
          (Fintype.card α + (1 + ωs (ℓ + 3)) * g.ratio (ℓ + 3) ^ 2 * Real.log t / D) := by
  filter_upwards [hyAlg_ae_integral_leader_eq_iSup w₀ β hw₀ ωs θ γ g hK hν,
    hyAlg_ae_logEnd_div_log_le_pullCount w₀ β hw₀ ωs θ γ g hK hν,
    hyAlg_ae_le_mul_testKinf_and_pullCount_le_max w₀ β hw₀ ωs θ γ g hK hν] with ω hLead hCnt hGood
  intro ℓ hℓ hR hγ ε m₂ z D Kp xp u a' a hε hD hKp ha' ha hm₂ hmε hm₂ε hsub hw₀U hz hT1₁ hT1₂ hu
    hT3 hmarg hT2 hx2 hx3 hA hV hPi hLo hUp
  set ms := ⨆ b, ∫ y, id y ∂(ν b) with hms
  set κ := Real.log (1 / (1 - (ms + ε))) with hκ
  -- `0 ≤ m⋆ - 2ε`: the mean of `a` is nonnegative and at most `m₂`
  have hma0 : 0 ≤ ∫ y, id y ∂(ν a) := (integral_id_mem_Icc_of_mem_unitLaws (hν.1 a)).1
  have hms2 : 0 ≤ ms - 2 * ε := by linarith [hm₂ a ha]
  -- Step 1: Lemma `lem:leaderA` at the test `t_(ℓ+3)`
  obtain ⟨⟨-, -, hμlo, hμhi⟩, -, hlead, hμprev⟩ := hLead (ℓ + 1) (by omega)
    (fun j h1 h2 ↦ hR j (by omega) (by omega)) ε m₂ z a' hε ha' hm₂ hmε hm₂ε hsub hw₀U hz
    (fun j h1 h2 ↦ hA j (by omega) (by omega)) hV hPi
  -- Step 1: Lemma `lem:countsA`, the counts of `a` at `t_(ℓ+2)` and `t_(ℓ+3)` are at least `u`
  have hAup : ∀ j, ℓ + 1 ≤ j → j ≤ ℓ + 3 → ∀ c,
      g.netSize β j ≤ 2 * pullCount IT.action c (g.t j) ω →
      HY.pseudoMean 0 (history IT.obs IT.action IT.feedback (g.t j) ω) (g.t j) c ≤
        (∫ y, id y ∂(ν c)) + ε :=
    fun j h1 h2 c hc ↦ by linarith [(abs_le.mp (hA j h1 h2 c hc)).2]
  have hκpos : 0 < κ := by
    by_contra hneg
    push Not at hneg
    have : κ * g.logEnd (ℓ + 1) ^ (β - 1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hneg (Real.rpow_nonneg (g.logEnd_pos (by omega)).le _)
    linarith
  have hN₂ : u ≤ pullCount IT.action a (g.t (ℓ + 2)) ω :=
    hu.trans (hCnt ℓ hℓ (fun j h1 h2 ↦ hR j h1 (by omega)) ε hmε hT1₁
      (hAup (ℓ + 1) le_rfl (by omega)) a)
  have hN₃ : u ≤ pullCount IT.action a (g.t (ℓ + 3)) ω := by
    have h := hCnt (ℓ + 1) (by omega) (fun j h1 h2 ↦ hR j (by omega) (by omega)) ε hmε hT1₂
      (hAup (ℓ + 2) (by omega) (by omega)) a
    refine hu.trans (le_trans ?_ h)
    exact div_le_div_of_nonneg_right (g.logEnd_monotone (by omega)) hκpos.le
  -- Step 1: outside `ℒ` and `𝒰`, at these counts; (T3) at the count `N_a(t_(ℓ+2))`
  have hLo' := not_lt.mp fun h ↦ hLo ⟨hN₃, h⟩
  have hUp' := not_lt.mp fun h ↦ hUp ⟨hN₂, h⟩
  have hT3' : w₀ * κ ≤ ε * pullCount IT.action a (g.t (ℓ + 2)) ω :=
    hT3.trans (mul_le_mul_of_nonneg_left hN₂ hε.le)
  -- Steps 2–4: Lemma `lem:goodA` at the test `t_(ℓ+3)`
  exact (hGood (ℓ + 2) (by omega) (fun j h1 h2 ↦ hR j (by omega) (by omega)) hγ ε D Kp xp a hε
    hD hKp ha hlead hμlo hμhi hμprev hms2 hmε hLo' hUp' hT3' hmarg hT2 hx2 hx3).2

open scoped Classical in
/-- [INC-P000, Lemma `lem:decompA`(a), (eq:DA), along a run] Along almost every run of HY
(`w₀ ≥ 0`, on a grid for `K ≥ 2` arms) on an instance `ν` of `𝒫`, for the test at `t_(ℓ+3)` (the
paper's `t_ℓ`) and two accuracies `ε`, `ε'`: assume the hypotheses of
`hyAlg_ae_pullCount_le_max_of_good` at the accuracy `ε`, and at the accuracy `ε' > 0` the
conditions of Lemma `lem:constA`(a) (`m⋆ + ε' < 1`, `m₂ + ε' < m⋆ - 2ε'`, `m_c + ε' < m⋆ - 3ε'`
for every sub-optimal `c`), `2 w₀ ≤ ε' U_(ℓ+3)`, `z + w₀ κ(m⋆ + ε') ≤ h̄_(ℓ+2)` and (T4)
`K + 1 + 8 x₊² L_(ℓ+4) / ε'² ≤ U_(ℓ+4)`. Let `𝒢` be the trace on the run of the good event at the
accuracy `ε` (the hypotheses on the run of `hyAlg_ae_pullCount_le_max_of_good`), and `ℱ^c` that
of the complement of the failure event at the accuracy `ε'` (`𝒜` at `t_(ℓ+2)` and `t_(ℓ+3)`, not
`𝒱` and not `Π` at the test `t_(ℓ+3)`). Then every round `t ∈ [t_(ℓ+3), t_(ℓ+4)]` has
`N_a(t) ≤ max(N_a(t_(ℓ+3)), K + (1 + ω_(ℓ+3)) y_(ℓ+3) log t / D, 2 U_(ℓ+4) 1(𝒢^c))
  + (t - t_(ℓ+3)) 1(ℱ)`.

The three cases of the paper's proof: on `𝒢`, `hyAlg_ae_pullCount_le_max_of_good`; on
`𝒢^c ∩ ℱ^c`, the leader is optimal and `K̃(a) ≥ ε'² / 8` (`hyAlg_ae_integral_leader_eq_iSup` at
the accuracy `ε'`), so `a` receives at most a net (`hyAlg_ae_net_le`); on `ℱ`, the whole batch
(`pullCount_le_add_sub`). -/
lemma hyAlg_ae_pullCount_le_max_add (w₀ β : ℝ) (hw₀ : 0 ≤ w₀) (ωs θ γ : ℕ → ℝ)
    (g : Grid (Fintype.card α)) (hK : 2 ≤ Fintype.card α) {ν : Kernel α ℝ} [IsMarkovKernel ν]
    (hν : ν ∈ unitBandits α) :
    ∀ᵐ ω ∂(trajMeasure (hyAlg w₀ β ωs θ γ g : Algorithm Unit α ℝ) (Environment.bandit ν)),
      ∀ ℓ, ℓ ≠ 0 →
      (∀ j, ℓ ≤ j → j ≤ ℓ + 3 → 0 ≤ θ j ∧ 0 ≤ ωs j ∧ 2 ≤ g.imedEnd θ j ∧
        (2 * (Fintype.card α - 1 : ℕ) * g.netSize β (j + 1) : ℝ) ≤
          g.imedEnd θ j * Real.log (g.imedEnd θ j) ∧
        Fintype.card α * (g.netSize β (j + 1) + Fintype.card α) ≤ g.t (j + 1) - g.imedEnd θ j) →
      0 ≤ γ (ℓ + 3) →
      ∀ (ε ε' m₂ z D Kp xp u : ℝ) (a' a : α), 0 < ε → 0 < ε' → 0 < D → 0 ≤ Kp →
      (∫ y, id y ∂(ν a')) = ⨆ b, ∫ y, id y ∂(ν b) →
      (∫ y, id y ∂(ν a)) < ⨆ b, ∫ y, id y ∂(ν b) →
      (∀ c, (∫ y, id y ∂(ν c)) < ⨆ b, ∫ y, id y ∂(ν b) → (∫ y, id y ∂(ν c)) ≤ m₂) →
      -- the constants at the accuracy `ε` (the good event)
      (⨆ b, ∫ y, id y ∂(ν b)) + ε < 1 →
      m₂ + ε < (⨆ b, ∫ y, id y ∂(ν b)) - 2 * ε →
      (∀ c, (∫ y, id y ∂(ν c)) < ⨆ b, ∫ y, id y ∂(ν b) →
        (∫ y, id y ∂(ν c)) + ε < (⨆ b, ∫ y, id y ∂(ν b)) - 3 * ε) →
      2 * w₀ ≤ ε * g.netSize β (ℓ + 3) →
      z + w₀ * Real.log (1 / (1 - ((⨆ b, ∫ y, id y ∂(ν b)) + ε))) ≤
        (1 - γ (ℓ + 2)) * g.ratio (ℓ + 1) ^ 2 * g.logEnd (ℓ + 2) →
      1 ≤ Real.log (1 / (1 - ((⨆ b, ∫ y, id y ∂(ν b)) + ε))) * g.logEnd (ℓ + 1) ^ (β - 1) →
      1 ≤ Real.log (1 / (1 - ((⨆ b, ∫ y, id y ∂(ν b)) + ε))) * g.logEnd (ℓ + 2) ^ (β - 1) →
      u ≤ g.logEnd (ℓ + 1) / Real.log (1 / (1 - ((⨆ b, ∫ y, id y ∂(ν b)) + ε))) →
      w₀ * Real.log (1 / (1 - ((⨆ b, ∫ y, id y ∂(ν b)) + ε))) ≤ ε * u →
      Kp + 2 * ε ≤ (1 + ωs (ℓ + 2)) * D →
      2 * xp ^ 3 ≤ D * g.logEnd (ℓ + 2) ^ (β - 1) → g.ratio (ℓ + 2) ≤ xp →
      g.ratio (ℓ + 3) ≤ xp →
      -- the constants at the accuracy `ε'` (the failure event)
      (⨆ b, ∫ y, id y ∂(ν b)) + ε' < 1 →
      m₂ + ε' < (⨆ b, ∫ y, id y ∂(ν b)) - 2 * ε' →
      (∀ c, (∫ y, id y ∂(ν c)) < ⨆ b, ∫ y, id y ∂(ν b) →
        (∫ y, id y ∂(ν c)) + ε' < (⨆ b, ∫ y, id y ∂(ν b)) - 3 * ε') →
      2 * w₀ ≤ ε' * g.netSize β (ℓ + 3) →
      z + w₀ * Real.log (1 / (1 - ((⨆ b, ∫ y, id y ∂(ν b)) + ε'))) ≤
        (1 - γ (ℓ + 2)) * g.ratio (ℓ + 1) ^ 2 * g.logEnd (ℓ + 2) →
      Fintype.card α + 1 + 8 * xp ^ 2 * g.logEnd (ℓ + 4) / ε' ^ 2 ≤ g.netSize β (ℓ + 4) →
      ∀ t, g.t (ℓ + 3) ≤ t → t ≤ g.t (ℓ + 4) →
        (pullCount IT.action a t ω : ℝ) ≤
          max (max (pullCount IT.action a (g.t (ℓ + 3)) ω : ℝ)
            (Fintype.card α + (1 + ωs (ℓ + 3)) * g.ratio (ℓ + 3) ^ 2 * Real.log t / D))
            (if (∀ j, ℓ + 1 ≤ j → j ≤ ℓ + 3 → ∀ c,
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
                      (g.t (ℓ + 3)) c)) ∧
              ¬ (u ≤ pullCount IT.action a (g.t (ℓ + 3)) ω ∧
                HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback (g.t (ℓ + 3)) ω)
                  (g.t (ℓ + 3)) a ((⨆ b, ∫ y, id y ∂(ν b)) - 2 * ε) < ENNReal.ofReal D) ∧
              ¬ (u ≤ pullCount IT.action a (g.t (ℓ + 2)) ω ∧
                ENNReal.ofReal (Kp + ε) <
                  HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback (g.t (ℓ + 2)) ω)
                    (g.t (ℓ + 2)) a ((⨆ b, ∫ y, id y ∂(ν b)) + ε))
            then 0 else (2 * g.netSize β (ℓ + 4) : ℝ)) +
          (if (∀ j, ℓ + 2 ≤ j → j ≤ ℓ + 3 → ∀ c,
                g.netSize β j ≤ 2 * pullCount IT.action c (g.t j) ω →
                |HY.pseudoMean 0 (history IT.obs IT.action IT.feedback (g.t j) ω) (g.t j) c -
                  ∫ y, id y ∂(ν c)| ≤ ε') ∧
              ¬ (2 * pullCount IT.action a' (g.t (ℓ + 3)) ω < g.netSize β (ℓ + 3) ∧
                ENNReal.ofReal z ≤ (pullCount IT.action a' (g.t (ℓ + 2)) ω : ℝ≥0∞) *
                  HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback (g.t (ℓ + 2)) ω)
                    (g.t (ℓ + 2)) a' (m₂ + ε')) ∧
              (∀ c, (∫ y, id y ∂(ν c)) < ⨆ b, ∫ y, id y ∂(ν b) →
                ¬ (2 * pullCount IT.action c (g.t (ℓ + 3)) ω < g.netSize β (ℓ + 3) ∧
                  ENNReal.ofReal z ≤ (pullCount IT.action c (g.t (ℓ + 2)) ω : ℝ≥0∞) *
                    HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback (g.t (ℓ + 2)) ω)
                      (g.t (ℓ + 2)) c ((⨆ b, ∫ y, id y ∂(ν b)) + ε') ∧
                  (⨆ b, ∫ y, id y ∂(ν b)) - 3 * ε' ≤
                    HY.pseudoMean 0 (history IT.obs IT.action IT.feedback (g.t (ℓ + 3)) ω)
                      (g.t (ℓ + 3)) c))
            then 0 else ((t - g.t (ℓ + 3) : ℕ) : ℝ)) := by
  filter_upwards [hyAlg_ae_pullCount_le_max_of_good w₀ β hw₀ ωs θ γ g hK hν,
    hyAlg_ae_integral_leader_eq_iSup w₀ β hw₀ ωs θ γ g hK hν,
    hyAlg_ae_net_le w₀ β hw₀ ωs θ γ g hK hν] with ω hGood hLead hNet
  intro ℓ hℓ hR hγ ε ε' m₂ z D Kp xp u a' a hε hε' hD hKp ha' ha hm₂ hmε hm₂ε hsub hw₀U hz hT1₁
    hT1₂ hu hT3 hmarg hT2 hx2 hx3 hmε' hm₂ε' hsub' hw₀U' hz' hT4 t ht1 ht2
  split_ifs with hG hF hF
  -- Case 1: on `𝒢`, the plan
  · rw [add_zero]
    exact (hGood ℓ hℓ hR hγ ε m₂ z D Kp xp u a' a hε hD hKp ha' ha hm₂ hmε hm₂ε hsub hw₀U hz
      hT1₁ hT1₂ hu hT3 hmarg hT2 hx2 hx3 hG.1 hG.2.1 hG.2.2.1 hG.2.2.2.1 hG.2.2.2.2 t ht1
      ht2).trans (le_max_left _ _)
  -- Case 3: on `ℱ`, the whole batch
  · have h := pullCount_le_add_sub (A := IT.action) (ω := ω) a ht1
    have h' : (pullCount IT.action a t ω : ℝ) ≤
        (pullCount IT.action a (g.t (ℓ + 3)) ω : ℝ) + ((t - g.t (ℓ + 3) : ℕ) : ℝ) := by
      exact_mod_cast h
    exact h'.trans (add_le_add_left ((le_max_left _ _).trans (le_max_left _ _)) _)
  -- Case 2: on `𝒢^c ∩ ℱ^c`, the net
  · rw [add_zero]
    obtain ⟨-, hsubK, hlead, -⟩ := hLead (ℓ + 1) (by omega)
      (fun j h1 h2 ↦ hR j (by omega) (by omega)) ε' m₂ z a' hε' ha' hm₂ hmε' hm₂ε' hsub' hw₀U'
      hz' hF.1 hF.2.1 hF.2.2
    have haL : a ≠ HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t (ℓ + 3)) ω)
        (g.t (ℓ + 3)) := by
      intro he
      rw [he] at ha
      exact ha.ne hlead
    obtain ⟨-, hK8, hKt⟩ := hsubK a ha
    obtain ⟨hθ, hω, hσ2, hσU, hlong⟩ := hR (ℓ + 3) (by omega) le_rfl
    have h := hNet (ℓ + 3) (by omega) hθ hω hσ2 hσU hlong ε' xp a hε' haL (hK8.trans hKt) hx3 hT4
      t ht1 ht2
    have h'' : pullCount IT.action a t ω ≤
        max (pullCount IT.action a (g.t (ℓ + 3)) ω) (2 * g.netSize β (ℓ + 4)) := h
    have h' : (pullCount IT.action a t ω : ℝ) ≤
        max (pullCount IT.action a (g.t (ℓ + 3)) ω : ℝ) (2 * g.netSize β (ℓ + 4) : ℕ) := by
      exact_mod_cast h''
    exact h'.trans (max_le_max (le_max_left _ _) (by push_cast; rfl))
  -- on `𝒢^c ∩ ℱ`: the whole batch
  · have h := pullCount_le_add_sub (A := IT.action) (ω := ω) a ht1
    have h' : (pullCount IT.action a t ω : ℝ) ≤
        (pullCount IT.action a (g.t (ℓ + 3)) ω : ℝ) + ((t - g.t (ℓ + 3) : ℕ) : ℝ) := by
      exact_mod_cast h
    exact h'.trans (add_le_add_left ((le_max_left _ _).trans (le_max_left _ _)) _)

end Incognita.BatchedBandits
