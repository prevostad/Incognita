/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.HY.Structure

/-! # A good batch of HY when `x > 1`

[INC-P000, Lemma `lem:goodA`], along almost every run of HY: in a good batch the sub-optimal arm
`a` is rejected at the test and is pulled at most according to its plan
`K + (1 + ω_ℓ) y_ℓ log t / D_ε` during the next batch.

* `hyAlg_ae_goodA`: Steps 2–4 of the paper's proof, along almost every run, with the facts of its
  Step 1 as hypotheses: they are the conclusions of `hyAlg_ae_leaderA` (the leaders are optimal,
  the test levels are accurate), of `hyAlg_ae_countsA` (the counts of `a` are above the count
  threshold), and the traces on the run of the events `ℒ_ℓ^c` and `𝒰_ℓ^c` at these counts
  (Definition `def:evA`), with the condition (T3) at these counts.

[INC-P000, Lemma `lem:decompA`], its pieces:
* (a), the three cases of (eq:DA) along a run: Case 1 is `hyAlg_ae_goodA`; Case 2,
  `hyAlg_ae_net_le` (an arm other than the leader with `K̃ ≥ ε'² / 8` receives at most a net
  `2 U_(ℓ+1)`); Case 3, `pullCount_le_add_sub` (the whole batch).
* (b), `le_max_add_sum_of_step`: the iteration of (eq:DA) over the batches, for any real sequence.

[INC-P000, Lemma `lem:goodhigh`] (the case `x = 1`), Step 2: `card_filter_lt_le_card`, at most `K`
high batches have a leader poorly observed at their start.

Indices: the paper's test at `t_ℓ` and batch `ℓ + 1` are the test at `t_(ℓ+1)` and the batch of
Lean index `ℓ + 1` (rounds `[t_(ℓ+1), t_(ℓ+2))`); the previous test is at `t_ℓ`.
-/

@[expose] public section

open Learning Finset MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace Incognita.BatchedBandits

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α]

/-- [INC-P000, Lemma `lem:goodA`, along a run] Along almost every run of HY (`w₀ ≥ 0`, on a grid
for `K ≥ 2` arms) on an instance `ν` of `𝒫`, let the batches of Lean indices `ℓ` and `ℓ + 1`
(`ℓ ≥ 1`) satisfy (R2) (the hypotheses of `hyAlg_ae_structA`, with `ω ≥ 0`), `γ_(ℓ+1) ≥ 0`, and
let `a` be a sub-optimal arm, `ε > 0`, `D = D_ε > 0` and `K⁺ = 𝒦_inf(ν_a, m⋆ + ε) ≥ 0` (so that
`K⁺ + 2ε` is the paper's `K_ε⁺`) with:
* (Step 1, `hyAlg_ae_leaderA`) the leader `ĉ_(ℓ+1)` is optimal,
  `m⋆ - 2ε ≤ μ̂_(ℓ+1) ≤ m⋆ + ε`, `μ̂_ℓ ≤ m⋆ + ε`, `0 ≤ m⋆ - 2ε` and `m⋆ + ε < 1`;
* (Step 1, `ℒ^c`) `𝒦_inf(ν̂_a(t_(ℓ+1)), m⋆ - 2ε) ≥ D`;
* (Step 1, `𝒰^c` and (T3)) `𝒦_inf(ν̂_a(t_ℓ), m⋆ + ε) ≤ K⁺ + ε` and
  `w₀ κ(m⋆ + ε) ≤ ε N_a(t_ℓ)`;
* (the margin) `K⁺ + 2ε ≤ (1 + ω_ℓ) D`;
* ((T2), (R1)) `D L_ℓ^(β-1) ≥ 2 x₊³`, `x_ℓ ≤ x₊` and `x_(ℓ+1) ≤ x₊`.
Then `a` is rejected at `t_(ℓ+1)` (`K̂_(ℓ+1)(a) > 0` and
`N_a(t_(ℓ+1)) K̂_(ℓ+1)(a) ≥ h̄_(ℓ+1) = (1 - γ_(ℓ+1)) y_ℓ L_(ℓ+1)`), `K̂_(ℓ+1)(a) ≥ D`, and every
round `t ∈ [t_(ℓ+1), t_(ℓ+2)]` has
`N_a(t) ≤ max(N_a(t_(ℓ+1)), K + (1 + ω_(ℓ+1)) y_(ℓ+1) log t / D)`.
-/
lemma hyAlg_ae_goodA (w₀ β : ℝ) (hw₀ : 0 ≤ w₀) (ωs θ γ : ℕ → ℝ)
    (g : Grid (Fintype.card α)) (hK : 2 ≤ Fintype.card α) {ν : Kernel α ℝ} [IsMarkovKernel ν]
    (hν : ν ∈ unitBandits α) :
    ∀ᵐ ω ∂(trajMeasure (hyAlg w₀ β ωs θ γ g : Algorithm Unit α ℝ) (Environment.bandit ν)),
      ∀ ℓ, ℓ ≠ 0 →
      (∀ j, ℓ ≤ j → j ≤ ℓ + 1 → 0 ≤ θ j ∧ 0 ≤ ωs j ∧ 2 ≤ g.imedEnd θ j ∧
        (2 * (Fintype.card α - 1 : ℕ) * g.netSize β (j + 1) : ℝ) ≤
          g.imedEnd θ j * Real.log (g.imedEnd θ j) ∧
        Fintype.card α * (g.netSize β (j + 1) + Fintype.card α) ≤ g.t (j + 1) - g.imedEnd θ j) →
      0 ≤ γ (ℓ + 1) →
      ∀ (ε D Kp xp : ℝ) (a : α), 0 < ε → 0 < D → 0 ≤ Kp →
      (∫ y, id y ∂(ν a)) < ⨆ b, ∫ y, id y ∂(ν b) →
      (∫ y, id y ∂(ν (HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t (ℓ + 1)) ω)
        (g.t (ℓ + 1))))) = ⨆ b, ∫ y, id y ∂(ν b) →
      (⨆ b, ∫ y, id y ∂(ν b)) - 2 * ε ≤
        HY.pseudoMean w₀ (history IT.obs IT.action IT.feedback (g.t (ℓ + 1)) ω) (g.t (ℓ + 1))
          (HY.reference w₀ (history IT.obs IT.action IT.feedback (g.t (ℓ + 1)) ω) (g.t (ℓ + 1))
            (g.netSize β (ℓ + 1))) →
      HY.pseudoMean w₀ (history IT.obs IT.action IT.feedback (g.t (ℓ + 1)) ω) (g.t (ℓ + 1))
          (HY.reference w₀ (history IT.obs IT.action IT.feedback (g.t (ℓ + 1)) ω) (g.t (ℓ + 1))
            (g.netSize β (ℓ + 1))) ≤ (⨆ b, ∫ y, id y ∂(ν b)) + ε →
      HY.pseudoMean w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ)
          (HY.reference w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ)
            (g.netSize β ℓ)) ≤ (⨆ b, ∫ y, id y ∂(ν b)) + ε →
      0 ≤ (⨆ b, ∫ y, id y ∂(ν b)) - 2 * ε → (⨆ b, ∫ y, id y ∂(ν b)) + ε < 1 →
      ENNReal.ofReal D ≤ HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback (g.t (ℓ + 1)) ω)
        (g.t (ℓ + 1)) a ((⨆ b, ∫ y, id y ∂(ν b)) - 2 * ε) →
      HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) a
        ((⨆ b, ∫ y, id y ∂(ν b)) + ε) ≤ ENNReal.ofReal (Kp + ε) →
      w₀ * Real.log (1 / (1 - ((⨆ b, ∫ y, id y ∂(ν b)) + ε))) ≤
        ε * pullCount IT.action a (g.t ℓ) ω →
      Kp + 2 * ε ≤ (1 + ωs ℓ) * D →
      2 * xp ^ 3 ≤ D * g.logEnd ℓ ^ (β - 1) → g.ratio ℓ ≤ xp → g.ratio (ℓ + 1) ≤ xp →
      ((0 < HY.testKinf w₀ (history IT.obs IT.action IT.feedback (g.t (ℓ + 1)) ω) (g.t (ℓ + 1))
          (g.netSize β (ℓ + 1)) a ∧
        ENNReal.ofReal ((1 - γ (ℓ + 1)) * g.ratio ℓ ^ 2 * g.logEnd (ℓ + 1)) ≤
          (pullCount IT.action a (g.t (ℓ + 1)) ω : ℝ≥0∞) *
            HY.testKinf w₀ (history IT.obs IT.action IT.feedback (g.t (ℓ + 1)) ω) (g.t (ℓ + 1))
              (g.netSize β (ℓ + 1)) a) ∧
        ENNReal.ofReal D ≤ HY.testKinf w₀ (history IT.obs IT.action IT.feedback (g.t (ℓ + 1)) ω)
          (g.t (ℓ + 1)) (g.netSize β (ℓ + 1)) a) ∧
      ∀ t, g.t (ℓ + 1) ≤ t → t ≤ g.t (ℓ + 2) →
        (pullCount IT.action a t ω : ℝ) ≤ max (pullCount IT.action a (g.t (ℓ + 1)) ω : ℝ)
          (Fintype.card α + (1 + ωs (ℓ + 1)) * g.ratio (ℓ + 1) ^ 2 * Real.log t / D) := by
  filter_upwards [hyAlg_ae_structA w₀ β ωs θ γ g (Environment.bandit ν) hK,
    hyAlg_ae_structA_S3 w₀ β ωs θ γ g (Environment.bandit ν) hK,
    hyAlg_ae_threshold_eq w₀ β ωs θ γ g (Environment.bandit ν) hK,
    hyAlg_ae_pullCount_le_max' w₀ β hw₀ ωs θ γ g hν,
    hyAlg_ae_one_le_pullCount w₀ β ωs θ γ g (Environment.bandit ν),
    ae_feedback_mem_Icc (alg := hyAlg w₀ β ωs θ γ g) hν] with ω hS hS3 hThr hImed hN1 hfb
  intro ℓ hℓ hR hγ ε D Kp xp a hε hD hKp ha hlead hμ₁lo hμ₁hi hμ₀hi hms2 hmε hLo hUp hT3 hmarg
    hT2 hx0 hx1
  -- notation
  set ms := ⨆ b, ∫ y, id y ∂(ν b) with hms
  set h₀ := history IT.obs IT.action IT.feedback (g.t ℓ) ω with hh₀
  set h₁ := history IT.obs IT.action IT.feedback (g.t (ℓ + 1)) ω with hh₁
  have hfb₀ : ∀ i, (h₀ i).feedback ∈ Set.Icc (0 : ℝ) 1 := fun i ↦ hfb i
  have hfb₁ : ∀ i, (h₁ i).feedback ∈ Set.Icc (0 : ℝ) 1 := fun i ↦ hfb i
  set N₀ := pullCount IT.action a (g.t ℓ) ω with hN₀
  set N₁ := pullCount IT.action a (g.t (ℓ + 1)) ω with hN₁
  have hN₀1 : 1 ≤ N₀ := hN1 ℓ (by omega) a
  have hN₁1 : 1 ≤ N₁ := hN1 (ℓ + 1) (by omega) a
  have hc₀ : HY.count h₀ (g.t ℓ) a = N₀ := HY.count_history le_rfl a
  have hc₁ : HY.count h₁ (g.t (ℓ + 1)) a = N₁ := HY.count_history le_rfl a
  obtain ⟨hθ0, hω0, hσ0, hσU0, hlong0⟩ := hR ℓ le_rfl (by omega)
  obtain ⟨hθ1, hω1, hσ1, hσU1, hlong1⟩ := hR (ℓ + 1) (by omega) le_rfl
  have hωy0 : 0 ≤ (1 + ωs ℓ) * g.ratio ℓ ^ 2 := by positivity
  have hωy1 : 0 ≤ (1 + ωs (ℓ + 1)) * g.ratio (ℓ + 1) ^ 2 := by positivity
  have hratio : ∀ j, 1 ≤ g.ratio j := g.one_le_ratio
  have hLpos : 0 < g.logEnd ℓ := g.logEnd_pos (by omega)
  have hL1pos : 0 < g.logEnd (ℓ + 1) := g.logEnd_pos (by omega)
  -- the threshold of the test at `t_(ℓ+1)` is deterministic (Lemma `lem:thrA`)
  have hthr := hThr (ℓ + 1) (by omega) hθ0 hω0 hσ0 hσU0 hlong0
  simp only [Nat.add_sub_cancel] at hthr
  set μ₀ := HY.pseudoMean w₀ h₀ (g.t ℓ) (HY.reference w₀ h₀ (g.t ℓ) (g.netSize β ℓ)) with hμ₀
  set μ₁ := HY.pseudoMean w₀ h₁ (g.t (ℓ + 1))
    (HY.reference w₀ h₁ (g.t (ℓ + 1)) (g.netSize β (ℓ + 1))) with hμ₁
  have hμ₀0 : 0 ≤ μ₀ := HY.pseudoMean_nonneg' hw₀ hfb₀ _
  have hμ₁1 : μ₁ < 1 := by linarith
  -- Step 1, last item: `K̂_(ℓ+1)(a) ≥ D`
  have hpos₁ : 0 < (HY.count h₁ (g.t (ℓ + 1)) a : ℝ) + w₀ := by
    rw [hc₁]
    have : (1 : ℝ) ≤ N₁ := by exact_mod_cast hN₁1
    linarith
  have hK₁ : ENNReal.ofReal D ≤ HY.testKinf w₀ h₁ (g.t (ℓ + 1)) (g.netSize β (ℓ + 1)) a := by
    refine hLo.trans ((HY.pseudoKinf_mono le_rfl hms2 hμ₁lo hμ₁1 hfb₁).trans ?_)
    exact HY.pseudoKinf_zero_le hw₀ hμ₁1 (hms2.trans hμ₁lo) hfb₁ (by rw [hc₁]; exact hN₁1)
  -- Step 2: `N_a(t_(ℓ+1)) K̂_(ℓ+1)(a) ≥ y_ℓ L_(ℓ+1)`
  have hND : g.ratio ℓ ^ 2 * g.logEnd (ℓ + 1) ≤ N₁ * D := by
    by_cases hW : g.netSize β (ℓ + 1) ≤ 2 * N₁
    · -- `a` is well sampled: (T2) and (R1)
      have hU : g.logEnd ℓ ^ β ≤ g.netSize β (ℓ + 1) := by
        rw [g.netSize_succ β (by omega : 1 ≤ ℓ)]
        exact Nat.le_ceil _
      have hW' : (g.netSize β (ℓ + 1) : ℝ) ≤ 2 * N₁ := by exact_mod_cast hW
      have hLb : g.logEnd ℓ ^ β = g.logEnd ℓ * g.logEnd ℓ ^ (β - 1) := by
        rw [Real.rpow_sub_one hLpos.ne', mul_div_cancel₀ _ hLpos.ne']
      have hL1 : g.logEnd (ℓ + 1) = g.ratio (ℓ + 1) * g.logEnd ℓ := g.logEnd_succ_eq (by omega)
      have hx3 : g.ratio ℓ ^ 2 * g.ratio (ℓ + 1) ≤ xp ^ 3 := by
        have h0 : 0 ≤ g.ratio ℓ := (zero_le_one.trans (hratio ℓ))
        have h1 : 0 ≤ g.ratio (ℓ + 1) := (zero_le_one.trans (hratio (ℓ + 1)))
        calc g.ratio ℓ ^ 2 * g.ratio (ℓ + 1) ≤ xp ^ 2 * xp := by gcongr
          _ = xp ^ 3 := by ring
      calc g.ratio ℓ ^ 2 * g.logEnd (ℓ + 1)
          = g.ratio ℓ ^ 2 * g.ratio (ℓ + 1) * g.logEnd ℓ := by rw [hL1]; ring
        _ ≤ xp ^ 3 * g.logEnd ℓ := by gcongr
        _ ≤ (D * g.logEnd ℓ ^ (β - 1) / 2) * g.logEnd ℓ := by gcongr; linarith
        _ = g.logEnd ℓ ^ β / 2 * D := by rw [hLb]; ring
        _ ≤ N₁ * D := by gcongr; linarith
    · -- `a` is not well sampled: (S3) at `ℓ` and `𝒰^c`
      obtain ⟨-, -, hS3a⟩ := hS3 ℓ hℓ hθ0 hωy0 hσ0 hσU0 hlong0 _ _ _ rfl rfl (fun _ _ ↦ rfl) a
        (by omega)
      -- `K̂_ℓ(a) ≤ K⁺ + 2ε`
      have hK₀ : HY.testKinf w₀ h₀ (g.t ℓ) (g.netSize β ℓ) a ≤ ENNReal.ofReal (Kp + 2 * ε) := by
        have hmono : HY.testKinf w₀ h₀ (g.t ℓ) (g.netSize β ℓ) a ≤
            HY.pseudoKinf w₀ h₀ (g.t ℓ) a (ms + ε) :=
          HY.pseudoKinf_mono hw₀ hμ₀0 hμ₀hi hmε hfb₀
        have hmul := HY.mul_pseudoKinf_le hw₀ hmε (by linarith) hfb₀ (c := a) (r := g.t ℓ)
          (by rw [hc₀]; exact hN₀1)
        rw [hc₀] at hmul
        have hN₀r : (1 : ℝ) ≤ N₀ := by exact_mod_cast hN₀1
        have hprod : (N₀ : ℝ≥0∞) * HY.testKinf w₀ h₀ (g.t ℓ) (g.netSize β ℓ) a ≤
            (N₀ : ℝ≥0∞) * ENNReal.ofReal (Kp + 2 * ε) := by
          calc (N₀ : ℝ≥0∞) * HY.testKinf w₀ h₀ (g.t ℓ) (g.netSize β ℓ) a
              ≤ (N₀ : ℝ≥0∞) * HY.pseudoKinf w₀ h₀ (g.t ℓ) a (ms + ε) := by gcongr
            _ ≤ (N₀ : ℝ≥0∞) * HY.pseudoKinf 0 h₀ (g.t ℓ) a (ms + ε) +
                ENNReal.ofReal (w₀ * Real.log (1 / (1 - (ms + ε)))) := hmul
            _ ≤ (N₀ : ℝ≥0∞) * ENNReal.ofReal (Kp + ε) + ENNReal.ofReal (ε * N₀) := by
                gcongr
            _ = (N₀ : ℝ≥0∞) * ENNReal.ofReal (Kp + 2 * ε) := by
                rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
                  ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
                    (by positivity)]
                congr 1
                ring
        have hN₀0 : (N₀ : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show N₀ ≠ 0 by omega)
        exact (ENNReal.mul_le_mul_iff_right hN₀0 (ENNReal.natCast_ne_top N₀)).mp hprod
      have h1 : ENNReal.ofReal ((1 + ωs ℓ) * g.ratio ℓ ^ 2 * g.logEnd (ℓ + 1)) ≤
          ENNReal.ofReal (N₁ * (Kp + 2 * ε)) := by
        refine hS3a.trans ?_
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
        gcongr
      have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
      have h3 : (1 + ωs ℓ) * (g.ratio ℓ ^ 2 * g.logEnd (ℓ + 1)) ≤ (1 + ωs ℓ) * (N₁ * D) := by
        have : (N₁ : ℝ) * (Kp + 2 * ε) ≤ N₁ * ((1 + ωs ℓ) * D) :=
          mul_le_mul_of_nonneg_left hmarg (Nat.cast_nonneg _)
        nlinarith
      exact le_of_mul_le_mul_left h3 (by linarith)
  have hZ : ENNReal.ofReal (g.ratio ℓ ^ 2 * g.logEnd (ℓ + 1)) ≤
      (N₁ : ℝ≥0∞) * HY.testKinf w₀ h₁ (g.t (ℓ + 1)) (g.netSize β (ℓ + 1)) a := by
    refine (ENNReal.ofReal_le_ofReal hND).trans ?_
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    gcongr
  have hyL : 0 ≤ g.ratio ℓ ^ 2 * g.logEnd (ℓ + 1) := by positivity
  have hrejR : ENNReal.ofReal ((1 - γ (ℓ + 1)) * g.ratio ℓ ^ 2 * g.logEnd (ℓ + 1)) ≤
      (N₁ : ℝ≥0∞) * HY.testKinf w₀ h₁ (g.t (ℓ + 1)) (g.netSize β (ℓ + 1)) a := by
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hZ
    have : (1 - γ (ℓ + 1)) * g.ratio ℓ ^ 2 * g.logEnd (ℓ + 1) =
        (1 - γ (ℓ + 1)) * (g.ratio ℓ ^ 2 * g.logEnd (ℓ + 1)) := by ring
    rw [this]
    nlinarith
  have hDpos : (0 : ℝ≥0∞) < ENNReal.ofReal D := ENNReal.ofReal_pos.mpr hD
  have hrej : 0 < HY.testKinf w₀ h₁ (g.t (ℓ + 1)) (g.netSize β (ℓ + 1)) a ∧
      ENNReal.ofReal ((1 - γ (ℓ + 1)) * g.ratio ℓ ^ 2 * g.logEnd (ℓ + 1)) ≤
        (N₁ : ℝ≥0∞) * HY.testKinf w₀ h₁ (g.t (ℓ + 1)) (g.netSize β (ℓ + 1)) a :=
    ⟨hDpos.trans_le hK₁, hrejR⟩
  refine ⟨⟨hrej, hK₁⟩, fun t ht1 ht2 ↦ ?_⟩
  -- Step 3: the IMED phase
  have haL : a ≠ HY.leader w₀ h₁ (g.t (ℓ + 1)) := by
    intro he
    rw [← he] at hlead
    exact ha.ne hlead
  have hKt : ENNReal.ofReal D ≤ HY.imedKinf w₀ h₁ (g.t (ℓ + 1)) a :=
    hK₁.trans (HY.testKinf_le_imedKinf hw₀ hfb₁ hpos₁)
  have htℓ1 : 2 ≤ g.t (ℓ + 1) := g.two_le_t (by omega)
  have hσ : g.t (ℓ + 1) ≤ g.imedEnd θ (ℓ + 1) := g.t_le_imedEnd hθ1
  have hKpos : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hK1 : (1 : ℝ) ≤ Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hbound : ∀ u : ℕ, 2 ≤ u → u ≤ t →
      1 + g.ratio (ℓ + 1) ^ 2 * Real.log u / D ≤
        Fintype.card α + (1 + ωs (ℓ + 1)) * g.ratio (ℓ + 1) ^ 2 * Real.log t / D := by
    intro u hu2 hut
    have hlogu : 0 ≤ Real.log u := Real.log_nonneg (by exact_mod_cast (show 1 ≤ u by omega))
    have hlogut : Real.log u ≤ Real.log t :=
      Real.log_le_log (by exact_mod_cast (show 0 < u by omega)) (by exact_mod_cast hut)
    have : g.ratio (ℓ + 1) ^ 2 * Real.log u ≤
        (1 + ωs (ℓ + 1)) * g.ratio (ℓ + 1) ^ 2 * Real.log t := by
      have hy := sq_nonneg (g.ratio (ℓ + 1))
      calc g.ratio (ℓ + 1) ^ 2 * Real.log u ≤ g.ratio (ℓ + 1) ^ 2 * Real.log t := by gcongr
        _ ≤ (1 + ωs (ℓ + 1)) * (g.ratio (ℓ + 1) ^ 2 * Real.log t) :=
          le_mul_of_one_le_left (by positivity) (by linarith)
        _ = _ := by ring
    have := div_le_div_of_nonneg_right this hD.le
    linarith
  have hσT : g.imedEnd θ (ℓ + 1) ≤ g.t (ℓ + 1 + 1) := by
    have : 0 < Fintype.card α * (g.netSize β (ℓ + 1 + 1) + Fintype.card α) :=
      Nat.mul_pos (by omega) (by omega)
    omega
  by_cases htσ : t ≤ g.imedEnd θ (ℓ + 1)
  · have h3 := hImed (ℓ + 1) (by omega) a haL D hD hKt t ht1 htσ ht2
    exact h3.trans (max_le_max le_rfl (hbound t (htℓ1.trans ht1) le_rfl))
  -- Step 4: the paced phase
  obtain ⟨hS1, -, -⟩ := hS (ℓ + 1) (by omega) hθ1 hωy1 hσ1 hσU1 hlong1 _ _ _ rfl rfl
    (fun _ _ ↦ rfl)
  have h4 := hS1 a haL t (by omega) ht2
  have h3 := hImed (ℓ + 1) (by omega) a haL D hD hKt (g.imedEnd θ (ℓ + 1)) hσ le_rfl hσT
  have hthr' : (1 - γ (ℓ + 1)) * g.ratio (ℓ + 1 - 1) ^ 2 * (if ℓ + 1 = 1 then g.logEnd 1 else
      HY.threshold w₀ (g.logEnd (ℓ + 1)) (g.ratio (ℓ + 1 - 1) ^ 2) h₁ (g.t (ℓ + 1))
        (g.t (ℓ + 1 - 1)) (g.netSize β (ℓ + 1)) (g.netSize β (ℓ + 1 - 1))) =
      (1 - γ (ℓ + 1)) * g.ratio ℓ ^ 2 * g.logEnd (ℓ + 1) := by
    rw [ite_eq_right (by omega)]
    simp only [Nat.add_sub_cancel]
    rw [hthr]
  have hrej' := hrej
  rw [← hthr', ← hc₁] at hrej'
  have htgt := HY.target_le_of_rejected (ω' := ωs (ℓ + 1)) (y := g.ratio (ℓ + 1) ^ 2)
    (logt := Real.log t) (Unext := g.netSize β (ℓ + 1 + 1))
    (mul_nonneg hωy1 (Real.log_nonneg (by exact_mod_cast (show 1 ≤ t by omega)))) hD hrej' hK₁
  rcases le_max_iff.mp h4 with h5 | h5
  · have h5' := (Nat.cast_le (α := ℝ)).mpr h5
    exact h5'.trans (h3.trans (max_le_max le_rfl (hbound _ (htℓ1.trans hσ) (by omega))))
  · have h5' := (Nat.cast_le (α := ℝ)).mpr h5
    exact h5'.trans (htgt.trans (le_max_right _ _))

/-! ### The decomposition of the counts, Lemma `lem:decompA` -/

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- [INC-P000, proof of Lemma `lem:decompA`(a), Case 3] For any sequence of actions, an arm is
pulled at most once per round: `N_c(t) ≤ N_c(s) + (t - s)` for `s ≤ t`. -/
lemma pullCount_le_add_sub {Ω : Type*} {A : ℕ → Ω → α} {ω : Ω} (c : α) {s t : ℕ}
    (hst : s ≤ t) : pullCount A c t ω ≤ pullCount A c s ω + (t - s) := by
  induction t, hst using Nat.le_induction with
  | base => simp
  | succ t hst ih =>
    rw [pullCount_add_one]
    split_ifs <;> omega

/-- [INC-P000, proof of Lemma `lem:decompA`(a), Case 2, along a run] Along almost every run of HY
(`w₀ ≥ 0`, on a grid for `K ≥ 2` arms) on an instance of `𝒫`, for a batch `ℓ + 1` (`ℓ ≥ 1`)
satisfying the hypotheses of `hyAlg_ae_structA` with `ω_ℓ ≥ 0`, an arm `a` other than the leader
`ĉ_ℓ` with `K̃_ℓ(a) ≥ ε'² / 8` (Lemma `lem:leaderA`(ii) at the accuracy `ε'`) receives at most a
net: if (R1) `x_ℓ ≤ x₊` and (T4) `K + 1 + 8 x₊² L_(ℓ+1) / ε'² ≤ U_(ℓ+1)` hold, then
`N_a(t) ≤ max(N_a(t_ℓ), 2 U_(ℓ+1))` for every round `t ∈ [t_ℓ, t_(ℓ+1)]`. -/
lemma hyAlg_ae_net_le (w₀ β : ℝ) (hw₀ : 0 ≤ w₀) (ωs θ γ : ℕ → ℝ)
    (g : Grid (Fintype.card α)) (hK : 2 ≤ Fintype.card α) {ν : Kernel α ℝ} [IsMarkovKernel ν]
    (hν : ν ∈ unitBandits α) :
    ∀ᵐ ω ∂(trajMeasure (hyAlg w₀ β ωs θ γ g : Algorithm Unit α ℝ) (Environment.bandit ν)),
      ∀ ℓ, ℓ ≠ 0 → 0 ≤ θ ℓ → 0 ≤ ωs ℓ → 2 ≤ g.imedEnd θ ℓ →
      (2 * (Fintype.card α - 1 : ℕ) * g.netSize β (ℓ + 1) : ℝ) ≤
        g.imedEnd θ ℓ * Real.log (g.imedEnd θ ℓ) →
      Fintype.card α * (g.netSize β (ℓ + 1) + Fintype.card α) ≤ g.t (ℓ + 1) - g.imedEnd θ ℓ →
      ∀ (ε' xp : ℝ) (a : α), 0 < ε' →
      a ≠ HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) →
      ENNReal.ofReal (ε' ^ 2 / 8) ≤
        HY.imedKinf w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) a →
      g.ratio ℓ ≤ xp →
      Fintype.card α + 1 + 8 * xp ^ 2 * g.logEnd (ℓ + 1) / ε' ^ 2 ≤ g.netSize β (ℓ + 1) →
      ∀ t, g.t ℓ ≤ t → t ≤ g.t (ℓ + 1) →
        pullCount IT.action a t ω ≤
          max (pullCount IT.action a (g.t ℓ) ω) (2 * g.netSize β (ℓ + 1)) := by
  filter_upwards [hyAlg_ae_structA w₀ β ωs θ γ g (Environment.bandit ν) hK,
    hyAlg_ae_pullCount_le_max' w₀ β hw₀ ωs θ γ g hν] with ω hS hImed
  intro ℓ hℓ hθ hω0 hσ2 hσU hlong ε' xp a hε' haL hKt hx hT4 t ht1 ht2
  set U := g.netSize β (ℓ + 1) with hU
  have hD : 0 < ε' ^ 2 / 8 := by positivity
  have hσ : g.t ℓ ≤ g.imedEnd θ ℓ := g.t_le_imedEnd hθ
  have hσT : g.imedEnd θ ℓ ≤ g.t (ℓ + 1) := by
    have : 0 < Fintype.card α * (U + Fintype.card α) := Nat.mul_pos (by omega) (by omega)
    omega
  have htℓ : 2 ≤ g.t ℓ := g.two_le_t (by omega)
  have hratio : 1 ≤ g.ratio ℓ := g.one_le_ratio ℓ
  -- the IMED rounds: `N_a(u) ≤ max(N_a(t_ℓ), U)` for `u ≤ s_ℓ`
  have himed : ∀ u, g.t ℓ ≤ u → u ≤ g.imedEnd θ ℓ → u ≤ g.t (ℓ + 1) →
      pullCount IT.action a u ω ≤ max (pullCount IT.action a (g.t ℓ) ω) U := by
    intro u hu1 hu2 hu3
    have h := hImed ℓ hℓ a haL _ hD hKt u hu1 hu2 hu3
    have hlog : Real.log u ≤ g.logEnd (ℓ + 1) := by
      unfold Grid.logEnd
      exact Real.log_le_log (by exact_mod_cast (show 0 < u by omega)) (by exact_mod_cast hu3)
    have hlog0 : 0 ≤ Real.log u := Real.log_nonneg (by exact_mod_cast (show 1 ≤ u by omega))
    have hb : 1 + g.ratio ℓ ^ 2 * Real.log u / (ε' ^ 2 / 8) ≤ U := by
      have h1 : g.ratio ℓ ^ 2 * Real.log u ≤ xp ^ 2 * g.logEnd (ℓ + 1) := by
        have : g.ratio ℓ ^ 2 ≤ xp ^ 2 := pow_le_pow_left₀ (by linarith) hx 2
        exact mul_le_mul this hlog hlog0 (by nlinarith)
      have h2 : g.ratio ℓ ^ 2 * Real.log u / (ε' ^ 2 / 8) =
          8 * (g.ratio ℓ ^ 2 * Real.log u) / ε' ^ 2 := by field_simp
      rw [h2]
      have h3 : 8 * (g.ratio ℓ ^ 2 * Real.log u) / ε' ^ 2 ≤
          8 * xp ^ 2 * g.logEnd (ℓ + 1) / ε' ^ 2 := by
        rw [mul_assoc]
        gcongr
      have hK0 : (0 : ℝ) ≤ Fintype.card α := Nat.cast_nonneg _
      linarith
    have h' := h.trans (max_le_max le_rfl hb)
    exact_mod_cast h'
  by_cases htσ : t ≤ g.imedEnd θ ℓ
  · exact (himed t ht1 htσ ht2).trans (max_le_max le_rfl (by omega))
  -- the paced rounds: `N_a(t) ≤ max(N_a(s_ℓ), K - 1 + U)`
  have hωy : 0 ≤ (1 + ωs ℓ) * g.ratio ℓ ^ 2 := by positivity
  obtain ⟨hS1, -, -⟩ := hS ℓ hℓ hθ hωy hσ2 hσU hlong _ _ _ rfl rfl (fun _ _ ↦ rfl)
  have h1 := hS1 a haL t (by omega) ht2
  have h2 := himed (g.imedEnd θ ℓ) hσ le_rfl hσT
  have h3 := HY.target_le (w₀ := w₀) (thr := (1 - γ ℓ) * g.ratio (ℓ - 1) ^ 2 *
    (if ℓ = 1 then g.logEnd 1 else HY.threshold w₀ (g.logEnd ℓ) (g.ratio (ℓ - 1) ^ 2)
      (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) (g.t (ℓ - 1)) (g.netSize β ℓ)
      (g.netSize β (ℓ - 1)))) (ω' := ωs ℓ) (y := g.ratio ℓ ^ 2) (logt := Real.log t)
    (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) (g.netSize β ℓ) U a
  have hKU : Fintype.card α - 1 ≤ U := by
    have : (Fintype.card α : ℝ) ≤ U := by
      have : 0 ≤ 8 * xp ^ 2 * g.logEnd (ℓ + 1) / ε' ^ 2 := by
        have := (g.logEnd_pos (show 1 ≤ ℓ + 1 by omega)).le
        positivity
      linarith
    have : Fintype.card α ≤ U := by exact_mod_cast this
    omega
  rcases le_max_iff.mp h1 with h | h
  · exact h.trans (h2.trans (max_le_max le_rfl (by omega)))
  · exact h.trans (h3.trans (le_max_of_le_right (by omega)))

omit [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- [INC-P000, proof of Lemma `lem:goodhigh`, Step 2, abstract form] Let `S` be a finite set of
batches, `L i` an arm for each batch (the leader `ĉ_(i-1)`), `N c j` counts nondecreasing in `j`
(`N_c(t_j)`), and `u` a level such that the arm `L i` has `N (L i) i ≥ u` for every `i ∈ S`
(Step 1: the leader of a high batch is well observed at its end). Then at most `K` batches of
`S` have a leader poorly observed at their start (`N (L i) (i - 1) < u`): two such batches
`i < i'` with the same leader `c` would give `N_c(i' - 1) ≥ N_c(i) ≥ u`, so `i ↦ L i` is
injective on them. -/
lemma card_filter_lt_le_card {N : α → ℕ → ℕ} (hN : ∀ c, Monotone (N c)) {L : ℕ → α}
    {S : Finset ℕ} {u : ℕ} (hS : ∀ i ∈ S, u ≤ N (L i) i) :
    (S.filter fun i ↦ N (L i) (i - 1) < u).card ≤ Fintype.card α := by
  refine Finset.card_le_card_of_injOn L (fun _ _ ↦ Finset.mem_univ _) ?_
  intro i hi i' hi' hii'
  simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hi hi'
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have h1 := hS i hi.1
    have h2 : N (L i') i ≤ N (L i') (i' - 1) := hN _ (by omega)
    rw [← hii'] at h2
    exact absurd (h1.trans h2) (not_le.mpr (hii' ▸ hi'.2))
  · have h1 := hS i' hi'.1
    have h2 : N (L i) i' ≤ N (L i) (i - 1) := hN _ (by omega)
    rw [hii'] at h2
    exact absurd (h1.trans h2) (not_le.mpr (hii' ▸ hi.2))

/-- [INC-P000, Lemma `lem:decompA`(b), the iteration] A real sequence `N_k` (the counts
`N_a(t_k)`) with `N_(k+1) ≤ max(N_k, M, Y) + S_k` for `i₀ ≤ k < j` and `S_k ≥ 0` (the paper's
inequality (eq:DA) at `t = t_(k+1)`, with `M ≥ m_k(ε_k, t_(k+1))` the largest plan, `Y` an upper
bound of the nets `2 U_(k+1) 1(𝒢_k^c)` and `S_k = B_(k+1) 1(ℱ_k)`) satisfies
`N_k ≤ max(N_(i₀), M, Y) + ∑_(i₀ ≤ i < k) S_i` for `i₀ ≤ k ≤ j`, since
`max(p + s, q) ≤ max(p, q) + s` for `s ≥ 0`. -/
lemma le_max_add_sum_of_step {N S : ℕ → ℝ} {M Y : ℝ} {i₀ j : ℕ} (hS : ∀ k, 0 ≤ S k)
    (hstep : ∀ k, i₀ ≤ k → k < j → N (k + 1) ≤ max (max (N k) M) Y + S k) :
    ∀ k, i₀ ≤ k → k ≤ j → N k ≤ max (max (N i₀) M) Y + ∑ i ∈ Finset.Ico i₀ k, S i := by
  intro k hk1 hk2
  induction k, hk1 using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    have ih := ih (by omega)
    have hsum0 : 0 ≤ ∑ i ∈ Finset.Ico i₀ k, S i := Finset.sum_nonneg fun i _ ↦ hS i
    rw [Finset.sum_Ico_succ_top hk]
    refine (hstep k hk (by omega)).trans ?_
    have h1 : max (max (N k) M) Y ≤ max (max (N i₀) M) Y + ∑ i ∈ Finset.Ico i₀ k, S i := by
      refine max_le (max_le ih ?_) ?_
      · exact (le_max_right (N i₀) M).trans ((le_max_left _ Y).trans (le_add_of_nonneg_right hsum0))
      · exact (le_max_right _ Y).trans (le_add_of_nonneg_right hsum0)
    linarith

end Incognita.BatchedBandits
