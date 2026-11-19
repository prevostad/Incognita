/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.HY.Run

/-! # The structure of a batch of HY with a long paced phase

[INC-P000, Lemma `lem:structA`] and [INC-P000, Lemma `lem:thrA`], along almost every run of HY,
for a batch whose paced phase is long: the conditions (R2) of Definition `def:ranksA` at the batch
are hypotheses here (the rank `ℓ_A` itself is a proof-internal definition, not formalised). For the
batch `ℓ + 1` (`ℓ ≥ 1`; Lean rounds `[t_ℓ, t_(ℓ+1))`, paced phase `[s_ℓ, t_(ℓ+1))`), the conditions
are `ϑ_ℓ ≥ 0`, `ω_ℓ ≥ 0`, `s_ℓ ≥ 2`, `s_ℓ log s_ℓ ≥ 2(K - 1) U_(ℓ+1)` and
`t_(ℓ+1) - s_ℓ ≥ K (U_(ℓ+1) + K)`.

* `HY.target_sub_le_imp`: the deterministic step of (S3): an arm whose count at the end of the batch
  is at least its paced target minus `K - 1`, below `U_(ℓ+1)` and positive, was rejected at `t_ℓ`
  with an uncapped target, so `N_c(t_(ℓ+1)) K̂_ℓ(c) ≥ (1 + ω_ℓ) y_ℓ L_(ℓ+1)`.
* `HY.threshold_eq_of_forall`: the deterministic step of `lem:thrA`: if every arm of `Q_ℓ` has
  `N_c K̂_(ℓ-1)(c) ≥ y_(ℓ-1) L_ℓ`, the consistency threshold `Λ̂_ℓ` is `L_ℓ`.
* `HY.le_target_sub`, `HY.testKinf_reference`: the deterministic steps of (S4) and of the claim
  on the reference; `HY.reference_spec`, `HY.pseudoMean_le_leader`: the reference and the leader
  maximise the pseudo-mean (over the well-sampled arms, over all arms);
  `HY.ofReal_le_mul_pseudoKinf_zero_add`: the inequality (eq:rejA) of the proof of
  Lemma `lem:leaderA` for a rejected arm.
* `hyAlg_ae_structA`: (S1) and (S2) along almost every run: every non-leader `c` has
  `N_c(t) ≤ max(N_c(s_ℓ), n_{ℓ,c}(t))` in the paced phase and `N_c(t_(ℓ+1)) ≥ n_{ℓ,c}(t_(ℓ+1)) -
  (K - 1)`; the leader `ĉ_ℓ` is pulled at least `U_(ℓ+1)` times in the paced phase.
* `hyAlg_ae_structA_S3`: (S3) along almost every run; `hyAlg_ae_reference_wellSampled`: its
  "in particular", the reference `r_ℓ` is well sampled at `t_(ℓ+1)` (on an instance of `𝒫`).
* `hyAlg_ae_structA_S4`: (S4) along almost every run on an instance of `𝒫`, without division;
  `hyAlg_ae_structA_S4_min`: the paper's form with `min`.
* `hyAlg_ae_threshold_eq`: Lemma `lem:thrA` along almost every run: `Λ̂_ℓ = L_ℓ` when (R2) holds
  at the batch `ℓ` (`ℓ ≥ 2`).
* `hyAlg_ae_testLevel_le`, `hyAlg_ae_leaderA`: Lemma `lem:leaderA` along almost every run (its
  last claim, and (i)–(iii)), with the paper's events on the stacks replaced by their traces on
  the run (each paper event implies its trace).
* `hyAlg_ae_countsA`: Lemma `lem:countsA` along almost every run.
* `hyAlg_ae_pullCount_le_max'`, `hyAlg_ae_pullCount_le_max`: Lemma `lem:imedround` (its
  consequence) along almost every run of HY on an instance of `𝒫`.
* `hyAlg_ae_logcountC`: Lemma `lem:logcountC` (the case `x = 1`) along almost every run, for one
  batch whose IMED indices at its end are at least `y v`.

The paper's events `𝒜_j`, `𝒱_j`, `Π_j` are events on the reward stacks
(Definition `def:evA`); here they are hypotheses on the run at the batch ends (`N_c(t_j)` pulls,
empirical law `ν̂_c(t_j) = ν̂_(c, N_c(t_j))`, `HY.pseudoMean 0`, `HY.pseudoKinf 0`), so that the
lemmas are deterministic statements about almost every run; the probabilistic part
(Lemma `lem:probasA`, through the stacks of Lemma `lem:stacks`) bounds the probability that a
trace fails by the probability of the paper's event.
-/

@[expose] public section

open Learning Finset MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace Incognita.BatchedBandits

namespace HY

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}

/-- [INC-P000, proof of Lemma `lem:structA`, (S3), the deterministic step] If the count `N ≥ 1` of
an arm `c` at the end of a batch satisfies `n_{ℓ,c}(t) - (K - 1) ≤ N < U_(ℓ+1)`, where the target
`n_{ℓ,c}(t)` is computed with `log t`, then `c` was rejected at `t_ℓ` (`K̂_ℓ(c) > 0` and
`N_c(t_ℓ) K̂_ℓ(c) ≥ h_ℓ`) and `N K̂_ℓ(c) ≥ (1 + ω_ℓ) y_ℓ log t` (in `ℝ≥0∞`): an ambiguous arm, or
a rejected arm with a capped target, has target `K - 1 + U_(ℓ+1)`. -/
lemma target_sub_le_imp {w₀ thr ω' y logt : ℝ} (h : Hist Unit α ℝ n) (r U Unext : ℕ) (c : α)
    {N : ℕ} (hN : target w₀ thr ω' y logt h r U Unext c - (Fintype.card α - 1) ≤ N)
    (hNU : N < Unext) (hN1 : 1 ≤ N) :
    (0 < testKinf w₀ h r U c ∧
      ENNReal.ofReal thr ≤ (count h r c : ℝ≥0∞) * testKinf w₀ h r U c) ∧
      ENNReal.ofReal ((1 + ω') * y * logt) ≤ (N : ℝ≥0∞) * testKinf w₀ h r U c := by
  unfold target at hN
  rw [Nat.add_sub_cancel_left] at hN
  by_cases hrej : 0 < testKinf w₀ h r U c ∧
      ENNReal.ofReal thr ≤ (count h r c : ℝ≥0∞) * testKinf w₀ h r U c
  · refine ⟨hrej, ?_⟩
    rw [ite_eq_left hrej] at hN
    by_cases htop : testKinf w₀ h r U c = ⊤
    · rw [htop, ENNReal.mul_top (by exact_mod_cast (show N ≠ 0 by omega))]
      exact le_top
    · rw [ite_eq_right htop] at hN
      have hmin : ⌈(1 + ω') * y * logt / (testKinf w₀ h r U c).toReal⌉₊ ≤ N := by
        rcases le_total Unext ⌈(1 + ω') * y * logt / (testKinf w₀ h r U c).toReal⌉₊ with
          hle | hle
        · rw [min_eq_left hle] at hN
          omega
        · rwa [min_eq_right hle] at hN
      have hpos : 0 < (testKinf w₀ h r U c).toReal := ENNReal.toReal_pos hrej.1.ne' htop
      have hle : (1 + ω') * y * logt / (testKinf w₀ h r U c).toReal ≤ N :=
        (Nat.le_ceil _).trans (by exact_mod_cast hmin)
      rw [div_le_iff₀ hpos] at hle
      calc ENNReal.ofReal ((1 + ω') * y * logt)
          ≤ ENNReal.ofReal ((N : ℝ) * (testKinf w₀ h r U c).toReal) := ENNReal.ofReal_le_ofReal hle
        _ = (N : ℝ≥0∞) * testKinf w₀ h r U c := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
            ENNReal.ofReal_toReal htop]
  · rw [ite_eq_right hrej] at hN
    omega

/-- [INC-P000, proof of Lemma `lem:thrA`, the deterministic step] If every arm `c` of `Q_ℓ` (not
well sampled at `t_ℓ` and other than the previous leader `ĉ_(ℓ-1)`) has
`N_c(t_ℓ) K̂_(ℓ-1)(c) ≥ y_(ℓ-1) L_ℓ`, then the consistency threshold is `Λ̂_ℓ = L_ℓ` (for `L_ℓ ≥ 0`,
`y_(ℓ-1) > 0`): every bracket `N_c K̂_(ℓ-1)(c) / y_(ℓ-1) + log N_c` is at least `L_ℓ`. -/
lemma threshold_eq_of_forall {w₀ L y' : ℝ} (hL : 0 ≤ L) (hy' : 0 < y') (h : Hist Unit α ℝ n)
    (r r' U U' : ℕ)
    (hc : ∀ c, ¬ IsWellSampled h r U c → c ≠ leader w₀ h r' →
      ENNReal.ofReal (y' * L) ≤ (count h r c : ℝ≥0∞) * testKinf w₀ h r' U' c) :
    threshold w₀ L y' h r r' U U' = L := by
  unfold threshold
  rw [min_eq_left, ENNReal.toReal_ofReal hL]
  refine le_iInf fun c ↦ ?_
  split_ifs with hQ
  · have hy'0 : ENNReal.ofReal y' ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hy'
    refine le_trans ?_ le_self_add
    rw [ENNReal.le_div_iff_mul_le (Or.inl hy'0) (Or.inl ENNReal.ofReal_ne_top),
      ← ENNReal.ofReal_mul hL, mul_comm L]
    exact hc c hQ.1 hQ.2
  · exact le_top

/-- [INC-P000, proof of Lemma `lem:structA`, (S4), the deterministic step] If the test divergence
satisfies `K̂_ℓ(c) ≤ κ` (`κ ≥ 0`, for instance `κ = κ(μ̂_ℓ)` by Lemma `lem:kinf`(i)), the paced
target `n` of `c` with `log t` satisfies `n - (K - 1) ≥ U_(ℓ+1)` or
`(n - (K - 1)) κ ≥ (1 + ω_ℓ) y_ℓ log t`, so `n - (K - 1) ≥ min(U_(ℓ+1), (1 + ω_ℓ) y_ℓ log t / κ)`:
an ambiguous arm has target `K - 1 + U_(ℓ+1)`, and a rejected arm has `K̂_ℓ(c) ∈ (0, κ]`. The
form without division also covers `κ = 0` (then `K̂_ℓ(c) = 0`, `c` is ambiguous). -/
lemma le_target_sub {w₀ thr ω' y logt : ℝ} (h : Hist Unit α ℝ n) (r U Unext : ℕ) (c : α)
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ : testKinf w₀ h r U c ≤ ENNReal.ofReal κ) :
    Unext ≤ target w₀ thr ω' y logt h r U Unext c - (Fintype.card α - 1) ∨
      (1 + ω') * y * logt ≤
        ((target w₀ thr ω' y logt h r U Unext c - (Fintype.card α - 1) : ℕ) : ℝ) * κ := by
  unfold target
  rw [Nat.add_sub_cancel_left]
  split_ifs with hrej htop
  · exact absurd (htop ▸ hκ) (by simp)
  · have hpos : 0 < (testKinf w₀ h r U c).toReal := ENNReal.toReal_pos hrej.1.ne' htop
    have hle : (testKinf w₀ h r U c).toReal ≤ κ := ENNReal.toReal_le_of_le_ofReal hκ0 hκ
    rcases le_total Unext ⌈(1 + ω') * y * logt / (testKinf w₀ h r U c).toReal⌉₊ with hU | hU
    · left
      rw [min_eq_left hU]
    · right
      rw [min_eq_right hU]
      have h1 : (1 + ω') * y * logt / (testKinf w₀ h r U c).toReal ≤
          ⌈(1 + ω') * y * logt / (testKinf w₀ h r U c).toReal⌉₊ := Nat.le_ceil _
      rw [div_le_iff₀ hpos] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg _))
  · left
    exact le_rfl

/-- [INC-P000, proof of Lemma `lem:structA`, the reference] For rewards in `[0, 1]`, `w₀ ≥ 0` and a
positive weight `N_r + w₀` of the reference `r`, its test divergence is
`K̂(r) = 𝒦_inf(ν̃_r, μ̂) = 0`, since `μ̂` is its own pseudo-mean (Lemma `lem:kinf`(ii), or the
convention at level `1`). -/
lemma testKinf_reference {w₀ : ℝ} (hw₀ : 0 ≤ w₀) {h : Hist Unit α ℝ n} {r U : ℕ}
    (hfb : ∀ i, (h i).feedback ∈ Set.Icc (0 : ℝ) 1)
    (hpos : 0 < (count h r (reference w₀ h r U) : ℝ) + w₀) :
    testKinf w₀ h r U (reference w₀ h r U) = 0 := by
  unfold testKinf
  by_cases hμ : pseudoMean w₀ h r (reference w₀ h r U) < 1
  · exact pseudoKinf_eq_zero_of_le_pseudoMean hw₀ hμ (fun i ↦ (hfb i).2) hpos le_rfl
  · have h1 : pseudoMean w₀ h r (reference w₀ h r U) = 1 :=
      le_antisymm (pseudoMean_le_one hw₀ hfb _) (not_lt.mp hμ)
    simp [pseudoKinf, h1]

/-- The reference maximises the pseudo-mean over the well-sampled arms, and is well sampled when
some arm is [INC-P000, Definition `def:hy`, (3)]. -/
lemma reference_spec {w₀ : ℝ} {h : Hist Unit α ℝ n} {r U : ℕ} {c : α}
    (hc : IsWellSampled h r U c) :
    IsWellSampled h r U (reference w₀ h r U) ∧
      pseudoMean w₀ h r c ≤ pseudoMean w₀ h r (reference w₀ h r U) := by
  classical
  have hex : ∃ c, IsWellSampled h r U c := ⟨c, hc⟩
  set f : α → EReal := fun c ↦ if IsWellSampled h r U c then
    (pseudoMean w₀ h r c : EReal) else ⊥ with hf
  have hmax : f c ≤ f (argmax f) := isMaxOn_argmax f (Set.mem_univ c)
  have href : reference w₀ h r U = argmax f := by
    unfold reference
    rw [ite_eq_left hex]
  rw [← href, hf] at hmax
  simp only [ite_eq_left hc] at hmax
  by_cases hws : IsWellSampled h r U (reference w₀ h r U)
  · rw [ite_eq_left hws] at hmax
    exact ⟨hws, EReal.coe_le_coe_iff.mp hmax⟩
  · rw [ite_eq_right hws] at hmax
    exact absurd hmax (by simp)

/-- The leader maximises the pseudo-mean [INC-P000, Definition `def:hy`, (2)]. -/
lemma pseudoMean_le_leader (w₀ : ℝ) (h : Hist Unit α ℝ n) (r : ℕ) (c : α) :
    pseudoMean w₀ h r c ≤ pseudoMean w₀ h r (leader w₀ h r) :=
  isMaxOn_argmax (fun c ↦ pseudoMean w₀ h r c) (Set.mem_univ c)

/-- [INC-P000, proof of Lemma `lem:leaderA`, (eq:rejA)] An arm `c` rejected at a cutoff `r` with the
threshold `h` (`N_c K̂(c) ≥ h`, `K̂(c) = 𝒦_inf(ν̃_c, μ̂)`), `N_c ≥ 1`, rewards in `[0, 1]` and
`w₀ ≥ 0`, has `N_c 𝒦_inf(ν̂_c, ρ) + w₀ κ(μ̂) ≥ h` for every level `ρ ∈ [μ̂, 1)`, `ν̂_c` the
empirical law (`w₀ = 0`): Lemma `lem:pseudo`(ii), then Lemma `lem:kinf`(iii). -/
lemma ofReal_le_mul_pseudoKinf_zero_add {w₀ thr ρ : ℝ} (hw₀ : 0 ≤ w₀) {h : Hist Unit α ℝ n}
    {r U : ℕ} {c : α} (hfb : ∀ i, (h i).feedback ∈ Set.Icc (0 : ℝ) 1) (hN : 1 ≤ count h r c)
    (hrej : ENNReal.ofReal thr ≤ (count h r c : ℝ≥0∞) * testKinf w₀ h r U c)
    (hμρ : pseudoMean w₀ h r (reference w₀ h r U) ≤ ρ) (hρ : ρ < 1) :
    ENNReal.ofReal thr ≤ (count h r c : ℝ≥0∞) * pseudoKinf 0 h r c ρ +
      ENNReal.ofReal (w₀ * Real.log (1 / (1 - pseudoMean w₀ h r (reference w₀ h r U)))) := by
  set μ := pseudoMean w₀ h r (reference w₀ h r U) with hμ
  have hμ0 : 0 ≤ μ := pseudoMean_nonneg' hw₀ hfb _
  have hμ1 : μ < 1 := hμρ.trans_lt hρ
  refine hrej.trans ?_
  unfold testKinf
  rw [← hμ]
  refine (mul_pseudoKinf_le hw₀ hμ1 hμ0 hfb hN).trans ?_
  gcongr
  exact pseudoKinf_mono le_rfl hμ0 hμρ hρ hfb

/-- [INC-P000, proof of Lemma `lem:leaderA`, (ii)] The test divergence is at most the IMED
divergence, `K̂(c) ≤ K̃(c)`, for rewards in `[0, 1]`, `w₀ ≥ 0` and `N_c + w₀ > 0`: the leader has
the largest pseudo-mean, `m̃⋆ ≥ μ̂` (Lemma `lem:kinf`(iii), or the convention at level `1`). -/
lemma testKinf_le_imedKinf {w₀ : ℝ} (hw₀ : 0 ≤ w₀) {h : Hist Unit α ℝ n} {r U : ℕ} {c : α}
    (hfb : ∀ i, (h i).feedback ∈ Set.Icc (0 : ℝ) 1) (hpos : 0 < (count h r c : ℝ) + w₀) :
    testKinf w₀ h r U c ≤ imedKinf w₀ h r c := by
  unfold testKinf imedKinf
  set μ := pseudoMean w₀ h r (reference w₀ h r U) with hμ
  set μ' := pseudoMean w₀ h r (leader w₀ h r) with hμ'
  have hμμ' : μ ≤ μ' := pseudoMean_le_leader w₀ h r _
  have hμ0 : 0 ≤ μ := pseudoMean_nonneg' hw₀ hfb _
  have hμ1 : μ ≤ 1 := pseudoMean_le_one hw₀ hfb _
  by_cases hl1 : μ' < 1
  · exact pseudoKinf_mono hw₀ hμ0 hμμ' hl1 hfb
  by_cases hc1 : pseudoMean w₀ h r c = 1
  · -- then `K̂(c) = 0`
    refine le_of_eq_of_le ?_ bot_le
    by_cases hμ1' : μ < 1
    · exact pseudoKinf_eq_zero_of_le_pseudoMean hw₀ hμ1' (fun i ↦ (hfb i).2) hpos (hc1 ▸ hμ1)
    · rw [pseudoKinf, ite_eq_right hμ1', ite_eq_left hc1]
      rfl
  · conv_rhs => rw [pseudoKinf, ite_eq_right hl1, ite_eq_right hc1]
    exact le_top

omit [Fintype α] [Nonempty α] in
/-- [INC-P000, proof of Lemma `lem:leaderA`] For rewards in `[0, 1]`, `w₀ ≥ 0` and an arm well
sampled for a net size `U ≥ 1` (`U ≤ 2 N_c`) with `2 w₀ ≤ ε U`, the pseudo-mean is at least the
empirical mean minus `ε`: Lemma `lem:pseudo`(i), `m̂_c - m̃_c ≤ 2 w₀ / U`. -/
lemma pseudoMean_zero_sub_le_of_two_mul_le {w₀ ε : ℝ} (hw₀ : 0 ≤ w₀) {h : Hist Unit α ℝ n}
    {r U : ℕ} {c : α} (hfb : ∀ i, (h i).feedback ∈ Set.Icc (0 : ℝ) 1) (hU : 1 ≤ U)
    (hc : U ≤ 2 * count h r c) (hwU : 2 * w₀ ≤ ε * U) :
    pseudoMean 0 h r c - ε ≤ pseudoMean w₀ h r c := by
  have h1 := pseudoMean_zero_sub_le_of_le hw₀ hfb hU hc
  have hUr : (0 : ℝ) < U := by exact_mod_cast hU
  have h2 : 2 * w₀ / U ≤ ε := by rw [div_le_iff₀ hUr]; linarith
  linarith

/-- [INC-P000, proof of Lemma `lem:goodA`, Step 4] The paced target of a rejected arm `c` with
`K̂_ℓ(c) ≥ D > 0` is at most `K + (1 + ω_ℓ) y_ℓ log t / D`, for `(1 + ω_ℓ) y_ℓ log t ≥ 0`. -/
lemma target_le_of_rejected {w₀ thr ω' y logt D : ℝ} (hf : 0 ≤ (1 + ω') * y * logt) (hD : 0 < D)
    {h : Hist Unit α ℝ n} {r U Unext : ℕ} {c : α}
    (hrej : 0 < testKinf w₀ h r U c ∧
      ENNReal.ofReal thr ≤ (count h r c : ℝ≥0∞) * testKinf w₀ h r U c)
    (hDK : ENNReal.ofReal D ≤ testKinf w₀ h r U c) :
    (target w₀ thr ω' y logt h r U Unext c : ℝ) ≤ Fintype.card α + (1 + ω') * y * logt / D := by
  have hK1 : 1 ≤ Fintype.card α := Fintype.card_pos
  have hfD : 0 ≤ (1 + ω') * y * logt / D := div_nonneg hf hD.le
  unfold target
  rw [ite_eq_left hrej]
  have hK' : ((Fintype.card α - 1 : ℕ) : ℝ) = Fintype.card α - 1 := by
    rw [Nat.cast_sub hK1, Nat.cast_one]
  rw [Nat.cast_add, hK']
  by_cases htop : testKinf w₀ h r U c = ⊤
  · rw [ite_eq_left htop, _root_.min_zero, Nat.cast_zero]
    linarith
  · rw [ite_eq_right htop]
    have hDle : D ≤ (testKinf w₀ h r U c).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal htop).mp hDK
    have hpos : 0 < (testKinf w₀ h r U c).toReal := hD.trans_le hDle
    have h1 : ((min Unext ⌈(1 + ω') * y * logt / (testKinf w₀ h r U c).toReal⌉₊ : ℕ) : ℝ) ≤
        (1 + ω') * y * logt / D + 1 := by
      refine (Nat.cast_le.mpr (min_le_right _ _)).trans ?_
      refine (Nat.ceil_lt_add_one (div_nonneg hf hpos.le)).le.trans ?_
      gcongr
    linarith

end HY

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] {K : ℕ}

/-- [INC-P000, Lemma `lem:structA`, (S1) and (S2), along a run] Along almost every run of HY with
`K ≥ 2` arms, for a batch `ℓ + 1` (`ℓ ≥ 1`) satisfying (R2) (`s_ℓ ≥ 2`,
`s_ℓ log s_ℓ ≥ 2(K - 1) U_(ℓ+1)`, `t_(ℓ+1) - s_ℓ ≥ K (U_(ℓ+1) + K)`), with `ϑ_ℓ ≥ 0` and
`(1 + ω_ℓ) y_ℓ ≥ 0`, and with the leader `ĉ_ℓ`, the threshold `h_ℓ` and the paced targets
`n_{ℓ,c}(t)` frozen at `t_ℓ` (given as `L`, `thr`, `tgt`):
* (S1) every `c ≠ ĉ_ℓ` has `N_c(t) ≤ max(N_c(s_ℓ), n_{ℓ,c}(t))` for `t ∈ [s_ℓ, t_(ℓ+1)]`, and
  `N_c(t_(ℓ+1)) ≥ n_{ℓ,c}(t_(ℓ+1)) - (K - 1)`;
* (S2) the leader `ĉ_ℓ` is pulled at least `U_(ℓ+1)` times in the paced phase `(s_ℓ, t_(ℓ+1)]`.
The paper's "`ℓ ∈ Act`" is implied by the length of the paced phase. -/
lemma hyAlg_ae_structA (w₀ β : ℝ) (ωs θ γ : ℕ → ℝ) (g : Grid K)
    (env : Environment Unit α ℝ) (hK : 2 ≤ Fintype.card α) :
    ∀ᵐ ω ∂(trajMeasure (hyAlg w₀ β ωs θ γ g : Algorithm Unit α ℝ) env), ∀ ℓ, ℓ ≠ 0 →
      0 ≤ θ ℓ → 0 ≤ (1 + ωs ℓ) * g.ratio ℓ ^ 2 → 2 ≤ g.imedEnd θ ℓ →
      (2 * (Fintype.card α - 1 : ℕ) * g.netSize β (ℓ + 1) : ℝ) ≤
        g.imedEnd θ ℓ * Real.log (g.imedEnd θ ℓ) →
      Fintype.card α * (g.netSize β (ℓ + 1) + Fintype.card α) ≤ g.t (ℓ + 1) - g.imedEnd θ ℓ →
      ∀ (L : α) (thr : ℝ) (tgt : α → ℕ → ℕ),
      L = HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) →
      thr = (1 - γ ℓ) * g.ratio (ℓ - 1) ^ 2 * (if ℓ = 1 then g.logEnd 1 else
        HY.threshold w₀ (g.logEnd ℓ) (g.ratio (ℓ - 1) ^ 2)
          (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) (g.t (ℓ - 1))
          (g.netSize β ℓ) (g.netSize β (ℓ - 1))) →
      (∀ c t, tgt c t = HY.target w₀ thr (ωs ℓ) (g.ratio ℓ ^ 2) (Real.log t)
        (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) (g.netSize β ℓ)
        (g.netSize β (ℓ + 1)) c) →
      (∀ c, c ≠ L → ∀ t, g.imedEnd θ ℓ ≤ t → t ≤ g.t (ℓ + 1) →
          pullCount IT.action c t ω ≤ max (pullCount IT.action c (g.imedEnd θ ℓ) ω) (tgt c t)) ∧
      (∀ c, c ≠ L → tgt c (g.t (ℓ + 1)) - (Fintype.card α - 1) ≤
          pullCount IT.action c (g.t (ℓ + 1)) ω) ∧
      g.netSize β (ℓ + 1) ≤
        pullCount IT.action L (g.t (ℓ + 1)) ω - pullCount IT.action L (g.imedEnd θ ℓ) ω := by
  filter_upwards [hyAlg_ae_paced_rule w₀ β ωs θ γ g env,
    hyAlg_ae_backlog_le_of_le w₀ β ωs θ γ g env hK] with ω hrule hQ
  intro ℓ hℓ hθ hωy hσ2 hσU hlong L thr tgt hL hthr htgt
  set σ := g.imedEnd θ ℓ with hσdef
  set T := g.t (ℓ + 1) with hTdef
  set U := g.netSize β (ℓ + 1) with hUdef
  set k := Fintype.card α - 1 with hkdef
  have hKpos : 0 < Fintype.card α * (U + Fintype.card α) :=
    Nat.mul_pos (by omega) (by omega)
  have hσT : σ ≤ T := by omega
  have hσ : g.t ℓ ≤ σ := g.t_le_imedEnd hθ
  have hlong' : k * (k + U) + U ≤ T - σ := by
    refine le_trans ?_ hlong
    obtain ⟨m, hm⟩ : ∃ m, Fintype.card α = m + 1 := ⟨Fintype.card α - 1, by omega⟩
    rw [hkdef, hm, Nat.add_sub_cancel]
    nlinarith
  -- the targets are nondecreasing and at most `K - 1 + U_(ℓ+1)` in the paced phase
  have hmono : ∀ c, MonotoneOn (tgt c) (Set.Icc σ T) := by
    intro c u hu v hv huv
    rw [htgt, htgt]
    refine HY.target_mono_logt hωy (Real.log_le_log ?_ (by exact_mod_cast huv)) _ _ _ _ c
    have : 2 ≤ u := hσ2.trans hu.1
    exact_mod_cast (show 0 < u by omega)
  have hB : ∀ c t, tgt c t ≤ k + U := fun c t ↦ by
    rw [htgt]
    exact HY.target_le _ _ _ _ c
  -- (rule) for a non-leader
  have hrule' : ∀ c, c ≠ L → ∀ t, σ < t → t ≤ T → IT.action (t - 1) ω = c →
      pullCount IT.action c (t - 1) ω < tgt c t := by
    intro c hc t ht1 ht2 hA
    have hb : g.batchOf (t - 1) = ℓ + 1 := g.batchOf_eq_iff.mpr ⟨by omega, by omega⟩
    have hpaced : ¬ t - 1 + 1 ≤ σ := by omega
    have hlog : Real.log (((t - 1 : ℕ) : ℝ) + 1) = Real.log t := by
      rw [Nat.cast_sub (by omega), Nat.cast_one, sub_add_cancel]
    have hne : IT.action (t - 1) ω ≠
        HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) := by
      rw [hA, ← hL]
      exact hc
    have h1 := (hrule ℓ (t - 1) hℓ hb hpaced).1 hne
    rw [hA] at h1
    rw [htgt, hthr, ← hlog]
    exact h1
  refine ⟨fun c hc t ht1 ht2 ↦ pullCount_le_max_target (hmono c) (hrule' c hc) ht1 ht2,
    fun c hc ↦ ?_, ?_⟩
  · -- (S1), at the end of the batch: the backlog is at most `K - 1`
    have hQT := hQ ℓ hℓ hθ hωy hσ2 hσU L thr tgt hL hthr htgt T hσT le_rfl
    have hmax : max (k * (k + U) - (T - σ)) k = k := max_eq_right (by omega)
    rw [hmax] at hQT
    have hmem : c ∈ Finset.univ.erase L := Finset.mem_erase.mpr ⟨hc, Finset.mem_univ c⟩
    have := Finset.single_le_sum (f := fun c ↦ tgt c T - pullCount IT.action c T ω)
      (fun _ _ ↦ Nat.zero_le _) hmem
    omega
  · -- (S2): the leader keeps the rounds that the non-leaders do not take
    have hBc : ∀ c ∈ Finset.univ.erase L,
        pullCount IT.action c T ω - pullCount IT.action c σ ω ≤ k + U := fun c hc ↦
      pullCount_sub_le_target (hmono c) (fun t _ _ ↦ hB c t)
        (hrule' c (Finset.ne_of_mem_erase hc)) hσT le_rfl
    have h1 := card_le_card_filter_not_mem (A := IT.action) (ω := ω) (Finset.univ.erase L) hσT hBc
    rw [Finset.card_erase_of_mem (Finset.mem_univ L), Finset.card_univ, ← hkdef] at h1
    have h2 : ((Finset.Ico σ T).filter fun u ↦ IT.action u ω ∉ Finset.univ.erase L) =
        (Finset.Ico σ T).filter fun u ↦ IT.action u ω ∈ ({L} : Finset α) :=
      Finset.filter_congr fun u _ ↦ by simp
    have h3 := card_filter_mem_eq_sum (A := IT.action) (ω := ω) ({L} : Finset α) hσT
    rw [Finset.sum_singleton] at h3
    rw [h2, h3] at h1
    omega

/-- [INC-P000, Lemma `lem:structA`, (S3), along a run] Along almost every run of HY on a grid for
`K ≥ 2` arms, for a batch `ℓ + 1` (`ℓ ≥ 1`) satisfying the hypotheses of `hyAlg_ae_structA`: an
arm `c` that is not well sampled at `t_(ℓ+1)` (`N_c(t_(ℓ+1)) < U_(ℓ+1) / 2`) is not the leader
`ĉ_ℓ`, was rejected at `t_ℓ` (`K̂_ℓ(c) > 0` and `N_c(t_ℓ) K̂_ℓ(c) ≥ h_ℓ`), and
`N_c(t_(ℓ+1)) K̂_ℓ(c) ≥ (1 + ω_ℓ) y_ℓ L_(ℓ+1)` (in `ℝ≥0∞`). The leader, the threshold and the
targets are given as `L`, `thr`, `tgt`, as in `hyAlg_ae_structA`. -/
lemma hyAlg_ae_structA_S3 (w₀ β : ℝ) (ωs θ γ : ℕ → ℝ) (g : Grid (Fintype.card α))
    (env : Environment Unit α ℝ) (hK : 2 ≤ Fintype.card α) :
    ∀ᵐ ω ∂(trajMeasure (hyAlg w₀ β ωs θ γ g : Algorithm Unit α ℝ) env), ∀ ℓ, ℓ ≠ 0 →
      0 ≤ θ ℓ → 0 ≤ (1 + ωs ℓ) * g.ratio ℓ ^ 2 → 2 ≤ g.imedEnd θ ℓ →
      (2 * (Fintype.card α - 1 : ℕ) * g.netSize β (ℓ + 1) : ℝ) ≤
        g.imedEnd θ ℓ * Real.log (g.imedEnd θ ℓ) →
      Fintype.card α * (g.netSize β (ℓ + 1) + Fintype.card α) ≤ g.t (ℓ + 1) - g.imedEnd θ ℓ →
      ∀ (L : α) (thr : ℝ) (tgt : α → ℕ → ℕ),
      L = HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) →
      thr = (1 - γ ℓ) * g.ratio (ℓ - 1) ^ 2 * (if ℓ = 1 then g.logEnd 1 else
        HY.threshold w₀ (g.logEnd ℓ) (g.ratio (ℓ - 1) ^ 2)
          (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) (g.t (ℓ - 1))
          (g.netSize β ℓ) (g.netSize β (ℓ - 1))) →
      (∀ c t, tgt c t = HY.target w₀ thr (ωs ℓ) (g.ratio ℓ ^ 2) (Real.log t)
        (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) (g.netSize β ℓ)
        (g.netSize β (ℓ + 1)) c) →
      ∀ c, 2 * pullCount IT.action c (g.t (ℓ + 1)) ω < g.netSize β (ℓ + 1) →
        c ≠ L ∧
        (0 < HY.testKinf w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ)
            (g.netSize β ℓ) c ∧
          ENNReal.ofReal thr ≤ (pullCount IT.action c (g.t ℓ) ω : ℝ≥0∞) *
            HY.testKinf w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ)
              (g.netSize β ℓ) c) ∧
        ENNReal.ofReal ((1 + ωs ℓ) * g.ratio ℓ ^ 2 * g.logEnd (ℓ + 1)) ≤
          (pullCount IT.action c (g.t (ℓ + 1)) ω : ℝ≥0∞) *
            HY.testKinf w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ)
              (g.netSize β ℓ) c := by
  filter_upwards [hyAlg_ae_structA w₀ β ωs θ γ g env hK,
    hyAlg_ae_one_le_pullCount w₀ β ωs θ γ g env] with ω hS hN1
  intro ℓ hℓ hθ hωy hσ2 hσU hlong L thr tgt hL hthr htgt c hc
  obtain ⟨-, hS1, hS2⟩ := hS ℓ hℓ hθ hωy hσ2 hσU hlong L thr tgt hL hthr htgt
  have hcL : c ≠ L := by
    rintro rfl
    have := Nat.sub_le (pullCount IT.action c (g.t (ℓ + 1)) ω)
      (pullCount IT.action c (g.imedEnd θ ℓ) ω)
    omega
  refine ⟨hcL, ?_⟩
  have hT := hS1 c hcL
  rw [htgt] at hT
  have h := HY.target_sub_le_imp _ _ _ _ c hT (by omega) (hN1 (ℓ + 1) (by omega) c)
  rw [HY.count_history le_rfl] at h
  exact h

/-- [INC-P000, Lemma `lem:thrA`, along a run] Along almost every run of HY on a grid for `K ≥ 2`
arms, if the batch `ℓ` (`ℓ ≥ 2`; Lean index `ℓ - 1`) satisfies (R2) (the hypotheses of
`hyAlg_ae_structA` at `ℓ - 1`, with `ω_(ℓ-1) ≥ 0`), the consistency threshold of the test at `t_ℓ`
is deterministic: `Λ̂_ℓ = L_ℓ`, so `h_ℓ = (1 - γ_ℓ) y_(ℓ-1) L_ℓ`. By (S3) at `ℓ - 1`, every arm
`c` of `Q_ℓ` has `N_c(t_ℓ) K̂_(ℓ-1)(c) ≥ (1 + ω_(ℓ-1)) y_(ℓ-1) L_ℓ ≥ y_(ℓ-1) L_ℓ`. -/
lemma hyAlg_ae_threshold_eq (w₀ β : ℝ) (ωs θ γ : ℕ → ℝ) (g : Grid (Fintype.card α))
    (env : Environment Unit α ℝ) (hK : 2 ≤ Fintype.card α) :
    ∀ᵐ ω ∂(trajMeasure (hyAlg w₀ β ωs θ γ g : Algorithm Unit α ℝ) env), ∀ ℓ, 2 ≤ ℓ →
      0 ≤ θ (ℓ - 1) → 0 ≤ ωs (ℓ - 1) → 2 ≤ g.imedEnd θ (ℓ - 1) →
      (2 * (Fintype.card α - 1 : ℕ) * g.netSize β ℓ : ℝ) ≤
        g.imedEnd θ (ℓ - 1) * Real.log (g.imedEnd θ (ℓ - 1)) →
      Fintype.card α * (g.netSize β ℓ + Fintype.card α) ≤ g.t ℓ - g.imedEnd θ (ℓ - 1) →
      HY.threshold w₀ (g.logEnd ℓ) (g.ratio (ℓ - 1) ^ 2)
        (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) (g.t (ℓ - 1))
        (g.netSize β ℓ) (g.netSize β (ℓ - 1)) = g.logEnd ℓ := by
  filter_upwards [hyAlg_ae_structA_S3 w₀ β ωs θ γ g env hK] with ω hS3
  intro ℓ hℓ hθ hω0 hσ2 hσU hlong
  obtain ⟨j, rfl⟩ : ∃ j, ℓ = j + 1 := ⟨ℓ - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hθ hω0 hσ2 hσU hlong ⊢
  have hj : j ≠ 0 := by omega
  have hy : 0 < g.ratio j ^ 2 := pow_pos (zero_lt_one.trans_le (g.one_le_ratio j)) 2
  have hL : 0 ≤ g.logEnd (j + 1) := (g.logEnd_pos (by omega)).le
  have hωy : 0 ≤ (1 + ωs j) * g.ratio j ^ 2 := by positivity
  refine HY.threshold_eq_of_forall hL hy _ _ _ _ _ fun c hc _ ↦ ?_
  have hc' : 2 * pullCount IT.action c (g.t (j + 1)) ω < g.netSize β (j + 1) := by
    rw [HY.isWellSampled_history_iff_le_pullCount le_rfl] at hc
    omega
  obtain ⟨-, -, h⟩ := hS3 j hj hθ hωy hσ2 hσU hlong _ _ _ rfl rfl (fun _ _ ↦ rfl) c hc'
  rw [HY.count_history le_rfl, HY.testKinf_history (g.strictMono.monotone (Nat.le_succ j))]
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) h
  have : g.ratio j ^ 2 * g.logEnd (j + 1) ≤ (1 + ωs j) * (g.ratio j ^ 2 * g.logEnd (j + 1)) :=
    le_mul_of_one_le_left (by positivity) (by linarith)
  linarith

/-- [INC-P000, Lemma `lem:structA`, (S3), "in particular"] Along almost every run of HY
(`w₀ ≥ 0`, on a grid for `K ≥ 2` arms) on an instance of `𝒫`, for a batch `ℓ + 1` (`ℓ ≥ 1`)
satisfying the hypotheses of `hyAlg_ae_structA`, the reference `r_ℓ` (computed at `t_ℓ` with the
net size `U_ℓ`) is well sampled at `t_(ℓ+1)`: `N_(r_ℓ)(t_(ℓ+1)) ≥ U_(ℓ+1) / 2`. Its test divergence
is `0`, so it is not rejected, and (S3) applies. -/
lemma hyAlg_ae_reference_wellSampled (w₀ β : ℝ) (hw₀ : 0 ≤ w₀) (ωs θ γ : ℕ → ℝ)
    (g : Grid (Fintype.card α)) (hK : 2 ≤ Fintype.card α) {ν : Kernel α ℝ} [IsMarkovKernel ν]
    (hν : ν ∈ unitBandits α) :
    ∀ᵐ ω ∂(trajMeasure (hyAlg w₀ β ωs θ γ g : Algorithm Unit α ℝ) (Environment.bandit ν)),
      ∀ ℓ, ℓ ≠ 0 → 0 ≤ θ ℓ → 0 ≤ (1 + ωs ℓ) * g.ratio ℓ ^ 2 → 2 ≤ g.imedEnd θ ℓ →
      (2 * (Fintype.card α - 1 : ℕ) * g.netSize β (ℓ + 1) : ℝ) ≤
        g.imedEnd θ ℓ * Real.log (g.imedEnd θ ℓ) →
      Fintype.card α * (g.netSize β (ℓ + 1) + Fintype.card α) ≤ g.t (ℓ + 1) - g.imedEnd θ ℓ →
      g.netSize β (ℓ + 1) ≤ 2 * pullCount IT.action
        (HY.reference w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ)
          (g.netSize β ℓ)) (g.t (ℓ + 1)) ω := by
  filter_upwards [hyAlg_ae_structA_S3 w₀ β ωs θ γ g (Environment.bandit ν) hK,
    hyAlg_ae_one_le_pullCount w₀ β ωs θ γ g (Environment.bandit ν),
    ae_feedback_mem_Icc (alg := hyAlg w₀ β ωs θ γ g) hν] with ω hS3 hN1 hfb
  intro ℓ hℓ hθ hωy hσ2 hσU hlong
  by_contra hc
  obtain ⟨-, ⟨hpos, -⟩, -⟩ := hS3 ℓ hℓ hθ hωy hσ2 hσU hlong _ _ _ rfl rfl (fun _ _ ↦ rfl)
    (HY.reference w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) (g.netSize β ℓ))
    (by omega)
  have hw : 0 < (HY.count (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ)
      (HY.reference w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ)
        (g.netSize β ℓ)) : ℝ) + w₀ := by
    rw [HY.count_history le_rfl]
    have : (1 : ℝ) ≤ pullCount IT.action (HY.reference w₀
        (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) (g.netSize β ℓ)) (g.t ℓ) ω := by
      exact_mod_cast hN1 ℓ (by omega) _
    linarith
  rw [HY.testKinf_reference (h := history IT.obs IT.action IT.feedback (g.t ℓ) ω) hw₀
    (fun i ↦ hfb i) hw] at hpos
  exact lt_irrefl _ hpos

/-- [INC-P000, Lemma `lem:structA`, (S4), along a run] Along almost every run of HY (`w₀ ≥ 0`, on
a grid for `K ≥ 2` arms) on an instance of `𝒫`, for a batch `ℓ + 1` (`ℓ ≥ 1`) satisfying the
hypotheses of `hyAlg_ae_structA` with `ω_ℓ ≥ 0`: if the test level `μ̂_ℓ` (the pseudo-mean of the
reference at `t_ℓ`) is `< 1`, every arm is explored: `N_c(t_(ℓ+1)) ≥ U_(ℓ+1)` or
`N_c(t_(ℓ+1)) κ(μ̂_ℓ) ≥ y_ℓ L_(ℓ+1)`, with `κ(μ) = log (1 / (1 - μ))`; this is the paper's
`N_c(t_(ℓ+1)) ≥ min(U_(ℓ+1), y_ℓ L_(ℓ+1) / κ(μ̂_ℓ))` without division (`κ(0) = 0`), see
`hyAlg_ae_structA_S4_min`. -/
lemma hyAlg_ae_structA_S4 (w₀ β : ℝ) (hw₀ : 0 ≤ w₀) (ωs θ γ : ℕ → ℝ)
    (g : Grid (Fintype.card α)) (hK : 2 ≤ Fintype.card α) {ν : Kernel α ℝ} [IsMarkovKernel ν]
    (hν : ν ∈ unitBandits α) :
    ∀ᵐ ω ∂(trajMeasure (hyAlg w₀ β ωs θ γ g : Algorithm Unit α ℝ) (Environment.bandit ν)),
      ∀ ℓ, ℓ ≠ 0 → 0 ≤ θ ℓ → 0 ≤ ωs ℓ → 2 ≤ g.imedEnd θ ℓ →
      (2 * (Fintype.card α - 1 : ℕ) * g.netSize β (ℓ + 1) : ℝ) ≤
        g.imedEnd θ ℓ * Real.log (g.imedEnd θ ℓ) →
      Fintype.card α * (g.netSize β (ℓ + 1) + Fintype.card α) ≤ g.t (ℓ + 1) - g.imedEnd θ ℓ →
      HY.pseudoMean w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ)
        (HY.reference w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ)
          (g.netSize β ℓ)) < 1 →
      ∀ c, g.netSize β (ℓ + 1) ≤ pullCount IT.action c (g.t (ℓ + 1)) ω ∨
        g.ratio ℓ ^ 2 * g.logEnd (ℓ + 1) ≤ pullCount IT.action c (g.t (ℓ + 1)) ω *
          Real.log (1 / (1 - HY.pseudoMean w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω)
            (g.t ℓ) (HY.reference w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ)
              (g.netSize β ℓ)))) := by
  filter_upwards [hyAlg_ae_structA w₀ β ωs θ γ g (Environment.bandit ν) hK,
    hyAlg_ae_one_le_pullCount w₀ β ωs θ γ g (Environment.bandit ν),
    ae_feedback_mem_Icc (alg := hyAlg w₀ β ωs θ γ g) hν] with ω hS hN1 hfb
  intro ℓ hℓ hθ hω0 hσ2 hσU hlong hμ c
  set h := history IT.obs IT.action IT.feedback (g.t ℓ) ω with hh
  set μ := HY.pseudoMean w₀ h (g.t ℓ) (HY.reference w₀ h (g.t ℓ) (g.netSize β ℓ)) with hμdef
  have hfbh : ∀ i, (h i).feedback ∈ Set.Icc (0 : ℝ) 1 := fun i ↦ hfb i
  have hμ0 : 0 ≤ μ := HY.pseudoMean_nonneg' hw₀ hfbh _
  have hκ0 : 0 ≤ Real.log (1 / (1 - μ)) :=
    Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
  have hy : 0 ≤ g.ratio ℓ ^ 2 := sq_nonneg _
  have hL : 0 ≤ g.logEnd (ℓ + 1) := (g.logEnd_pos (by omega)).le
  have hωy : 0 ≤ (1 + ωs ℓ) * g.ratio ℓ ^ 2 := by positivity
  obtain ⟨-, hS1, hS2⟩ := hS ℓ hℓ hθ hωy hσ2 hσU hlong _ _ _ rfl rfl (fun _ _ ↦ rfl)
  by_cases hcL : c = HY.leader w₀ h (g.t ℓ)
  · -- the leader is pulled at least `U_(ℓ+1)` times
    rw [hcL]
    left
    have := Nat.sub_le (pullCount IT.action (HY.leader w₀ h (g.t ℓ)) (g.t (ℓ + 1)) ω)
      (pullCount IT.action (HY.leader w₀ h (g.t ℓ)) (g.imedEnd θ ℓ) ω)
    exact hS2.trans this
  · have hpos : 0 < (HY.count h (g.t ℓ) c : ℝ) + w₀ := by
      rw [hh, HY.count_history le_rfl]
      have : (1 : ℝ) ≤ pullCount IT.action c (g.t ℓ) ω := by exact_mod_cast hN1 ℓ (by omega) c
      linarith
    have hκ : HY.testKinf w₀ h (g.t ℓ) (g.netSize β ℓ) c ≤
        ENNReal.ofReal (Real.log (1 / (1 - μ))) :=
      HY.pseudoKinf_le_ofReal_log hw₀ hμ hμ0 hfbh hpos
    set X := HY.target w₀ ((1 - γ ℓ) * g.ratio (ℓ - 1) ^ 2 *
        (if ℓ = 1 then g.logEnd 1 else HY.threshold w₀ (g.logEnd ℓ) (g.ratio (ℓ - 1) ^ 2) h (g.t ℓ)
          (g.t (ℓ - 1)) (g.netSize β ℓ) (g.netSize β (ℓ - 1)))) (ωs ℓ) (g.ratio ℓ ^ 2)
        (g.logEnd (ℓ + 1)) h (g.t ℓ) (g.netSize β ℓ) (g.netSize β (ℓ + 1)) c -
          (Fintype.card α - 1) with hX
    have h1 := HY.le_target_sub (thr := (1 - γ ℓ) * g.ratio (ℓ - 1) ^ 2 *
      (if ℓ = 1 then g.logEnd 1 else HY.threshold w₀ (g.logEnd ℓ) (g.ratio (ℓ - 1) ^ 2) h (g.t ℓ)
        (g.t (ℓ - 1)) (g.netSize β ℓ) (g.netSize β (ℓ - 1)))) (ω' := ωs ℓ) (y := g.ratio ℓ ^ 2)
      (logt := g.logEnd (ℓ + 1)) h (g.t ℓ) (g.netSize β ℓ) (g.netSize β (ℓ + 1)) c hκ0 hκ
    rw [← hX] at h1
    have h2 : X ≤ pullCount IT.action c (g.t (ℓ + 1)) ω := hS1 c hcL
    rcases h1 with h1 | h1
    · exact Or.inl (h1.trans h2)
    · right
      have h2' : (X : ℝ) ≤ pullCount IT.action c (g.t (ℓ + 1)) ω := by exact_mod_cast h2
      have : g.ratio ℓ ^ 2 * g.logEnd (ℓ + 1) ≤ (1 + ωs ℓ) * g.ratio ℓ ^ 2 * g.logEnd (ℓ + 1) := by
        nlinarith [mul_nonneg hy hL]
      exact this.trans (h1.trans (mul_le_mul_of_nonneg_right h2' hκ0))

/-- [INC-P000, Lemma `lem:structA`, (S4), the paper's form] Under the hypotheses of
`hyAlg_ae_structA_S4`, `N_c(t_(ℓ+1)) ≥ min(U_(ℓ+1), y_ℓ L_(ℓ+1) / κ(μ̂_ℓ))` (with `x / 0 = 0` in
Lean; `hyAlg_ae_structA_S4` is the stronger form). -/
lemma hyAlg_ae_structA_S4_min (w₀ β : ℝ) (hw₀ : 0 ≤ w₀) (ωs θ γ : ℕ → ℝ)
    (g : Grid (Fintype.card α)) (hK : 2 ≤ Fintype.card α) {ν : Kernel α ℝ} [IsMarkovKernel ν]
    (hν : ν ∈ unitBandits α) :
    ∀ᵐ ω ∂(trajMeasure (hyAlg w₀ β ωs θ γ g : Algorithm Unit α ℝ) (Environment.bandit ν)),
      ∀ ℓ, ℓ ≠ 0 → 0 ≤ θ ℓ → 0 ≤ ωs ℓ → 2 ≤ g.imedEnd θ ℓ →
      (2 * (Fintype.card α - 1 : ℕ) * g.netSize β (ℓ + 1) : ℝ) ≤
        g.imedEnd θ ℓ * Real.log (g.imedEnd θ ℓ) →
      Fintype.card α * (g.netSize β (ℓ + 1) + Fintype.card α) ≤ g.t (ℓ + 1) - g.imedEnd θ ℓ →
      HY.pseudoMean w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ)
        (HY.reference w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ)
          (g.netSize β ℓ)) < 1 →
      ∀ c, min (g.netSize β (ℓ + 1) : ℝ) (g.ratio ℓ ^ 2 * g.logEnd (ℓ + 1) /
          Real.log (1 / (1 - HY.pseudoMean w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω)
            (g.t ℓ) (HY.reference w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ)
              (g.netSize β ℓ))))) ≤ pullCount IT.action c (g.t (ℓ + 1)) ω := by
  filter_upwards [hyAlg_ae_structA_S4 w₀ β hw₀ ωs θ γ g hK hν] with ω hS4
  intro ℓ hℓ hθ hω0 hσ2 hσU hlong hμ c
  rcases hS4 ℓ hℓ hθ hω0 hσ2 hσU hlong hμ c with h | h
  · exact (min_le_left _ _).trans (by exact_mod_cast h)
  · refine (min_le_right _ _).trans ?_
    set κ := Real.log (1 / (1 - HY.pseudoMean w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω)
      (g.t ℓ) (HY.reference w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ)
        (g.netSize β ℓ)))) with hκ
    rcases le_or_gt κ 0 with hκ0 | hκ0
    · rw [div_eq_mul_inv]
      have : κ⁻¹ ≤ 0 := inv_nonpos.mpr hκ0
      have hyL : 0 ≤ g.ratio ℓ ^ 2 * g.logEnd (ℓ + 1) :=
        mul_nonneg (sq_nonneg _) (g.logEnd_pos (by omega)).le
      exact (mul_nonpos_of_nonneg_of_nonpos hyL this).trans (Nat.cast_nonneg _)
    · rwa [div_le_iff₀ hκ0]

/-- [INC-P000, Lemma `lem:imedround`, consequence, along a run] `hyAlg_ae_pullCount_le_max` with
the hypothesis `K̃_ℓ(c) ≥ D` in `ℝ≥0∞` (so `K̃_ℓ(c) = ∞` is allowed): along almost every run of HY
(`w₀ ≥ 0`, on a grid for `K` arms) on an instance of `𝒫`, for a batch `ℓ + 1` (`ℓ ≥ 1`) and an
arm `c ≠ ĉ_ℓ` with `K̃_ℓ(c) ≥ D > 0`, every round `t'` of the IMED phase of the batch has
`N_c(t') ≤ max(N_c(t_ℓ), 1 + y_ℓ log t' / D)`. At an IMED round that pulls `c`, `K̃_ℓ(c) < ∞`
(Lemma `lem:imedround`). -/
lemma hyAlg_ae_pullCount_le_max' (w₀ β : ℝ) (hw₀ : 0 ≤ w₀) (ωs θ γ : ℕ → ℝ)
    (g : Grid (Fintype.card α)) {ν : Kernel α ℝ} [IsMarkovKernel ν] (hν : ν ∈ unitBandits α) :
    ∀ᵐ ω ∂(trajMeasure (hyAlg w₀ β ωs θ γ g : Algorithm Unit α ℝ) (Environment.bandit ν)),
      ∀ ℓ, ℓ ≠ 0 → ∀ c, c ≠ HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) →
      ∀ D : ℝ, 0 < D →
      ENNReal.ofReal D ≤ HY.imedKinf w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) c →
      ∀ t', g.t ℓ ≤ t' → t' ≤ g.imedEnd θ ℓ → t' ≤ g.t (ℓ + 1) →
        (pullCount IT.action c t' ω : ℝ) ≤
          max (pullCount IT.action c (g.t ℓ) ω : ℝ) (1 + g.ratio ℓ ^ 2 * Real.log t' / D) := by
  filter_upwards [hyAlg_ae_action_eq w₀ β ωs θ γ g (Environment.bandit ν),
    ae_feedback_mem_Icc (alg := hyAlg w₀ β ωs θ γ g) hν,
    hyAlg_ae_one_le_pullCount w₀ β ωs θ γ g (Environment.bandit ν)] with ω hω hfb hN1
  intro ℓ hℓ c hc D hD hDK t' ht'1 ht'2 ht'3
  have hℓ1 : 1 ≤ ℓ := Nat.one_le_iff_ne_zero.mpr hℓ
  have hy1 : 1 ≤ g.ratio ℓ ^ 2 := one_le_pow₀ (g.one_le_ratio _)
  have hy0 : 0 < g.ratio ℓ ^ 2 := by linarith
  have htℓ : 2 ≤ g.t ℓ := g.two_le_t hℓ1
  have hg : Monotone fun k : ℕ ↦ g.ratio ℓ ^ 2 * Real.log ((k : ℝ) + 1) := by
    intro k k' hkk'
    refine mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) ?_) hy0.le
    exact_mod_cast Nat.add_le_add_right hkk' 1
  have h := pullCount_le_max_of_forall (A := IT.action) (ω := ω) (c := c) hD hg ht'1
    (fun k hk1 hk2 hAk ↦ by
      have hb : g.batchOf k = ℓ + 1 := g.batchOf_eq_iff.mpr ⟨hk1, by omega⟩
      have himed : k + 1 ≤ g.imedEnd θ ℓ := by omega
      have hA := hω k
      rw [HY.next_of_imedPhase w₀ β ωs θ γ g hb hℓ himed] at hA
      have hfbk : ∀ i, (history IT.obs IT.action IT.feedback k ω i).feedback ∈
          Set.Icc (0 : ℝ) 1 := fun i ↦ hfb i
      have hlead := HY.leader_history (O := IT.obs) (A := IT.action) (Y := IT.feedback)
        (ω := ω) hk1 w₀
      have hpos : 0 < (HY.count (history IT.obs IT.action IT.feedback k ω) (g.t ℓ)
          (HY.leader w₀ (history IT.obs IT.action IT.feedback k ω) (g.t ℓ)) : ℝ) + w₀ := by
        rw [HY.count_history hk1]
        have : (1 : ℝ) ≤ pullCount IT.action
            (HY.leader w₀ (history IT.obs IT.action IT.feedback k ω) (g.t ℓ)) (g.t ℓ) ω := by
          exact_mod_cast hN1 ℓ hℓ1 _
        linarith
      have hne : HY.imedArm w₀ (g.ratio ℓ ^ 2) (history IT.obs IT.action IT.feedback k ω)
          (g.t ℓ) ≠ HY.leader w₀ (history IT.obs IT.action IT.feedback k ω) (g.t ℓ) := by
        rw [← hA, hAk, hlead]
        exact hc
      have hNk : 1 ≤ pullCount' k (history IT.obs IT.action IT.feedback k ω)
          (HY.imedArm w₀ (g.ratio ℓ ^ 2) (history IT.obs IT.action IT.feedback k ω) (g.t ℓ)) := by
        rw [← hA, hAk, ← pullCount_eq_pullCount']
        exact (hN1 ℓ hℓ1 c).trans (pullCount_mono _ hk1 _)
      have hk1' : 1 ≤ k := by omega
      have hfin := HY.imedKinf_imedArm_ne_top hw₀ hy0 hfbk hpos hk1' hne hNk
      have hlt := HY.mul_toReal_imedKinf_add_lt hw₀ hy0 hfbk hpos hk1' hne hNk
      rw [← hA, hAk, ← pullCount_eq_pullCount', HY.imedKinf_history hk1] at hlt
      rw [← hA, hAk, HY.imedKinf_history hk1] at hfin
      have hDK' : D ≤ (HY.imedKinf w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω)
          (g.t ℓ) c).toReal := (ENNReal.ofReal_le_iff_le_toReal hfin).mp hDK
      have hNk' : (1 : ℝ) ≤ pullCount IT.action c k ω := by
        exact_mod_cast (hN1 ℓ hℓ1 c).trans (pullCount_mono _ hk1 _)
      have hlogN : 0 ≤ g.ratio ℓ ^ 2 * Real.log (pullCount IT.action c k ω) :=
        mul_nonneg hy0.le (Real.log_nonneg hNk')
      have hmul : (pullCount IT.action c k ω : ℝ) * D ≤ (pullCount IT.action c k ω : ℝ) *
          (HY.imedKinf w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) c).toReal :=
        mul_le_mul_of_nonneg_left hDK' (by linarith)
      linarith)
  have hcast : g.ratio ℓ ^ 2 * Real.log (((t' - 1 : ℕ) : ℝ) + 1) = g.ratio ℓ ^ 2 * Real.log t' := by
    rw [Nat.cast_sub (by omega), Nat.cast_one, sub_add_cancel]
  rw [hcast] at h
  exact h

/-- [INC-P000, Lemma `lem:imedround`, consequence, along a run] Along almost every run of HY
(`w₀ ≥ 0`, on a grid for `K` arms) on an instance of `𝒫`, for a batch `ℓ + 1` (`ℓ ≥ 1`) and an arm
`c` other than the leader `ĉ_ℓ` with IMED divergence `K̃_ℓ(c) ≥ D > 0` (both frozen at `t_ℓ`),
every round `t'` of the batch in its IMED phase (`t_ℓ ≤ t' ≤ s_ℓ`, `t' ≤ t_(ℓ+1)`) has
`N_c(t') ≤ max(N_c(t_ℓ), 1 + y_ℓ log t' / D)`: `hyAlg_ae_pullCount_le_max'`, since `D > 0`
forces `K̃_ℓ(c) < ∞`. -/
lemma hyAlg_ae_pullCount_le_max (w₀ β : ℝ) (hw₀ : 0 ≤ w₀) (ωs θ γ : ℕ → ℝ)
    (g : Grid (Fintype.card α)) {ν : Kernel α ℝ} [IsMarkovKernel ν] (hν : ν ∈ unitBandits α) :
    ∀ᵐ ω ∂(trajMeasure (hyAlg w₀ β ωs θ γ g : Algorithm Unit α ℝ) (Environment.bandit ν)),
      ∀ ℓ, ℓ ≠ 0 → ∀ c, c ≠ HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) →
      ∀ D : ℝ, 0 < D →
      D ≤ (HY.imedKinf w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) c).toReal →
      ∀ t', g.t ℓ ≤ t' → t' ≤ g.imedEnd θ ℓ → t' ≤ g.t (ℓ + 1) →
        (pullCount IT.action c t' ω : ℝ) ≤
          max (pullCount IT.action c (g.t ℓ) ω : ℝ) (1 + g.ratio ℓ ^ 2 * Real.log t' / D) := by
  filter_upwards [hyAlg_ae_pullCount_le_max' w₀ β hw₀ ωs θ γ g hν] with ω h
  intro ℓ hℓ c hc D hD hDK
  refine h ℓ hℓ c hc D hD ((ENNReal.ofReal_le_iff_le_toReal fun htop ↦ ?_).2 hDK)
  rw [htop, ENNReal.toReal_top] at hDK
  linarith

/-- [INC-P000, Lemma `lem:logcountC`, along a run] Along almost every run of HY (`w₀ ≥ 0`, on a grid
for `K` arms) on an instance of `𝒫`, for a batch `ℓ + 1` (`ℓ ≥ 1`) whose IMED level is
`m̃⋆_ℓ ≤ ρ < 1`: if the IMED index of an arm `c` at the end of the batch is at least `y_ℓ v`
(`J_ℓ(c, t_(ℓ+1) + 1) ≥ y_ℓ v`, which holds for every arm when the water level of the batch is at
least `v`, (W1); the paper's `v = (1 - δ) L_j` for a `(δ, j)`-high batch), then
`v ≤ (κ(ρ) + 1) N_c(t_(ℓ+1))`: `J/y ≤ N K̃_ℓ(c) + log N ≤ κ(ρ) N + N`. -/
lemma hyAlg_ae_logcountC (w₀ β : ℝ) (hw₀ : 0 ≤ w₀) (ωs θ γ : ℕ → ℝ)
    (g : Grid (Fintype.card α)) {ν : Kernel α ℝ} [IsMarkovKernel ν] (hν : ν ∈ unitBandits α) :
    ∀ᵐ ω ∂(trajMeasure (hyAlg w₀ β ωs θ γ g : Algorithm Unit α ℝ) (Environment.bandit ν)),
      ∀ ℓ, ℓ ≠ 0 → ∀ (c : α) (v ρ : ℝ), ρ < 1 →
      HY.pseudoMean w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ)
        (HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ)) ≤ ρ →
      ((g.ratio ℓ ^ 2 * v : ℝ) : EReal) ≤ HY.imedIndex w₀ (g.ratio ℓ ^ 2)
        (history IT.obs IT.action IT.feedback (g.t (ℓ + 1)) ω) (g.t ℓ) c →
      v ≤ (Real.log (1 / (1 - ρ)) + 1) * pullCount IT.action c (g.t (ℓ + 1)) ω := by
  filter_upwards [hyAlg_ae_one_le_pullCount w₀ β ωs θ γ g (Environment.bandit ν),
    ae_feedback_mem_Icc (alg := hyAlg w₀ β ωs θ γ g) hν] with ω hN1 hfb
  intro ℓ hℓ c v ρ hρ hμρ hJ
  set h := history IT.obs IT.action IT.feedback (g.t ℓ) ω with hh
  set y := g.ratio ℓ ^ 2 with hy
  set N := pullCount IT.action c (g.t (ℓ + 1)) ω with hN
  have hy1 : 1 ≤ y := one_le_pow₀ (g.one_le_ratio ℓ)
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1 (ℓ + 1) (by omega) c
  have hfbh : ∀ i, (h i).feedback ∈ Set.Icc (0 : ℝ) 1 := fun i ↦ hfb i
  set μ' := HY.pseudoMean w₀ h (g.t ℓ) (HY.leader w₀ h (g.t ℓ)) with hμ'
  have hμ'0 : 0 ≤ μ' := HY.pseudoMean_nonneg' hw₀ hfbh _
  have hρ0 : 0 ≤ ρ := hμ'0.trans hμρ
  have hpos : 0 < (HY.count h (g.t ℓ) c : ℝ) + w₀ := by
    rw [hh, HY.count_history le_rfl]
    have : (1 : ℝ) ≤ pullCount IT.action c (g.t ℓ) ω := by exact_mod_cast hN1 ℓ (by omega) c
    linarith
  set κ := Real.log (1 / (1 - ρ)) with hκ
  have hκ0 : 0 ≤ κ := Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
  -- `K̃_ℓ(c) ≤ κ(m̃⋆) ≤ κ(ρ)`
  have hK : HY.imedKinf w₀ h (g.t ℓ) c ≤ ENNReal.ofReal κ := by
    unfold HY.imedKinf
    rw [← hμ']
    refine (HY.pseudoKinf_le_ofReal_log hw₀ (hμρ.trans_lt hρ) hμ'0 hfbh hpos).trans ?_
    refine ENNReal.ofReal_le_ofReal (Real.log_le_log (one_div_pos.mpr (by linarith)) ?_)
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  rw [HY.imedIndex_history (g.strictMono.monotone (Nat.le_succ ℓ)), ← hN, ← hh] at hJ
  have hprod : ((N : ℝ≥0∞) * HY.imedKinf w₀ h (g.t ℓ) c : ℝ≥0∞) ≤ ENNReal.ofReal (N * κ) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    gcongr
  have hNκ : 0 ≤ (N : ℝ) * κ := mul_nonneg (Nat.cast_nonneg _) hκ0
  have hJ' : ((y * v : ℝ) : EReal) ≤ ((N * κ + y * Real.log N : ℝ) : EReal) := by
    refine hJ.trans ?_
    rw [EReal.coe_add]
    gcongr
    refine (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hprod).trans_eq ?_
    rw [EReal.coe_ennreal_ofReal, max_eq_left hNκ]
  have hJr := EReal.coe_le_coe_iff.mp hJ'
  have hlog : Real.log N ≤ N := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  nlinarith

/-- [INC-P000, Lemma `lem:leaderA`, last claim, along a run] Along almost every run of HY
(`w₀ ≥ 0`, on a grid for `K ≥ 2` arms) on an instance of `𝒫`, if the batch `ℓ + 1` (`ℓ ≥ 1`)
satisfies the hypotheses of `hyAlg_ae_structA` and every arm well sampled at `t_(ℓ+1)` has an
empirical mean at most `m_c + ε` (the event `𝒜_(ℓ+1)`, read on the run), then the test level at
`t_(ℓ+1)` is `μ̂_(ℓ+1) ≤ m⋆ + ε`: the leader `ĉ_ℓ` is well sampled at `t_(ℓ+1)` by (S2), so the
reference is a well-sampled arm, and `m̃ ≤ m̂` (Lemma `lem:pseudo`(iii)). -/
lemma hyAlg_ae_testLevel_le (w₀ β : ℝ) (hw₀ : 0 ≤ w₀) (ωs θ γ : ℕ → ℝ)
    (g : Grid (Fintype.card α)) (hK : 2 ≤ Fintype.card α) {ν : Kernel α ℝ} [IsMarkovKernel ν]
    (hν : ν ∈ unitBandits α) :
    ∀ᵐ ω ∂(trajMeasure (hyAlg w₀ β ωs θ γ g : Algorithm Unit α ℝ) (Environment.bandit ν)),
      ∀ ℓ, ℓ ≠ 0 → 0 ≤ θ ℓ → 0 ≤ (1 + ωs ℓ) * g.ratio ℓ ^ 2 → 2 ≤ g.imedEnd θ ℓ →
      (2 * (Fintype.card α - 1 : ℕ) * g.netSize β (ℓ + 1) : ℝ) ≤
        g.imedEnd θ ℓ * Real.log (g.imedEnd θ ℓ) →
      Fintype.card α * (g.netSize β (ℓ + 1) + Fintype.card α) ≤ g.t (ℓ + 1) - g.imedEnd θ ℓ →
      ∀ ε : ℝ, (∀ c, g.netSize β (ℓ + 1) ≤ 2 * pullCount IT.action c (g.t (ℓ + 1)) ω →
        HY.pseudoMean 0 (history IT.obs IT.action IT.feedback (g.t (ℓ + 1)) ω) (g.t (ℓ + 1)) c ≤
          (∫ y, id y ∂(ν c)) + ε) →
      HY.pseudoMean w₀ (history IT.obs IT.action IT.feedback (g.t (ℓ + 1)) ω) (g.t (ℓ + 1))
          (HY.reference w₀ (history IT.obs IT.action IT.feedback (g.t (ℓ + 1)) ω) (g.t (ℓ + 1))
            (g.netSize β (ℓ + 1))) ≤ (⨆ b, ∫ y, id y ∂(ν b)) + ε := by
  filter_upwards [hyAlg_ae_structA w₀ β ωs θ γ g (Environment.bandit ν) hK,
    ae_feedback_mem_Icc (alg := hyAlg w₀ β ωs θ γ g) hν] with ω hS hfb
  intro ℓ hℓ hθ hωy hσ2 hσU hlong ε hA
  obtain ⟨-, -, hS2⟩ := hS ℓ hℓ hθ hωy hσ2 hσU hlong _ _ _ rfl rfl (fun _ _ ↦ rfl)
  set h₁ := history IT.obs IT.action IT.feedback (g.t (ℓ + 1)) ω with hh₁
  set L := HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ)
  have hW : HY.IsWellSampled h₁ (g.t (ℓ + 1)) (g.netSize β (ℓ + 1)) L := by
    rw [hh₁, HY.isWellSampled_history_iff_le_pullCount le_rfl]
    have := Nat.sub_le (pullCount IT.action L (g.t (ℓ + 1)) ω)
      (pullCount IT.action L (g.imedEnd θ ℓ) ω)
    omega
  set r := HY.reference w₀ h₁ (g.t (ℓ + 1)) (g.netSize β (ℓ + 1))
  have hrW : g.netSize β (ℓ + 1) ≤ 2 * pullCount IT.action r (g.t (ℓ + 1)) ω := by
    have := (HY.reference_spec (w₀ := w₀) hW).1
    rwa [hh₁, HY.isWellSampled_history_iff_le_pullCount le_rfl] at this
  have h1 : HY.pseudoMean w₀ h₁ (g.t (ℓ + 1)) r ≤ HY.pseudoMean 0 h₁ (g.t (ℓ + 1)) r :=
    HY.pseudoMean_le_pseudoMean_zero hw₀ fun i ↦ (hfb i).1
  have h2 := hA r hrW
  have h3 : (∫ y, id y ∂(ν r)) ≤ ⨆ b, ∫ y, id y ∂(ν b) :=
    le_ciSup (f := fun b ↦ ∫ y, id y ∂(ν b)) (Set.finite_range _).bddAbove r
  linarith

/-- [INC-P000, Lemma `lem:countsA`, along a run] Along almost every run of HY (`w₀ ≥ 0`, on a grid
for `K ≥ 2` arms) on an instance of `𝒫`, if the batches `ℓ + 1` and `ℓ + 2` (`ℓ ≥ 1`) satisfy
the hypotheses of `hyAlg_ae_structA` with `ω ≥ 0`, `m⋆ + ε < 1`, the condition (T1)
`κ_ε L_(ℓ+1)^(β-1) ≥ 1` with `κ_ε = κ(m⋆ + ε) = log (1 / (1 - m⋆ - ε))`, and every arm well
sampled at `t_(ℓ+1)` has an empirical mean at most `m_c + ε` (the event `𝒜_(ℓ+1)` on the run),
then every arm has `N_c(t_(ℓ+2)) ≥ L_(ℓ+1) / κ_ε`; this is at least the count threshold
`u_(ℓ+2)(ε) = L_ℓ / κ_ε` of the paper (the paper's `ℓ` is `ℓ + 2`; its second claim is this lemma
one index lower). Step 1 of the paper's proof: (S4) at `ℓ + 1` and `μ̂_(ℓ+1) ≤ m⋆ + ε`. -/
lemma hyAlg_ae_countsA (w₀ β : ℝ) (hw₀ : 0 ≤ w₀) (ωs θ γ : ℕ → ℝ)
    (g : Grid (Fintype.card α)) (hK : 2 ≤ Fintype.card α) {ν : Kernel α ℝ} [IsMarkovKernel ν]
    (hν : ν ∈ unitBandits α) :
    ∀ᵐ ω ∂(trajMeasure (hyAlg w₀ β ωs θ γ g : Algorithm Unit α ℝ) (Environment.bandit ν)),
      ∀ ℓ, ℓ ≠ 0 →
      (∀ j, ℓ ≤ j → j ≤ ℓ + 1 → 0 ≤ θ j ∧ 0 ≤ ωs j ∧ 2 ≤ g.imedEnd θ j ∧
        (2 * (Fintype.card α - 1 : ℕ) * g.netSize β (j + 1) : ℝ) ≤
          g.imedEnd θ j * Real.log (g.imedEnd θ j) ∧
        Fintype.card α * (g.netSize β (j + 1) + Fintype.card α) ≤ g.t (j + 1) - g.imedEnd θ j) →
      ∀ ε : ℝ, (⨆ b, ∫ y, id y ∂(ν b)) + ε < 1 →
      1 ≤ Real.log (1 / (1 - ((⨆ b, ∫ y, id y ∂(ν b)) + ε))) * g.logEnd (ℓ + 1) ^ (β - 1) →
      (∀ c, g.netSize β (ℓ + 1) ≤ 2 * pullCount IT.action c (g.t (ℓ + 1)) ω →
        HY.pseudoMean 0 (history IT.obs IT.action IT.feedback (g.t (ℓ + 1)) ω) (g.t (ℓ + 1)) c ≤
          (∫ y, id y ∂(ν c)) + ε) →
      ∀ c, g.logEnd (ℓ + 1) / Real.log (1 / (1 - ((⨆ b, ∫ y, id y ∂(ν b)) + ε))) ≤
        pullCount IT.action c (g.t (ℓ + 2)) ω := by
  filter_upwards [hyAlg_ae_testLevel_le w₀ β hw₀ ωs θ γ g hK hν,
    hyAlg_ae_structA_S4 w₀ β hw₀ ωs θ γ g hK hν,
    ae_feedback_mem_Icc (alg := hyAlg w₀ β ωs θ γ g) hν] with ω hT hS4 hfb
  intro ℓ hℓ hR ε hmε hT1 hA c
  obtain ⟨hθ0, hω0, hσ0, hσU0, hlong0⟩ := hR ℓ le_rfl (by omega)
  obtain ⟨hθ1, hω1, hσ1, hσU1, hlong1⟩ := hR (ℓ + 1) (by omega) le_rfl
  have hμ := hT ℓ hℓ hθ0 (by positivity) hσ0 hσU0 hlong0 ε hA
  set μ := HY.pseudoMean w₀ (history IT.obs IT.action IT.feedback (g.t (ℓ + 1)) ω) (g.t (ℓ + 1))
    (HY.reference w₀ (history IT.obs IT.action IT.feedback (g.t (ℓ + 1)) ω) (g.t (ℓ + 1))
      (g.netSize β (ℓ + 1))) with hμdef
  set ms := ⨆ b, ∫ y, id y ∂(ν b)
  set κ := Real.log (1 / (1 - (ms + ε))) with hκ
  set L := g.logEnd (ℓ + 1) with hL
  have hμ0 : 0 ≤ μ := HY.pseudoMean_nonneg' hw₀ (fun i ↦ hfb i) _
  have hLpos : 0 < L := g.logEnd_pos (by omega)
  have hLb : 0 < L ^ (β - 1) := Real.rpow_pos_of_pos hLpos _
  have hκpos : 0 < κ := by
    by_contra hneg
    push Not at hneg
    have : κ * L ^ (β - 1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg hLb.le
    linarith
  rw [div_le_iff₀ hκpos]
  rcases hS4 (ℓ + 1) (by omega) hθ1 hω1 hσ1 hσU1 hlong1 (by linarith) c with h | h
  · -- `N_c ≥ U_(ℓ+2) ≥ L^β = L L^(β-1) ≥ L / κ`
    rw [g.netSize_succ β (by omega : 1 ≤ ℓ + 1)] at h
    have h1 : L ^ β ≤ pullCount IT.action c (g.t (ℓ + 2)) ω :=
      (Nat.le_ceil _).trans (by exact_mod_cast h)
    have h2 : L ^ β = L * L ^ (β - 1) := by
      rw [Real.rpow_sub_one hLpos.ne', mul_div_cancel₀ _ hLpos.ne']
    have h3 : L ≤ L ^ β * κ := by
      rw [h2, mul_assoc]
      exact le_mul_of_one_le_right hLpos.le (by linarith [mul_comm κ (L ^ (β - 1))])
    exact h3.trans (mul_le_mul_of_nonneg_right h1 hκpos.le)
  · -- `N_c κ ≥ N_c κ(μ̂) ≥ y L_(ℓ+2) ≥ L`
    have hy : 1 ≤ g.ratio (ℓ + 1) ^ 2 := one_le_pow₀ (g.one_le_ratio _)
    have hLL : L ≤ g.logEnd (ℓ + 2) := by
      unfold Grid.logEnd
      refine Real.log_le_log (by exact_mod_cast (show 0 < g.t (ℓ + 1) by
        have := g.two_le_t (show 1 ≤ ℓ + 1 by omega); omega)) ?_
      exact_mod_cast g.strictMono.monotone (by omega)
    have hκμ : Real.log (1 / (1 - μ)) ≤ κ := by
      refine Real.log_le_log (one_div_pos.mpr (by linarith)) ?_
      exact one_div_le_one_div_of_le (by linarith) (by linarith)
    have hL2 : 0 ≤ g.logEnd (ℓ + 2) := hLpos.le.trans hLL
    calc L ≤ g.ratio (ℓ + 1) ^ 2 * g.logEnd (ℓ + 2) := by nlinarith
      _ ≤ _ := h
      _ ≤ _ := mul_le_mul_of_nonneg_left hκμ (Nat.cast_nonneg _)

/-- `ENNReal.ofReal z ≤ x` once `ENNReal.ofReal (z + a) ≤ x + ENNReal.ofReal a`, for `a ≥ 0`. -/
private lemma ofReal_le_of_ofReal_add_le {z a : ℝ} {x : ℝ≥0∞} (ha : 0 ≤ a)
    (h : ENNReal.ofReal (z + a) ≤ x + ENNReal.ofReal a) : ENNReal.ofReal z ≤ x := by
  by_cases hz0 : z ≤ 0
  · rw [ENNReal.ofReal_of_nonpos hz0]
    exact bot_le
  refine (ENNReal.add_le_add_iff_right (ENNReal.ofReal_ne_top :
    ENNReal.ofReal a ≠ ⊤)).mp ?_
  rwa [← ENNReal.ofReal_add (by linarith) ha]

/-- [INC-P000, Lemma `lem:leaderA`, along a run] Along almost every run of HY (`w₀ ≥ 0`, on a grid
for `K ≥ 2` arms) on an instance `ν` of `𝒫`, for the test at `t_(ℓ+2)` (the paper's `ℓ`; `ℓ ≥ 1`)
such that the batches `ℓ + 1` and `ℓ + 2` satisfy (R2) (the hypotheses of `hyAlg_ae_structA` at
the Lean indices `ℓ` and `ℓ + 1`, with `ω ≥ 0`). The constants: an accuracy `ε > 0`, an optimal
arm `a⋆`, a bound `m₂` of the means of the sub-optimal arms, the conditions of
Lemma `lem:constA`(a) (`m⋆ + ε < 1`, `m₂ + ε < m⋆ - 2ε`, `m_c + ε < m⋆ - 3ε` for every sub-optimal
`c`), `2 w₀ ≤ ε U_(ℓ+2)`, and a level `z` with `z + w₀ κ(m⋆ + ε) ≤ h̄_(ℓ+1) = (1 - γ_(ℓ+1)) y_ℓ
L_(ℓ+1)` (the paper's `z_ℓ = h̄_(ℓ-1) - w₀ κ(m⋆ + ε̄)` satisfies it). The events, read on the run
(each is implied by the paper's event on the stacks, since the empirical law of `c` at `t_j` is
`ν̂_(c, N_c(t_j))`):
* `𝒜_(ℓ+1)`, `𝒜_(ℓ+2)`: every arm well sampled at `t_j` has an empirical mean within `ε` of its
  mean;
* not `𝒱_(ℓ+2)`: it is not the case that `a⋆` is not well sampled at `t_(ℓ+2)` and
  `N_(a⋆)(t_(ℓ+1)) 𝒦_inf(ν̂_(a⋆)(t_(ℓ+1)), m₂ + ε) ≥ z`;
* not `Π_(ℓ+2)`: no sub-optimal `c` is not well sampled at `t_(ℓ+2)`, with
  `N_c(t_(ℓ+1)) 𝒦_inf(ν̂_c(t_(ℓ+1)), m⋆ + ε) ≥ z` and `m̂_c(t_(ℓ+2)) ≥ m⋆ - 3ε`.
Then: (i) some optimal arm is well sampled at `t_(ℓ+2)`, the reference `r_(ℓ+2)` is optimal and
`m⋆ - 2ε ≤ μ̂_(ℓ+2) ≤ m⋆ + ε`; (ii) every sub-optimal `c` has `m̂_c(t_(ℓ+2)) < m⋆ - 3ε` and
`K̃_(ℓ+2)(c) ≥ K̂_(ℓ+2)(c) ≥ ε² / 8`; (iii) the leader `ĉ_(ℓ+2)` is optimal; and
`μ̂_(ℓ+1) ≤ m⋆ + ε`. -/
lemma hyAlg_ae_leaderA (w₀ β : ℝ) (hw₀ : 0 ≤ w₀) (ωs θ γ : ℕ → ℝ)
    (g : Grid (Fintype.card α)) (hK : 2 ≤ Fintype.card α) {ν : Kernel α ℝ} [IsMarkovKernel ν]
    (hν : ν ∈ unitBandits α) :
    ∀ᵐ ω ∂(trajMeasure (hyAlg w₀ β ωs θ γ g : Algorithm Unit α ℝ) (Environment.bandit ν)),
      ∀ ℓ, ℓ ≠ 0 →
      (∀ j, ℓ ≤ j → j ≤ ℓ + 1 → 0 ≤ θ j ∧ 0 ≤ ωs j ∧ 2 ≤ g.imedEnd θ j ∧
        (2 * (Fintype.card α - 1 : ℕ) * g.netSize β (j + 1) : ℝ) ≤
          g.imedEnd θ j * Real.log (g.imedEnd θ j) ∧
        Fintype.card α * (g.netSize β (j + 1) + Fintype.card α) ≤ g.t (j + 1) - g.imedEnd θ j) →
      ∀ (ε m₂ z : ℝ) (a' : α), 0 < ε →
      (∫ y, id y ∂(ν a')) = ⨆ b, ∫ y, id y ∂(ν b) →
      (∀ c, (∫ y, id y ∂(ν c)) < ⨆ b, ∫ y, id y ∂(ν b) → (∫ y, id y ∂(ν c)) ≤ m₂) →
      (⨆ b, ∫ y, id y ∂(ν b)) + ε < 1 →
      m₂ + ε < (⨆ b, ∫ y, id y ∂(ν b)) - 2 * ε →
      (∀ c, (∫ y, id y ∂(ν c)) < ⨆ b, ∫ y, id y ∂(ν b) →
        (∫ y, id y ∂(ν c)) + ε < (⨆ b, ∫ y, id y ∂(ν b)) - 3 * ε) →
      2 * w₀ ≤ ε * g.netSize β (ℓ + 2) →
      z + w₀ * Real.log (1 / (1 - ((⨆ b, ∫ y, id y ∂(ν b)) + ε))) ≤
        (1 - γ (ℓ + 1)) * g.ratio ℓ ^ 2 * g.logEnd (ℓ + 1) →
      (∀ j, ℓ + 1 ≤ j → j ≤ ℓ + 2 → ∀ c, g.netSize β j ≤ 2 * pullCount IT.action c (g.t j) ω →
        |HY.pseudoMean 0 (history IT.obs IT.action IT.feedback (g.t j) ω) (g.t j) c -
          ∫ y, id y ∂(ν c)| ≤ ε) →
      ¬ (2 * pullCount IT.action a' (g.t (ℓ + 2)) ω < g.netSize β (ℓ + 2) ∧
        ENNReal.ofReal z ≤ (pullCount IT.action a' (g.t (ℓ + 1)) ω : ℝ≥0∞) *
          HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback (g.t (ℓ + 1)) ω) (g.t (ℓ + 1)) a'
            (m₂ + ε)) →
      (∀ c, (∫ y, id y ∂(ν c)) < ⨆ b, ∫ y, id y ∂(ν b) →
        ¬ (2 * pullCount IT.action c (g.t (ℓ + 2)) ω < g.netSize β (ℓ + 2) ∧
          ENNReal.ofReal z ≤ (pullCount IT.action c (g.t (ℓ + 1)) ω : ℝ≥0∞) *
            HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback (g.t (ℓ + 1)) ω) (g.t (ℓ + 1)) c
              ((⨆ b, ∫ y, id y ∂(ν b)) + ε) ∧
          (⨆ b, ∫ y, id y ∂(ν b)) - 3 * ε ≤
            HY.pseudoMean 0 (history IT.obs IT.action IT.feedback (g.t (ℓ + 2)) ω) (g.t (ℓ + 2))
              c)) →
      ((∃ a'', (∫ y, id y ∂(ν a'')) = ⨆ b, ∫ y, id y ∂(ν b) ∧
          g.netSize β (ℓ + 2) ≤ 2 * pullCount IT.action a'' (g.t (ℓ + 2)) ω) ∧
        (∫ y, id y ∂(ν (HY.reference w₀ (history IT.obs IT.action IT.feedback (g.t (ℓ + 2)) ω)
          (g.t (ℓ + 2)) (g.netSize β (ℓ + 2))))) = ⨆ b, ∫ y, id y ∂(ν b) ∧
        (⨆ b, ∫ y, id y ∂(ν b)) - 2 * ε ≤
          HY.pseudoMean w₀ (history IT.obs IT.action IT.feedback (g.t (ℓ + 2)) ω) (g.t (ℓ + 2))
            (HY.reference w₀ (history IT.obs IT.action IT.feedback (g.t (ℓ + 2)) ω) (g.t (ℓ + 2))
              (g.netSize β (ℓ + 2))) ∧
        HY.pseudoMean w₀ (history IT.obs IT.action IT.feedback (g.t (ℓ + 2)) ω) (g.t (ℓ + 2))
            (HY.reference w₀ (history IT.obs IT.action IT.feedback (g.t (ℓ + 2)) ω) (g.t (ℓ + 2))
              (g.netSize β (ℓ + 2))) ≤ (⨆ b, ∫ y, id y ∂(ν b)) + ε) ∧
      (∀ c, (∫ y, id y ∂(ν c)) < ⨆ b, ∫ y, id y ∂(ν b) →
        HY.pseudoMean 0 (history IT.obs IT.action IT.feedback (g.t (ℓ + 2)) ω) (g.t (ℓ + 2)) c <
          (⨆ b, ∫ y, id y ∂(ν b)) - 3 * ε ∧
        ENNReal.ofReal (ε ^ 2 / 8) ≤ HY.testKinf w₀
          (history IT.obs IT.action IT.feedback (g.t (ℓ + 2)) ω) (g.t (ℓ + 2))
          (g.netSize β (ℓ + 2)) c ∧
        HY.testKinf w₀ (history IT.obs IT.action IT.feedback (g.t (ℓ + 2)) ω) (g.t (ℓ + 2))
          (g.netSize β (ℓ + 2)) c ≤
          HY.imedKinf w₀ (history IT.obs IT.action IT.feedback (g.t (ℓ + 2)) ω) (g.t (ℓ + 2)) c) ∧
      (∫ y, id y ∂(ν (HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t (ℓ + 2)) ω)
          (g.t (ℓ + 2))))) = ⨆ b, ∫ y, id y ∂(ν b) ∧
      HY.pseudoMean w₀ (history IT.obs IT.action IT.feedback (g.t (ℓ + 1)) ω) (g.t (ℓ + 1))
          (HY.reference w₀ (history IT.obs IT.action IT.feedback (g.t (ℓ + 1)) ω) (g.t (ℓ + 1))
            (g.netSize β (ℓ + 1))) ≤ (⨆ b, ∫ y, id y ∂(ν b)) + ε := by
  filter_upwards [hyAlg_ae_structA w₀ β ωs θ γ g (Environment.bandit ν) hK,
    hyAlg_ae_structA_S3 w₀ β ωs θ γ g (Environment.bandit ν) hK,
    hyAlg_ae_reference_wellSampled w₀ β hw₀ ωs θ γ g hK hν,
    hyAlg_ae_threshold_eq w₀ β ωs θ γ g (Environment.bandit ν) hK,
    hyAlg_ae_one_le_pullCount w₀ β ωs θ γ g (Environment.bandit ν),
    ae_feedback_mem_Icc (alg := hyAlg w₀ β ωs θ γ g) hν] with ω hS hS3 hRef hThr hN1 hfb
  intro ℓ hℓ hR ε m₂ z a' hε ha' hm₂ hmε hm₂ε hsub hw₀U hz hA hV hPi
  -- notation
  set m : α → ℝ := fun c ↦ ∫ y, id y ∂(ν c) with hm
  set ms := ⨆ b, ∫ y, id y ∂(ν b) with hms
  have hle_ms : ∀ c, m c ≤ ms := fun c ↦ le_ciSup (Set.finite_range _).bddAbove c
  set h₁ := history IT.obs IT.action IT.feedback (g.t (ℓ + 1)) ω with hh₁
  set h₂ := history IT.obs IT.action IT.feedback (g.t (ℓ + 2)) ω with hh₂
  have hfb₁ : ∀ i, (h₁ i).feedback ∈ Set.Icc (0 : ℝ) 1 := fun i ↦ hfb i
  have hfb₂ : ∀ i, (h₂ i).feedback ∈ Set.Icc (0 : ℝ) 1 := fun i ↦ hfb i
  have hws : ∀ j c, HY.IsWellSampled (history IT.obs IT.action IT.feedback (g.t j) ω) (g.t j)
      (g.netSize β j) c ↔ g.netSize β j ≤ 2 * pullCount IT.action c (g.t j) ω := fun _ _ ↦
    HY.isWellSampled_history_iff_le_pullCount le_rfl _ _
  -- the structural facts at the Lean indices `ℓ` and `ℓ + 1`
  obtain ⟨hθ0, hω0, hσ0, hσU0, hlong0⟩ := hR ℓ le_rfl (by omega)
  obtain ⟨hθ1, hω1, hσ1, hσU1, hlong1⟩ := hR (ℓ + 1) (by omega) le_rfl
  have hωy0 : 0 ≤ (1 + ωs ℓ) * g.ratio ℓ ^ 2 := by positivity
  have hωy1 : 0 ≤ (1 + ωs (ℓ + 1)) * g.ratio (ℓ + 1) ^ 2 := by positivity
  obtain ⟨-, -, hS2₀⟩ := hS ℓ hℓ hθ0 hωy0 hσ0 hσU0 hlong0 _ _ _ rfl rfl (fun _ _ ↦ rfl)
  obtain ⟨-, -, hS2₁⟩ := hS (ℓ + 1) (by omega) hθ1 hωy1 hσ1 hσU1 hlong1 _ _ _ rfl rfl
    (fun _ _ ↦ rfl)
  have hRef₁ := hRef (ℓ + 1) (by omega) hθ1 hωy1 hσ1 hσU1 hlong1
  have hthr := hThr (ℓ + 1) (by omega) hθ0 hω0 hσ0 hσU0 hlong0
  simp only [Nat.add_sub_cancel] at hthr
  -- Step 0: the previous test level
  set μ₁ := HY.pseudoMean w₀ h₁ (g.t (ℓ + 1)) (HY.reference w₀ h₁ (g.t (ℓ + 1))
    (g.netSize β (ℓ + 1))) with hμ₁
  set r₁ := HY.reference w₀ h₁ (g.t (ℓ + 1)) (g.netSize β (ℓ + 1)) with hr₁
  have hW₁ : HY.IsWellSampled h₁ (g.t (ℓ + 1)) (g.netSize β (ℓ + 1))
      (HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ)) := by
    rw [hh₁, hws]
    have := Nat.sub_le (pullCount IT.action (HY.leader w₀
      (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ)) (g.t (ℓ + 1)) ω)
      (pullCount IT.action (HY.leader w₀
        (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ)) (g.imedEnd θ ℓ) ω)
    omega
  have hr₁W : g.netSize β (ℓ + 1) ≤ 2 * pullCount IT.action r₁ (g.t (ℓ + 1)) ω :=
    (hws (ℓ + 1) r₁).mp (HY.reference_spec hW₁).1
  have hμ₁_le : μ₁ ≤ m r₁ + ε := by
    have h1 : μ₁ ≤ HY.pseudoMean 0 h₁ (g.t (ℓ + 1)) r₁ :=
      HY.pseudoMean_le_pseudoMean_zero hw₀ fun i ↦ (hfb₁ i).1
    have h2 := (abs_le.mp (hA (ℓ + 1) le_rfl (by omega) r₁ hr₁W)).2
    linarith
  have hμ₁ms : μ₁ ≤ ms + ε := hμ₁_le.trans (by linarith [hle_ms r₁])
  have hμ₁0 : 0 ≤ μ₁ := HY.pseudoMean_nonneg' hw₀ hfb₁ _
  -- the rejected arms at `t_(ℓ+1)` (eq:rejA)
  have hrejA : ∀ c, 2 * pullCount IT.action c (g.t (ℓ + 2)) ω < g.netSize β (ℓ + 2) →
      ∀ ρ, μ₁ ≤ ρ → ρ < 1 → ENNReal.ofReal z ≤
        (pullCount IT.action c (g.t (ℓ + 1)) ω : ℝ≥0∞) * HY.pseudoKinf 0 h₁ (g.t (ℓ + 1)) c ρ := by
    intro c hc ρ hμρ hρ
    obtain ⟨-, ⟨-, hrej⟩, -⟩ := hS3 (ℓ + 1) (by omega) hθ1 hωy1 hσ1 hσU1 hlong1 _ _ _ rfl rfl
      (fun _ _ ↦ rfl) c hc
    rw [ite_eq_right (by omega : ¬ ℓ + 1 = 1), Nat.add_sub_cancel, hthr] at hrej
    have hN : 1 ≤ HY.count h₁ (g.t (ℓ + 1)) c := by
      rw [hh₁, HY.count_history le_rfl]
      exact hN1 (ℓ + 1) (by omega) c
    rw [← HY.count_history (n := g.t (ℓ + 1)) le_rfl] at hrej
    have key := HY.ofReal_le_mul_pseudoKinf_zero_add hw₀ hfb₁ hN hrej hμρ hρ
    rw [HY.count_history le_rfl] at key
    have hκ : w₀ * Real.log (1 / (1 - μ₁)) ≤ w₀ * Real.log (1 / (1 - (ms + ε))) := by
      refine mul_le_mul_of_nonneg_left (Real.log_le_log ?_ ?_) hw₀
      · exact one_div_pos.mpr (by linarith)
      · exact one_div_le_one_div_of_le (by linarith) (by linarith)
    have hκ0 : 0 ≤ w₀ * Real.log (1 / (1 - μ₁)) :=
      mul_nonneg hw₀ (Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith))
    -- `h̄_(ℓ+1) ≥ z + w₀ κ(μ̂_(ℓ+1))`, and the term `w₀ κ(μ̂_(ℓ+1))` cancels
    refine ofReal_le_of_ofReal_add_le hκ0 (le_trans (ENNReal.ofReal_le_ofReal ?_) key)
    linarith
  -- (i): some optimal arm is well sampled at `t_(ℓ+2)`
  have hU2 : 1 ≤ g.netSize β (ℓ + 2) := g.one_le_netSize β _
  have hi : ∃ a'', m a'' = ms ∧
      g.netSize β (ℓ + 2) ≤ 2 * pullCount IT.action a'' (g.t (ℓ + 2)) ω := by
    by_contra hno
    push Not at hno
    have hsubW : ∀ c, g.netSize β (ℓ + 2) ≤ 2 * pullCount IT.action c (g.t (ℓ + 2)) ω →
        m c < ms := fun c hc ↦ lt_of_le_of_ne (hle_ms c) fun he ↦ (hno c he).not_ge hc
    have hr₁sub : m r₁ < ms := hsubW r₁ hRef₁
    have ha'W : 2 * pullCount IT.action a' (g.t (ℓ + 2)) ω < g.netSize β (ℓ + 2) := by
      by_contra hc
      exact (hno a' ha').not_ge (not_lt.mp hc)
    have hμ₁m₂ : μ₁ ≤ m₂ + ε := hμ₁_le.trans (by linarith [hm₂ r₁ hr₁sub])
    exact hV ⟨ha'W, hrejA a' ha'W (m₂ + ε) hμ₁m₂ (by linarith)⟩
  obtain ⟨a'', ha''m, ha''W⟩ := hi
  -- the pseudo-means at `t_(ℓ+2)` of the well-sampled arms
  have hacc : ∀ c, g.netSize β (ℓ + 2) ≤ 2 * pullCount IT.action c (g.t (ℓ + 2)) ω →
      |HY.pseudoMean 0 h₂ (g.t (ℓ + 2)) c - m c| ≤ ε := fun c hc ↦ hA (ℓ + 2) (by omega) le_rfl c hc
  have hlow : ∀ c, g.netSize β (ℓ + 2) ≤ 2 * pullCount IT.action c (g.t (ℓ + 2)) ω →
      HY.pseudoMean 0 h₂ (g.t (ℓ + 2)) c - ε ≤ HY.pseudoMean w₀ h₂ (g.t (ℓ + 2)) c :=
    fun c hc ↦ HY.pseudoMean_zero_sub_le_of_two_mul_le hw₀ hfb₂ hU2
      (by rwa [hh₂, HY.count_history le_rfl]) hw₀U
  have hup : ∀ c, HY.pseudoMean w₀ h₂ (g.t (ℓ + 2)) c ≤ HY.pseudoMean 0 h₂ (g.t (ℓ + 2)) c :=
    fun c ↦ HY.pseudoMean_le_pseudoMean_zero hw₀ fun i ↦ (hfb₂ i).1
  set r₂ := HY.reference w₀ h₂ (g.t (ℓ + 2)) (g.netSize β (ℓ + 2)) with hr₂
  set μ₂ := HY.pseudoMean w₀ h₂ (g.t (ℓ + 2)) r₂ with hμ₂
  obtain ⟨hr₂W, ha''r₂⟩ := HY.reference_spec (w₀ := w₀)
    ((hws (ℓ + 2) a'').mpr ha''W)
  rw [← hr₂] at hr₂W ha''r₂
  have hr₂W' := (hws (ℓ + 2) r₂).mp hr₂W
  have hμ₂low : ms - 2 * ε ≤ μ₂ := by
    have := hlow a'' ha''W
    have := (abs_le.mp (hacc a'' ha''W)).1
    linarith
  have hμ₂up : μ₂ ≤ ms + ε := by
    have := hup r₂
    have := (abs_le.mp (hacc r₂ hr₂W')).2
    linarith [hle_ms r₂]
  have hr₂opt : m r₂ = ms := by
    by_contra hne
    have hlt : m r₂ < ms := lt_of_le_of_ne (hle_ms r₂) hne
    have := hup r₂
    have := (abs_le.mp (hacc r₂ hr₂W')).2
    linarith [hm₂ r₂ hlt]
  -- (ii): the sub-optimal arms
  have hii : ∀ c, m c < ms → HY.pseudoMean 0 h₂ (g.t (ℓ + 2)) c < ms - 3 * ε := by
    intro c hc
    by_cases hcW : g.netSize β (ℓ + 2) ≤ 2 * pullCount IT.action c (g.t (ℓ + 2)) ω
    · have := (abs_le.mp (hacc c hcW)).2
      linarith [hsub c hc]
    · by_contra hge
      exact hPi c hc ⟨by omega, hrejA c (by omega) (ms + ε) hμ₁ms hmε, not_lt.mp hge⟩
  have hμ₂1 : μ₂ < 1 := by linarith
  have hμ₂0 : 0 ≤ μ₂ := HY.pseudoMean_nonneg' hw₀ hfb₂ _
  refine ⟨⟨⟨a'', ha''m, ha''W⟩, hr₂opt, hμ₂low, hμ₂up⟩, fun c hc ↦ ?_, ?_, hμ₁ms⟩
  · have hc3 := hii c hc
    have hm3 : 0 < ms - 3 * ε := by
      have : 0 ≤ m c := (integral_id_mem_Icc_of_mem_unitLaws (hν.1 c)).1
      linarith [hsub c hc]
    have hN : 1 ≤ HY.count h₂ (g.t (ℓ + 2)) c := by
      rw [hh₂, HY.count_history le_rfl]
      exact hN1 (ℓ + 2) (by omega) c
    have hpos : 0 < (HY.count h₂ (g.t (ℓ + 2)) c : ℝ) + 0 := by
      have : (1 : ℝ) ≤ HY.count h₂ (g.t (ℓ + 2)) c := by exact_mod_cast hN
      linarith
    have h8 := HY.ofReal_sq_div_eight_le_pseudoKinf (w₀ := 0) le_rfl (μ := ms - 2 * ε)
      (q := ms - 3 * ε) (by linarith) (by linarith) hfb₂ hpos hc3.le (by linarith)
    rw [show ms - 2 * ε - (ms - 3 * ε) = ε by ring] at h8
    refine ⟨hc3, ?_, ?_⟩
    · refine h8.trans ((HY.pseudoKinf_mono le_rfl (by linarith) hμ₂low hμ₂1 hfb₂).trans ?_)
      exact HY.pseudoKinf_zero_le hw₀ hμ₂1 hμ₂0 hfb₂ hN
    · -- `K̃ ≥ K̂`: the leader has the largest pseudo-mean
      exact HY.testKinf_le_imedKinf hw₀ hfb₂ (by linarith)
  · -- (iii): the leader is optimal
    set L₂ := HY.leader w₀ h₂ (g.t (ℓ + 2)) with hL₂
    by_contra hne
    have hlt : m L₂ < ms := lt_of_le_of_ne (hle_ms L₂) hne
    have h1 := HY.pseudoMean_le_leader w₀ h₂ (g.t (ℓ + 2)) r₂
    have h2 := hup L₂
    have h3 := hii L₂ hlt
    rw [← hL₂] at h1
    linarith

end Incognita.BatchedBandits
