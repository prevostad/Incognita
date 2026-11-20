/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.HY.GoodBatch
public import Incognita.BatchedBandits.HighBatches

/-! # High batches of HY when `x = 1`

[INC-P000, Lemmas `lem:levelC`, `lem:goodhigh`, `lem:fewC`, `lem:optW`, `lem:logcountC`,
`lem:pullsC` and `lem:sumC`], along almost every run of HY. A batch `i ≥ 2` of the paper (Lean
rounds `[t_(i-1), t_i)`, statistics frozen at `t_(i-1)`) is high at the level `v` for an arm `c`
when the IMED index of `c` at its end is at least `y_(i-1) v`: `J_(i-1)(c, t_i + 1) ≥ y_(i-1) v`
(in Lean `HY.imedIndex w₀ y (history … (t i)) (t (i-1)) c`); the paper's `(δ, j)`-high batch
(Definition `def:high`, `Λ_i ≥ (1 - δ) L_j`) is high at the level `v = (1 - δ) L_j` for every
arm, by (W1).

* `HY.sub_two_mul_le_pseudoMean`: the step of Lemma `lem:pseudo`(iii) used by the inclusions of
  `lem:fewC` and by `lem:optW`.
* `hyAlg_ae_le_log_pullCount_leader`: Step 1 of the proof of `lem:goodhigh`, the leader of a
  high batch has `log N_(ĉ_(i-1))(t_i) ≥ v` (its IMED divergence is `0`).
* `hyAlg_ae_card_le_card_filter_le_pullCount_leader_add`: Steps 1–2 of `lem:goodhigh` for a set
  of high batches: every leader is observed at least `u ≤ e^v` times at the end of its batch, and
  all but at most `K` of the batches have a leader observed at least `u` times at their start
  (the set `S_go`).
* `hyAlg_ae_exists_mem_pullCount_lt_and_le_mul_pseudoKinf`: the common step of the proof of
  `lem:fewC`: an arm `c` with fewer than `u` observations, in a family of high batches whose IMED
  levels are at most `r' < 1`, carries at some batch start `t_(i-1)` the evidence
  `N_c(t_(i-1)) 𝒦_inf(ν̂_c(t_(i-1)), r') ≥ (1 - δ)(v - log u) - w₀ κ(r')` with
  `1 ≤ N_c(t_(i-1)) < u`, unless the family is too small (the chain, Lemma `lem:chain`).
* `hyAlg_ae_exists_mem_pullCount_lt_and_le_mul_pseudoKinf_of_pseudoMean_leader_lt`,
  `hyAlg_ae_pullCount_lt_and_exists_mem_le_mul_pseudoKinf_of_le_pseudoMean`: the two inclusions
  of `lem:fewC`, `𝒟_j^c ∩ 𝒰_j ⊂ 𝒱⋆_j` and `𝒟_j^c ∩ {m̂_a(t_(j-1)) ≥ m⋆ - 3ε} ⊂ 𝒱_(a,j)`, read
  on the run.
* `hyAlg_ae_integral_reference_eq_iSup`: Lemma `lem:optW`, on the traces of
  `𝒟_j^c ∩ (𝒱⋆_j)^c`: an optimal arm is well sampled at `t_(j-1)`, the reference is optimal, the
  test level is accurate, and the sub-optimal well-sampled arms have pseudo-means below
  `m⋆ - 2ε`.
* `hyAlg_ae_le_mul_pullCount_of_le_imedIndex_leader`: Lemma `lem:logcountC`.
* `HY.pseudoMean_lt_and_ne_leader_and_pseudoKinf_le_testKinf`,
  `hyAlg_ae_pullCount_le_card_add_div`, `hyAlg_ae_pullCount_le_max_of_le_imedKinf`:
  Lemma `lem:pullsC`(i)–(iii); `pullCount_le_max_of_forall_add_one` (the last pull,
  `HY/Imed.lean`) and `hyAlg_ae_pullCount_add_one_le` (one round of the batch) are their steps.
* `hyAlg_ae_le_card_filter_le_imedIndex`: Lemma `lem:levelC`, many batches high for every arm,
  with a rank independent of the run (the rank of `exists_rank_le_card_filter_le`);
  `hyAlg_ae_le_card_filter_le_imedIndex_and_le_pullCount_leader`: at least `M + 2` of them have a
  leader observed `u` times at their start (with `lem:goodhigh`).
* `Grid.sum_sub_mul_rpow_neg_le`: Lemma `lem:sumC`, with `one_div_one_sub_exp_neg_le` of
  `LogInequalities`.

The paper's events `𝒟_j`, `𝒱⋆_j`, `𝒱_a,j` (Definition `def:evC`) are events on the reward stacks;
here their traces on the run are used (`HY.pseudoMean 0`, `HY.pseudoKinf 0` at the counts
`N_c(t_i)`), as in `HY/Structure.lean`.
-/

@[expose] public section

open Learning Finset MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace Incognita.BatchedBandits

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α]

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- [INC-P000, Lemma `lem:pseudo`(iii), as used in the proofs of Lemmas `lem:fewC` and `lem:optW`]
For rewards in `[0, 1]`, `w₀ ≥ 0`, `ε ≥ 0` and an arm with `N_c ≥ 1`, `N_c ≥ u` and `w₀ ≤ ε u`,
an empirical mean `m̂_c ≥ m - ε` gives the pseudo-mean `m̃_c ≥ m - 2ε`. -/
lemma HY.sub_two_mul_le_pseudoMean {n : ℕ} {h : Hist Unit α ℝ n} {r : ℕ} {c : α} {w₀ ε u m : ℝ}
    (hw₀ : 0 ≤ w₀) (hε : 0 ≤ ε) (hfb : ∀ i, (h i).feedback ∈ Set.Icc (0 : ℝ) 1)
    (hN : 1 ≤ HY.count h r c) (hu : u ≤ HY.count h r c) (hwu : w₀ ≤ ε * u)
    (hm : m - ε ≤ HY.pseudoMean 0 h r c) : m - 2 * ε ≤ HY.pseudoMean w₀ h r c := by
  have h1 := HY.pseudoMean_zero_sub_le_pseudoMean hw₀ hfb hN
  have hN' : (1 : ℝ) ≤ HY.count h r c := by exact_mod_cast hN
  have h2 : w₀ / ((HY.count h r c : ℝ) + w₀) ≤ ε := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- For nonnegative rewards and `w₀ ≥ 0`, an empirical mean within `ε` of `m` gives the
pseudo-mean `m̃_c ≤ m + ε` (the pseudo-mean is at most the empirical mean,
`HY.pseudoMean_le_pseudoMean_zero`). -/
lemma HY.pseudoMean_le_add_of_abs_sub_le {n : ℕ} {h : Hist Unit α ℝ n} {r : ℕ} {c : α}
    {w₀ ε m : ℝ} (hw₀ : 0 ≤ w₀) (hdev : |HY.pseudoMean 0 h r c - m| ≤ ε)
    (hfb : ∀ i, 0 ≤ (h i).feedback) : HY.pseudoMean w₀ h r c ≤ m + ε := by
  have := HY.pseudoMean_le_pseudoMean_zero (h := h) (r := r) (c := c) hw₀ hfb
  linarith [(abs_le.mp hdev).2]

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- [INC-P000, proofs of Lemmas `lem:fewC` and `lem:optW`, a well-observed arm beats the leader]
For rewards in `[0, 1]`, `w₀, ε ≥ 0` and an arm `c` with `N_c ≥ 1`, `N_c ≥ u`, `w₀ ≤ ε u` and
`|m̂_c - m| ≤ ε`, the leader has `m̃_(ĉ) ≥ m - 2ε` (`HY.sub_two_mul_le_pseudoMean` and
`HY.pseudoMean_le_leader`). -/
lemma HY.sub_two_mul_le_pseudoMean_leader {n : ℕ} {h : Hist Unit α ℝ n} {r : ℕ} {c : α}
    {w₀ ε u m : ℝ} (hw₀ : 0 ≤ w₀) (hε : 0 ≤ ε) (hfb : ∀ i, (h i).feedback ∈ Set.Icc (0 : ℝ) 1)
    (hN : 1 ≤ HY.count h r c) (hu : u ≤ HY.count h r c) (hwu : w₀ ≤ ε * u)
    (hdev : |HY.pseudoMean 0 h r c - m| ≤ ε) :
    m - 2 * ε ≤ HY.pseudoMean w₀ h r (HY.leader w₀ h r) :=
  (HY.sub_two_mul_le_pseudoMean hw₀ hε hfb hN hu hwu (by linarith [(abs_le.mp hdev).1])).trans
    (HY.pseudoMean_le_leader w₀ h r c)

/-- [INC-P000, proof of Lemma `lem:goodhigh`, Step 1, along a run] Along almost every run of HY
(`w₀ ≥ 0`) on an instance of `𝒫`, for a batch `ℓ + 1` (`ℓ ≥ 1`) high at the level `v` for its
leader `ĉ_ℓ` (`J_ℓ(ĉ_ℓ, t_(ℓ+1) + 1) ≥ y_ℓ v`), the leader has `log N_(ĉ_ℓ)(t_(ℓ+1)) ≥ v`: its
IMED divergence is `0`, so its index is `y_ℓ log N_(ĉ_ℓ)(t_(ℓ+1))`. (With `v = (1 - δ) L_j` this
is the paper's `N_(ĉ_(i-1))(t_i) ≥ t_j^(1-δ)`.) -/
lemma hyAlg_ae_le_log_pullCount_leader (w₀ β : ℝ) (hw₀ : 0 ≤ w₀) (ωs θ γ : ℕ → ℝ)
    (g : Grid (Fintype.card α)) {ν : Kernel α ℝ} [IsMarkovKernel ν] (hν : ν ∈ unitBandits α) :
    ∀ᵐ ω ∂(trajMeasure (hyAlg w₀ β ωs θ γ g : Algorithm Unit α ℝ) (Environment.bandit ν)),
      ∀ ℓ, ℓ ≠ 0 → ∀ v : ℝ,
      ((g.ratio ℓ ^ 2 * v : ℝ) : EReal) ≤ HY.imedIndex w₀ (g.ratio ℓ ^ 2)
        (history IT.obs IT.action IT.feedback (g.t (ℓ + 1)) ω) (g.t ℓ)
        (HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ)) →
      v ≤ Real.log (pullCount IT.action
        (HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ))
          (g.t (ℓ + 1)) ω) := by
  filter_upwards [hyAlg_ae_one_le_pullCount w₀ β ωs θ γ g (Environment.bandit ν),
    ae_feedback_mem_Icc (alg := hyAlg w₀ β ωs θ γ g) hν] with ω hN1 hfb
  intro ℓ hℓ v hJ
  set h := history IT.obs IT.action IT.feedback (g.t ℓ) ω with hh
  set L := HY.leader w₀ h (g.t ℓ) with hL
  have hy1 : 1 ≤ g.ratio ℓ ^ 2 := one_le_pow₀ (g.one_le_ratio ℓ)
  have hfbh : ∀ i, (h i).feedback ∈ Set.Icc (0 : ℝ) 1 := fun i ↦ hfb i
  have hpos : 0 < (HY.count h (g.t ℓ) L : ℝ) + w₀ := by
    rw [hh, HY.count_history le_rfl]
    have : (1 : ℝ) ≤ pullCount IT.action L (g.t ℓ) ω := by
      exact_mod_cast hN1 ℓ (Nat.one_le_iff_ne_zero.mpr hℓ) L
    linarith
  have hK0 : HY.imedKinf w₀ h (g.t ℓ) L = 0 := HY.imedKinf_leader hw₀ hfbh hpos
  rw [HY.imedIndex_history (g.strictMono.monotone (Nat.le_succ ℓ)), ← hh, hK0, mul_zero,
    EReal.coe_ennreal_zero, zero_add, EReal.coe_le_coe_iff] at hJ
  exact le_of_mul_le_mul_left hJ (by linarith)

/-- [INC-P000, Lemma `lem:goodhigh`, Steps 1–2, along a run] Along almost every run of HY
(`w₀ ≥ 0`) on an instance of `𝒫`, let `S` be a finite set of batches `i ≥ 2`, each high at the
level `v` for its leader `ĉ_(i-1)`, and `u ≤ e^v`. Then every `i ∈ S` has
`N_(ĉ_(i-1))(t_i) ≥ u` (Step 1), and at most `K` batches of `S` have a leader observed fewer than
`u` times at their start (Step 2): `|S| ≤ |S_go| + K` with
`S_go = {i ∈ S : N_(ĉ_(i-1))(t_(i-1)) ≥ u}`. -/
lemma hyAlg_ae_card_le_card_filter_le_pullCount_leader_add (w₀ β : ℝ) (hw₀ : 0 ≤ w₀)
    (ωs θ γ : ℕ → ℝ)
    (g : Grid (Fintype.card α)) {ν : Kernel α ℝ} [IsMarkovKernel ν] (hν : ν ∈ unitBandits α) :
    ∀ᵐ ω ∂(trajMeasure (hyAlg w₀ β ωs θ γ g : Algorithm Unit α ℝ) (Environment.bandit ν)),
      ∀ (S : Finset ℕ) (v u : ℝ), (∀ i ∈ S, 2 ≤ i) → u ≤ Real.exp v →
      (∀ i ∈ S, ((g.ratio (i - 1) ^ 2 * v : ℝ) : EReal) ≤ HY.imedIndex w₀ (g.ratio (i - 1) ^ 2)
        (history IT.obs IT.action IT.feedback (g.t i) ω) (g.t (i - 1))
        (HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t (i - 1)) ω) (g.t (i - 1)))) →
      (∀ i ∈ S, u ≤ pullCount IT.action
        (HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t (i - 1)) ω) (g.t (i - 1)))
          (g.t i) ω) ∧
      S.card ≤ (S.filter fun i ↦ u ≤ pullCount IT.action
        (HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t (i - 1)) ω) (g.t (i - 1)))
          (g.t (i - 1)) ω).card + Fintype.card α := by
  filter_upwards [hyAlg_ae_le_log_pullCount_leader w₀ β hw₀ ωs θ γ g hν,
    hyAlg_ae_one_le_pullCount w₀ β ωs θ γ g (Environment.bandit ν)] with ω hS1 hN1
  intro S v u hS2 huv hhigh
  set L : ℕ → α := fun i ↦
    HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t (i - 1)) ω) (g.t (i - 1)) with hL
  -- Step 1
  have hstep1 : ∀ i ∈ S, u ≤ pullCount IT.action (L i) (g.t i) ω := by
    intro i hi
    have hi2 := hS2 i hi
    have h := hS1 (i - 1) (by omega) v
    rw [show i - 1 + 1 = i by omega] at h
    have hlog := h (hhigh i hi)
    have hN : (0 : ℝ) < pullCount IT.action (L i) (g.t i) ω := by
      exact_mod_cast hN1 i (by omega) (L i)
    calc u ≤ Real.exp v := huv
      _ ≤ Real.exp (Real.log (pullCount IT.action (L i) (g.t i) ω)) := Real.exp_le_exp.mpr hlog
      _ = _ := Real.exp_log hN
  refine ⟨hstep1, ?_⟩
  -- Step 2
  change S.card ≤ (S.filter fun i ↦ u ≤ (pullCount IT.action (L i) (g.t (i - 1)) ω : ℝ)).card +
    Fintype.card α
  have hmono : ∀ c, Monotone fun j ↦ pullCount IT.action c (g.t j) ω :=
    fun c _ _ hjj' ↦ pullCount_mono _ (g.strictMono.monotone hjj') _
  have hu : ∀ i ∈ S, ⌈u⌉₊ ≤ pullCount IT.action (L i) (g.t i) ω :=
    fun i hi ↦ Nat.ceil_le.mpr (hstep1 i hi)
  have h2 := card_filter_lt_le_card (N := fun c j ↦ pullCount IT.action c (g.t j) ω) hmono hu
  have hsplit := Finset.card_filter_add_card_filter_not (s := S)
    (fun i ↦ u ≤ (pullCount IT.action (L i) (g.t (i - 1)) ω : ℝ))
  have hsub : (S.filter fun i ↦ ¬ u ≤ (pullCount IT.action (L i) (g.t (i - 1)) ω : ℝ)) ⊆
      S.filter fun i ↦ pullCount IT.action (L i) (g.t (i - 1)) ω < ⌈u⌉₊ := by
    intro i hi
    obtain ⟨hiS, hiu⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨hiS, Nat.lt_ceil.mpr (not_le.mp hiu)⟩
  have := Finset.card_le_card hsub
  omega

/-- [INC-P000, proof of Lemma `lem:fewC`, the common step, along a run] Along almost every run of
HY (`w₀ ≥ 0`) on an instance of `𝒫`, let `c` be an arm, `S` a nonempty finite set of batches
`i ∈ [2, J]`, and `u, v, r', δ` with `N_c(t_J) < u`, `Y = v - log u > 0`, `r' < 1`, `δ < 1` and
`u ≤ (1 - δ)^(-(|S| - 1)) Y / κ(r')`. If every batch `i ∈ S` has its IMED level
`m̃⋆_(i-1) ≤ r'` and is high at the level `v` for `c`, then some `i ∈ S` has
`1 ≤ N_c(t_(i-1)) < u` and
`N_c(t_(i-1)) 𝒦_inf(ν̂_c(t_(i-1)), r') ≥ (1 - δ) Y - w₀ κ(r')` (in `ℝ≥0∞`, with the empirical
law `ν̂_c(t_(i-1))` of the rewards of `c` before `t_(i-1)`). The paper takes `J = j - 1`, `S =
S_go`,
`v = (1 - δ) L_j`, `u = u_j` (Lemma `lem:fewC`) or `J = i_m - 1`, `S = S_go ∖ {i_m}`
(Lemma `lem:optW`); `Y ≥ (1 - 2δ) L_j` and `(1 - δ)(1 - 2δ) L_j - w₀ κ(r') ≥ (1 - 4δ) L_j` are
Lemma `lem:constC`. -/
lemma hyAlg_ae_exists_mem_pullCount_lt_and_le_mul_pseudoKinf (w₀ β : ℝ) (hw₀ : 0 ≤ w₀)
    (ωs θ γ : ℕ → ℝ)
    (g : Grid (Fintype.card α)) {ν : Kernel α ℝ} [IsMarkovKernel ν] (hν : ν ∈ unitBandits α) :
    ∀ᵐ ω ∂(trajMeasure (hyAlg w₀ β ωs θ γ g : Algorithm Unit α ℝ) (Environment.bandit ν)),
      ∀ (c : α) (S : Finset ℕ) (J : ℕ) (u v r' δ : ℝ), S.Nonempty → (∀ i ∈ S, 2 ≤ i ∧ i ≤ J) →
      (pullCount IT.action c (g.t J) ω : ℝ) < u → 0 < v - Real.log u → r' < 1 → δ < 1 →
      u ≤ ((1 - δ)⁻¹) ^ (S.card - 1) * (v - Real.log u) / Real.log (1 / (1 - r')) →
      (∀ i ∈ S, HY.pseudoMean w₀ (history IT.obs IT.action IT.feedback (g.t (i - 1)) ω)
        (g.t (i - 1)) (HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t (i - 1)) ω)
          (g.t (i - 1))) ≤ r') →
      (∀ i ∈ S, ((g.ratio (i - 1) ^ 2 * v : ℝ) : EReal) ≤ HY.imedIndex w₀ (g.ratio (i - 1) ^ 2)
        (history IT.obs IT.action IT.feedback (g.t i) ω) (g.t (i - 1)) c) →
      ∃ i ∈ S, 1 ≤ pullCount IT.action c (g.t (i - 1)) ω ∧
        (pullCount IT.action c (g.t (i - 1)) ω : ℝ) < u ∧
        ENNReal.ofReal ((1 - δ) * (v - Real.log u) - w₀ * Real.log (1 / (1 - r'))) ≤
          (pullCount IT.action c (g.t (i - 1)) ω : ℝ≥0∞) *
            HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback (g.t (i - 1)) ω) (g.t (i - 1))
              c r' := by
  -- Each batch gives the evidence `N_c(t_i) D_i ≥ Y` at its end, with
  -- `D_i = 𝒦_inf(ν̃_c(t_(i-1)), r') ∈ (0, κ(r')]` (Lemma `lem:highC`); the chain
  -- (Lemma `lem:chain`) turns it into the evidence `N_c(t_(i-1)) D_i ≥ (1 - δ) Y` at its start,
  -- since the other case, `N_c(t_J) ≥ (1 - δ)^(-(|S| - 1)) Y / κ(r') ≥ u`, is excluded;
  -- Lemma `lem:pseudo`(ii) passes from the pseudo-empirical law to the empirical law.
  filter_upwards [hyAlg_ae_one_le_pullCount w₀ β ωs θ γ g (Environment.bandit ν),
    ae_feedback_mem_Icc (alg := hyAlg w₀ β ωs θ γ g) hν] with ω hN1 hfb
  intro c S J u v r' δ hSne hSJ huJ hY hr' hδ hcard hlev hhigh
  set Dk : ℕ → ℝ≥0∞ := fun i ↦
    HY.pseudoKinf w₀ (history IT.obs IT.action IT.feedback (g.t (i - 1)) ω) (g.t (i - 1)) c r'
    with hDk
  set w : ℕ → ℝ := fun i ↦ (pullCount IT.action c (g.t (i - 1)) ω : ℝ) with hw
  set Y := v - Real.log u with hYdef
  set κ := Real.log (1 / (1 - r')) with hκ
  have hfbH : ∀ i k, (history IT.obs IT.action IT.feedback (g.t (i - 1)) ω k).feedback ∈
      Set.Icc (0 : ℝ) 1 := fun i k ↦ hfb k
  have hmonoN : ∀ a b, a ≤ b →
      (pullCount IT.action c (g.t a) ω : ℝ) ≤ pullCount IT.action c (g.t b) ω :=
    fun a b hab ↦ by exact_mod_cast pullCount_mono (A := IT.action) c (g.strictMono.monotone hab) ω
  have hwmono : Monotone w := fun i i' hii' ↦ hmonoN _ _ (by omega)
  -- the counts of `c` in the batches of `S` are below `u`
  have hcount_lt : ∀ i ∈ S, (pullCount IT.action c (g.t i) ω : ℝ) < u := fun i hi ↦
    (hmonoN _ _ (hSJ i hi).2).trans_lt huJ
  have hcount_lt' : ∀ i ∈ S, (pullCount IT.action c (g.t (i - 1)) ω : ℝ) < u := fun i hi ↦
    (hmonoN _ _ (Nat.sub_le i 1)).trans_lt (hcount_lt i hi)
  -- the evidence at the end of each batch (Lemma `lem:highC`)
  have hev : ∀ i ∈ S, 0 < Dk i ∧ Dk i ≤ ENNReal.ofReal κ ∧
      ENNReal.ofReal Y ≤ (pullCount IT.action c (g.t i) ω : ℝ≥0∞) * Dk i := by
    intro i hi
    have hi2 := (hSJ i hi).1
    have hy1 : 1 ≤ g.ratio (i - 1) ^ 2 := one_le_pow₀ (g.one_le_ratio _)
    have hpos : 0 < (HY.count (history IT.obs IT.action IT.feedback (g.t (i - 1)) ω)
        (g.t (i - 1)) c : ℝ) + w₀ := by
      rw [HY.count_history le_rfl]
      have : (1 : ℝ) ≤ pullCount IT.action c (g.t (i - 1)) ω := by
        exact_mod_cast hN1 (i - 1) (by omega) c
      linarith
    have hW := hhigh i hi
    rw [HY.imedIndex_history (g.strictMono.monotone (Nat.sub_le i 1))] at hW
    have hW1 := ofReal_sub_log_le_div (by linarith) hW
    exact HY.pseudoKinf_pos_and_le_mul_pseudoKinf hw₀ (hfbH i) hpos hr' (hlev i hi)
      (hN1 i (by omega) c) hy1 (hcount_lt i hi).le hY hW1
  -- the chain (Lemma `lem:chain`)
  have hfin : ∀ i ∈ S, Dk i ≠ ⊤ := fun i hi ↦
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hev i hi).2.1
  have hD : ∀ i ∈ S, 0 < (Dk i).toReal ∧ (Dk i).toReal ≤ κ ∧ Y ≤ w (i + 1) * (Dk i).toReal := by
    intro i hi
    obtain ⟨h0, hle, hY'⟩ := hev i hi
    refine ⟨ENNReal.toReal_pos h0.ne' (hfin i hi), ?_, ?_⟩
    · exact ENNReal.toReal_le_of_le_ofReal (Real.log_nonneg (by
        rw [le_div_iff₀ (by linarith)]
        linarith [(HY.pseudoMean_nonneg hw₀ (hfbH i) _).trans (hlev i hi)])) hle
    · simp only [hw, Nat.add_sub_cancel]
      rw [← ENNReal.ofReal_toReal (hfin i hi), ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at hY'
      exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Nat.cast_nonneg _)
        ENNReal.toReal_nonneg)).mp hY'
  rcases exists_le_mul_or_forall_le_mul_of_monotone hY.le hδ hwmono S hSne hD with
    ⟨i, hi, hiY⟩ | hall
  · refine ⟨i, hi, hN1 (i - 1) (by have := (hSJ i hi).1; omega) c, hcount_lt' i hi, ?_⟩
    have hi2 := (hSJ i hi).1
    have hr'0 : 0 ≤ r' := (HY.pseudoMean_nonneg hw₀ (hfbH i) _).trans (hlev i hi)
    have hcnt : HY.count (history IT.obs IT.action IT.feedback (g.t (i - 1)) ω) (g.t (i - 1)) c =
        pullCount IT.action c (g.t (i - 1)) ω := by
      rw [HY.count_history le_rfl]
    have hpseudo := HY.mul_pseudoKinf_le
      (h := history IT.obs IT.action IT.feedback (g.t (i - 1)) ω) (r := g.t (i - 1)) (c := c)
      hw₀ hr' hr'0
      (hfbH i) (by rw [hcnt]; exact hN1 (i - 1) (by omega) c)
    rw [hcnt] at hpseudo
    have hstart : ENNReal.ofReal ((1 - δ) * Y) ≤
        (pullCount IT.action c (g.t (i - 1)) ω : ℝ≥0∞) * Dk i := by
      rw [← ENNReal.ofReal_toReal (hfin i hi), ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      exact ENNReal.ofReal_le_ofReal hiY
    have hwκ : 0 ≤ w₀ * κ := mul_nonneg hw₀ (Real.log_nonneg (by
      rw [le_div_iff₀ (by linarith)]
      linarith))
    rw [ENNReal.ofReal_sub _ hwκ, tsub_le_iff_right]
    exact hstart.trans hpseudo
  · exfalso
    have h := hall J fun i hi ↦ (hSJ i hi).2
    simp only [hw, Nat.add_sub_cancel] at h
    linarith

/-- [INC-P000, Lemma `lem:fewC`, first inclusion, along a run] Along almost every run of HY
(`w₀ ≥ 0`) on an instance of `𝒫`, let `a⋆` be an optimal arm, `m₂` a bound of the means of the
sub-optimal arms, `ε ≥ 0` with `m₂ + ε < m⋆ - 2ε`, `m⋆ + ε < 1` and `w₀ ≤ ε u`, and `S` a
nonempty set of batches `i ∈ [2, J]` that are high at the level `v` for `a⋆` and whose leaders
`ĉ_(i-1)` have at least `u` observations at `t_(i-1)` (the paper's `S_go`), with the size
condition of `hyAlg_ae_exists_mem_pullCount_lt_and_le_mul_pseudoKinf` at the level `r' = m₂ + ε`.
Assume the trace of `𝒟_j^c` up to
`t_J` (every arm with `N_c(t_k) ≥ u`, `k ≤ J`, has `|m̂_c(t_k) - m_c| ≤ ε`) and the class `𝒰_j`
(`m̃⋆_J < m⋆ - 2ε`). Then the trace of `𝒱⋆_j` holds: some `i ∈ S` has `1 ≤ N_(a⋆)(t_(i-1)) < u` and
`N_(a⋆)(t_(i-1)) 𝒦_inf(ν̂_(a⋆)(t_(i-1)), m₂ + ε) ≥ (1 - δ)(v - log u) - w₀ κ(m₂ + ε)`.
(The paper: `J = j - 1`, and Lemma `lem:constC` turns the right side into `(1 - 4δ) L_j`.) -/
lemma hyAlg_ae_exists_mem_pullCount_lt_and_le_mul_pseudoKinf_of_pseudoMean_leader_lt (w₀ β : ℝ)
    (hw₀ : 0 ≤ w₀) (ωs θ γ : ℕ → ℝ)
    (g : Grid (Fintype.card α)) {ν : Kernel α ℝ} [IsMarkovKernel ν] (hν : ν ∈ unitBandits α) :
    ∀ᵐ ω ∂(trajMeasure (hyAlg w₀ β ωs θ γ g : Algorithm Unit α ℝ) (Environment.bandit ν)),
      ∀ (aS : α) (S : Finset ℕ) (J : ℕ) (u v δ ε m₂ : ℝ),
      (∫ y, id y ∂(ν aS)) = (⨆ b, ∫ y, id y ∂(ν b)) →
      (∀ c, (∫ y, id y ∂(ν c)) < (⨆ b, ∫ y, id y ∂(ν b)) → (∫ y, id y ∂(ν c)) ≤ m₂) →
      0 ≤ ε → m₂ + ε < (⨆ b, ∫ y, id y ∂(ν b)) - 2 * ε →
      (⨆ b, ∫ y, id y ∂(ν b)) + ε < 1 → w₀ ≤ ε * u →
      S.Nonempty → (∀ i ∈ S, 2 ≤ i ∧ i ≤ J) → 0 < v - Real.log u → δ < 1 →
      u ≤ ((1 - δ)⁻¹) ^ (S.card - 1) * (v - Real.log u) / Real.log (1 / (1 - (m₂ + ε))) →
      (∀ c k, k ≤ J → u ≤ pullCount IT.action c (g.t k) ω →
        |HY.pseudoMean 0 (history IT.obs IT.action IT.feedback (g.t k) ω) (g.t k) c -
          ∫ y, id y ∂(ν c)| ≤ ε) →
      (∀ i ∈ S, u ≤ pullCount IT.action
        (HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t (i - 1)) ω) (g.t (i - 1)))
          (g.t (i - 1)) ω) →
      (∀ i ∈ S, ((g.ratio (i - 1) ^ 2 * v : ℝ) : EReal) ≤ HY.imedIndex w₀ (g.ratio (i - 1) ^ 2)
        (history IT.obs IT.action IT.feedback (g.t i) ω) (g.t (i - 1)) aS) →
      HY.pseudoMean w₀ (history IT.obs IT.action IT.feedback (g.t J) ω) (g.t J)
        (HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t J) ω) (g.t J)) <
          (⨆ b, ∫ y, id y ∂(ν b)) - 2 * ε →
      ∃ i ∈ S, 1 ≤ pullCount IT.action aS (g.t (i - 1)) ω ∧
        (pullCount IT.action aS (g.t (i - 1)) ω : ℝ) < u ∧
        ENNReal.ofReal ((1 - δ) * (v - Real.log u) - w₀ * Real.log (1 / (1 - (m₂ + ε)))) ≤
          (pullCount IT.action aS (g.t (i - 1)) ω : ℝ≥0∞) *
            HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback (g.t (i - 1)) ω) (g.t (i - 1))
              aS (m₂ + ε) := by
  filter_upwards [hyAlg_ae_exists_mem_pullCount_lt_and_le_mul_pseudoKinf w₀ β hw₀ ωs θ γ g hν,
    hyAlg_ae_one_le_pullCount w₀ β ωs θ γ g (Environment.bandit ν),
    ae_feedback_mem_Icc (alg := hyAlg w₀ β ωs θ γ g) hν] with ω hcommon hN1 hfb
  intro aS S J u v δ ε m₂ haS hm₂ hε hgap hm1 hwu hSne hSJ hY hδ hcard hDev hgo hhigh hU
  set ms := ⨆ b, ∫ y, id y ∂(ν b) with hms
  have hle_ms : ∀ c, (∫ y, id y ∂(ν c)) ≤ ms := fun c ↦
    le_ciSup (Finite.bddAbove_range fun b ↦ ∫ y, id y ∂(ν b)) c
  obtain ⟨i₀, hi₀⟩ := hSne
  have hJ2 : 2 ≤ J := (hSJ i₀ hi₀).1.trans (hSJ i₀ hi₀).2
  -- every optimal arm has fewer than `u` observations at `t_J`
  have hopt : ∀ a', (∫ y, id y ∂(ν a')) = ms →
      (pullCount IT.action a' (g.t J) ω : ℝ) < u := by
    intro a' ha'
    by_contra hge
    have hge := not_lt.mp hge
    have hcnt := HY.count_history (O := IT.obs) (A := IT.action) (Y := IT.feedback) (ω := ω)
      (le_refl (g.t J)) a'
    have hlow := HY.sub_two_mul_le_pseudoMean_leader
      (h := history IT.obs IT.action IT.feedback (g.t J) ω) (r := g.t J) (c := a') hw₀ hε
      (fun k ↦ hfb k) (by rw [hcnt]; exact hN1 J (by omega) a') (by rw [hcnt]; exact hge) hwu
      (hDev a' J le_rfl hge)
    linarith
  -- the leaders of the batches of `S` are sub-optimal, so their levels are at most `m₂ + ε`
  have hlev : ∀ i ∈ S, HY.pseudoMean w₀ (history IT.obs IT.action IT.feedback (g.t (i - 1)) ω)
      (g.t (i - 1)) (HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t (i - 1)) ω)
        (g.t (i - 1))) ≤ m₂ + ε := by
    intro i hi
    set L := HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t (i - 1)) ω) (g.t (i - 1))
      with hL
    have hgoi := hgo i hi
    have hJi : (pullCount IT.action L (g.t (i - 1)) ω : ℝ) ≤ pullCount IT.action L (g.t J) ω := by
      exact_mod_cast pullCount_mono (A := IT.action) L
        (g.strictMono.monotone (show i - 1 ≤ J by have := (hSJ i hi).2; omega)) ω
    have hsub : (∫ y, id y ∂(ν L)) < ms := lt_of_le_of_ne (hle_ms L) fun heq ↦
      absurd (hopt L heq) (not_lt.mpr (hgoi.trans hJi))
    have hmean := HY.pseudoMean_le_add_of_abs_sub_le hw₀
      (hDev L (i - 1) (by have := (hSJ i hi).2; omega) hgoi) (fun k ↦ (hfb k).1)
    linarith [hm₂ L hsub]
  exact hcommon aS S J u v (m₂ + ε) δ ⟨i₀, hi₀⟩ hSJ (hopt aS haS) hY (by linarith) hδ hcard
    hlev hhigh

/-- [INC-P000, Lemma `lem:fewC`, second inclusion, along a run] Along almost every run of HY
(`w₀ ≥ 0`) on an instance of `𝒫`, let `a` be an arm, `ε ≥ 0` with `m_a + ε < m⋆ - 3ε` and
`m⋆ + ε < 1`, and `S` a nonempty set of batches `i ∈ [2, J]` that are high at the level `v` for
`a` and whose leaders have at least `u` observations at `t_(i-1)`, with the size condition of
`hyAlg_ae_exists_mem_pullCount_lt_and_le_mul_pseudoKinf` at the level `r' = m⋆ + ε`. Assume the
trace of `𝒟_j^c` up to `t_J` and
`m̂_a(t_J) ≥ m⋆ - 3ε`. Then `N_a(t_J) < u`, and some `i ∈ S` has `1 ≤ N_a(t_(i-1)) < u` and
`N_a(t_(i-1)) 𝒦_inf(ν̂_a(t_(i-1)), m⋆ + ε) ≥ (1 - δ)(v - log u) - w₀ κ(m⋆ + ε)`: with
`n' = N_a(t_J)`, this is the trace of `𝒱_(a,j)`. -/
lemma hyAlg_ae_pullCount_lt_and_exists_mem_le_mul_pseudoKinf_of_le_pseudoMean (w₀ β : ℝ)
    (hw₀ : 0 ≤ w₀) (ωs θ γ : ℕ → ℝ)
    (g : Grid (Fintype.card α)) {ν : Kernel α ℝ} [IsMarkovKernel ν] (hν : ν ∈ unitBandits α) :
    ∀ᵐ ω ∂(trajMeasure (hyAlg w₀ β ωs θ γ g : Algorithm Unit α ℝ) (Environment.bandit ν)),
      ∀ (a : α) (S : Finset ℕ) (J : ℕ) (u v δ ε : ℝ),
      0 ≤ ε → (∫ y, id y ∂(ν a)) + ε < (⨆ b, ∫ y, id y ∂(ν b)) - 3 * ε →
      (⨆ b, ∫ y, id y ∂(ν b)) + ε < 1 →
      S.Nonempty → (∀ i ∈ S, 2 ≤ i ∧ i ≤ J) → 0 < v - Real.log u → δ < 1 →
      u ≤ ((1 - δ)⁻¹) ^ (S.card - 1) * (v - Real.log u) /
        Real.log (1 / (1 - ((⨆ b, ∫ y, id y ∂(ν b)) + ε))) →
      (∀ c k, k ≤ J → u ≤ pullCount IT.action c (g.t k) ω →
        |HY.pseudoMean 0 (history IT.obs IT.action IT.feedback (g.t k) ω) (g.t k) c -
          ∫ y, id y ∂(ν c)| ≤ ε) →
      (∀ i ∈ S, u ≤ pullCount IT.action
        (HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t (i - 1)) ω) (g.t (i - 1)))
          (g.t (i - 1)) ω) →
      (∀ i ∈ S, ((g.ratio (i - 1) ^ 2 * v : ℝ) : EReal) ≤ HY.imedIndex w₀ (g.ratio (i - 1) ^ 2)
        (history IT.obs IT.action IT.feedback (g.t i) ω) (g.t (i - 1)) a) →
      (⨆ b, ∫ y, id y ∂(ν b)) - 3 * ε ≤
        HY.pseudoMean 0 (history IT.obs IT.action IT.feedback (g.t J) ω) (g.t J) a →
      (pullCount IT.action a (g.t J) ω : ℝ) < u ∧
      ∃ i ∈ S, 1 ≤ pullCount IT.action a (g.t (i - 1)) ω ∧
        (pullCount IT.action a (g.t (i - 1)) ω : ℝ) < u ∧
        ENNReal.ofReal ((1 - δ) * (v - Real.log u) -
            w₀ * Real.log (1 / (1 - ((⨆ b, ∫ y, id y ∂(ν b)) + ε)))) ≤
          (pullCount IT.action a (g.t (i - 1)) ω : ℝ≥0∞) *
            HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback (g.t (i - 1)) ω) (g.t (i - 1))
              a ((⨆ b, ∫ y, id y ∂(ν b)) + ε) := by
  filter_upwards [hyAlg_ae_exists_mem_pullCount_lt_and_le_mul_pseudoKinf w₀ β hw₀ ωs θ γ g hν,
    ae_feedback_mem_Icc (alg := hyAlg w₀ β ωs θ γ g) hν] with ω hcommon hfb
  intro a S J u v δ ε hε hgap hm1 hSne hSJ hY hδ hcard hDev hgo hhigh hmean
  set ms := ⨆ b, ∫ y, id y ∂(ν b) with hms
  have hle_ms : ∀ c, (∫ y, id y ∂(ν c)) ≤ ms := fun c ↦
    le_ciSup (Finite.bddAbove_range fun b ↦ ∫ y, id y ∂(ν b)) c
  -- `a` has few observations, since its empirical mean is far from `m_a`
  have hfew : (pullCount IT.action a (g.t J) ω : ℝ) < u := by
    by_contra hge
    have hdev := abs_le.mp (hDev a J le_rfl (not_lt.mp hge))
    linarith
  refine ⟨hfew, ?_⟩
  -- the levels of the batches of `S` are at most `m⋆ + ε`
  have hlev : ∀ i ∈ S, HY.pseudoMean w₀ (history IT.obs IT.action IT.feedback (g.t (i - 1)) ω)
      (g.t (i - 1)) (HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t (i - 1)) ω)
        (g.t (i - 1))) ≤ ms + ε := by
    intro i hi
    set L := HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t (i - 1)) ω) (g.t (i - 1))
      with hL
    have hmean := HY.pseudoMean_le_add_of_abs_sub_le hw₀
      (hDev L (i - 1) (by have := (hSJ i hi).2; omega) (hgo i hi)) (fun k ↦ (hfb k).1)
    linarith [hle_ms L]
  exact hcommon a S J u v (ms + ε) δ hSne hSJ hfew hY hm1 hδ hcard hlev hhigh

/-- [INC-P000, proof of Lemma `lem:optW`, Part 1, along a run] Along almost every run of HY
(`w₀ ≥ 0`) on an instance of `𝒫`, with the hypotheses of `hyAlg_ae_integral_reference_eq_iSup`
that this part uses: some optimal arm is well sampled at `t_J` (`U ≤ 2 N_(a')(t_J)`). -/
lemma hyAlg_ae_exists_integral_eq_iSup_and_le_two_mul_pullCount (w₀ β : ℝ) (hw₀ : 0 ≤ w₀)
    (ωs θ γ : ℕ → ℝ) (g : Grid (Fintype.card α)) {ν : Kernel α ℝ} [IsMarkovKernel ν]
    (hν : ν ∈ unitBandits α) :
    ∀ᵐ ω ∂(trajMeasure (hyAlg w₀ β ωs θ γ g : Algorithm Unit α ℝ) (Environment.bandit ν)),
      ∀ (aS : α) (S : Finset ℕ) (J U : ℕ) (u v δ ε m₂ : ℝ),
      (∫ y, id y ∂(ν aS)) = (⨆ b, ∫ y, id y ∂(ν b)) →
      (∀ c, (∫ y, id y ∂(ν c)) < (⨆ b, ∫ y, id y ∂(ν b)) → (∫ y, id y ∂(ν c)) ≤ m₂) →
      0 ≤ ε → m₂ + ε < (⨆ b, ∫ y, id y ∂(ν b)) - 2 * ε →
      (⨆ b, ∫ y, id y ∂(ν b)) + ε < 1 → w₀ ≤ ε * u → (U : ℝ) ≤ 2 * Real.exp v →
      2 ≤ S.card → (∀ i ∈ S, 2 ≤ i ∧ i ≤ J) → 0 < v - Real.log u → δ < 1 →
      u ≤ ((1 - δ)⁻¹) ^ (S.card - 2) * (v - Real.log u) / Real.log (1 / (1 - (m₂ + ε))) →
      (∀ c k, k ≤ J → u ≤ pullCount IT.action c (g.t k) ω →
        |HY.pseudoMean 0 (history IT.obs IT.action IT.feedback (g.t k) ω) (g.t k) c -
          ∫ y, id y ∂(ν c)| ≤ ε) →
      (∀ k, k ≤ J → (pullCount IT.action aS (g.t k) ω : ℝ) < u →
        ¬ ENNReal.ofReal ((1 - δ) * (v - Real.log u) - w₀ * Real.log (1 / (1 - (m₂ + ε)))) ≤
          (pullCount IT.action aS (g.t k) ω : ℝ≥0∞) *
            HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback (g.t k) ω) (g.t k) aS
              (m₂ + ε)) →
      (∀ i ∈ S, u ≤ pullCount IT.action
        (HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t (i - 1)) ω) (g.t (i - 1)))
          (g.t (i - 1)) ω) →
      (∀ i ∈ S, ∀ c', ((g.ratio (i - 1) ^ 2 * v : ℝ) : EReal) ≤
        HY.imedIndex w₀ (g.ratio (i - 1) ^ 2)
          (history IT.obs IT.action IT.feedback (g.t i) ω) (g.t (i - 1)) c') →
      ∃ a', (∫ y, id y ∂(ν a')) = (⨆ b, ∫ y, id y ∂(ν b)) ∧
        U ≤ 2 * pullCount IT.action a' (g.t J) ω := by
  filter_upwards [hyAlg_ae_exists_mem_pullCount_lt_and_le_mul_pseudoKinf w₀ β hw₀ ωs θ γ g hν,
    hyAlg_ae_le_log_pullCount_leader w₀ β hw₀ ωs θ γ g hν,
    hyAlg_ae_one_le_pullCount w₀ β ωs θ γ g (Environment.bandit ν),
    ae_feedback_mem_Icc (alg := hyAlg w₀ β ωs θ γ g) hν] with ω hcommon hS1 hN1 hfb
  intro aS S J U u v δ ε m₂ haS hm₂ hε hgap hm1 hwu hUv hS2 hSJ hY hδ hcard hDev hV hgo hhigh
  set ms := ⨆ b, ∫ y, id y ∂(ν b) with hms
  have hle_ms : ∀ c, (∫ y, id y ∂(ν c)) ≤ ms := fun c ↦
    le_ciSup (Finite.bddAbove_range fun b ↦ ∫ y, id y ∂(ν b)) c
  have hmonoN : ∀ c a b, a ≤ b →
      (pullCount IT.action c (g.t a) ω : ℝ) ≤ pullCount IT.action c (g.t b) ω :=
    fun c a b hab ↦ by
      exact_mod_cast pullCount_mono (A := IT.action) c (g.strictMono.monotone hab) ω
  by_contra hno
  push Not at hno
  -- Step 1: the leaders of the batches of `S` are sub-optimal, with levels `≤ m₂ + ε`
  have hlev : ∀ i ∈ S, HY.pseudoMean w₀
      (history IT.obs IT.action IT.feedback (g.t (i - 1)) ω) (g.t (i - 1))
      (HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t (i - 1)) ω) (g.t (i - 1))) ≤
        m₂ + ε := by
    intro i hi
    have hi2 := (hSJ i hi).1
    set L := HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t (i - 1)) ω)
      (g.t (i - 1)) with hL
    have hlog := hS1 (i - 1) (by omega) v
    rw [show i - 1 + 1 = i by omega] at hlog
    have hlog := hlog (hhigh i hi L)
    have hNpos : (0 : ℝ) < pullCount IT.action L (g.t i) ω := by
      exact_mod_cast hN1 i (by omega) L
    have hexp : Real.exp v ≤ pullCount IT.action L (g.t i) ω :=
      (Real.exp_le_exp.mpr hlog).trans_eq (Real.exp_log hNpos)
    have hiJ := hmonoN L i J (hSJ i hi).2
    have hsub : (∫ y, id y ∂(ν L)) < ms := by
      refine lt_of_le_of_ne (hle_ms L) fun heq ↦ ?_
      have h1 := hno L heq
      have h2 : ((2 * pullCount IT.action L (g.t J) ω : ℕ) : ℝ) < U := by exact_mod_cast h1
      push_cast at h2
      linarith
    have hmean := HY.pseudoMean_le_add_of_abs_sub_le hw₀
      (hDev L (i - 1) (by have := (hSJ i hi).2; omega) (hgo i hi)) (fun k ↦ (hfb k).1)
    linarith [hm₂ L hsub]
  -- Step 2: `a⋆` is poorly observed at the starts of the batches of `S`
  have hpoor : ∀ i ∈ S, (pullCount IT.action aS (g.t (i - 1)) ω : ℝ) < u := by
    intro i hi
    have hi2 := (hSJ i hi).1
    by_contra hge
    have hge := not_lt.mp hge
    have hcnt := HY.count_history (O := IT.obs) (A := IT.action) (Y := IT.feedback) (ω := ω)
      (le_refl (g.t (i - 1))) aS
    have hlow := HY.sub_two_mul_le_pseudoMean_leader
      (h := history IT.obs IT.action IT.feedback (g.t (i - 1)) ω) (r := g.t (i - 1)) (c := aS)
      hw₀ hε (fun k ↦ hfb k) (by rw [hcnt]; exact hN1 (i - 1) (by omega) aS)
      (by rw [hcnt]; exact hge) hwu (hDev aS (i - 1) (by have := (hSJ i hi).2; omega) hge)
    linarith [hlev i hi]
  -- Step 3: the chain on `S` without its largest batch
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  set im := S.max' hSne with him
  have himS : im ∈ S := S.max'_mem hSne
  set S' := S.erase im with hS'
  have hS'card : S'.card = S.card - 1 := Finset.card_erase_of_mem himS
  have hS'ne : S'.Nonempty := Finset.card_pos.mp (by omega)
  have hS'J : ∀ i ∈ S', 2 ≤ i ∧ i ≤ im - 1 := by
    intro i hi
    obtain ⟨hne, hiS⟩ := Finset.mem_erase.mp hi
    have hle : i ≤ im := S.le_max' i hiS
    exact ⟨(hSJ i hiS).1, by omega⟩
  have hcard' : u ≤ ((1 - δ)⁻¹) ^ (S'.card - 1) * (v - Real.log u) /
      Real.log (1 / (1 - (m₂ + ε))) := by
    rw [hS'card, show S.card - 1 - 1 = S.card - 2 by omega]
    exact hcard
  obtain ⟨i, hi, -, hilt, hiz⟩ := hcommon aS S' (im - 1) u v (m₂ + ε) δ hS'ne hS'J
    (hpoor im himS) hY (by linarith) hδ hcard'
    (fun i hi ↦ hlev i (Finset.mem_of_mem_erase hi))
    (fun i hi ↦ hhigh i (Finset.mem_of_mem_erase hi) aS)
  have hiS := Finset.mem_of_mem_erase hi
  exact hV (i - 1) (by have := (hSJ i hiS).2; omega) hilt hiz

/-- [INC-P000, Lemma `lem:optW`, along a run] Along almost every run of HY (`w₀ ≥ 0`) on an
instance of `𝒫`, let `a⋆` be an optimal arm, `m₂` a bound of the means of the sub-optimal arms,
`ε ≥ 0` with `m₂ + ε < m⋆ - 2ε` and `m⋆ + ε < 1`, a net size `U ≥ 1` (the paper's `U_(j-1)`)
and a count threshold `u` with `w₀ ≤ ε u`, `2 w₀ ≤ ε U`, `u ≤ U / 2 ≤ e^v` (the paper's
`u_j ≤ ½ U_(j-1) ≤ t_j^(1-δ)` for `v = (1 - δ) L_j`). Let `S` be a set of at least two batches
`i ∈ [2, J]`, high at the level `v` for every arm, whose leaders have at least `u` observations at
`t_(i-1)` (the paper's `S_go`), with the size condition
`u ≤ (1 - δ)^(-(|S| - 2)) (v - log u) / κ(m₂ + ε)` (the common step of
`hyAlg_ae_exists_mem_pullCount_lt_and_le_mul_pseudoKinf` is
applied to `S` without its largest batch). Assume the trace of `𝒟_j^c` up to `t_J` (every arm with
`N_c(t_k) ≥ u`, `k ≤ J`, has `|m̂_c(t_k) - m_c| ≤ ε`) and the trace of `(𝒱⋆_j)^c` up to `t_J`
(no `k ≤ J` has `N_(a⋆)(t_k) < u` and
`N_(a⋆)(t_k) 𝒦_inf(ν̂_(a⋆)(t_k), m₂ + ε) ≥ (1 - δ)(v - log u) - w₀ κ(m₂ + ε)`). Then, at `t_J`:
* some optimal arm is well sampled (`U ≤ 2 N_(a')(t_J)`), and the reference `r_J` is optimal;
* the test level is accurate: `m⋆ - 2ε ≤ μ̂_J ≤ m⋆ + ε`;
* every sub-optimal well-sampled arm `c` has `m̃_c(t_J) < m⋆ - 2ε`. -/
lemma hyAlg_ae_integral_reference_eq_iSup (w₀ β : ℝ) (hw₀ : 0 ≤ w₀) (ωs θ γ : ℕ → ℝ)
    (g : Grid (Fintype.card α)) {ν : Kernel α ℝ} [IsMarkovKernel ν] (hν : ν ∈ unitBandits α) :
    ∀ᵐ ω ∂(trajMeasure (hyAlg w₀ β ωs θ γ g : Algorithm Unit α ℝ) (Environment.bandit ν)),
      ∀ (aS : α) (S : Finset ℕ) (J U : ℕ) (u v δ ε m₂ : ℝ),
      (∫ y, id y ∂(ν aS)) = (⨆ b, ∫ y, id y ∂(ν b)) →
      (∀ c, (∫ y, id y ∂(ν c)) < (⨆ b, ∫ y, id y ∂(ν b)) → (∫ y, id y ∂(ν c)) ≤ m₂) →
      0 ≤ ε → m₂ + ε < (⨆ b, ∫ y, id y ∂(ν b)) - 2 * ε →
      (⨆ b, ∫ y, id y ∂(ν b)) + ε < 1 → w₀ ≤ ε * u → 2 * w₀ ≤ ε * U → 1 ≤ U →
      2 * u ≤ U → (U : ℝ) ≤ 2 * Real.exp v →
      2 ≤ S.card → (∀ i ∈ S, 2 ≤ i ∧ i ≤ J) → 0 < v - Real.log u → δ < 1 →
      u ≤ ((1 - δ)⁻¹) ^ (S.card - 2) * (v - Real.log u) / Real.log (1 / (1 - (m₂ + ε))) →
      (∀ c k, k ≤ J → u ≤ pullCount IT.action c (g.t k) ω →
        |HY.pseudoMean 0 (history IT.obs IT.action IT.feedback (g.t k) ω) (g.t k) c -
          ∫ y, id y ∂(ν c)| ≤ ε) →
      (∀ k, k ≤ J → (pullCount IT.action aS (g.t k) ω : ℝ) < u →
        ¬ ENNReal.ofReal ((1 - δ) * (v - Real.log u) - w₀ * Real.log (1 / (1 - (m₂ + ε)))) ≤
          (pullCount IT.action aS (g.t k) ω : ℝ≥0∞) *
            HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback (g.t k) ω) (g.t k) aS
              (m₂ + ε)) →
      (∀ i ∈ S, u ≤ pullCount IT.action
        (HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t (i - 1)) ω) (g.t (i - 1)))
          (g.t (i - 1)) ω) →
      (∀ i ∈ S, ∀ c', ((g.ratio (i - 1) ^ 2 * v : ℝ) : EReal) ≤
        HY.imedIndex w₀ (g.ratio (i - 1) ^ 2)
          (history IT.obs IT.action IT.feedback (g.t i) ω) (g.t (i - 1)) c') →
      (∃ a', (∫ y, id y ∂(ν a')) = (⨆ b, ∫ y, id y ∂(ν b)) ∧
        U ≤ 2 * pullCount IT.action a' (g.t J) ω) ∧
      (∫ y, id y ∂(ν (HY.reference w₀ (history IT.obs IT.action IT.feedback (g.t J) ω) (g.t J) U)))
        = (⨆ b, ∫ y, id y ∂(ν b)) ∧
      (⨆ b, ∫ y, id y ∂(ν b)) - 2 * ε ≤
        HY.pseudoMean w₀ (history IT.obs IT.action IT.feedback (g.t J) ω) (g.t J)
          (HY.reference w₀ (history IT.obs IT.action IT.feedback (g.t J) ω) (g.t J) U) ∧
      HY.pseudoMean w₀ (history IT.obs IT.action IT.feedback (g.t J) ω) (g.t J)
          (HY.reference w₀ (history IT.obs IT.action IT.feedback (g.t J) ω) (g.t J) U) ≤
        (⨆ b, ∫ y, id y ∂(ν b)) + ε ∧
      ∀ c, (∫ y, id y ∂(ν c)) < (⨆ b, ∫ y, id y ∂(ν b)) →
        U ≤ 2 * pullCount IT.action c (g.t J) ω →
        HY.pseudoMean w₀ (history IT.obs IT.action IT.feedback (g.t J) ω) (g.t J) c <
          (⨆ b, ∫ y, id y ∂(ν b)) - 2 * ε := by
  filter_upwards [hyAlg_ae_exists_integral_eq_iSup_and_le_two_mul_pullCount w₀ β hw₀ ωs θ γ g hν,
    ae_feedback_mem_Icc (alg := hyAlg w₀ β ωs θ γ g) hν] with ω hpart hfb
  intro aS S J U u v δ ε m₂ haS hm₂ hε hgap hm1 hwu hwU hU1 huU hUv hS2 hSJ hY hδ hcard hDev
    hV hgo hhigh
  set ms := ⨆ b, ∫ y, id y ∂(ν b) with hms
  have hle_ms : ∀ c, (∫ y, id y ∂(ν c)) ≤ ms := fun c ↦
    le_ciSup (Finite.bddAbove_range fun b ↦ ∫ y, id y ∂(ν b)) c
  have hU1' : (1 : ℝ) ≤ U := by exact_mod_cast hU1
  -- Part 1 (`hyAlg_ae_exists_integral_eq_iSup_and_le_two_mul_pullCount`), then the reference and
  -- the test level
  obtain ⟨a', ha'opt, ha'ws⟩ := hpart aS S J U u v δ ε m₂ haS hm₂ hε hgap hm1 hwu hUv hS2 hSJ hY
    hδ hcard hDev hV hgo hhigh
  set h := history IT.obs IT.action IT.feedback (g.t J) ω with hh
  have hcntJ : ∀ c, HY.count h (g.t J) c = pullCount IT.action c (g.t J) ω := fun c ↦
    HY.count_history (O := IT.obs) (A := IT.action) (Y := IT.feedback) (ω := ω) le_rfl c
  have hfbh : ∀ k, (h k).feedback ∈ Set.Icc (0 : ℝ) 1 := fun k ↦ hfb k
  -- a well-sampled arm has an `ε`-accurate empirical mean
  have hacc : ∀ c, U ≤ 2 * pullCount IT.action c (g.t J) ω →
      |HY.pseudoMean 0 h (g.t J) c - ∫ y, id y ∂(ν c)| ≤ ε := by
    intro c hc
    refine hDev c J le_rfl ?_
    have : ((U : ℕ) : ℝ) ≤ ((2 * pullCount IT.action c (g.t J) ω : ℕ) : ℝ) := by exact_mod_cast hc
    push_cast at this
    linarith
  -- sub-optimal well-sampled arms have a pseudo-mean below `m⋆ - 2ε`
  have hsubopt : ∀ c, (∫ y, id y ∂(ν c)) < ms → U ≤ 2 * pullCount IT.action c (g.t J) ω →
      HY.pseudoMean w₀ h (g.t J) c < ms - 2 * ε := by
    intro c hc hcws
    have hmean := HY.pseudoMean_le_add_of_abs_sub_le hw₀
      (hacc c hcws) (fun k ↦ (hfbh k).1)
    linarith [hm₂ c hc]
  -- the well-sampled optimal arm has a pseudo-mean at least `m⋆ - 2ε`
  have hws' : HY.IsWellSampled h (g.t J) U a' := by
    unfold HY.IsWellSampled
    rw [hcntJ]
    exact ha'ws
  have ha'low : ms - 2 * ε ≤ HY.pseudoMean w₀ h (g.t J) a' := by
    have hdev := abs_le.mp (hacc a' ha'ws)
    have h1 := HY.pseudoMean_zero_sub_le_of_le hw₀ hfbh hU1 hws'
    have h2 : 2 * w₀ / U ≤ ε := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    linarith
  obtain ⟨hrefws, hrefge⟩ := HY.reference_spec (w₀ := w₀) hws'
  set ref := HY.reference w₀ h (g.t J) U with href
  have hrefws' : U ≤ 2 * pullCount IT.action ref (g.t J) ω := by
    have := hrefws
    unfold HY.IsWellSampled at this
    rwa [hcntJ] at this
  have hrefopt : (∫ y, id y ∂(ν ref)) = ms := by
    refine le_antisymm (hle_ms ref) (not_lt.mp fun hlt ↦ ?_)
    have := hsubopt ref hlt hrefws'
    linarith
  have hrefup : HY.pseudoMean w₀ h (g.t J) ref ≤ ms + ε := by
    have hmean := HY.pseudoMean_le_add_of_abs_sub_le hw₀
      (hacc ref hrefws') (fun k ↦ (hfbh k).1)
    linarith
  exact ⟨⟨a', ha'opt, ha'ws⟩, hrefopt, ha'low.trans hrefge, hrefup, hsubopt⟩

/-- [INC-P000, Lemma `lem:logcountC`, along a run] Along almost every run of HY (`w₀ ≥ 0`) on an
instance of `𝒫`, let `ε ≥ 0` with `m⋆ + ε < 1`, and let `i ∈ [2, J]` be a batch whose leader
`ĉ_(i-1)` has at least `u` observations at `t_(i-1)` (`i ∈ S_go`), with the trace of `𝒟_j^c` at
`t_(i-1)` (every arm with `N_c(t_(i-1)) ≥ u` has `m̂_c(t_(i-1)) ≤ m_c + ε`). If the batch is high
at the level `v` for an arm `c`, then `v ≤ (κ(m⋆ + ε) + 1) N_c(t_J)`: the IMED level is
`m̃⋆_(i-1) ≤ m⋆ + ε` (Lemma `lem:goodhigh`, Step 3), and
`hyAlg_ae_le_mul_pullCount_of_le_imedIndex`. With `v = (1 - δ) L_j` and `J = j - 1` this is the
paper's `(1 - δ) L_j ≤ (κ(m⋆ + ε) + 1) N_c(t_(j-1))`. -/
lemma hyAlg_ae_le_mul_pullCount_of_le_imedIndex_leader (w₀ β : ℝ) (hw₀ : 0 ≤ w₀) (ωs θ γ : ℕ → ℝ)
    (g : Grid (Fintype.card α)) {ν : Kernel α ℝ} [IsMarkovKernel ν] (hν : ν ∈ unitBandits α) :
    ∀ᵐ ω ∂(trajMeasure (hyAlg w₀ β ωs θ γ g : Algorithm Unit α ℝ) (Environment.bandit ν)),
      ∀ (c : α) (i J : ℕ) (u v ε : ℝ), 2 ≤ i → i ≤ J → (⨆ b, ∫ y, id y ∂(ν b)) + ε < 1 →
      (∀ c', u ≤ pullCount IT.action c' (g.t (i - 1)) ω →
        HY.pseudoMean 0 (history IT.obs IT.action IT.feedback (g.t (i - 1)) ω) (g.t (i - 1)) c' ≤
          (∫ y, id y ∂(ν c')) + ε) →
      u ≤ pullCount IT.action
        (HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t (i - 1)) ω) (g.t (i - 1)))
          (g.t (i - 1)) ω →
      ((g.ratio (i - 1) ^ 2 * v : ℝ) : EReal) ≤ HY.imedIndex w₀ (g.ratio (i - 1) ^ 2)
        (history IT.obs IT.action IT.feedback (g.t i) ω) (g.t (i - 1)) c →
      v ≤ (Real.log (1 / (1 - ((⨆ b, ∫ y, id y ∂(ν b)) + ε))) + 1) *
        pullCount IT.action c (g.t J) ω := by
  filter_upwards [hyAlg_ae_le_mul_pullCount_of_le_imedIndex w₀ β hw₀ ωs θ γ g hν,
    ae_feedback_mem_Icc (alg := hyAlg w₀ β ωs θ γ g) hν] with ω hlog hfb
  intro c i J u v ε hi2 hiJ hm1 hDev hgo hhigh
  set ms := ⨆ b, ∫ y, id y ∂(ν b) with hms
  set L := HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t (i - 1)) ω) (g.t (i - 1))
    with hL
  have hle_ms : (∫ y, id y ∂(ν L)) ≤ ms :=
    le_ciSup (Finite.bddAbove_range fun b ↦ ∫ y, id y ∂(ν b)) L
  have hmean := HY.pseudoMean_le_pseudoMean_zero (h := history IT.obs IT.action IT.feedback
    (g.t (i - 1)) ω) (r := g.t (i - 1)) (c := L) hw₀ (fun k ↦ (hfb k).1)
  have hlev : HY.pseudoMean w₀ (history IT.obs IT.action IT.feedback (g.t (i - 1)) ω)
      (g.t (i - 1)) L ≤ ms + ε := by
    linarith [hDev L hgo]
  have h := hlog (i - 1) (by omega) c v (ms + ε) hm1 hlev
  rw [show i - 1 + 1 = i by omega] at h
  have h1 := h hhigh
  have hκ : 0 ≤ Real.log (1 / (1 - (ms + ε))) + 1 := by
    have : 0 ≤ Real.log (1 / (1 - (ms + ε))) :=
      Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith [hmean,
        HY.pseudoMean_nonneg hw₀ (fun k ↦ hfb k) (h := history IT.obs IT.action IT.feedback
          (g.t (i - 1)) ω) (r := g.t (i - 1)) L])
    linarith
  have hmono : (pullCount IT.action c (g.t i) ω : ℝ) ≤ pullCount IT.action c (g.t J) ω := by
    exact_mod_cast pullCount_mono (A := IT.action) c (g.strictMono.monotone hiJ) ω
  exact h1.trans (mul_le_mul_of_nonneg_left hmono hκ)

/-! ### Lemma `lem:pullsC` -/

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- [INC-P000, Lemma `lem:pullsC`(i), the deterministic step] For rewards in `[0, 1]`, `w₀ ≥ 0`
and an arm `a` with `N_a ≥ 1`, let `μ ≥ 0` be a level below the test level, `μ ≤ μ̂ < 1`
(`μ̂` the pseudo-mean of the reference), with `D = 𝒦_inf(ν̂_a, μ) > 0` for the empirical law
`ν̂_a`. Then `m̂_a < μ` (Lemma `lem:kinf`(ii)), `a` is not the leader, and
`K̃(a) ≥ K̂(a) ≥ D` (Lemmas `lem:kinf`(iii), `lem:pseudo`(i)). In the paper `μ = m⋆ - 2ε` and the
test level is accurate by Lemma `lem:optW` (`hyAlg_ae_integral_reference_eq_iSup`); `D ≥ ε² / 8` on
the class `𝒪_j` is
`HY.ofReal_sq_div_eight_le_pseudoKinf`. -/
lemma HY.pseudoMean_lt_and_ne_leader_and_pseudoKinf_le_testKinf {n : ℕ} {h : Hist Unit α ℝ n}
    {r U : ℕ} {a : α} {w₀ μ : ℝ} (hw₀ : 0 ≤ w₀)
    (hfb : ∀ i, (h i).feedback ∈ Set.Icc (0 : ℝ) 1) (hN : 1 ≤ HY.count h r a) (hμ0 : 0 ≤ μ)
    (hμ : μ ≤ HY.pseudoMean w₀ h r (HY.reference w₀ h r U))
    (hμ1 : HY.pseudoMean w₀ h r (HY.reference w₀ h r U) < 1)
    (hD : 0 < HY.pseudoKinf 0 h r a μ) :
    HY.pseudoMean 0 h r a < μ ∧ a ≠ HY.leader w₀ h r ∧
      HY.pseudoKinf 0 h r a μ ≤ HY.testKinf w₀ h r U a ∧
      HY.testKinf w₀ h r U a ≤ HY.imedKinf w₀ h r a := by
  have hN' : (1 : ℝ) ≤ HY.count h r a := by exact_mod_cast hN
  have hlt1 : μ < 1 := hμ.trans_lt hμ1
  have hmean : HY.pseudoMean 0 h r a < μ := by
    by_contra hge
    have h0 := HY.pseudoKinf_eq_zero_of_le_pseudoMean le_rfl hlt1 (fun i ↦ (hfb i).2)
      (by rw [add_zero]; linarith) (not_lt.mp hge)
    exact hD.ne' h0
  refine ⟨hmean, fun heq ↦ ?_, ?_, HY.testKinf_le_imedKinf hw₀ hfb (by linarith)⟩
  · have h1 := HY.pseudoMean_le_pseudoMean_zero (h := h) (r := r) (c := a) hw₀
      (fun i ↦ (hfb i).1)
    have h2 := HY.pseudoMean_le_leader w₀ h r (HY.reference w₀ h r U)
    rw [← heq] at h2
    linarith
  · exact (HY.pseudoKinf_zero_le hw₀ hlt1 hμ0 hfb hN).trans
      (HY.pseudoKinf_mono hw₀ hμ0 hμ hμ1 hfb)

/-- [INC-P000, proof of Lemma `lem:pullsC`(ii)–(iii), one round, along a run] Along almost every
run of HY (`w₀ ≥ 0`) on an instance of `𝒫`, let `ℓ ≥ 1`, an arm `a ≠ ĉ_ℓ` with
`K̃_ℓ(a) ≥ D > 0` (in `ℝ≥0∞`), and a round `k` of batch `ℓ + 1` that pulls `a`. At an IMED
round (`k + 1 ≤ s_ℓ`), `N_a(k) + 1 ≤ 1 + y_ℓ log (k + 1) / D` (Lemma `lem:imedround`); at a paced
round, `N_a(k) + 1 ≤ n_(ℓ,a)(k + 1)`, the paced target (the paced rule). -/
lemma hyAlg_ae_pullCount_add_one_le (w₀ β : ℝ) (hw₀ : 0 ≤ w₀) (ωs θ γ : ℕ → ℝ)
    (g : Grid (Fintype.card α)) {ν : Kernel α ℝ} [IsMarkovKernel ν] (hν : ν ∈ unitBandits α) :
    ∀ᵐ ω ∂(trajMeasure (hyAlg w₀ β ωs θ γ g : Algorithm Unit α ℝ) (Environment.bandit ν)),
      ∀ ℓ, ℓ ≠ 0 → ∀ a, a ≠ HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) →
      ∀ D : ℝ, 0 < D →
      ENNReal.ofReal D ≤ HY.imedKinf w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) a →
      ∀ k, g.batchOf k = ℓ + 1 → IT.action k ω = a →
      (k + 1 ≤ g.imedEnd θ ℓ →
        (pullCount IT.action a k ω : ℝ) + 1 ≤ 1 + g.ratio ℓ ^ 2 * Real.log (k + 1) / D) ∧
      (¬ k + 1 ≤ g.imedEnd θ ℓ →
        pullCount IT.action a k ω + 1 ≤
          HY.target w₀ ((1 - γ ℓ) * g.ratio (ℓ - 1) ^ 2 * (if ℓ = 1 then g.logEnd 1 else
            HY.threshold w₀ (g.logEnd ℓ) (g.ratio (ℓ - 1) ^ 2)
              (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) (g.t (ℓ - 1))
              (g.netSize β ℓ) (g.netSize β (ℓ - 1))))
            (ωs ℓ) (g.ratio ℓ ^ 2) (Real.log (k + 1))
            (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) (g.netSize β ℓ)
            (g.netSize β (ℓ + 1)) a) := by
  filter_upwards [hyAlg_ae_action_eq w₀ β ωs θ γ g (Environment.bandit ν),
    hyAlg_ae_paced_rule w₀ β ωs θ γ g (Environment.bandit ν),
    ae_feedback_mem_Icc (alg := hyAlg w₀ β ωs θ γ g) hν,
    hyAlg_ae_one_le_pullCount w₀ β ωs θ γ g (Environment.bandit ν)] with ω hω hpaced hfb hN1
  intro ℓ hℓ a ha D hD hDK k hb hAk
  have hℓ1 : 1 ≤ ℓ := Nat.one_le_iff_ne_zero.mpr hℓ
  have hk1 := (g.batchOf_eq_iff.mp hb).1
  refine ⟨fun himed ↦ ?_, fun hnot ↦ ?_⟩
  · -- an IMED round: Lemma `lem:imedround`
    have hy0 : 0 < g.ratio ℓ ^ 2 := pow_pos (zero_lt_one.trans_le (g.one_le_ratio ℓ)) 2
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
      exact ha
    have hNk : 1 ≤ pullCount' k (history IT.obs IT.action IT.feedback k ω)
        (HY.imedArm w₀ (g.ratio ℓ ^ 2) (history IT.obs IT.action IT.feedback k ω) (g.t ℓ)) := by
      rw [← hA, hAk, ← pullCount_eq_pullCount']
      exact (hN1 ℓ hℓ1 a).trans (pullCount_mono _ hk1 _)
    have hk1' : 1 ≤ k := le_trans (by have := g.two_le_t hℓ1; omega) hk1
    have hfin := HY.imedKinf_imedArm_ne_top hw₀ hy0 hfbk hpos hk1' hne hNk
    have hlt := HY.mul_toReal_imedKinf_add_lt hw₀ hy0 hfbk hpos hk1' hne hNk
    rw [← hA, hAk, ← pullCount_eq_pullCount', HY.imedKinf_history hk1] at hlt
    rw [← hA, hAk, HY.imedKinf_history hk1] at hfin
    have hDK' : D ≤ (HY.imedKinf w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω)
        (g.t ℓ) a).toReal := (ENNReal.ofReal_le_iff_le_toReal hfin).mp hDK
    have hNk' : (1 : ℝ) ≤ pullCount IT.action a k ω := by
      exact_mod_cast (hN1 ℓ hℓ1 a).trans (pullCount_mono _ hk1 _)
    have hlogN : 0 ≤ g.ratio ℓ ^ 2 * Real.log (pullCount IT.action a k ω) :=
      mul_nonneg hy0.le (Real.log_nonneg hNk')
    have hmul : (pullCount IT.action a k ω : ℝ) * D ≤ (pullCount IT.action a k ω : ℝ) *
        (HY.imedKinf w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) a).toReal :=
      mul_le_mul_of_nonneg_left hDK' (by linarith)
    have : (pullCount IT.action a k ω : ℝ) ≤ g.ratio ℓ ^ 2 * Real.log (k + 1) / D := by
      rw [le_div_iff₀ hD]
      linarith
    linarith
  · -- a paced round: the paced rule
    have h := (hpaced ℓ k hℓ hb hnot).1 (by rw [hAk]; exact ha)
    rw [hAk] at h
    exact h

/-- [INC-P000, Lemma `lem:pullsC`(ii), along a run] Along almost every run of HY (`w₀ ≥ 0`) on an
instance of `𝒫`, let `ℓ ≥ 1`, `ω_ℓ ≥ 0`, an arm `a ≠ ĉ_ℓ` with `K̂_ℓ(a) ≥ D > 0` (in `ℝ≥0∞`), such
that the batch `ℓ + 1` is not activated (`t_(ℓ+1) ≤ s_ℓ`) or `a` is rejected at `t_ℓ`
(`K̂_ℓ(a) > 0` and `N_a(t_ℓ) K̂_ℓ(a) ≥ h_ℓ`). If `a` is pulled in the batch, then
`N_a(t_(ℓ+1)) ≤ K + (1 + ω_ℓ) y_ℓ L_(ℓ+1) / D`. (The paper's batch `j = ℓ + 1`, with `D` the
empirical divergence of Lemma `lem:pullsC`(i),
`HY.pseudoMean_lt_and_ne_leader_and_pseudoKinf_le_testKinf`.) -/
lemma hyAlg_ae_pullCount_le_card_add_div (w₀ β : ℝ) (hw₀ : 0 ≤ w₀) (ωs θ γ : ℕ → ℝ)
    (g : Grid (Fintype.card α)) {ν : Kernel α ℝ} [IsMarkovKernel ν] (hν : ν ∈ unitBandits α) :
    ∀ᵐ ω ∂(trajMeasure (hyAlg w₀ β ωs θ γ g : Algorithm Unit α ℝ) (Environment.bandit ν)),
      ∀ ℓ, ℓ ≠ 0 → 0 ≤ ωs ℓ →
      ∀ a, a ≠ HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) →
      ∀ D : ℝ, 0 < D →
      ENNReal.ofReal D ≤ HY.testKinf w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ)
        (g.netSize β ℓ) a →
      (g.t (ℓ + 1) ≤ g.imedEnd θ ℓ ∨
        (0 < HY.testKinf w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ)
            (g.netSize β ℓ) a ∧
          ENNReal.ofReal ((1 - γ ℓ) * g.ratio (ℓ - 1) ^ 2 * (if ℓ = 1 then g.logEnd 1 else
            HY.threshold w₀ (g.logEnd ℓ) (g.ratio (ℓ - 1) ^ 2)
              (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) (g.t (ℓ - 1))
              (g.netSize β ℓ) (g.netSize β (ℓ - 1)))) ≤
            (pullCount IT.action a (g.t ℓ) ω : ℝ≥0∞) *
              HY.testKinf w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ)
                (g.netSize β ℓ) a)) →
      (∃ k, g.t ℓ ≤ k ∧ k < g.t (ℓ + 1) ∧ IT.action k ω = a) →
      (pullCount IT.action a (g.t (ℓ + 1)) ω : ℝ) ≤
        Fintype.card α + (1 + ωs ℓ) * g.ratio ℓ ^ 2 * g.logEnd (ℓ + 1) / D := by
  filter_upwards [hyAlg_ae_pullCount_add_one_le w₀ β hw₀ ωs θ γ g hν,
    hyAlg_ae_one_le_pullCount w₀ β ωs θ γ g (Environment.bandit ν),
    ae_feedback_mem_Icc (alg := hyAlg w₀ β ωs θ γ g) hν] with ω hround hN1 hfb
  intro ℓ hℓ hω a ha D hD hDK hcase hex
  have hℓ1 : 1 ≤ ℓ := Nat.one_le_iff_ne_zero.mpr hℓ
  set h₀ := history IT.obs IT.action IT.feedback (g.t ℓ) ω with hh₀
  have hfb₀ : ∀ i, (h₀ i).feedback ∈ Set.Icc (0 : ℝ) 1 := fun i ↦ hfb i
  have hc₀ : HY.count h₀ (g.t ℓ) a = pullCount IT.action a (g.t ℓ) ω := HY.count_history le_rfl a
  have hpos : 0 < (HY.count h₀ (g.t ℓ) a : ℝ) + w₀ := by
    rw [hc₀]
    have : (1 : ℝ) ≤ pullCount IT.action a (g.t ℓ) ω := by exact_mod_cast hN1 ℓ hℓ1 a
    linarith
  have hKt : ENNReal.ofReal D ≤ HY.imedKinf w₀ h₀ (g.t ℓ) a :=
    hDK.trans (HY.testKinf_le_imedKinf hw₀ hfb₀ hpos)
  have hy1 : 1 ≤ g.ratio ℓ ^ 2 := one_le_pow₀ (g.one_le_ratio ℓ)
  have hωy : 0 ≤ (1 + ωs ℓ) * g.ratio ℓ ^ 2 := by positivity
  have hK1 : (1 : ℝ) ≤ Fintype.card α := by exact_mod_cast Fintype.card_pos
  set G : ℕ → ℝ := fun k ↦ Fintype.card α + (1 + ωs ℓ) * g.ratio ℓ ^ 2 * Real.log (k + 1) / D
    with hG
  have hGmono : Monotone G := by
    intro k k' hkk'
    simp only [hG]
    gcongr
  have hstep : ∀ k, g.t ℓ ≤ k → k < g.t (ℓ + 1) → IT.action k ω = a →
      (pullCount IT.action a k ω : ℝ) + 1 ≤ G k := by
    intro k hk1 hk2 hAk
    have hb : g.batchOf k = ℓ + 1 := g.batchOf_eq_iff.mpr ⟨hk1, hk2⟩
    have hlog0 : 0 ≤ Real.log ((k : ℝ) + 1) :=
      Real.log_nonneg (by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)])
    obtain ⟨himed, hpace⟩ := hround ℓ hℓ a ha D hD hKt k hb hAk
    by_cases hk : k + 1 ≤ g.imedEnd θ ℓ
    · refine (himed hk).trans ?_
      have : g.ratio ℓ ^ 2 * Real.log (k + 1) ≤ (1 + ωs ℓ) * g.ratio ℓ ^ 2 * Real.log (k + 1) := by
        have : 0 ≤ g.ratio ℓ ^ 2 * Real.log (k + 1) := by positivity
        nlinarith
      have := div_le_div_of_nonneg_right this hD.le
      simp only [hG]
      linarith
    · -- a paced round, so the batch is activated and `a` is rejected
      have hrej := hcase.resolve_left (by omega)
      rw [← hc₀] at hrej
      have htgt := HY.target_le_of_rejected (ω' := ωs ℓ) (y := g.ratio ℓ ^ 2)
        (logt := Real.log (k + 1)) (Unext := g.netSize β (ℓ + 1)) (mul_nonneg hωy hlog0) hD
        hrej hDK
      have h1 := hpace hk
      have h1' := (Nat.cast_le (α := ℝ)).mpr h1
      push_cast at h1'
      exact h1'.trans htgt
  have hT := (pullCount_le_max_of_forall_add_one hGmono
    (g.strictMono.monotone (Nat.le_succ ℓ)) hstep).2 hex
  have hcast : ((g.t (ℓ + 1) - 1 : ℕ) : ℝ) + 1 = g.t (ℓ + 1) := by
    have : 1 ≤ g.t (ℓ + 1) := le_trans (by have := g.two_le_t hℓ1; omega)
      (g.strictMono.monotone (Nat.le_succ ℓ))
    rw [Nat.cast_sub this, Nat.cast_one, sub_add_cancel]
  simp only [hG, hcast] at hT
  exact hT

/-- [INC-P000, Lemma `lem:pullsC`(iii), general form, along a run] Along almost every run of HY
(`w₀ ≥ 0`) on an instance of `𝒫`, let `ℓ ≥ 1`, `ϑ_ℓ ≥ 0` and an arm `a ≠ ĉ_ℓ` with
`K̃_ℓ(a) ≥ D > 0` (in `ℝ≥0∞`). Then, whatever its verdict,
`N_a(t_(ℓ+1)) ≤ max(N_a(t_ℓ), max(1 + y_ℓ log s_ℓ / D, K - 1 + U_(ℓ+1)))`: at an IMED round
`N_a(t) < 1 + y_ℓ log s_ℓ / D` (Lemma `lem:imedround`), at a paced round `N_a(t) <` its target,
at most `K - 1 + U_(ℓ+1)`. With `D ≥ ε² / 8`, `log s_ℓ ≤ 2 L_ℓ` and `y_ℓ ≤ ȳ`, this is the
paper's `N_a(t_(ℓ+1)) - N_a(t_ℓ) ≤ c_ℓ = U_(ℓ+1) + K + 16 ȳ L_ℓ / ε²`. -/
lemma hyAlg_ae_pullCount_le_max_of_le_imedKinf (w₀ β : ℝ) (hw₀ : 0 ≤ w₀) (ωs θ γ : ℕ → ℝ)
    (g : Grid (Fintype.card α)) {ν : Kernel α ℝ} [IsMarkovKernel ν] (hν : ν ∈ unitBandits α) :
    ∀ᵐ ω ∂(trajMeasure (hyAlg w₀ β ωs θ γ g : Algorithm Unit α ℝ) (Environment.bandit ν)),
      ∀ ℓ, ℓ ≠ 0 → 0 ≤ θ ℓ →
      ∀ a, a ≠ HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) →
      ∀ D : ℝ, 0 < D →
      ENNReal.ofReal D ≤ HY.imedKinf w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) a →
      (pullCount IT.action a (g.t (ℓ + 1)) ω : ℝ) ≤
        max (pullCount IT.action a (g.t ℓ) ω : ℝ)
          (max (1 + g.ratio ℓ ^ 2 * Real.log (g.imedEnd θ ℓ) / D)
            ((Fintype.card α - 1 : ℕ) + g.netSize β (ℓ + 1))) := by
  filter_upwards [hyAlg_ae_pullCount_add_one_le w₀ β hw₀ ωs θ γ g hν] with ω hround
  intro ℓ hℓ hθ a ha D hD hKt
  have hℓ1 : 1 ≤ ℓ := Nat.one_le_iff_ne_zero.mpr hℓ
  have hy0 : 0 ≤ g.ratio ℓ ^ 2 := sq_nonneg _
  have hσ : g.t ℓ ≤ g.imedEnd θ ℓ := g.t_le_imedEnd hθ
  have hσ1 : 1 ≤ g.imedEnd θ ℓ := le_trans (by have := g.two_le_t hℓ1; omega) hσ
  have hσ1' : (1 : ℝ) ≤ g.imedEnd θ ℓ := by exact_mod_cast hσ1
  set G : ℕ → ℝ := fun k ↦
    max (1 + g.ratio ℓ ^ 2 * Real.log (min ((k : ℝ) + 1) (g.imedEnd θ ℓ : ℝ)) / D)
      ((Fintype.card α - 1 : ℕ) + g.netSize β (ℓ + 1)) with hG
  have hmin_pos : ∀ k : ℕ, (0 : ℝ) < min ((k : ℝ) + 1) (g.imedEnd θ ℓ : ℝ) := fun k ↦
    lt_min (by positivity) (by linarith)
  have hGmono : Monotone G := by
    intro k k' hkk'
    simp only [hG]
    refine max_le_max ?_ le_rfl
    have h2 : min ((k : ℝ) + 1) (g.imedEnd θ ℓ : ℝ) ≤ min ((k' : ℝ) + 1) (g.imedEnd θ ℓ : ℝ) :=
      min_le_min_right _ (by exact_mod_cast Nat.succ_le_succ hkk')
    have := Real.log_le_log (hmin_pos k) h2
    gcongr
  have hstep : ∀ k, g.t ℓ ≤ k → k < g.t (ℓ + 1) → IT.action k ω = a →
      (pullCount IT.action a k ω : ℝ) + 1 ≤ G k := by
    intro k hk1 hk2 hAk
    have hb : g.batchOf k = ℓ + 1 := g.batchOf_eq_iff.mpr ⟨hk1, hk2⟩
    obtain ⟨himed, hpace⟩ := hround ℓ hℓ a ha D hD hKt k hb hAk
    by_cases hk : k + 1 ≤ g.imedEnd θ ℓ
    · refine (himed hk).trans (le_trans ?_ (le_max_left _ _))
      have hk' : (k : ℝ) + 1 ≤ g.imedEnd θ ℓ := by exact_mod_cast hk
      rw [min_eq_left hk']
    · have h1 := hpace hk
      have h2 := HY.target_le (w₀ := w₀) (thr := (1 - γ ℓ) * g.ratio (ℓ - 1) ^ 2 *
        (if ℓ = 1 then g.logEnd 1 else HY.threshold w₀ (g.logEnd ℓ) (g.ratio (ℓ - 1) ^ 2)
          (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) (g.t (ℓ - 1))
          (g.netSize β ℓ) (g.netSize β (ℓ - 1)))) (ω' := ωs ℓ) (y := g.ratio ℓ ^ 2)
        (logt := Real.log (k + 1)) (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ)
        (g.netSize β ℓ) (g.netSize β (ℓ + 1)) a
      have h3 : pullCount IT.action a k ω + 1 ≤ Fintype.card α - 1 + g.netSize β (ℓ + 1) :=
        h1.trans h2
      refine le_trans ?_ (le_max_right _ _)
      exact_mod_cast h3
  have hT := (pullCount_le_max_of_forall_add_one hGmono
    (g.strictMono.monotone (Nat.le_succ ℓ)) hstep).1
  refine hT.trans (max_le_max le_rfl (max_le_max ?_ le_rfl))
  have := Real.log_le_log (hmin_pos (g.t (ℓ + 1) - 1)) (min_le_right _ _)
  gcongr

/-! ### Lemma `lem:levelC` and the count of good high batches -/

open Filter in
/-- [INC-P000, Lemma `lem:levelC`, along a run] On a grid with `x_ℓ → 1`, for HY with any
parameters and any environment, let `g ∈ (0, 1)`, `m'`, and a rank `ℓ_W ≥ 2` from which every
batch `ℓ + 1 ≥ ℓ_W` is not activated or has a long IMED phase (`s_ℓ - t_ℓ ≥ K t_ℓ`, the third
condition defining `ℓ_W` in Definition `def:water`). There is a rank `L₀`, which does not depend on
the run, such that along almost every run every `L ≥ L₀` has at least `m'` batches `j ∈ [2, L)`
high at the level `(1 - g) L_L` for every arm: `J_(j-1)(c, t_j + 1) ≥ y_(j-1) (1 - g) L_L`. -/
lemma hyAlg_ae_le_card_filter_le_imedIndex (w₀ β : ℝ) (ωs θ γ : ℕ → ℝ) (g : Grid (Fintype.card α))
    (hgr : Tendsto g.ratio atTop (nhds 1)) {gg : ℝ} (hg0 : 0 < gg) (hg1 : gg < 1) (m' lW : ℕ)
    (hlW : 2 ≤ lW) (env : Environment Unit α ℝ)
    (hW : ∀ ℓ, lW ≤ ℓ + 1 →
      g.t (ℓ + 1) ≤ g.imedEnd θ ℓ ∨ Fintype.card α * g.t ℓ ≤ g.imedEnd θ ℓ - g.t ℓ) :
    ∃ L₀, ∀ᵐ ω ∂(trajMeasure (hyAlg w₀ β ωs θ γ g : Algorithm Unit α ℝ) env), ∀ L, L₀ ≤ L →
      m' ≤ ((Finset.Ico 2 L).filter fun j ↦ ∀ c,
        ((g.ratio (j - 1) ^ 2 * ((1 - gg) * g.logEnd L) : ℝ) : EReal) ≤
          HY.imedIndex w₀ (g.ratio (j - 1) ^ 2)
            (history IT.obs IT.action IT.feedback (g.t j) ω) (g.t (j - 1)) c).card := by
  -- The water level of the batch `j` is taken as
  -- `Λ_j = min(min_c J_(j-1)(c, t_j + 1), y_(j-1) log t_(j-1)) / y_(j-1)` (the cap keeps it finite
  -- and keeps (W2)); Lemma `lem:W`(i) gives (W2) (`hyAlg_ae_mul_log_pullCount_le_imedIndex`),
  -- Lemma `lem:lowmass` the low mass (`exists_card_le_sum_low_le`), and the rank is the one of
  -- `exists_rank_le_card_filter_le`.
  classical
  obtain ⟨L₀, hL₀⟩ := exists_rank_le_card_filter_le g hgr hg0 hg1 m' (Fintype.card α) lW (by omega)
  refine ⟨L₀, ?_⟩
  filter_upwards [hyAlg_ae_mul_log_pullCount_le_imedIndex w₀ β ωs θ γ g env] with ω hW2
  intro L hL
  -- the water levels
  set I : ℕ → EReal := fun j ↦ min (⨅ c, HY.imedIndex w₀ (g.ratio (j - 1) ^ 2)
    (history IT.obs IT.action IT.feedback (g.t j) ω) (g.t (j - 1)) c)
    ((g.ratio (j - 1) ^ 2 * Real.log (g.t (j - 1)) : ℝ) : EReal) with hI
  set Λ : ℕ → ℝ := fun j ↦ (I j).toReal / g.ratio (j - 1) ^ 2 with hΛ
  -- the indices are nonnegative, so `I j` is finite
  have hidx0 : ∀ j c, (0 : EReal) ≤ HY.imedIndex w₀ (g.ratio (j - 1) ^ 2)
      (history IT.obs IT.action IT.feedback (g.t j) ω) (g.t (j - 1)) c := by
    intro j c
    unfold HY.imedIndex
    have h2 : (0 : ℝ) ≤ g.ratio (j - 1) ^ 2 * Real.log (pullCount' (g.t j)
        (history IT.obs IT.action IT.feedback (g.t j) ω) c) :=
      mul_nonneg (sq_nonneg _) (Real.log_natCast_nonneg _)
    exact add_nonneg (EReal.coe_ennreal_nonneg _) (EReal.coe_nonneg.mpr h2)
  have hI0 : ∀ j, (0 : EReal) ≤ I j := by
    intro j
    refine le_min (le_iInf fun c ↦ hidx0 j c) (EReal.coe_nonneg.mpr ?_)
    exact mul_nonneg (sq_nonneg _) (Real.log_natCast_nonneg _)
  have hIfin : ∀ j, I j = ((I j).toReal : EReal) := by
    intro j
    refine (EReal.coe_toReal ?_ ?_).symm
    · exact ne_top_of_le_ne_top (EReal.coe_ne_top _) (min_le_right _ _)
    · exact ne_bot_of_le_ne_bot (by simp) (hI0 j)
  -- (W2) for these water levels
  have hlow : ∀ L', lW < L' → ∀ v : ℝ, 0 ≤ v → ∃ E : Finset ℕ, E.card ≤ Fintype.card α ∧
      ∑ i ∈ (Finset.Ico lW L').filter (fun i ↦ Λ i < v ∧ i ∉ E),
        ((g.t i : ℝ) - g.t (i - 1)) ≤ Fintype.card α * Real.exp v := by
    intro L' _ v _
    refine exists_card_le_sum_low_le (A := IT.action) (ω := ω) (v := v) g (by omega) ?_
    intro i hi _ c hpull
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hpull ⊢
    have hk0 : k ≠ 0 := by omega
    have hy0 : 0 < g.ratio k ^ 2 := pow_pos (zero_lt_one.trans_le (g.one_le_ratio k)) 2
    -- the arm `c` is pulled at some round of the batch `k + 1`
    obtain ⟨n, hn1, hn2, hAn⟩ := exists_action_eq_of_pullCount_lt hpull
    have hb : g.batchOf n = k + 1 := g.batchOf_eq_iff.mpr ⟨hn1, hn2⟩
    have hidx := fun c' ↦ hW2 k hk0 (hW k (by omega)) n hb c'
    rw [hAn] at hidx
    -- `y log N_c(t_(i-1)) ≤ I_i`
    have hlogt : Real.log (pullCount IT.action c (g.t k) ω) ≤ Real.log (g.t k) :=
      Real.log_natCast_le_log_natCast (pullCount_le _ _ _)
    have hle : ((g.ratio k ^ 2 * Real.log (pullCount IT.action c (g.t k) ω) : ℝ) :
        EReal) ≤ I (k + 1) := by
      simp only [hI, Nat.add_sub_cancel]
      refine le_min (le_iInf hidx) (EReal.coe_le_coe_iff.mpr ?_)
      exact mul_le_mul_of_nonneg_left hlogt (sq_nonneg _)
    rw [hIfin (k + 1), EReal.coe_le_coe_iff] at hle
    simp only [hΛ, Nat.add_sub_cancel]
    rw [le_div_iff₀ hy0]
    linarith
  -- many high batches
  have hcard := hL₀ Λ hlow L hL
  refine hcard.trans (Finset.card_le_card fun j hj ↦ ?_)
  obtain ⟨hjI, hjΛ⟩ := Finset.mem_filter.mp hj
  refine Finset.mem_filter.mpr ⟨hjI, fun c ↦ ?_⟩
  have hj2 := (Finset.mem_Ico.mp hjI).1
  have hy0 : 0 < g.ratio (j - 1) ^ 2 := pow_pos (zero_lt_one.trans_le (g.one_le_ratio _)) 2
  simp only [hΛ] at hjΛ
  rw [le_div_iff₀ hy0] at hjΛ
  have h1 : ((g.ratio (j - 1) ^ 2 * ((1 - gg) * g.logEnd L) : ℝ) : EReal) ≤ I j := by
    rw [hIfin j, EReal.coe_le_coe_iff]
    linarith
  exact h1.trans ((min_le_left _ _).trans (iInf_le _ c))

open Filter in
/-- [INC-P000, Lemma `lem:goodhigh`, first two claims, along a run] Under the hypotheses of
`hyAlg_ae_le_card_filter_le_imedIndex` (for HY with `w₀ ≥ 0` on an instance of `𝒫`), for every `M`
there is a rank
`L₀`, independent of the run, such that along almost every run every `L ≥ L₀` and every
`u ≤ e^((1 - g) L_L)` (the paper's `u_j ≤ t_j^(1-δ)`, `g = δ`) have at least `M + 2` batches
`j ∈ [2, L)` that are high at the level `(1 - g) L_L` for every arm and whose leader has at least
`u` observations at `t_(j-1)` (the paper's `S_go`, with `|S_hi| ≥ M + K + 2`): Lemma `lem:levelC`
(`hyAlg_ae_le_card_filter_le_imedIndex` with `m' = M + K + 2`) and Steps 1–2 of Lemma `lem:goodhigh`
(`hyAlg_ae_card_le_card_filter_le_pullCount_leader_add`). -/
lemma hyAlg_ae_le_card_filter_le_imedIndex_and_le_pullCount_leader (w₀ β : ℝ) (hw₀ : 0 ≤ w₀)
    (ωs θ γ : ℕ → ℝ)
    (g : Grid (Fintype.card α)) (hgr : Tendsto g.ratio atTop (nhds 1)) {gg : ℝ} (hg0 : 0 < gg)
    (hg1 : gg < 1) (M lW : ℕ) (hlW : 2 ≤ lW) {ν : ProbabilityTheory.Kernel α ℝ}
    [ProbabilityTheory.IsMarkovKernel ν] (hν : ν ∈ unitBandits α)
    (hW : ∀ ℓ, lW ≤ ℓ + 1 →
      g.t (ℓ + 1) ≤ g.imedEnd θ ℓ ∨ Fintype.card α * g.t ℓ ≤ g.imedEnd θ ℓ - g.t ℓ) :
    ∃ L₀, ∀ᵐ ω ∂(trajMeasure (hyAlg w₀ β ωs θ γ g : Algorithm Unit α ℝ) (Environment.bandit ν)),
      ∀ L, L₀ ≤ L → ∀ u : ℝ, u ≤ Real.exp ((1 - gg) * g.logEnd L) →
      M + 2 ≤ ((Finset.Ico 2 L).filter fun j ↦ (∀ c,
        ((g.ratio (j - 1) ^ 2 * ((1 - gg) * g.logEnd L) : ℝ) : EReal) ≤
          HY.imedIndex w₀ (g.ratio (j - 1) ^ 2)
            (history IT.obs IT.action IT.feedback (g.t j) ω) (g.t (j - 1)) c) ∧
        u ≤ pullCount IT.action
          (HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t (j - 1)) ω) (g.t (j - 1)))
            (g.t (j - 1)) ω).card := by
  obtain ⟨L₀, hL₀⟩ := hyAlg_ae_le_card_filter_le_imedIndex w₀ β ωs θ γ g hgr hg0 hg1
      (M + Fintype.card α + 2) lW hlW
    (Environment.bandit ν) hW
  refine ⟨L₀, ?_⟩
  filter_upwards
      [hL₀, hyAlg_ae_card_le_card_filter_le_pullCount_leader_add w₀ β hw₀ ωs θ γ g hν] with ω hlev
      hgood
  intro L hL u hu
  set Shi := (Finset.Ico 2 L).filter fun j ↦ ∀ c,
    ((g.ratio (j - 1) ^ 2 * ((1 - gg) * g.logEnd L) : ℝ) : EReal) ≤
      HY.imedIndex w₀ (g.ratio (j - 1) ^ 2)
        (history IT.obs IT.action IT.feedback (g.t j) ω) (g.t (j - 1)) c with hShi
  have hcard : M + Fintype.card α + 2 ≤ Shi.card := hlev L hL
  obtain ⟨-, h2⟩ := hgood Shi ((1 - gg) * g.logEnd L) u
    (fun i hi ↦ (Finset.mem_Ico.mp (Finset.mem_filter.mp hi).1).1) hu
    (fun i hi ↦ (Finset.mem_filter.mp hi).2 _)
  rw [Finset.filter_filter] at h2
  omega


/-! ### Lemma `lem:sumC` -/

/-- [INC-P000, Lemma `lem:sumC`] On every grid, for `K, C₀ ≥ 0`, `ε > 0` and `η > 0`, with
`u_j = (1 + η) L_j / (2ε²)` and
`π_j = (2K / (1 - e^(-2ε²)) + 2 C₀ (1 + u_j⁴)) t_j^(-(1+η))`, every partial sum has
`∑_{2 ≤ j < L} B_j π_j ≤ C_π(ε) = (2K (1 + 1/(2ε²)) + 2C₀)(1 + 2/η)
  + 2C₀ ((1 + η)/(2ε²))⁴ (8/(eη))⁴ (1 + 2/η)` (Lemma `lem:sums`(vi) for the two sums
`∑ B_j t_j^(-(1+η))` and `∑ B_j L_j⁴ t_j^(-(1+η))`). The paper's `η` is `η₀`. -/
lemma Grid.sum_sub_mul_rpow_neg_le {K' : ℕ} (g : Grid K') {K C₀ ε η : ℝ} (hK : 0 ≤ K) (hC₀ : 0 ≤ C₀)
    (hε : 0 < ε) (hη : 0 < η) (L : ℕ) :
    ∑ j ∈ Finset.Ico 2 L, ((g.t j : ℝ) - g.t (j - 1)) *
        ((2 * K / (1 - Real.exp (-(2 * ε ^ 2))) +
          2 * C₀ * (1 + ((1 + η) * g.logEnd j / (2 * ε ^ 2)) ^ 4)) * (g.t j : ℝ) ^ (-(1 + η))) ≤
      (2 * K * (1 + 1 / (2 * ε ^ 2)) + 2 * C₀) * (1 + 2 / η) +
        2 * C₀ * ((1 + η) / (2 * ε ^ 2)) ^ 4 * ((8 / (Real.exp 1 * η)) ^ 4 * (1 + 2 / η)) := by
  have hv : 0 < 2 * ε ^ 2 := by positivity
  have he : 0 < 1 - Real.exp (-(2 * ε ^ 2)) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  set A := 2 * K / (1 - Real.exp (-(2 * ε ^ 2))) + 2 * C₀ with hA
  set c := (1 + η) / (2 * ε ^ 2) with hc
  have hA0 : 0 ≤ A := by positivity
  have hAle : A ≤ 2 * K * (1 + 1 / (2 * ε ^ 2)) + 2 * C₀ := by
    have h := one_div_one_sub_exp_neg_le hv
    have h' : 2 * K / (1 - Real.exp (-(2 * ε ^ 2))) =
        2 * K * (1 / (1 - Real.exp (-(2 * ε ^ 2)))) := by ring
    have := mul_le_mul_of_nonneg_left h (by linarith : 0 ≤ 2 * K)
    linarith
  have hsplit : ∑ j ∈ Finset.Ico 2 L, ((g.t j : ℝ) - g.t (j - 1)) *
      ((2 * K / (1 - Real.exp (-(2 * ε ^ 2))) +
        2 * C₀ * (1 + ((1 + η) * g.logEnd j / (2 * ε ^ 2)) ^ 4)) * (g.t j : ℝ) ^ (-(1 + η))) =
      A * ∑ j ∈ Finset.Ico 2 L, ((g.t j : ℝ) - g.t (j - 1)) * (g.t j : ℝ) ^ (-(1 + η)) +
      2 * C₀ * c ^ 4 * ∑ j ∈ Finset.Ico 2 L, ((g.t j : ℝ) - g.t (j - 1)) *
        Real.log (g.t j) ^ 4 * (g.t j : ℝ) ^ (-(1 + η)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [Grid.logEnd, hA, hc]
    ring
  rw [hsplit]
  have h1 := g.sum_mul_rpow_le_one_add hη L
  have h4 := g.sum_mul_log_pow_four_le hη L
  have hc4 : 0 ≤ 2 * C₀ * c ^ 4 := by positivity
  calc A * ∑ j ∈ Finset.Ico 2 L, ((g.t j : ℝ) - g.t (j - 1)) * (g.t j : ℝ) ^ (-(1 + η)) +
        2 * C₀ * c ^ 4 * ∑ j ∈ Finset.Ico 2 L, ((g.t j : ℝ) - g.t (j - 1)) *
          Real.log (g.t j) ^ 4 * (g.t j : ℝ) ^ (-(1 + η))
      ≤ A * (1 + 2 / η) + 2 * C₀ * c ^ 4 * ((8 / (Real.exp 1 * η)) ^ 4 * (1 + 2 / η)) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 hA0) (mul_le_mul_of_nonneg_left h4 hc4)
    _ ≤ _ := by
        have : 0 ≤ 1 + 2 / η := by positivity
        have := mul_le_mul_of_nonneg_right hAle this
        linarith

end Incognita.BatchedBandits
