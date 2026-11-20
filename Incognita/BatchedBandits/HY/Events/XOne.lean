/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.HY.Events
public import Incognita.BatchedBandits.KInf.Dual
public import Incognita.BatchedBandits.Counting

/-! # The class `𝒪` when `x = 1`

[INC-P000, Lemma `lem:controlC`(d)], for the trace on the run of the class `𝒪` of the
decomposition `lem:decompC`. This holds for every learner that observes the arm in batch 1. The
traces of the events `𝒟_j`, `𝒱⋆_j` and `𝒱_(a,j)` (Lemma `lem:controlC`(a)–(c)) are in
`Incognita.BatchedBandits.HY.Events`, as generalisations of the bounds of Lemma `lem:probasA`:
`measure_exists_mem_le_pullCount_abs_sub_gt_le`, `measure_exists_mem_lt_mul_pseudoKinf_le` and
`measure_exists_mem_lt_mul_pseudoKinf_and_le_le`.

* `lintegral_sum_ite_pseudoKinf_lt_le`: Lemma `lem:controlC`(d), the class `𝒪`: the expectation of
  `∑_(2 ≤ j ≤ L) N_a(t_(j-1)) 1(𝒦_inf(ν̂_a(t_(j-1)), μ) < A - 3ε'/4, N_a(t_(j-1)) < N_a(t_j))` is at
  most `1/ρ'²`, through Lemmas `lem:distinct`(i) and `lem:lowerdev`, and `sum_Icc_mul_exp_neg_le`
  (`∑_(1 ≤ n ≤ M) n e^(-ρ n) ≤ 1/ρ²`).
* `measure_le_pullCount_pseudoKinf_lt_dInf_sub_le`,
  `measure_le_pullCount_dInf_add_lt_pseudoKinf_le`: [INC-P000, Lemma `lem:probasA`(c)] at the
  levels of the primal `𝒦_inf(ν_a, ·)`: the traces of the events `ℒ`
  (`𝒦_inf(ν̂_a(t), μ) < 𝒦_inf(ν_a, μ) - ε'`) and `𝒰`
  (`𝒦_inf(ν̂_a(t), μ) > 𝒦_inf(ν_a, μ) + ε'`), through the two directions of the primal formula
  (`Incognita.BatchedBandits.KInf.Dual`);
  `measure_exists_mem_le_pullCount_pseudoKinf_lt_or_lt_le`: the trace of `KC_ℓ^c` of [INC-P000,
  Definition `def:amb`] at a finite
  set of cutoffs (the step 5 of the proof of Lemma `lem:amb`).
-/

@[expose] public section

open Learning Finset MeasureTheory ProbabilityTheory Bandits LMLExplore.Bandits

open scoped ENNReal

namespace Incognita.BatchedBandits

variable {α : Type*} [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- [INC-P000, Lemma `lem:controlC`(d), for the trace of the class `𝒪` on the run] For every learner
on an instance `ν` of `𝒫` that observes the arm `a` in batch 1 (`N_a(t_1) ≥ 1` almost surely, as HY
does), every grid, a level `μ ∈ [0, 1)`, `ε' > 0` and `λ ∈ [0, 1/(1-μ))` with
`A = E_(ν_a)[log (1 - λ (Y - μ))]`, and every `L`:
`E[∑_(2 ≤ j ≤ L) N_a(t_(j-1)) 1(𝒦_inf(ν̂_a(t_(j-1)), μ) < A - 3ε'/4, N_a(t_(j-1)) < N_a(t_j))]
  ≤ 1 / ρ'²`, `ρ' = ε'² / (2 (κ(μ) - log (1 - e^(-ε'/4)))²)`. With `μ = m⋆ - 2ε`, `ε' = ε` and an
  `ε/4`-optimal `λ`
(`A - 3ε/4 ≥ 𝒦_inf(ν_a, m⋆ - 2ε) - ε = D'_ε`), the event contains the paper's
`{𝒦_inf(ν̂_(a,n), m⋆ - 2ε) < D'_ε}`; the paper's `≤` is the same bound for the closed event, which
the decomposition `lem:decompC` does not need. -/
lemma lintegral_sum_ite_pseudoKinf_lt_le [Countable α] {alg : Algorithm Unit α ℝ}
    {ν : Kernel α ℝ} [IsMarkovKernel ν] (hν : ν ∈ unitBandits α) {K' : ℕ} (g : Grid K') (a : α)
    {μ ε' lam : ℝ} (hμ0 : 0 ≤ μ) (hμ : μ < 1) (hε' : 0 < ε') (hlam0 : 0 ≤ lam)
    (hlam1 : lam * (1 - μ) < 1)
    (h1 : ∀ᵐ ω ∂(trajMeasure alg (Environment.bandit ν)), 1 ≤ pullCount IT.action a (g.t 1) ω)
    (L : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (∑ j ∈ Finset.Ico 2 (L + 1),
      if HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback (g.t (j - 1)) ω) (g.t (j - 1)) a
          μ < ENNReal.ofReal (∫ y, Real.log (1 - lam * (y - μ)) ∂(ν a) - 3 * ε' / 4) ∧
        pullCount IT.action a (g.t (j - 1)) ω < pullCount IT.action a (g.t j) ω
      then (pullCount IT.action a (g.t (j - 1)) ω : ℝ) else 0)
      ∂(trajMeasure alg (Environment.bandit ν)) ≤
    ENNReal.ofReal (1 / (ε' ^ 2 / (2 * (Real.log (1 / (1 - μ)) -
        Real.log (1 - Real.exp (-(ε' / 4)))) ^ 2)) ^ 2) := by
  -- On the stacks, the batches in which the count of `a` increases start at distinct counts
  -- `n ∈ [1, t_L]` (Lemma `lem:distinct`(i)), the trace at the count `n` is in the event of
  -- Lemma `lem:lowerdev` (probability `≤ e^(-ρ' n)`), and `∑_n n e^(-ρ' n) ≤ 1/ρ'²`.
  classical
  set P := trajMeasure alg (Environment.bandit ν) with hP
  have hseq := IT.isAlgEnvSeq_trajMeasure alg (Environment.bandit ν)
  set B := ∫ y, Real.log (1 - lam * (y - μ)) ∂(ν a) - 3 * ε' / 4 with hB
  set ρ := ε' ^ 2 / (2 * (Real.log (1 / (1 - μ)) - Real.log (1 - Real.exp (-(ε' / 4)))) ^ 2)
    with hρ
  set Q := P.prod (streamMeasure ν) with hQ
  set Z : ℕ → (ℕ → Round Unit α ℝ) × (ℕ → α → ℝ) → ℝ :=
    fun i ω' ↦ rewardByCount IT.action IT.feedback a (i + 1) ω' with hZ
  set H : ℕ → Set ((ℕ → Round Unit α ℝ) × (ℕ → α → ℝ)) := fun n ↦
    {ω' | ∀ l, 0 ≤ l → l * (1 - μ) < 1 →
      ∑ i ∈ range n, Real.log (1 - l * (Z i ω' - μ)) ≤ n * B} with hH
  set M := g.t L with hM
  -- the pointwise bound on the product with the stacks
  have hmap : P = Q.map Prod.fst := by
    rw [hQ, Measure.map_fst_prod, measure_univ, one_smul]
  have hgood : ∀ᵐ ω' ∂Q, (∀ n, IT.feedback n ω'.1 ∈ Set.Icc (0 : ℝ) 1) ∧
      1 ≤ pullCount IT.action a (g.t 1) ω'.1 := by
    have hP' : ∀ᵐ ω ∂P, (∀ n, IT.feedback n ω ∈ Set.Icc (0 : ℝ) 1) ∧
        1 ≤ pullCount IT.action a (g.t 1) ω := (ae_feedback_mem_Icc (alg := alg) hν).and h1
    rw [hmap] at hP'
    exact ae_of_ae_map measurable_fst.aemeasurable hP'
  have hpoint : ∀ᵐ ω' ∂Q, ENNReal.ofReal (∑ j ∈ Finset.Ico 2 (L + 1),
      if HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback (g.t (j - 1)) ω'.1) (g.t (j - 1))
          a μ < ENNReal.ofReal B ∧
        pullCount IT.action a (g.t (j - 1)) ω'.1 < pullCount IT.action a (g.t j) ω'.1
      then (pullCount IT.action a (g.t (j - 1)) ω'.1 : ℝ) else 0) ≤
      ∑ n ∈ Finset.Icc 1 M, (toMeasurable Q (H n)).indicator (fun _ ↦ (n : ℝ≥0∞)) ω' := by
    filter_upwards [hgood] with ω' hω'
    obtain ⟨hfb, hN1⟩ := hω'
    obtain ⟨ω, x⟩ := ω'
    simp only at hfb hN1 ⊢
    set N : ℕ → ℕ := fun j ↦ pullCount IT.action a (g.t j) ω with hNdef
    have hNmono : Monotone N := fun j j' hjj' ↦
      pullCount_mono (A := IT.action) a (g.strictMono.monotone hjj') ω
    -- the trace at a count `n ≥ 1` is in the event `H n` of the stacks
    have hincl : ∀ s : ℕ, 1 ≤ pullCount IT.action a s ω →
        HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback s ω) s a μ < ENNReal.ofReal B →
        (ω, x) ∈ H (pullCount IT.action a s ω) := by
      intro s hs1 hlt l hl0 hl1
      exact sum_log_rewardByCount_le_of_pseudoKinf_lt x hμ0 hμ hfb hlt hl0 hl1
    -- termwise, then the distinct counts (Lemma `lem:distinct`(i))
    have hterm : ∀ j ∈ Finset.Ico 2 (L + 1),
        (if HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback (g.t (j - 1)) ω) (g.t (j - 1))
            a μ < ENNReal.ofReal B ∧ N (j - 1) < N j then (N (j - 1) : ℝ) else 0) ≤
        (if (ω, x) ∈ H (N (j - 1)) ∧ N (j - 1) < N j then (N (j - 1) : ℝ) else 0) := by
      intro j _
      by_cases hc : HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback (g.t (j - 1)) ω)
          (g.t (j - 1)) a μ < ENNReal.ofReal B ∧ N (j - 1) < N j
      · rw [ite_eq_left hc]
        by_cases h0 : N (j - 1) = 0
        · simp only [h0, Nat.cast_zero]
          split_ifs <;> simp
        · rw [ite_eq_left ⟨hincl _ (Nat.one_le_iff_ne_zero.mpr h0) hc.1, hc.2⟩]
      · rw [ite_eq_right hc]
        split_ifs <;> positivity
    have hNL : N L ≤ M := pullCount_le _ _ _
    have hdist := sum_ite_le_sum_Icc_of_monotone hNmono hN1 hNL
      (g := fun n : ℕ ↦ (n : ℝ)) (fun n ↦ Nat.cast_nonneg n) (fun n ↦ (ω, x) ∈ H n)
    have hreal := (Finset.sum_le_sum hterm).trans hdist
    refine (ENNReal.ofReal_le_ofReal hreal).trans ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun n _ ↦ by split_ifs <;> positivity)]
    refine Finset.sum_le_sum fun n _ ↦ ?_
    split_ifs with hn
    · rw [Set.indicator_of_mem (subset_toMeasurable Q _ hn), ENNReal.ofReal_natCast]
    · rw [ENNReal.ofReal_zero]
      exact zero_le
  -- integrate
  have hstep1 : ∫⁻ ω, ENNReal.ofReal (∑ j ∈ Finset.Ico 2 (L + 1),
      if HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback (g.t (j - 1)) ω) (g.t (j - 1))
          a μ < ENNReal.ofReal B ∧
        pullCount IT.action a (g.t (j - 1)) ω < pullCount IT.action a (g.t j) ω
      then (pullCount IT.action a (g.t (j - 1)) ω : ℝ) else 0) ∂P ≤
      ∫⁻ ω', ENNReal.ofReal (∑ j ∈ Finset.Ico 2 (L + 1),
      if HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback (g.t (j - 1)) ω'.1) (g.t (j - 1))
          a μ < ENNReal.ofReal B ∧
        pullCount IT.action a (g.t (j - 1)) ω'.1 < pullCount IT.action a (g.t j) ω'.1
      then (pullCount IT.action a (g.t (j - 1)) ω'.1 : ℝ) else 0) ∂Q := by
    conv_lhs => rw [hmap]
    exact lintegral_map_le _ measurable_fst.aemeasurable
  refine hstep1.trans ((lintegral_mono_ae hpoint).trans ?_)
  rw [lintegral_finsetSum _ fun n _ ↦
    measurable_const.indicator (measurableSet_toMeasurable Q _)]
  simp_rw [lintegral_indicator_const (measurableSet_toMeasurable Q _), measure_toMeasurable]
  -- each event of the stacks, by Lemma `lem:lowerdev`
  have hlaw := fun i ↦ hasLaw_rewardByCount_add_one hseq a i
  have hρ0 : 0 < ρ := deviation_rate_pos hμ0 hμ hε'
  have hterm : ∀ n ∈ Finset.Icc 1 M, (n : ℝ≥0∞) * Q (H n) ≤
      ENNReal.ofReal ((n : ℝ) * Real.exp (-(ρ * n))) := by
    intro n hn
    have hQ := measure_forall_sum_log_le_le (Y := Z) (iIndepFun_rewardByCount_add_one_action hseq a)
      (fun i ↦ measurable_rewardByCount IT.measurable_action IT.measurable_feedback a (i + 1))
      (fun i ↦ (hlaw i).map_eq) (hν.1 a).2 hμ0 hμ hε' hlam0 hlam1 (N := n)
      (Finset.mem_Icc.mp hn).1
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    gcongr
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ ↦ by positivity)]
  exact ENNReal.ofReal_le_ofReal (sum_Icc_mul_exp_neg_le hρ0 M)

/-- [INC-P000, Lemma `lem:probasA`(c), the event `ℒ`, at the primal level] For every learner on an
instance `ν` of `𝒫`, every cutoff `t`, an arm `a`, `μ ∈ [0, 1)`, `ε' > 0` and `u > 0`: the
probability that `N_a(t) ≥ u` and `𝒦_inf(ν̂_a(t), μ) < 𝒦_inf(ν_a, μ) - ε'` (the primal
`𝒦_inf(ν_a, μ)` of the frozen statements) is at most `e^(-ρ' u) / (1 - e^(-ρ'))`, `ρ'` of
Lemma `lem:lowerdev`: an `ε'/4`-optimal `λ` of the dual formula (`exists_dInf_sub_lt_dual`) has
`A - 3ε'/4 > 𝒦_inf(ν_a, μ) - ε'`, and `measure_le_pullCount_pseudoKinf_lt_le`. With
`μ = m⋆ - 2ε` and `ε' = ε` this is the paper's `𝒦_inf(ν̂, m⋆ - 2ε) < D_ε`. -/
lemma measure_le_pullCount_pseudoKinf_lt_dInf_sub_le [Countable α] {alg : Algorithm Unit α ℝ}
    {ν : Kernel α ℝ} [IsMarkovKernel ν] (hν : ν ∈ unitBandits α) (t : ℕ) (a : α) {μ ε' u : ℝ}
    (hμ0 : 0 ≤ μ) (hμ : μ < 1) (hε' : 0 < ε') (hu : 0 < u) :
    trajMeasure alg (Environment.bandit ν) {ω | u ≤ pullCount IT.action a t ω ∧
      HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback t ω) t a μ <
        ENNReal.ofReal ((dInf unitLaws (ν a) μ).toReal - ε')} ≤
    ENNReal.ofReal (Real.exp (-(ε' ^ 2 / (2 * (Real.log (1 / (1 - μ)) -
        Real.log (1 - Real.exp (-(ε' / 4)))) ^ 2) * u)) /
      (1 - Real.exp (-(ε' ^ 2 / (2 * (Real.log (1 / (1 - μ)) -
        Real.log (1 - Real.exp (-(ε' / 4)))) ^ 2))))) := by
  obtain ⟨lam, hl0, hl1, hlam⟩ := exists_dInf_sub_lt_dual (hν.1 a) hμ0 hμ (ε := ε' / 4)
    (by positivity)
  have hsub : {ω | u ≤ pullCount IT.action a t ω ∧
      HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback t ω) t a μ <
        ENNReal.ofReal ((dInf unitLaws (ν a) μ).toReal - ε')} ⊆
      {ω | u ≤ pullCount IT.action a t ω ∧
        HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback t ω) t a μ <
          ENNReal.ofReal (∫ y, Real.log (1 - lam * (y - μ)) ∂(ν a) - 3 * ε' / 4)} :=
    fun ω hω ↦ ⟨hω.1, hω.2.trans_le (ENNReal.ofReal_le_ofReal (by linarith))⟩
  exact (measure_mono hsub).trans
    (measure_le_pullCount_pseudoKinf_lt_le hν t a hμ0 hμ hε' hl0 hl1 hu)

/-- [INC-P000, Lemma `lem:probasA`(c), the event `𝒰`, at the primal level] For every learner on an
instance `ν` of `𝒫`, every cutoff `t`, an arm `a`, `μ ∈ [0, 1)`, `ε' > 0` and `u > 0`: the
probability that `N_a(t) ≥ u` and `𝒦_inf(ν̂_a(t), μ) > 𝒦_inf(ν_a, μ) + ε'` is at most
`n_g e^(-ρ' u) / (1 - e^(-ρ'))` (Lemma `lem:upperdev`): the primal `𝒦_inf(ν_a, μ)` (finite,
`dInf_unitLaws_ne_top`) bounds the dual formula (`ofReal_dual_le_dInf`), and
`measure_le_pullCount_lt_pseudoKinf_le`. With `μ = m⋆ + ε` and `ε' = ε` this is the paper's
event `𝒰`. -/
lemma measure_le_pullCount_dInf_add_lt_pseudoKinf_le [Countable α] {alg : Algorithm Unit α ℝ}
    {ν : Kernel α ℝ} [IsMarkovKernel ν] (hν : ν ∈ unitBandits α) (t : ℕ) (a : α) {μ ε' u : ℝ}
    (hμ0 : 0 ≤ μ) (hμ : μ < 1) (hε' : 0 < ε') (hu : 0 < u) :
    trajMeasure alg (Environment.bandit ν) {ω | u ≤ pullCount IT.action a t ω ∧
      ENNReal.ofReal ((dInf unitLaws (ν a) μ).toReal + ε') <
        HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback t ω) t a μ} ≤
    ENNReal.ofReal ((⌈8 / (ε' * (1 - Real.exp (-(ε' / 4))) * (1 - μ))⌉₊ + 1 : ℕ) *
      Real.exp (-(ε' ^ 2 / (2 * (Real.log (1 / (1 - μ)) -
        Real.log (1 - Real.exp (-(ε' / 4)))) ^ 2) * u)) /
      (1 - Real.exp (-(ε' ^ 2 / (2 * (Real.log (1 / (1 - μ)) -
        Real.log (1 - Real.exp (-(ε' / 4)))) ^ 2))))) := by
  refine measure_le_pullCount_lt_pseudoKinf_le hν t a hμ0 hμ hε' (fun l hl0 hl1 ↦ ?_) hu
  have h := ofReal_dual_le_dInf (hν.1 a) (μ := μ) hl0 hl1
  rw [← ENNReal.ofReal_toReal (dInf_unitLaws_ne_top (hν.1 a) hμ)] at h
  exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp h

/-- [INC-P000, proof of Lemma `lem:amb`, Step 5, the event `KC_ℓ^c`, for its trace on the run] For
every learner on an instance `ν` of `𝒫`, a finite set `T` of cutoffs, an arm `a`, `μ ∈ [0, 1)`,
`ε' > 0` and `u > 0`: the probability that some `s ∈ T` has `N_a(s) ≥ u` and
`|𝒦_inf(ν̂_a(s), μ) - 𝒦_inf(ν_a, μ)| > ε'` is at most `|T| (p_ℒ + p_𝒰)`, the bounds of
`measure_le_pullCount_pseudoKinf_lt_dInf_sub_le` and
`measure_le_pullCount_dInf_add_lt_pseudoKinf_le` (the paper's `T = {t_(ℓ-1), t_ℓ}`, `μ = m⋆`,
`ε' = ζ'_ℓ`, `u = n_ℓ`). -/
lemma measure_exists_mem_le_pullCount_pseudoKinf_lt_or_lt_le [Countable α]
    {alg : Algorithm Unit α ℝ} {ν : Kernel α ℝ}
    [IsMarkovKernel ν] (hν : ν ∈ unitBandits α) (T : Finset ℕ) (a : α) {μ ε' u : ℝ}
    (hμ0 : 0 ≤ μ) (hμ : μ < 1) (hε' : 0 < ε') (hu : 0 < u) :
    trajMeasure alg (Environment.bandit ν) {ω | ∃ s ∈ T, u ≤ pullCount IT.action a s ω ∧
      (HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback s ω) s a μ <
          ENNReal.ofReal ((dInf unitLaws (ν a) μ).toReal - ε') ∨
        ENNReal.ofReal ((dInf unitLaws (ν a) μ).toReal + ε') <
          HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback s ω) s a μ)} ≤
    T.card * (ENNReal.ofReal (Real.exp (-(ε' ^ 2 / (2 * (Real.log (1 / (1 - μ)) -
        Real.log (1 - Real.exp (-(ε' / 4)))) ^ 2) * u)) /
      (1 - Real.exp (-(ε' ^ 2 / (2 * (Real.log (1 / (1 - μ)) -
        Real.log (1 - Real.exp (-(ε' / 4)))) ^ 2))))) +
      ENNReal.ofReal ((⌈8 / (ε' * (1 - Real.exp (-(ε' / 4))) * (1 - μ))⌉₊ + 1 : ℕ) *
      Real.exp (-(ε' ^ 2 / (2 * (Real.log (1 / (1 - μ)) -
        Real.log (1 - Real.exp (-(ε' / 4)))) ^ 2) * u)) /
      (1 - Real.exp (-(ε' ^ 2 / (2 * (Real.log (1 / (1 - μ)) -
        Real.log (1 - Real.exp (-(ε' / 4)))) ^ 2)))))) := by
  set P := trajMeasure alg (Environment.bandit ν) with hP
  have hsub : {ω | ∃ s ∈ T, u ≤ pullCount IT.action a s ω ∧
      (HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback s ω) s a μ <
          ENNReal.ofReal ((dInf unitLaws (ν a) μ).toReal - ε') ∨
        ENNReal.ofReal ((dInf unitLaws (ν a) μ).toReal + ε') <
          HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback s ω) s a μ)} ⊆
      ⋃ s ∈ T, ({ω | u ≤ pullCount IT.action a s ω ∧
        HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback s ω) s a μ <
          ENNReal.ofReal ((dInf unitLaws (ν a) μ).toReal - ε')} ∪
        {ω | u ≤ pullCount IT.action a s ω ∧
          ENNReal.ofReal ((dInf unitLaws (ν a) μ).toReal + ε') <
            HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback s ω) s a μ}) := by
    rintro ω ⟨s, hs, hu', hlt | hgt⟩
    · exact Set.mem_biUnion hs (Or.inl ⟨hu', hlt⟩)
    · exact Set.mem_biUnion hs (Or.inr ⟨hu', hgt⟩)
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun s _ ↦ (measure_union_le _ _).trans (add_le_add ?_ ?_)
  · exact measure_le_pullCount_pseudoKinf_lt_dInf_sub_le hν s a hμ0 hμ hε' hu
  · exact measure_le_pullCount_dInf_add_lt_pseudoKinf_le hν s a hμ0 hμ hε' hu

end Incognita.BatchedBandits
