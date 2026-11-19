/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.HY.Run
public import Incognita.ForMathlib.Probability.Moments.Hoeffding
public import Incognita.BatchedBandits.KInf.Deviations
public import Incognita.BatchedBandits.Deviations
public import Incognita.BatchedBandits.Tilt
public import LeanMachineLearning.Online.Bandit.RewardByCountMeasure

/-! # The probability of inaccurate means at a batch end

[INC-P000, Lemma `lem:probasA`(a)], for the trace on the run of the event `𝒜_ℓ`
(Definition `def:evA`): the probability that some arm with `N_c(t) ≥ U / 2` pulls before a cutoff
`t` has an empirical mean at distance more than `ε` from its mean is at most
`2K e^(-ε² U) / (1 - e^(-2ε²))`, the paper's `c_𝒜(ε) e^(-ε² U_ℓ)`. This holds for every learner.

The reward stacks of [INC-P000, Definition `def:stacks`] are LML's rewards by count
`rewardByCount A R c m` on the product `P ⊗ streamMeasure ν` (the reward at the `m`-th pull of
`c`, independent, of law `ν_c`); on a run, the empirical mean of `c` before `t` is the mean of the
first `N_c(t)` rewards of its stack (`HY.pseudoMean_zero_history_eq`), which is
[INC-P000, Lemma `lem:stacks`] for the empirical means.

* `HY.pseudoMean_zero_history_eq`: the empirical mean of `c` at the cutoff `t` of a run is
  `(∑_(i < N) rewardByCount A R c (i + 1)) / N`, `N = N_c(t)`; `sum_comp_rewardByCount_eq` and
  `HY.pseudoLogMean_zero_history_eq`: the same for a function of the rewards, and for the function
  of the dual formula of `𝒦_inf(ν̂_c(t), μ)`; `sum_log_rewardByCount_le_of_pseudoKinf_lt`: a low
  empirical divergence at a count `N ≥ 1` bounds the dual sums of the first `N` rewards of the
  stack (the step shared by the traces of the event `ℒ` and of the class `𝒪`).
* `measure_exists_wellSampled_abs_sub_gt_le`: Lemma `lem:probasA`(a) for the trace of `𝒜`, the
  case `T = {t}`, `u = U / 2` of `measure_exists_mem_le_pullCount_abs_sub_gt_le`
  ([INC-P000, Lemma `lem:controlC`(a)], the trace of `𝒟_j`): some arm `c` and some cutoff `s` of a
  set `T` with `N_c(s) ≥ u` and `|m̂_c(s) - m_c| > ε`, with probability at most
  `K · 2 e^(-2ε² u) / (1 - e^(-2ε²))`.
* `measure_le_pullCount_pseudoKinf_lt_le`, `measure_le_pullCount_lt_pseudoKinf_le`:
  Lemma `lem:probasA`(c) for the traces of the events `ℒ` and `𝒰` (low and high empirical
  divergence of `a`), through Lemmas `lem:lowerdev` and `lem:upperdev`.
* `measure_lt_mul_pseudoKinf_le`: Lemma `lem:probasA`(b), first bound, for the trace of the
  event `𝒱` (an optimal arm not well sampled, rejected against a sub-optimal level), through
  Lemma `lem:single` (with the gain of Lemma `lem:constA`(b) as the hypothesis `2 η r ≤ m - r`);
  it is the case `T = {s}` of `measure_exists_mem_lt_mul_pseudoKinf_le`
  ([INC-P000, Lemma `lem:controlC`(b)], the trace of `𝒱⋆_j`: some cutoff `s ∈ T` with `N(s) < U`
  and `N(s) 𝒦_inf(ν̂(s), r) ≥ z`).
* `measure_lt_mul_pseudoKinf_and_le_le`: Lemma `lem:probasA`(b), second bound, for the trace of
  the event `Π` and one sub-optimal arm, through Lemma `lem:pair` (with the moment conditions of
  Lemma `lem:constA`(c) as hypotheses); it is the case `T = {s}` of
  `measure_exists_mem_lt_mul_pseudoKinf_and_le_le` ([INC-P000, Lemma `lem:controlC`(c)], the
  trace of `𝒱_(a,j)`: `N_a(t) < U`, `m̂_a(t) ≥ q` and some cutoff `s ∈ T`, `s ≤ t`, with
  `N_a(s) 𝒦_inf(ν̂_a(s), r) ≥ z`).
* `deviation_rate_pos`: the rate `ρ'` of Lemmas `lem:lowerdev` and `lem:upperdev` is positive.
* `exists_tilt_moment_le`: Lemma `lem:constA`(c), the moment conditions, for the law of one
  sub-optimal arm (from Lemma `lem:theta`); `iSup_integral_add_lt_one_and_integral_add_lt_sub`:
  Lemma `lem:constA`(a).
* `exists_tilt_moment_le_forall`: [INC-P000, Lemma `lem:constA`(c), Definition `def:constA`] the
  tilts of all the sub-optimal arms with one constant `c_θ > 0` and one accuracy `ε_θ > 0` (the
  minima over the arms of `exists_tilt_moment_le`).
-/

@[expose] public section

open Learning Finset MeasureTheory ProbabilityTheory Bandits

open scoped ENNReal

namespace Incognita.BatchedBandits

variable {α : Type*} [DecidableEq α] [MeasurableSpace α]

omit [MeasurableSpace α] in
/-- [INC-P000, Lemma `lem:stacks`, for the empirical means] On a run, the empirical mean of `c` at
the cutoff `t` (`HY.pseudoMean 0` of the history of the rounds `< t`) is the mean of the first
`N = N_c(t)` rewards of the stack of `c`: `(∑_(i < N) rewardByCount A R c (i + 1) ω') / N`, for
every point `ω' = (ω, z)` of the product space over `ω`. -/
lemma HY.pseudoMean_zero_history_eq {Ω : Type*} {O : ℕ → Ω → Unit} {A : ℕ → Ω → α}
    {R : ℕ → Ω → ℝ} (t : ℕ) (c : α) (ω' : Ω × (ℕ → α → ℝ)) :
    HY.pseudoMean 0 (history O A R t ω'.1) t c =
      (∑ i ∈ range (pullCount A c t ω'.1), rewardByCount A R c (i + 1) ω') /
        pullCount A c t ω'.1 := by
  unfold HY.pseudoMean
  rw [HY.sum_ind_mul_feedback_history le_rfl, HY.count_history le_rfl, add_zero]
  congr 1
  have h1 := sum_rewardByCount_eq_sumRewards (A := A) (R := R) c t ω'
  unfold sumRewards at h1
  rw [← h1, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [add_comm]

omit [MeasurableSpace α] in
/-- [INC-P000, Lemma `lem:stacks`] On a run, the sum of `φ` over the rewards of `c` in the rounds
`< t` is the sum of `φ` over the first `N_c(t)` rewards of the stack of `c`. -/
lemma sum_comp_rewardByCount_eq {Ω : Type*} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ} (φ : ℝ → ℝ)
    (c : α) (t : ℕ) (ω' : Ω × (ℕ → α → ℝ)) :
    ∑ m ∈ Icc 1 (pullCount A c t ω'.1), φ (rewardByCount A R c m ω') =
      ∑ s ∈ range t, if A s ω'.1 = c then φ (R s ω'.1) else 0 := by
  induction t with
  | zero => simp [pullCount]
  | succ t ht =>
    by_cases hta : A t ω'.1 = c
    · rw [← hta] at ht ⊢
      rw [pullCount_action_eq_pullCount_add_one, sum_Icc_succ_top (Nat.le_add_left 1 _), ht,
        sum_range_succ, ite_eq_left rfl, rewardByCount_pullCount_add_one_eq_reward]
    · rw [pullCount_eq_pullCount_of_action_ne hta, sum_range_succ, ite_eq_right hta, add_zero, ht]

omit [MeasurableSpace α] in
/-- [INC-P000, Lemma `lem:stacks`, for the dual formula] On a run, the function of the dual
formula of `𝒦_inf(ν̂_c(t), μ)` (`w₀ = 0`) at `λ` is
`(∑_(i < N) log (1 - λ (X_(c,i) - μ))) / N`, `N = N_c(t)`, with the stack of `c`. -/
lemma HY.pseudoLogMean_zero_history_eq {Ω : Type*} {O : ℕ → Ω → Unit} {A : ℕ → Ω → α}
    {R : ℕ → Ω → ℝ} (t : ℕ) (c : α) (q μ : ℝ) (ω' : Ω × (ℕ → α → ℝ)) :
    HY.pseudoLogMean 0 (history O A R t ω'.1) t c q μ =
      (∑ i ∈ range (pullCount A c t ω'.1),
        Real.log (1 - q * (rewardByCount A R c (i + 1) ω' - μ))) / pullCount A c t ω'.1 := by
  unfold HY.pseudoLogMean
  rw [HY.sum_ind_mul_history le_rfl c (fun x ↦ Real.log (1 - q * (x - μ))),
    HY.count_history le_rfl, zero_mul, add_zero, add_zero]
  congr 1
  have h1 := sum_comp_rewardByCount_eq (A := A) (R := R) (fun x ↦ Real.log (1 - q * (x - μ))) c t
    ω'
  rw [← h1, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [add_comm]

omit [MeasurableSpace α] in
/-- [INC-P000, Lemma `lem:grid`, the evidence on the stack] On a run, if
`N_c(s) 𝒦_inf(ν̂_c(s), r) ≥ z` with `z > 0` and `r < 1`, then `N_c(s) ≥ 1` and some
`λ ∈ [0, 1/(1-r))` has `∑_(i < N_c(s)) log (1 - λ (X_(c,i) - r)) ≥ z - 1` on the stack of `c`:
otherwise every term of the dual supremum is below `(z - 1) / N_c(s)`. -/
private lemma exists_le_sum_log_of_le_mul_pseudoKinf {Ω : Type*} {O : ℕ → Ω → Unit}
    {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ} {s : ℕ} {c : α} {r z : ℝ} (hr : r < 1) (hz : 0 < z)
    (ω' : Ω × (ℕ → α → ℝ))
    (hzK : ENNReal.ofReal z ≤
      (pullCount A c s ω'.1 : ℝ≥0∞) * HY.pseudoKinf 0 (history O A R s ω'.1) s c r) :
    1 ≤ pullCount A c s ω'.1 ∧ ∃ lam, 0 ≤ lam ∧ lam * (1 - r) < 1 ∧
      z - 1 ≤ ∑ i ∈ range (pullCount A c s ω'.1),
        Real.log (1 - lam * (rewardByCount A R c (i + 1) ω' - r)) := by
  set n := pullCount A c s ω'.1 with hn
  -- `n ≥ 1`, since otherwise the right side is `0`
  have hn1 : 1 ≤ n := by
    by_contra h0
    rw [show n = 0 by omega, Nat.cast_zero, zero_mul] at hzK
    exact (ENNReal.ofReal_pos.mpr hz).ne' (le_antisymm hzK bot_le)
  refine ⟨hn1, ?_⟩
  by_contra hno'
  have hno : ∀ lam, 0 ≤ lam → lam * (1 - r) < 1 →
      ∑ i ∈ range n, Real.log (1 - lam * (rewardByCount A R c (i + 1) ω' - r)) < z - 1 :=
    fun lam h0 h1 ↦ not_le.mp fun hle ↦ hno' ⟨lam, h0, h1, hle⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  -- every term of the dual supremum is below `(z - 1) / n`
  have hsup : HY.pseudoKinf 0 (history O A R s ω'.1) s c r ≤ ENNReal.ofReal ((z - 1) / n) := by
    rw [HY.pseudoKinf, ite_eq_left hr]
    refine iSup_le fun q ↦ ?_
    split_ifs with hq
    · refine ENNReal.ofReal_le_ofReal ?_
      rw [HY.pseudoLogMean_zero_history_eq, ← hn, div_le_div_iff_of_pos_right hnpos]
      exact (hno q hq.1 hq.2).le
    · exact bot_le
  have hmul : (n : ℝ≥0∞) * HY.pseudoKinf 0 (history O A R s ω'.1) s c r ≤
      (n : ℝ≥0∞) * ENNReal.ofReal ((z - 1) / n) := by gcongr
  have h1 : (n : ℝ≥0∞) * HY.pseudoKinf 0 (history O A R s ω'.1) s c r ≤
      ENNReal.ofReal (z - 1) := by
    refine hmul.trans_eq ?_
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      mul_div_cancel₀ _ hnpos.ne']
  have h2 : ENNReal.ofReal (z - 1) < ENNReal.ofReal z :=
    (ENNReal.ofReal_lt_ofReal_iff hz).mpr (by linarith)
  exact (lt_irrefl _) ((hzK.trans h1).trans_lt h2)

/-- An event of the runs has the probability of its product with all the reward stacks (or with
any probability measure). -/
private lemma measure_eq_prod_univ {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (P : Measure Ω) (Q : Measure β) [IsProbabilityMeasure Q] (E : Set Ω) :
    P E = (P.prod Q) (E ×ˢ Set.univ) := by
  rw [Measure.prod_prod, measure_univ, mul_one]

/-- The rate `ρ' = ε'² / (2 (κ(μ) - log (1 - e^(-ε'/4)))²)` of Lemmas `lem:lowerdev` and
`lem:upperdev` is positive for `μ ∈ [0, 1)` and `ε' > 0`, since `κ(μ) ≥ 0 > log (1 - e^(-ε'/4))`. -/
lemma deviation_rate_pos {μ ε' : ℝ} (hμ0 : 0 ≤ μ) (hμ : μ < 1) (hε' : 0 < ε') :
    0 < ε' ^ 2 / (2 * (Real.log (1 / (1 - μ)) - Real.log (1 - Real.exp (-(ε' / 4)))) ^ 2) := by
  have hden : 0 < Real.log (1 / (1 - μ)) - Real.log (1 - Real.exp (-(ε' / 4))) := by
    have h1μ : 0 < 1 - μ := by linarith
    have hκ : 0 ≤ Real.log (1 / (1 - μ)) := Real.log_nonneg (by rw [le_div_iff₀ h1μ]; linarith)
    have he : Real.exp (-(ε' / 4)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have he0 : 0 < 1 - Real.exp (-(ε' / 4)) := by linarith
    have : Real.log (1 - Real.exp (-(ε' / 4))) < 0 :=
      Real.log_neg he0 (by linarith [Real.exp_pos (-(ε' / 4))])
    linarith
  positivity

/-- The geometric tail of the union bounds of Lemma `lem:probasA`(c): if the events `H k` have
`P (H k) ≤ C e^(-ρ (⌈u⌉ + k))` with `C ≥ 0` and `ρ > 0`, then
`P (⋃ k, H k) ≤ C e^(-ρ u) / (1 - e^(-ρ))`. -/
private lemma measure_iUnion_le_geometric {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {H : ℕ → Set Ω} {C ρ u : ℝ} (hC : 0 ≤ C) (hρ : 0 < ρ)
    (hH : ∀ k : ℕ, P (H k) ≤ ENNReal.ofReal (C * Real.exp (-(ρ * ((⌈u⌉₊ + k : ℕ) : ℝ))))) :
    P (⋃ k, H k) ≤ ENNReal.ofReal (C * Real.exp (-(ρ * u)) / (1 - Real.exp (-ρ))) := by
  set q := Real.exp (-ρ) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  -- the bounds are the terms `C q^⌈u⌉ q^k` of a geometric series
  have hterm : ∀ k : ℕ, P (H k) ≤ ENNReal.ofReal (C * q ^ ⌈u⌉₊ * q ^ k) := fun k ↦ by
    refine (hH k).trans_eq ?_
    rw [mul_assoc, ← pow_add, hq, ← Real.exp_nat_mul]
    congr 3
    push_cast
    ring
  have hsum : Summable fun k : ℕ ↦ C * q ^ ⌈u⌉₊ * q ^ k :=
    (summable_geometric_of_lt_one hq0.le hq1).mul_left _
  refine (measure_iUnion_le _).trans ((tsum_le_tsum hterm).trans ?_)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k ↦ by positivity) hsum, tsum_mul_left,
    tsum_geometric_of_lt_one hq0.le hq1]
  refine ENNReal.ofReal_le_ofReal ?_
  -- `q^⌈u⌉ ≤ e^(-ρ u)`
  have hqN : q ^ ⌈u⌉₊ ≤ Real.exp (-(ρ * u)) := by
    rw [hq, ← Real.exp_nat_mul, Real.exp_le_exp]
    have : u ≤ ⌈u⌉₊ := Nat.le_ceil u
    nlinarith
  rw [div_eq_mul_inv]
  have := inv_pos.mpr (show 0 < 1 - q by linarith)
  gcongr

variable [Fintype α] [MeasurableSingletonClass α]

/-- [INC-P000, Lemma `lem:controlC`(a), for the trace of `𝒟_j` on the run] For every learner on an
instance `ν` of `𝒫`, every set `T` of cutoffs, `u > 0` and `ε > 0`, the probability that some arm
`c` and some cutoff `s ∈ T` have `N_c(s) ≥ u` and `|m̂_c(s) - m_c| > ε` is at most
`K · 2 e^(-2ε² u) / (1 - e^(-2ε²))`: on the product with the reward stacks, such an arm has
`|(∑_(i < n) X_(c,i)) / n - m_c| > ε` for some `n ≥ u`, the paper's event `𝒟_j` (with
`u = u_j`, `2ε² u_j = (1 + η₀) L_j`), and Lemma `lem:hoeffding`(b) bounds it for each arm. -/
lemma measure_exists_mem_le_pullCount_abs_sub_gt_le {alg : Algorithm Unit α ℝ}
    {ν : Kernel α ℝ} [IsMarkovKernel ν] (hν : ν ∈ unitBandits α) (T : Set ℕ) {u : ℝ}
    (hu : 0 < u) {ε : ℝ} (hε : 0 < ε) :
    trajMeasure alg (Environment.bandit ν) {ω | ∃ c, ∃ s ∈ T, u ≤ pullCount IT.action c s ω ∧
      ε < |HY.pseudoMean 0 (history IT.obs IT.action IT.feedback s ω) s c - ∫ y, id y ∂(ν c)|} ≤
    Fintype.card α * ENNReal.ofReal (2 * Real.exp (-(2 * ε ^ 2 * u)) /
      (1 - Real.exp (-(2 * ε ^ 2)))) := by
  set P := trajMeasure alg (Environment.bandit ν) with hP
  have hseq := IT.isAlgEnvSeq_trajMeasure alg (Environment.bandit ν)
  set E := {ω | ∃ c, ∃ s ∈ T, u ≤ pullCount IT.action c s ω ∧
    ε < |HY.pseudoMean 0 (history IT.obs IT.action IT.feedback s ω) s c - ∫ y, id y ∂(ν c)|}
  set Z : α → ℕ → (ℕ → Round Unit α ℝ) × (ℕ → α → ℝ) → ℝ :=
    fun c i ω' ↦ rewardByCount IT.action IT.feedback c (i + 1) ω' with hZ
  set F : α → Set ((ℕ → Round Unit α ℝ) × (ℕ → α → ℝ)) := fun c ↦
    {ω' | ∃ n : ℕ, u ≤ n ∧ ε < |(∑ i ∈ range n, Z c i ω') / n - ∫ y, id y ∂(ν c)|} with hF
  have hsub : E ×ˢ (Set.univ : Set (ℕ → α → ℝ)) ⊆ ⋃ c, F c := by
    rintro ⟨ω, z⟩ ⟨⟨c, s, -, hcu, hcε⟩, -⟩
    refine Set.mem_iUnion.mpr ⟨c, pullCount IT.action c s ω, hcu, ?_⟩
    have := HY.pseudoMean_zero_history_eq (O := IT.obs) (A := IT.action) (R := IT.feedback) s c
      (ω, z)
    simp only at this
    rw [this] at hcε
    exact hcε
  rw [measure_eq_prod_univ P (streamMeasure ν) E]
  refine (measure_mono hsub).trans ((measure_iUnion_fintype_le _ _).trans ?_)
  refine (Finset.sum_le_sum fun c _ ↦ ?_).trans
    (by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ])
  have hlaw := fun i ↦ hasLaw_rewardByCount_add_one hseq c i
  refine measure_exists_ge_abs_div_sub_gt_le (Z := Z c)
    (iIndepFun_rewardByCount_add_one_action hseq c) (fun i ↦ (hlaw i).aemeasurable)
    (fun i ↦ ?_) (fun i ↦ ?_) hε hu
  · exact ((hlaw i).ae_iff (p := fun y : ℝ ↦ y ∈ Set.Icc (0 : ℝ) 1)
      (measurable_mem.mpr measurableSet_Icc)).mpr (hν.1 c).2
  · simpa using (hlaw i).integral_eq

/-- [INC-P000, Lemma `lem:probasA`(a), for the trace of `𝒜` on the run] For every learner on an
instance `ν` of `𝒫`, every cutoff `t`, every `U ≥ 1` and `ε > 0`, the probability that some arm `c`
with `2 N_c(t) ≥ U` has `|m̂_c(t) - m_c| > ε` is at most `K · 2 e^(-ε² U) / (1 - e^(-2ε²))`:
on the product with the reward stacks, such an arm has `|(∑_(i < n) X_(c,i)) / n - m_c| > ε` for
some `n ≥ U / 2`, and Lemma `lem:hoeffding`(b) bounds this for each arm. -/
lemma measure_exists_wellSampled_abs_sub_gt_le {alg : Algorithm Unit α ℝ} {ν : Kernel α ℝ}
    [IsMarkovKernel ν] (hν : ν ∈ unitBandits α) (t : ℕ) {U : ℕ} (hU : 1 ≤ U) {ε : ℝ}
    (hε : 0 < ε) :
    trajMeasure alg (Environment.bandit ν) {ω | ∃ c, U ≤ 2 * pullCount IT.action c t ω ∧
      ε < |HY.pseudoMean 0 (history IT.obs IT.action IT.feedback t ω) t c - ∫ y, id y ∂(ν c)|} ≤
    Fintype.card α * ENNReal.ofReal (2 * Real.exp (-(ε ^ 2 * U)) /
      (1 - Real.exp (-(2 * ε ^ 2)))) := by
  have hU2 : (0 : ℝ) < U / 2 := by
    have : (1 : ℝ) ≤ U := by exact_mod_cast hU
    linarith
  refine (measure_mono ?_).trans
    ((measure_exists_mem_le_pullCount_abs_sub_gt_le hν {t} hU2 hε).trans_eq ?_)
  · rintro ω ⟨c, hcU, hcε⟩
    refine ⟨c, t, Set.mem_singleton t, ?_, hcε⟩
    have : (U : ℝ) ≤ 2 * pullCount IT.action c t ω := by exact_mod_cast hcU
    linarith
  · rw [show 2 * ε ^ 2 * ((U : ℝ) / 2) = ε ^ 2 * U by ring]

omit [Fintype α] [MeasurableSingletonClass α] [MeasurableSpace α] in
/-- [INC-P000, Lemma `lem:stacks`, the trace of a low empirical divergence] On a run with rewards
in `[0, 1]`, if `N = N_a(s)` and `𝒦_inf(ν̂_a(s), μ) < B` (`w₀ = 0`, `μ ∈ [0, 1)`), then every
`λ ≥ 0` with `λ(1 - μ) < 1` has `∑_(i < N) log (1 - λ (X_(a,i) - μ)) ≤ N B` on the stack of `a`:
the dual formula at `λ` is at most `𝒦_inf(ν̂_a(s), μ)`. -/
lemma sum_log_rewardByCount_le_of_pseudoKinf_lt {μ B l : ℝ} {s : ℕ} {a : α}
    {ω : ℕ → Round Unit α ℝ} (x : ℕ → α → ℝ) (hμ0 : 0 ≤ μ) (hμ : μ < 1)
    (hfb : ∀ n, IT.feedback n ω ∈ Set.Icc (0 : ℝ) 1)
    (hlt : HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback s ω) s a μ < ENNReal.ofReal B)
    (hl0 : 0 ≤ l) (hl1 : l * (1 - μ) < 1) :
    ∑ i ∈ range (pullCount IT.action a s ω),
        Real.log (1 - l * (rewardByCount IT.action IT.feedback a (i + 1) (ω, x) - μ)) ≤
      pullCount IT.action a s ω * B := by
  rcases Nat.eq_zero_or_pos (pullCount IT.action a s ω) with h0 | hs1
  · simp [h0]
  have hfbh : ∀ i, (history IT.obs IT.action IT.feedback s ω i).feedback ≤ 1 :=
    fun i ↦ (hfb i).2
  have h1 := HY.ofReal_pseudoLogMean_le_pseudoKinf (w₀ := 0) (r := s) (c := a) hμ hμ0 hfbh hl0 hl1
  have h2 : HY.pseudoLogMean 0 (history IT.obs IT.action IT.feedback s ω) s a l μ < B := by
    by_contra hge
    exact (lt_irrefl _) ((ENNReal.ofReal_le_ofReal (not_lt.mp hge)).trans_lt (h1.trans_lt hlt))
  have h3 := HY.pseudoLogMean_zero_history_eq (O := IT.obs) (A := IT.action) (R := IT.feedback)
    s a l μ (ω, x)
  simp only at h3
  rw [h3] at h2
  have hNpos : (0 : ℝ) < pullCount IT.action a s ω := by exact_mod_cast hs1
  rw [div_lt_iff₀ hNpos] at h2
  linarith

omit [Fintype α] in
/-- [INC-P000, Lemma `lem:probasA`(c), the event `ℒ`, for its trace on the run] For every learner
on an instance `ν` of `𝒫`, every cutoff `t`, every arm `a`, a level `μ ∈ [0, 1)`, `ε' > 0`,
`λ ∈ [0, 1/(1-μ))` with `A = E_(ν_a)[log (1 - λ (Y - μ))]` (for `λ` `ε'/4`-optimal in the dual
formula, `A - 3ε'/4 ≥ 𝒦_inf(ν_a, μ) - ε'`), and `u > 0`: the probability that
`N_a(t) ≥ u` and `𝒦_inf(ν̂_a(t), μ) < A - 3ε'/4` is at most `e^(-ρ' u) / (1 - e^(-ρ'))`, with
`ρ' = ε'² / (2 (κ(μ) - log (1 - e^(-ε'/4)))²)` (the paper's `C_(ℒ𝒰)`, `r_ε` for this event). On
the stacks, the run's event is in the union over `N ≥ u` of the events of Lemma `lem:lowerdev`,
and the bounds `e^(-ρ' N)` sum to the geometric tail. -/
lemma measure_le_pullCount_pseudoKinf_lt_le [Countable α] {alg : Algorithm Unit α ℝ}
    {ν : Kernel α ℝ}
    [IsMarkovKernel ν] (hν : ν ∈ unitBandits α) (t : ℕ) (a : α) {μ ε' lam u : ℝ} (hμ0 : 0 ≤ μ)
    (hμ : μ < 1) (hε' : 0 < ε') (hlam0 : 0 ≤ lam) (hlam1 : lam * (1 - μ) < 1) (hu : 0 < u) :
    trajMeasure alg (Environment.bandit ν) {ω | u ≤ pullCount IT.action a t ω ∧
      HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback t ω) t a μ <
        ENNReal.ofReal (∫ y, Real.log (1 - lam * (y - μ)) ∂(ν a) - 3 * ε' / 4)} ≤
    ENNReal.ofReal (Real.exp (-(ε' ^ 2 / (2 * (Real.log (1 / (1 - μ)) -
        Real.log (1 - Real.exp (-(ε' / 4)))) ^ 2) * u)) /
      (1 - Real.exp (-(ε' ^ 2 / (2 * (Real.log (1 / (1 - μ)) -
        Real.log (1 - Real.exp (-(ε' / 4)))) ^ 2))))) := by
  set P := trajMeasure alg (Environment.bandit ν) with hP
  have hseq := IT.isAlgEnvSeq_trajMeasure alg (Environment.bandit ν)
  set B := ∫ y, Real.log (1 - lam * (y - μ)) ∂(ν a) - 3 * ε' / 4 with hB
  set ρ := ε' ^ 2 / (2 * (Real.log (1 / (1 - μ)) - Real.log (1 - Real.exp (-(ε' / 4)))) ^ 2)
    with hρ
  set E := {ω | u ≤ pullCount IT.action a t ω ∧
    HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback t ω) t a μ < ENNReal.ofReal B}
  set G := {ω : ℕ → Round Unit α ℝ | ∀ n, IT.feedback n ω ∈ Set.Icc (0 : ℝ) 1}
  have hG : ∀ᵐ ω ∂P, ω ∈ G := ae_feedback_mem_Icc (alg := alg) hν
  -- the stack of `a`
  set Z : ℕ → (ℕ → Round Unit α ℝ) × (ℕ → α → ℝ) → ℝ :=
    fun i ω' ↦ rewardByCount IT.action IT.feedback a (i + 1) ω' with hZ
  set N₀ := ⌈u⌉₊ with hN₀
  have hN₀1 : 1 ≤ N₀ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hu).ne'
  set H : ℕ → Set ((ℕ → Round Unit α ℝ) × (ℕ → α → ℝ)) := fun k ↦
    {ω' | ∀ l, 0 ≤ l → l * (1 - μ) < 1 →
      ∑ i ∈ range (N₀ + k), Real.log (1 - l * (Z i ω' - μ)) ≤ (N₀ + k : ℕ) * B} with hH
  have hsub : (E ∩ G) ×ˢ (Set.univ : Set (ℕ → α → ℝ)) ⊆ ⋃ k, H k := by
    rintro ⟨ω, z⟩ ⟨⟨⟨huN, hlt⟩, hfb⟩, -⟩
    set N := pullCount IT.action a t ω with hN
    have hNN₀ : N₀ ≤ N := Nat.ceil_le.mpr huN
    refine Set.mem_iUnion.mpr ⟨N - N₀, fun l hl0 hl1 ↦ ?_⟩
    rw [show N₀ + (N - N₀) = N by omega]
    exact sum_log_rewardByCount_le_of_pseudoKinf_lt z hμ0 hμ hfb hlt hl0 hl1
  have hE : P E ≤ (P.prod (streamMeasure ν)) ((E ∩ G) ×ˢ Set.univ) := by
    rw [← measure_eq_prod_univ P (streamMeasure ν)]
    exact measure_mono_ae (hG.mono fun ω hω hωE ↦ ⟨hωE, hω⟩)
  refine hE.trans ((measure_mono hsub).trans ?_)
  -- each event of the union, by Lemma `lem:lowerdev`, then the geometric tail
  have hlaw := fun i ↦ hasLaw_rewardByCount_add_one hseq a i
  refine (measure_iUnion_le_geometric (P := P.prod (streamMeasure ν)) (H := H) (C := 1) (ρ := ρ)
    (u := u) zero_le_one (deviation_rate_pos hμ0 hμ hε') fun k ↦ ?_).trans_eq (by rw [one_mul])
  rw [one_mul]
  exact measure_forall_sum_log_le_le (Y := Z) (iIndepFun_rewardByCount_add_one_action hseq a)
    (fun i ↦ measurable_rewardByCount IT.measurable_action IT.measurable_feedback a (i + 1))
    (fun i ↦ (hlaw i).map_eq) (hν.1 a).2 hμ0 hμ hε' hlam0 hlam1 (N := N₀ + k) (by omega)

omit [Fintype α] in
/-- [INC-P000, Lemma `lem:probasA`(c), the event `𝒰`, for its trace on the run] For every learner
on an instance `ν` of `𝒫`, every cutoff `t`, every arm `a`, a level `μ ∈ [0, 1)`, `ε' > 0`, an
upper bound `K⁺` of the dual formula of `𝒦_inf(ν_a, μ)` (`E_(ν_a)[log (1 - λ (Y - μ))] ≤ K⁺` for
every `λ ∈ [0, 1/(1-μ))`) and `u > 0`: the probability that `N_a(t) ≥ u` and
`𝒦_inf(ν̂_a(t), μ) > K⁺ + ε'` is at most `n_g e^(-ρ' u) / (1 - e^(-ρ'))`, with `n_g` and `ρ'` of
Lemma `lem:upperdev`. On the stacks, the run's event is in the union over `N ≥ u` of the events
of Lemma `lem:upperdev` (a rational `λ` of the dual supremum above `K⁺ + ε'`). -/
lemma measure_le_pullCount_lt_pseudoKinf_le [Countable α] {alg : Algorithm Unit α ℝ}
    {ν : Kernel α ℝ} [IsMarkovKernel ν] (hν : ν ∈ unitBandits α) (t : ℕ) (a : α)
    {μ ε' Kp u : ℝ} (hμ0 : 0 ≤ μ) (hμ : μ < 1) (hε' : 0 < ε')
    (hK : ∀ l, 0 ≤ l → l * (1 - μ) < 1 → ∫ y, Real.log (1 - l * (y - μ)) ∂(ν a) ≤ Kp)
    (hu : 0 < u) :
    trajMeasure alg (Environment.bandit ν) {ω | u ≤ pullCount IT.action a t ω ∧
      ENNReal.ofReal (Kp + ε') <
        HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback t ω) t a μ} ≤
    ENNReal.ofReal ((⌈8 / (ε' * (1 - Real.exp (-(ε' / 4))) * (1 - μ))⌉₊ + 1 : ℕ) *
      Real.exp (-(ε' ^ 2 / (2 * (Real.log (1 / (1 - μ)) -
        Real.log (1 - Real.exp (-(ε' / 4)))) ^ 2) * u)) /
      (1 - Real.exp (-(ε' ^ 2 / (2 * (Real.log (1 / (1 - μ)) -
        Real.log (1 - Real.exp (-(ε' / 4)))) ^ 2))))) := by
  set P := trajMeasure alg (Environment.bandit ν) with hP
  have hseq := IT.isAlgEnvSeq_trajMeasure alg (Environment.bandit ν)
  set ρ := ε' ^ 2 / (2 * (Real.log (1 / (1 - μ)) - Real.log (1 - Real.exp (-(ε' / 4)))) ^ 2)
    with hρ
  set ng : ℕ := ⌈8 / (ε' * (1 - Real.exp (-(ε' / 4))) * (1 - μ))⌉₊ + 1 with hng
  set E := {ω | u ≤ pullCount IT.action a t ω ∧
    ENNReal.ofReal (Kp + ε') < HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback t ω) t a μ}
  -- the stack of `a`
  set Z : ℕ → (ℕ → Round Unit α ℝ) × (ℕ → α → ℝ) → ℝ :=
    fun i ω' ↦ rewardByCount IT.action IT.feedback a (i + 1) ω' with hZ
  set N₀ := ⌈u⌉₊ with hN₀
  have hN₀1 : 1 ≤ N₀ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hu).ne'
  set H : ℕ → Set ((ℕ → Round Unit α ℝ) × (ℕ → α → ℝ)) := fun k ↦
    {ω' | ∃ l, 0 ≤ l ∧ l * (1 - μ) < 1 ∧
      (N₀ + k : ℕ) * (Kp + 7 * ε' / 8) ≤ ∑ i ∈ range (N₀ + k), Real.log (1 - l * (Z i ω' - μ))}
    with hH
  have hsub : E ×ˢ (Set.univ : Set (ℕ → α → ℝ)) ⊆ ⋃ k, H k := by
    rintro ⟨ω, z⟩ ⟨⟨huN, hlt⟩, -⟩
    set N := pullCount IT.action a t ω with hN
    have hNN₀ : N₀ ≤ N := Nat.ceil_le.mpr huN
    rw [HY.pseudoKinf, ite_eq_left hμ] at hlt
    obtain ⟨q, hq⟩ := lt_iSup_iff.mp hlt
    split_ifs at hq with hcond
    swap
    · exact absurd hq not_lt_zero
    refine Set.mem_iUnion.mpr ⟨N - N₀, q, hcond.1, hcond.2, ?_⟩
    rw [show N₀ + (N - N₀) = N by omega]
    have h2 : Kp + ε' < HY.pseudoLogMean 0 (history IT.obs IT.action IT.feedback t ω) t a q μ := by
      by_contra hge
      exact (lt_irrefl _) (hq.trans_le (ENNReal.ofReal_le_ofReal (not_lt.mp hge)))
    have h3 := HY.pseudoLogMean_zero_history_eq (O := IT.obs) (A := IT.action) (R := IT.feedback)
      t a q μ (ω, z)
    simp only at h3
    rw [h3, ← hN] at h2
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    rw [lt_div_iff₀ hNpos] at h2
    have : (N : ℝ) * (Kp + 7 * ε' / 8) ≤ (Kp + ε') * N := by nlinarith
    linarith
  rw [measure_eq_prod_univ P (streamMeasure ν) E]
  refine (measure_mono hsub).trans ?_
  -- each event of the union, by Lemma `lem:upperdev`, then the geometric tail
  have hlaw := fun i ↦ hasLaw_rewardByCount_add_one hseq a i
  refine measure_iUnion_le_geometric (P := P.prod (streamMeasure ν)) (H := H) (C := ng) (ρ := ρ)
    (u := u) (Nat.cast_nonneg _) (deviation_rate_pos hμ0 hμ hε') fun k ↦ ?_
  exact measure_exists_add_le_sum_log_le (Y := Z) (iIndepFun_rewardByCount_add_one_action hseq a)
    (fun i ↦ measurable_rewardByCount IT.measurable_action IT.measurable_feedback a (i + 1))
    (fun i ↦ (hlaw i).map_eq) (hν.1 a).2 hμ0 hμ hε' hK (n := N₀ + k) (by omega)

omit [Fintype α] in
/-- [INC-P000, Lemma `lem:controlC`(b), for the trace of `𝒱⋆_j` on the run] For every learner on an
instance `ν` of `𝒫`, every set `T` of cutoffs, an arm `a'`, a level `r ∈ [0, 1)` and a gain
`η ≥ 0` with `2 η r ≤ m_(a') - r`, `z > 0` and `U`: the probability that some cutoff `s ∈ T` has
`N_(a')(s) < U` and `N_(a')(s) 𝒦_inf(ν̂_(a')(s), r) ≥ z` is at most `C_η U³ e^(-(1+2η) z)`,
`C_η = (4 + 2κ(r)) e^(2(1+2η))`: on the stacks, the trace is in the union over `1 ≤ n < U` of the
events of Lemma `lem:single` (the paper's `𝒱⋆_j`, with `a' = a⋆`, `r = m₂ + ε`, `η = η₀`,
`U = u_j`, `z = (1 - 4δ) L_j`). -/
lemma measure_exists_mem_lt_mul_pseudoKinf_le [Countable α] {alg : Algorithm Unit α ℝ}
    {ν : Kernel α ℝ} [IsMarkovKernel ν] (hν : ν ∈ unitBandits α) (T : Set ℕ) (a' : α)
    {r η z : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (hη : 0 ≤ η)
    (hηr : 2 * η * r ≤ (∫ y, id y ∂(ν a')) - r) (hz : 0 < z) (U : ℕ) :
    trajMeasure alg (Environment.bandit ν) {ω | ∃ s ∈ T, pullCount IT.action a' s ω < U ∧
      ENNReal.ofReal z ≤ (pullCount IT.action a' s ω : ℝ≥0∞) *
        HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback s ω) s a' r} ≤
    ENNReal.ofReal ((4 + 2 * Real.log (1 / (1 - r))) * Real.exp (2 * (1 + 2 * η)) * U ^ 3 *
      Real.exp (-(1 + 2 * η) * z)) := by
  set P := trajMeasure alg (Environment.bandit ν) with hP
  have hseq := IT.isAlgEnvSeq_trajMeasure alg (Environment.bandit ν)
  set C := (4 + 2 * Real.log (1 / (1 - r))) * Real.exp (2 * (1 + 2 * η)) with hC
  set E := {ω | ∃ s ∈ T, pullCount IT.action a' s ω < U ∧
    ENNReal.ofReal z ≤ (pullCount IT.action a' s ω : ℝ≥0∞) *
      HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback s ω) s a' r}
  set Z : ℕ → (ℕ → Round Unit α ℝ) × (ℕ → α → ℝ) → ℝ :=
    fun i ω' ↦ rewardByCount IT.action IT.feedback a' (i + 1) ω' with hZ
  set H : ℕ → Set ((ℕ → Round Unit α ℝ) × (ℕ → α → ℝ)) := fun n ↦
    {ω' | ∃ lam, 0 ≤ lam ∧ lam * (1 - r) < 1 ∧
      z - 1 ≤ ∑ i ∈ range n, Real.log (1 - lam * (Z i ω' - r))} with hH
  have hsub : E ×ˢ (Set.univ : Set (ℕ → α → ℝ)) ⊆ ⋃ n ∈ Finset.Ico 1 U, H n := by
    rintro ⟨ω, x⟩ ⟨⟨s, -, hU, hzK⟩, -⟩
    -- the evidence at `s`: `N_(a')(s) ≥ 1`, and a `λ` of the dual formula above `z - 1`
    obtain ⟨hn1, hev⟩ := exists_le_sum_log_of_le_mul_pseudoKinf (O := IT.obs) (A := IT.action)
      (R := IT.feedback) hr hz (ω, x) hzK
    simp only at hn1 hev
    exact Set.mem_iUnion₂.mpr ⟨_, Finset.mem_Ico.mpr ⟨hn1, hU⟩, hev⟩
  rw [measure_eq_prod_univ P (streamMeasure ν) E]
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  have hlaw := fun i ↦ hasLaw_rewardByCount_add_one hseq a' i
  have hterm : ∀ n ∈ Finset.Ico 1 U, (P.prod (streamMeasure ν)) (H n) ≤
      ENNReal.ofReal (C * n ^ 2 * Real.exp (-(1 + 2 * η) * z)) := by
    intro n hn
    refine measure_exists_le_sum_log_le' (Y := Z) (iIndepFun_rewardByCount_add_one_action hseq a')
      (fun i ↦ measurable_rewardByCount IT.measurable_action IT.measurable_feedback a' (i + 1))
      (fun i ↦ ?_) (fun i ↦ ?_) hr0 hr hη hηr (Finset.mem_Ico.mp hn).1 z
    · exact ((hlaw i).ae_iff (p := fun y : ℝ ↦ y ∈ Set.Icc (0 : ℝ) 1)
        (measurable_mem.mpr measurableSet_Icc)).mpr (hν.1 a').2
    · simpa using (hlaw i).integral_eq
  refine (Finset.sum_le_sum hterm).trans ?_
  have hC0 : 0 ≤ C := by
    have h1r : 0 < 1 - r := by linarith
    have : 0 ≤ Real.log (1 / (1 - r)) := Real.log_nonneg (by rw [le_div_iff₀ h1r]; linarith)
    positivity
  rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ ↦ by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hsq : ∀ n ∈ Finset.Ico 1 U, C * (n : ℝ) ^ 2 * Real.exp (-(1 + 2 * η) * z) ≤
      C * (U : ℝ) ^ 2 * Real.exp (-(1 + 2 * η) * z) := by
    intro n hn
    have : (n : ℝ) ≤ U := by exact_mod_cast (Finset.mem_Ico.mp hn).2.le
    gcongr
  refine (Finset.sum_le_sum hsq).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ico]
  have hU1 : ((U - 1 : ℕ) : ℝ) ≤ U := by exact_mod_cast Nat.sub_le U 1
  have : 0 ≤ C * (U : ℝ) ^ 2 * Real.exp (-(1 + 2 * η) * z) := by positivity
  calc ((U - 1 : ℕ) : ℝ) * (C * (U : ℝ) ^ 2 * Real.exp (-(1 + 2 * η) * z))
      ≤ U * (C * (U : ℝ) ^ 2 * Real.exp (-(1 + 2 * η) * z)) :=
        mul_le_mul_of_nonneg_right hU1 this
    _ = C * U ^ 3 * Real.exp (-(1 + 2 * η) * z) := by ring

omit [Fintype α] in
/-- [INC-P000, Lemma `lem:probasA`(b), the event `𝒱`, for its trace on the run] For every learner
on an instance `ν` of `𝒫`, cutoffs `s ≤ t`, an arm `a'` of mean `m`, a level `r ∈ [0, 1)`, a gain
`η ≥ 0` with `2 η r ≤ m - r` (the paper's `r = m₂ + ε`, `a' = a⋆`), `z > 0` and `U`: the
probability that `2 N_(a')(t) < U` and `N_(a')(s) 𝒦_inf(ν̂_(a')(s), r) ≥ z` is at most
`C_η U³ e^(-(1+2η) z)`, `C_η = (4 + 2 κ(r)) e^(2(1+2η))`. On the stacks, the run's event is in
the union over `1 ≤ n < U` of the events of Lemma `lem:single` at the level `z - 1`
(Lemma `lem:grid`), each of probability at most `C_η n² e^(-(1+2η) z)`. -/
lemma measure_lt_mul_pseudoKinf_le [Countable α] {alg : Algorithm Unit α ℝ} {ν : Kernel α ℝ}
    [IsMarkovKernel ν] (hν : ν ∈ unitBandits α) {s t : ℕ} (hst : s ≤ t) (a' : α) {r η z : ℝ}
    (hr0 : 0 ≤ r) (hr : r < 1) (hη : 0 ≤ η) (hηr : 2 * η * r ≤ (∫ y, id y ∂(ν a')) - r)
    (hz : 0 < z) (U : ℕ) :
    trajMeasure alg (Environment.bandit ν) {ω | 2 * pullCount IT.action a' t ω < U ∧
      ENNReal.ofReal z ≤ (pullCount IT.action a' s ω : ℝ≥0∞) *
        HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback s ω) s a' r} ≤
    ENNReal.ofReal ((4 + 2 * Real.log (1 / (1 - r))) * Real.exp (2 * (1 + 2 * η)) * U ^ 3 *
      Real.exp (-(1 + 2 * η) * z)) := by
  refine (measure_mono ?_).trans
    (measure_exists_mem_lt_mul_pseudoKinf_le hν {s} a' hr0 hr hη hηr hz U)
  rintro ω ⟨hU, hzK⟩
  exact ⟨s, Set.mem_singleton s, lt_of_le_of_lt ((pullCount_mono _ hst _).trans
    (Nat.le_mul_of_pos_left _ two_pos)) hU, hzK⟩

omit [Fintype α] in
/-- [INC-P000, Lemma `lem:controlC`(c), for the trace of `𝒱_(a,j)` on the run] For every learner on
an instance `ν` of `𝒫`, every set `T` of cutoffs, a cutoff `t`, an arm `c`, a level `r ∈ [0, 1)`, a
mean level `q`, a tilt `θ ≥ 0` and a gain `η ≥ 0` with the moment conditions of Lemma `lem:pair`
for `ν_c` (`e^(2ηκ(r)) E_(ν_c)[e^(θ(Y - q))] ≤ 1` and
`e^(2ηκ(r)) E_(ν_c)[(1 - Y) e^(θ(Y - q))] ≤ 1 - r`; the paper's `r = m⋆ + ε`, `q = m⋆ - 3ε`,
`θ = θ_c`, `η = η₀`, Lemma `lem:constC`(c)), `z > 0` and `U`: the probability that `N_c(t) < U`,
`m̂_c(t) ≥ q` and some cutoff `s ∈ T`, `s ≤ t`, has `N_c(s) 𝒦_inf(ν̂_c(s), r) ≥ z` is at most
`C_η U⁴ e^(-(1+2η) z)`, `C_η = (4 + 2κ(r)) e^(2(1+2η))`: the union over `1 ≤ n ≤ n' < U` of the
events of Lemma `lem:pair` (with `n = N_c(s)`, `n' = N_c(t)`; the paper's `U = u_j`,
`z = (1 - 4δ) L_j`, `t = t_(j-1)`). -/
lemma measure_exists_mem_lt_mul_pseudoKinf_and_le_le [Countable α] {alg : Algorithm Unit α ℝ}
    {ν : Kernel α ℝ} [IsMarkovKernel ν] (hν : ν ∈ unitBandits α) (T : Set ℕ) (t : ℕ) (c : α)
    {r q θ η z : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (hθ : 0 ≤ θ) (hη : 0 ≤ η)
    (hΦ : Real.exp (2 * η * Real.log (1 / (1 - r))) * ∫ y, Real.exp (θ * (y - q)) ∂(ν c) ≤ 1)
    (hΨ : Real.exp (2 * η * Real.log (1 / (1 - r))) *
      ∫ y, (1 - y) * Real.exp (θ * (y - q)) ∂(ν c) ≤ 1 - r)
    (hz : 0 < z) (U : ℕ) :
    trajMeasure alg (Environment.bandit ν) {ω | pullCount IT.action c t ω < U ∧
      (∃ s ∈ T, s ≤ t ∧ ENNReal.ofReal z ≤ (pullCount IT.action c s ω : ℝ≥0∞) *
        HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback s ω) s c r) ∧
      q ≤ HY.pseudoMean 0 (history IT.obs IT.action IT.feedback t ω) t c} ≤
    ENNReal.ofReal ((4 + 2 * Real.log (1 / (1 - r))) * Real.exp (2 * (1 + 2 * η)) * U ^ 4 *
      Real.exp (-(1 + 2 * η) * z)) := by
  set P := trajMeasure alg (Environment.bandit ν) with hP
  have hseq := IT.isAlgEnvSeq_trajMeasure alg (Environment.bandit ν)
  set C := (4 + 2 * Real.log (1 / (1 - r))) * Real.exp (2 * (1 + 2 * η)) with hC
  set E := {ω | pullCount IT.action c t ω < U ∧
    (∃ s ∈ T, s ≤ t ∧ ENNReal.ofReal z ≤ (pullCount IT.action c s ω : ℝ≥0∞) *
      HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback s ω) s c r) ∧
    q ≤ HY.pseudoMean 0 (history IT.obs IT.action IT.feedback t ω) t c}
  set Z : ℕ → (ℕ → Round Unit α ℝ) × (ℕ → α → ℝ) → ℝ :=
    fun i ω' ↦ rewardByCount IT.action IT.feedback c (i + 1) ω' with hZ
  set H : ℕ × ℕ → Set ((ℕ → Round Unit α ℝ) × (ℕ → α → ℝ)) := fun p ↦
    {ω' | (∃ lam, 0 ≤ lam ∧ lam * (1 - r) < 1 ∧
      z - 1 ≤ ∑ i ∈ range p.1, Real.log (1 - lam * (Z i ω' - r))) ∧
      p.2 * q ≤ ∑ i ∈ range p.2, Z i ω'} with hH
  set S := (Finset.Ico 1 U ×ˢ Finset.Ico 1 U).filter fun p : ℕ × ℕ ↦ p.1 ≤ p.2 with hS
  have hsub : E ×ˢ (Set.univ : Set (ℕ → α → ℝ)) ⊆ ⋃ p ∈ S, H p := by
    rintro ⟨ω, x⟩ ⟨⟨hU, ⟨s, -, hst, hzK⟩, hq⟩, -⟩
    -- the evidence at `s`, as in `measure_exists_mem_lt_mul_pseudoKinf_le`
    obtain ⟨hn1, hev⟩ := exists_le_sum_log_of_le_mul_pseudoKinf (O := IT.obs) (A := IT.action)
      (R := IT.feedback) hr hz (ω, x) hzK
    simp only at hn1 hev
    set n := pullCount IT.action c s ω with hn
    set n' := pullCount IT.action c t ω with hn'
    have hns : n ≤ n' := pullCount_mono _ hst _
    have hn'U : n' < U := hU
    refine Set.mem_iUnion₂.mpr ⟨(n, n'), ?_, hev, ?_⟩
    · simp only [hS, Finset.mem_filter, Finset.mem_product, Finset.mem_Ico]
      omega
    · -- the mean at `t`
      have h3 := HY.pseudoMean_zero_history_eq (O := IT.obs) (A := IT.action) (R := IT.feedback)
        t c (ω, x)
      simp only at h3
      rw [h3, ← hn'] at hq
      have hn'pos : (0 : ℝ) < n' := by exact_mod_cast (show 0 < n' by omega)
      rw [le_div_iff₀ hn'pos] at hq
      simp only
      linarith
  rw [measure_eq_prod_univ P (streamMeasure ν) E]
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  have hlaw := fun i ↦ hasLaw_rewardByCount_add_one hseq c i
  have hterm : ∀ p ∈ S, (P.prod (streamMeasure ν)) (H p) ≤
      ENNReal.ofReal (C * (U : ℝ) ^ 2 * Real.exp (-(1 + 2 * η) * z)) := by
    intro p hp
    simp only [hS, Finset.mem_filter, Finset.mem_product, Finset.mem_Ico] at hp
    refine (measure_exists_le_sum_log_le_and_le_sum (Y := Z)
      (iIndepFun_rewardByCount_add_one_action hseq c)
      (fun i ↦ measurable_rewardByCount IT.measurable_action IT.measurable_feedback c (i + 1))
      (fun i ↦ ((hlaw i).ae_iff (p := fun y : ℝ ↦ y ∈ Set.Icc (0 : ℝ) 1)
        (measurable_mem.mpr measurableSet_Icc)).mpr (hν.1 c).2)
      hr0 hr hθ hη (fun i ↦ ?_) (fun i ↦ ?_) hp.1.1.1 hp.2 z).trans (ENNReal.ofReal_le_ofReal ?_)
    · have h := (hlaw i).integral_comp (f := fun y ↦ Real.exp (θ * (y - q))) (by fun_prop)
      refine le_of_eq_of_le ?_ hΦ
      congr 1
    · have h := (hlaw i).integral_comp (f := fun y ↦ (1 - y) * Real.exp (θ * (y - q)))
        (by fun_prop)
      refine le_of_eq_of_le ?_ hΨ
      congr 1
    · have hg := dualGridSize_le hp.1.1.1 hr0 hr
      have hpU : (p.1 : ℝ) ≤ U := by exact_mod_cast hp.1.1.2.le
      have hp0 : (0 : ℝ) ≤ p.1 := Nat.cast_nonneg _
      have he : 0 ≤ Real.exp (2 * (1 + 2 * η)) * Real.exp (-(1 + 2 * η) * z) := by positivity
      calc ((⌈2 * p.1 * Real.log (p.1 / (1 - r))⌉₊ + 1 : ℕ) : ℝ) * Real.exp (2 * (1 + 2 * η)) *
            Real.exp (-(1 + 2 * η) * z)
          = ((⌈2 * p.1 * Real.log (p.1 / (1 - r))⌉₊ + 1 : ℕ) : ℝ) *
            (Real.exp (2 * (1 + 2 * η)) * Real.exp (-(1 + 2 * η) * z)) := by ring
        _ ≤ (4 + 2 * Real.log (1 / (1 - r))) * (p.1 : ℝ) ^ 2 *
            (Real.exp (2 * (1 + 2 * η)) * Real.exp (-(1 + 2 * η) * z)) :=
          mul_le_mul_of_nonneg_right hg he
        _ ≤ (4 + 2 * Real.log (1 / (1 - r))) * (U : ℝ) ^ 2 *
            (Real.exp (2 * (1 + 2 * η)) * Real.exp (-(1 + 2 * η) * z)) := by
          have h1r : 0 < 1 - r := by linarith
          have : 0 ≤ 4 + 2 * Real.log (1 / (1 - r)) := by
            have := Real.log_nonneg (show (1 : ℝ) ≤ 1 / (1 - r) by rw [le_div_iff₀ h1r]; linarith)
            linarith
          gcongr
        _ = C * (U : ℝ) ^ 2 * Real.exp (-(1 + 2 * η) * z) := by rw [hC]; ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hC0 : 0 ≤ C := by
    have h1r : 0 < 1 - r := by linarith
    have : 0 ≤ Real.log (1 / (1 - r)) := Real.log_nonneg (by rw [le_div_iff₀ h1r]; linarith)
    positivity
  have hcard : (S.card : ℝ) ≤ (U : ℝ) ^ 2 := by
    have : S.card ≤ U * U := by
      refine (Finset.card_filter_le _ _).trans ?_
      rw [Finset.card_product, Nat.card_Ico]
      exact Nat.mul_le_mul (Nat.sub_le U 1) (Nat.sub_le U 1)
    have : (S.card : ℝ) ≤ (U * U : ℕ) := by exact_mod_cast this
    push_cast at this
    nlinarith
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have : 0 ≤ C * (U : ℝ) ^ 2 * Real.exp (-(1 + 2 * η) * z) := by positivity
  calc (S.card : ℝ) * (C * (U : ℝ) ^ 2 * Real.exp (-(1 + 2 * η) * z))
      ≤ (U : ℝ) ^ 2 * (C * (U : ℝ) ^ 2 * Real.exp (-(1 + 2 * η) * z)) :=
        mul_le_mul_of_nonneg_right hcard this
    _ = C * U ^ 4 * Real.exp (-(1 + 2 * η) * z) := by ring

omit [Fintype α] in
/-- [INC-P000, Lemma `lem:probasA`(b), the event `Π`, for its trace on the run, one arm] For every
learner on an instance `ν` of `𝒫`, cutoffs `s ≤ t`, an arm `c`, a level `r ∈ [0, 1)`, a mean level
`q`, a tilt `θ ≥ 0` and a gain `η ≥ 0` with the moment conditions of Lemma `lem:pair` for `ν_c`
(`e^(2ηκ(r)) E_(ν_c)[e^(θ(Y - q))] ≤ 1` and `e^(2ηκ(r)) E_(ν_c)[(1 - Y) e^(θ(Y - q))] ≤ 1 - r`;
the paper's `r = m⋆ + ε`, `q = m⋆ - 3ε`, from Lemmas `lem:theta` and `lem:constA`(c)), `z > 0`
and `U`: the probability that `2 N_c(t) < U`, `N_c(s) 𝒦_inf(ν̂_c(s), r) ≥ z` and
`m̂_c(t) ≥ q` is at most `C_η U⁴ e^(-(1+2η) z)`, `C_η = (4 + 2 κ(r)) e^(2(1+2η))`: the union over
`1 ≤ n ≤ n' < U` of the events of Lemma `lem:pair`. -/
lemma measure_lt_mul_pseudoKinf_and_le_le [Countable α] {alg : Algorithm Unit α ℝ}
    {ν : Kernel α ℝ} [IsMarkovKernel ν] (hν : ν ∈ unitBandits α) {s t : ℕ} (hst : s ≤ t) (c : α)
    {r q θ η z : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (hθ : 0 ≤ θ) (hη : 0 ≤ η)
    (hΦ : Real.exp (2 * η * Real.log (1 / (1 - r))) * ∫ y, Real.exp (θ * (y - q)) ∂(ν c) ≤ 1)
    (hΨ : Real.exp (2 * η * Real.log (1 / (1 - r))) *
      ∫ y, (1 - y) * Real.exp (θ * (y - q)) ∂(ν c) ≤ 1 - r)
    (hz : 0 < z) (U : ℕ) :
    trajMeasure alg (Environment.bandit ν) {ω | 2 * pullCount IT.action c t ω < U ∧
      ENNReal.ofReal z ≤ (pullCount IT.action c s ω : ℝ≥0∞) *
        HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback s ω) s c r ∧
      q ≤ HY.pseudoMean 0 (history IT.obs IT.action IT.feedback t ω) t c} ≤
    ENNReal.ofReal ((4 + 2 * Real.log (1 / (1 - r))) * Real.exp (2 * (1 + 2 * η)) * U ^ 4 *
      Real.exp (-(1 + 2 * η) * z)) := by
  refine (measure_mono ?_).trans
    (measure_exists_mem_lt_mul_pseudoKinf_and_le_le hν {s} t c hr0 hr hθ hη hΦ hΨ hz U)
  rintro ω ⟨hU, hzK, hq⟩
  exact ⟨lt_of_le_of_lt (Nat.le_mul_of_pos_left _ two_pos) hU, ⟨s, Set.mem_singleton s, hst, hzK⟩,
    hq⟩

omit [DecidableEq α] [MeasurableSingletonClass α] [Fintype α] in
/-- [INC-P000, Lemma `lem:constA`(a)] For an instance of means `m_c` with largest mean
`m⋆ = sup_b m_b`, `Δ` at most every positive gap and `m₂` with `m₂ ≤ m⋆ - Δ`, every
`ε ∈ (0, min(Δ/5, (1 - m⋆)/2)]` has `m⋆ + ε < 1`, `m_c + ε < m⋆ - 3ε` for every sub-optimal `c`,
and `m₂ + ε < m⋆ - 2ε`. (The paper's `ε̄` is also below the `ε_(θ,c)`; it takes `m₂` the second
largest mean and `Δ` the smallest positive gap; `m⋆ < 1` follows from `0 < ε ≤ (1 - m⋆)/2`.) -/
lemma iSup_integral_add_lt_one_and_integral_add_lt_sub (ν : Kernel α ℝ) {Δ m₂ ε : ℝ}
    (hΔ : ∀ c, (∫ y, id y ∂(ν c)) < ⨆ b, ∫ y, id y ∂(ν b) →
      Δ ≤ (⨆ b, ∫ y, id y ∂(ν b)) - ∫ y, id y ∂(ν c))
    (hm₂ : m₂ ≤ (⨆ b, ∫ y, id y ∂(ν b)) - Δ) (hε : 0 < ε) (hεΔ : ε ≤ Δ / 5)
    (hε1 : ε ≤ (1 - ⨆ b, ∫ y, id y ∂(ν b)) / 2) :
    (⨆ b, ∫ y, id y ∂(ν b)) + ε < 1 ∧
      (∀ c, (∫ y, id y ∂(ν c)) < ⨆ b, ∫ y, id y ∂(ν b) →
        (∫ y, id y ∂(ν c)) + ε < (⨆ b, ∫ y, id y ∂(ν b)) - 3 * ε) ∧
      m₂ + ε < (⨆ b, ∫ y, id y ∂(ν b)) - 2 * ε := by
  refine ⟨by linarith, fun c hc ↦ ?_, by linarith⟩
  have := hΔ c hc
  linarith

@[deprecated (since := "2026-11-19")]
alias constA_means := iSup_integral_add_lt_one_and_integral_add_lt_sub

/-- [INC-P000, Lemma `lem:constA`(c), the moment conditions, for one law] For a law `Q` on `[0, 1]`
of mean `m < m⋆ < 1` (the law `ν_c` of a sub-optimal arm), there are a tilt `θ > 0`, a constant
`c_θ > 0` and an accuracy `ε_θ > 0` such that every `ε ≤ ε_θ`, every level `r ≤ m⋆ + ε` and every
gain `η ≥ 0` with `2 η κ(r) ≤ c_θ` satisfy the moment conditions of Lemma `lem:pair` at the mean
level `q = m⋆ - 3ε`: `e^(2ηκ(r)) E_Q[e^(θ(Y - q))] ≤ 1` and
`e^(2ηκ(r)) E_Q[(1 - Y) e^(θ(Y - q))] ≤ 1 - r`. This is Lemma `lem:theta`, with Step 3 of its
proof (`Φ⋆, Ψ⋆ > 0`, the latter since `Q(Y < 1) > 0` as `m < 1`). -/
lemma exists_tilt_moment_le {Q : Measure ℝ} (hQ : Q ∈ unitLaws) {ms : ℝ}
    (hm : ∫ y, id y ∂Q < ms) (hms : ms < 1) :
    ∃ θ c₀ ε₀ : ℝ, 0 < θ ∧ 0 < c₀ ∧ 0 < ε₀ ∧ ∀ ε, ε ≤ ε₀ → ∀ r η : ℝ, r ≤ ms + ε → 0 ≤ η →
      2 * η * Real.log (1 / (1 - r)) ≤ c₀ →
      Real.exp (2 * η * Real.log (1 / (1 - r))) *
          ∫ y, Real.exp (θ * (y - (ms - 3 * ε))) ∂Q ≤ 1 ∧
        Real.exp (2 * η * Real.log (1 / (1 - r))) *
          ∫ y, (1 - y) * Real.exp (θ * (y - (ms - 3 * ε))) ∂Q ≤ 1 - r := by
  have := hQ.1
  have hb : ∀ᵐ y ∂Q, id y ∈ Set.Icc (0 : ℝ) 1 := hQ.2
  obtain ⟨θ, hθ, hΦ1, hΨ1⟩ := exists_tilt (P := Q) (Y := id) measurable_id hb rfl hm hms
  simp only [id] at hΦ1 hΨ1
  -- integrability of the moments (bounded integrands)
  have hint : ∀ q : ℝ, Integrable (fun y ↦ Real.exp (θ * (y - q))) Q := fun q ↦
    Integrable.of_bound (by fun_prop) (Real.exp (θ * (1 - q))) (by
      filter_upwards [hQ.2] with y hy
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [hy.2]) hθ.le))
  have hint' : ∀ q : ℝ, Integrable (fun y ↦ (1 - y) * Real.exp (θ * (y - q))) Q := fun q ↦
    Integrable.of_bound (by fun_prop) (Real.exp (θ * (1 - q))) (by
      filter_upwards [hQ.2] with y hy
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith [hy.2]) (Real.exp_pos _).le)]
      calc (1 - y) * Real.exp (θ * (y - q)) ≤ 1 * Real.exp (θ * (y - q)) :=
            mul_le_mul_of_nonneg_right (by linarith [hy.1]) (Real.exp_pos _).le
        _ ≤ Real.exp (θ * (1 - q)) := by
            rw [one_mul]
            exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [hy.2]) hθ.le))
  have hnn : ∀ q : ℝ, 0 ≤ᵐ[Q] fun y ↦ (1 - y) * Real.exp (θ * (y - q)) := fun q ↦ by
    filter_upwards [hQ.2] with y hy
    exact mul_nonneg (by linarith [hy.2]) (Real.exp_pos _).le
  -- `Φ⋆ > 0` and `Ψ⋆ > 0`
  have hΦ0 : 0 < ∫ y, Real.exp (θ * (y - ms)) ∂Q :=
    integral_exp_pos (hint ms)
  have hΨ0 : 0 < ∫ y, (1 - y) * Real.exp (θ * (y - ms)) ∂Q := by
    refine lt_of_le_of_ne (integral_nonneg_of_ae (hnn ms)) fun h0 ↦ ?_
    have hzero := (integral_eq_zero_iff_of_nonneg_ae (hnn ms) (hint' ms)).mp h0.symm
    have hone : ∀ᵐ y ∂Q, y = 1 := by
      filter_upwards [hzero] with y hy
      have := (mul_eq_zero.mp hy).resolve_right (Real.exp_pos _).ne'
      linarith
    have : ∫ y, id y ∂Q = 1 := by
      rw [integral_congr_ae (hone.mono fun y hy ↦ (by simp [hy] : id y = (fun _ ↦ (1 : ℝ)) y))]
      simp
    linarith
  obtain ⟨hc, hε⟩ := half_mul_min_log_pos_and_min_pos hΦ0 hΦ1 hΨ0 hΨ1 hθ
  refine ⟨θ, _, _, hθ, hc, hε, fun ε hεθ r η hr hη hηc ↦ ?_⟩
  have hsh := exp_mul_integral_exp_le_one_and_le_one_sub (P := Q) (Y := id) hθ hΦ0 hΦ1 hΨ0 hΨ1 hεθ
  simp only [id] at hsh
  have hexp : Real.exp (2 * η * Real.log (1 / (1 - r))) ≤
      Real.exp ((1 / 2) * min (Real.log (1 / ∫ y, Real.exp (θ * (y - ms)) ∂Q))
        (Real.log ((1 - ms) / ∫ y, (1 - y) * Real.exp (θ * (y - ms)) ∂Q))) :=
    Real.exp_le_exp.mpr hηc
  constructor
  · refine le_trans ?_ hsh.1
    exact mul_le_mul_of_nonneg_right hexp (integral_nonneg fun y ↦ (Real.exp_pos _).le)
  · refine le_trans ?_ (hsh.2.trans (by linarith))
    exact mul_le_mul_of_nonneg_right hexp (integral_nonneg_of_ae (hnn _))

omit [DecidableEq α] [MeasurableSingletonClass α] [Fintype α] in
/-- [INC-P000, Definition `def:constA` and Lemma `lem:constA`(c), uniformly over the arms] For an
instance `ν` of `𝒫` on a finite set of arms, there are tilts `θ_c > 0` of the sub-optimal arms, a
constant `c_θ > 0` and an accuracy `ε_θ > 0` such that every sub-optimal `c`, every `ε ≤ ε_θ`,
every level `r ≤ m⋆ + ε` and every gain `η ≥ 0` with `2ηκ(r) ≤ c_θ` satisfy the moment conditions
of Lemma `lem:pair` for `ν_c` at the mean level `m⋆ - 3ε` (the paper's `min_c c_(θ,c)` and
`min_c ε_(θ,c)`). -/
lemma exists_tilt_moment_le_forall [Finite α] [Nonempty α] {ν : Kernel α ℝ}
    (hν : ν ∈ unitBandits α) :
    ∃ θ : α → ℝ, ∃ cθ εθ : ℝ, 0 < cθ ∧ 0 < εθ ∧ ∀ c,
      (∫ y, id y ∂(ν c)) < (⨆ b, ∫ y, id y ∂(ν b)) → 0 < θ c ∧
      ∀ ε, ε ≤ εθ → ∀ r η : ℝ, r ≤ (⨆ b, ∫ y, id y ∂(ν b)) + ε → 0 ≤ η →
        2 * η * Real.log (1 / (1 - r)) ≤ cθ →
        Real.exp (2 * η * Real.log (1 / (1 - r))) *
            ∫ y, Real.exp (θ c * (y - ((⨆ b, ∫ y, id y ∂(ν b)) - 3 * ε))) ∂(ν c) ≤ 1 ∧
          Real.exp (2 * η * Real.log (1 / (1 - r))) *
            ∫ y, (1 - y) * Real.exp (θ c * (y - ((⨆ b, ∫ y, id y ∂(ν b)) - 3 * ε))) ∂(ν c) ≤
              1 - r := by
  classical
  have := Fintype.ofFinite α
  set ms := ⨆ b, ∫ y, id y ∂(ν b) with hms
  have hex : ∀ c, ∃ θ c₀ ε₀ : ℝ, 0 < θ ∧ 0 < c₀ ∧ 0 < ε₀ ∧
      ((∫ y, id y ∂(ν c)) < ms → ∀ ε, ε ≤ ε₀ → ∀ r η : ℝ, r ≤ ms + ε → 0 ≤ η →
        2 * η * Real.log (1 / (1 - r)) ≤ c₀ →
        Real.exp (2 * η * Real.log (1 / (1 - r))) *
            ∫ y, Real.exp (θ * (y - (ms - 3 * ε))) ∂(ν c) ≤ 1 ∧
          Real.exp (2 * η * Real.log (1 / (1 - r))) *
            ∫ y, (1 - y) * Real.exp (θ * (y - (ms - 3 * ε))) ∂(ν c) ≤ 1 - r) := by
    intro c
    by_cases hc : (∫ y, id y ∂(ν c)) < ms
    · obtain ⟨θ, c₀, ε₀, hθ, hc₀, hε₀, h⟩ := exists_tilt_moment_le (hν.1 c) hc hν.2
      exact ⟨θ, c₀, ε₀, hθ, hc₀, hε₀, fun _ ↦ h⟩
    · exact ⟨1, 1, 1, one_pos, one_pos, one_pos, fun h ↦ absurd h hc⟩
  choose θ c₀ ε₀ hθ hc₀ hε₀ h using hex
  set cθ := Finset.univ.inf' Finset.univ_nonempty c₀ with hcθ
  set εθ := Finset.univ.inf' Finset.univ_nonempty ε₀ with hεθ
  have hcθ0 : 0 < cθ := (Finset.lt_inf'_iff _).mpr fun c _ ↦ hc₀ c
  have hεθ0 : 0 < εθ := (Finset.lt_inf'_iff _).mpr fun c _ ↦ hε₀ c
  refine ⟨θ, cθ, εθ, hcθ0, hεθ0, fun c hc ↦ ⟨hθ c, fun ε hε r η hr hη hηc ↦ ?_⟩⟩
  have h1 : εθ ≤ ε₀ c := Finset.inf'_le _ (Finset.mem_univ c)
  have h2 : cθ ≤ c₀ c := Finset.inf'_le _ (Finset.mem_univ c)
  exact h c hc ε (hε.trans h1) r η hr hη (hηc.trans h2)

end Incognita.BatchedBandits
