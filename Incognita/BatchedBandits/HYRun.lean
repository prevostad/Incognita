/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.HYImed
public import Incognita.BatchedBandits.WaterLevel
public import Incognita.BatchedBandits.Queue
public import Incognita.BatchedBandits.Instances
public import LeanMachineLearning.SequentialLearning.StationaryEnv
public import LeanMachineLearning.SequentialLearning.IonescuTulceaSpace
public import LeanMachineLearning.SequentialLearning.Deterministic

/-! # The statistics of HY along a run

On a trajectory `(O, A, Y)` (LML's `history O A Y n ω` is the history of the rounds `< n`), the
statistics of HY at a cutoff `r` [INC-P000, Definition `def:hy`, (1)–(3)] read only the rounds
`< r`: for every `n ≥ r` they are those of the history of length `r`. So the statistics frozen at
a batch end `t_ℓ` are constant during batch `ℓ + 1`, as the paper uses throughout
(`def:hy`: "all computed at every end `t_ℓ`"; Definition `def:water`: "`K̃_(j-1)` and `y_(j-1)`
are fixed during the batch").

* `HY.sum_ind_mul_history`: the sums `∑_i 1(i < r, A_i = c) φ(Y_i)` of a history of length
  `n ≥ r` are sums over the rounds `< r`.
* `HY.count_history`: `N_c(r)` of the history is LML's `pullCount A c r`.
* `HY.pseudoMean_history`, `HY.pseudoLogMean_history`, `HY.pseudoKinf_history`,
  `HY.leader_history`, `HY.imedKinf_history`: the statistics at the cutoff `r` of the history of
  length `n ≥ r` are those of the history of length `r`.
* `HY.imedIndex_history`: along a run, the IMED index of the round `n` is
  `N_c(n) K̃(c) + y log N_c(n)` with the divergence `K̃(c)` frozen at `r ≤ n`; so it is
  nondecreasing in `n` (`HY.imedIndex_history_mono`), the hypothesis (mono) of the water-level
  lemma `lem:W`.
* `HY.next_of_imedPhase`, `hyAlg_ae_action_eq`, `hyAlg_ae_imedIndex_action_le`: along almost every
  run, the action is HY's rule applied to the history, and at an IMED round the pulled arm
  minimises the index (the hypothesis (min) of `lem:W`).
* `hyAlg_ae_log_pullCount_le_imedIndex`: Lemma `lem:W`, Step 1 ((W2) at the IMED rounds), along
  almost every run of HY.
* `hyAlg_ae_log_le_imedIndex`: Lemma `lem:W`(ii), Step 2, along almost every run of HY: the
  water level of a batch is at least `log ((s - t_ℓ) / K)`, `s` the end of its IMED phase;
  `hyAlg_ae_one_le_pullCount` (every count at `t_ℓ`, `ℓ ≥ 1`, is at least `1`) and
  `hyAlg_ae_log_le_imedIndex'` (the same without that hypothesis).
* `HY.reference_history`, `HY.testKinf_history`, `HY.threshold_history`, `HY.target_history`,
  `HY.next_of_pacedPhase`, `HY.target_mono_logt`, `HY.target_le`, `hyAlg_ae_paced_rule`,
  `hyAlg_ae_backlog_le`: Lemma `lem:service`(b) along almost every run of HY, given the slow
  arrivals of Step (b2); `HY.two_mul_target_sub_le`, `hyAlg_ae_backlog_le_of_le`: Step (b2) for
  HY's targets, so Lemma `lem:service`(b) under the paper's condition
  `s_ℓ log s_ℓ ≥ 2(K - 1) U_(ℓ+1)`.
* `ae_feedback_mem_Icc`: on an instance of `𝒫`, the rewards of almost every run are in `[0, 1]`.
* `hyAlg_ae_pullCount_le_max`: Lemma `lem:imedround` (its consequence) along almost every run of
  HY on an instance of `𝒫`.
* `hyAlg_ae_W2`: (W2) at every round of a batch that is not activated or has a long IMED phase,
  Lemma `lem:W`(i) along almost every run of HY.
-/

@[expose] public section

open Learning Finset MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace Incognita.BatchedBandits

namespace HY

variable {α Ω : Type*} [Fintype α] [DecidableEq α] {O : ℕ → Ω → Unit} {A : ℕ → Ω → α}
  {Y : ℕ → Ω → ℝ} {ω : Ω}

omit [Fintype α] in
/-- The sums of the statistics of a history of length `n ≥ r`, at the cutoff `r`, are sums over
the rounds `< r` of the trajectory. -/
lemma sum_ind_mul_history {n r : ℕ} (hrn : r ≤ n) (c : α) (φ : ℝ → ℝ) :
    ∑ i, ind (history O A Y n ω) r c i * φ ((history O A Y n ω i).feedback) =
      ∑ i ∈ Finset.range r, if A i ω = c then φ (Y i ω) else 0 := by
  have h1 : ∑ i, ind (history O A Y n ω) r c i * φ ((history O A Y n ω i).feedback) =
      ∑ i ∈ Finset.range n, (if i < r ∧ A i ω = c then 1 else 0) * φ (Y i ω) :=
    Fin.sum_univ_eq_sum_range (fun i ↦ (if i < r ∧ A i ω = c then (1 : ℝ) else 0) * φ (Y i ω)) n
  rw [h1, ← Finset.sum_range_add_sum_Ico _ hrn]
  have h0 : ∑ i ∈ Finset.Ico r n, (if i < r ∧ A i ω = c then (1 : ℝ) else 0) * φ (Y i ω) = 0 :=
    Finset.sum_eq_zero fun i hi ↦ by
      rw [ite_eq_right fun h ↦ absurd h.1 (not_lt.mpr (Finset.mem_Ico.mp hi).1), zero_mul]
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hir : i < r := Finset.mem_range.mp hi
  by_cases hA : A i ω = c
  · rw [ite_eq_left ⟨hir, hA⟩, ite_eq_left hA, one_mul]
  · rw [ite_eq_right fun h ↦ hA h.2, ite_eq_right hA, zero_mul]

omit [Fintype α] in
/-- `sum_ind_mul_history` for the rewards themselves. -/
lemma sum_ind_mul_feedback_history {n r : ℕ} (hrn : r ≤ n) (c : α) :
    ∑ i, ind (history O A Y n ω) r c i * (history O A Y n ω i).feedback =
      ∑ i ∈ Finset.range r, if A i ω = c then Y i ω else 0 :=
  sum_ind_mul_history hrn c id

omit [Fintype α] in
/-- The count `N_c(r)` of a history of length `n ≥ r` is `pullCount A c r`. -/
lemma count_history {n r : ℕ} (hrn : r ≤ n) (c : α) :
    count (history O A Y n ω) r c = pullCount A c r ω := by
  have h1 : count (history O A Y n ω) r c =
      ∑ i ∈ Finset.range n, if i < r ∧ A i ω = c then 1 else 0 :=
    Fin.sum_univ_eq_sum_range (fun i ↦ if i < r ∧ A i ω = c then 1 else 0) n
  rw [h1, ← Finset.sum_range_add_sum_Ico _ hrn, pullCount_eq_sum]
  have h0 : ∑ i ∈ Finset.Ico r n, (if i < r ∧ A i ω = c then 1 else 0) = 0 :=
    Finset.sum_eq_zero fun i hi ↦
      ite_eq_right fun h ↦ absurd h.1 (not_lt.mpr (Finset.mem_Ico.mp hi).1)
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hir : i < r := Finset.mem_range.mp hi
  by_cases hA : A i ω = c
  · rw [ite_eq_left ⟨hir, hA⟩, ite_eq_left hA]
  · rw [ite_eq_right fun h ↦ hA h.2, ite_eq_right hA]

omit [Fintype α] in
lemma count_history_eq {n r : ℕ} (hrn : r ≤ n) (c : α) :
    count (history O A Y n ω) r c = count (history O A Y r ω) r c := by
  rw [count_history hrn, count_history le_rfl]

omit [Fintype α] in
lemma pseudoMean_history {n r : ℕ} (hrn : r ≤ n) (w₀ : ℝ) (c : α) :
    pseudoMean w₀ (history O A Y n ω) r c = pseudoMean w₀ (history O A Y r ω) r c := by
  unfold pseudoMean
  rw [count_history_eq hrn, sum_ind_mul_feedback_history hrn c,
    sum_ind_mul_feedback_history le_rfl c]

omit [Fintype α] in
lemma pseudoLogMean_history {n r : ℕ} (hrn : r ≤ n) (w₀ : ℝ) (c : α) (q μ : ℝ) :
    pseudoLogMean w₀ (history O A Y n ω) r c q μ =
      pseudoLogMean w₀ (history O A Y r ω) r c q μ := by
  unfold pseudoLogMean
  rw [count_history_eq hrn,
    sum_ind_mul_history hrn c (fun x ↦ Real.log (1 - q * (x - μ))),
    sum_ind_mul_history le_rfl c (fun x ↦ Real.log (1 - q * (x - μ)))]

omit [Fintype α] in
lemma pseudoKinf_history {n r : ℕ} (hrn : r ≤ n) (w₀ : ℝ) (c : α) (μ : ℝ) :
    pseudoKinf w₀ (history O A Y n ω) r c μ = pseudoKinf w₀ (history O A Y r ω) r c μ := by
  unfold pseudoKinf
  simp_rw [pseudoLogMean_history hrn, pseudoMean_history hrn]

variable [Nonempty α]

lemma leader_history {n r : ℕ} (hrn : r ≤ n) (w₀ : ℝ) :
    leader w₀ (history O A Y n ω) r = leader w₀ (history O A Y r ω) r := by
  unfold leader
  simp_rw [pseudoMean_history hrn]

lemma imedKinf_history {n r : ℕ} (hrn : r ≤ n) (w₀ : ℝ) (c : α) :
    imedKinf w₀ (history O A Y n ω) r c = imedKinf w₀ (history O A Y r ω) r c := by
  unfold imedKinf
  rw [leader_history hrn, pseudoKinf_history hrn, pseudoMean_history hrn]

omit [Fintype α] [Nonempty α] in
lemma isWellSampled_history {n r : ℕ} (hrn : r ≤ n) (U : ℕ) (c : α) :
    IsWellSampled (history O A Y n ω) r U c ↔ IsWellSampled (history O A Y r ω) r U c := by
  unfold IsWellSampled
  rw [count_history_eq hrn]

lemma reference_history {n r : ℕ} (hrn : r ≤ n) (w₀ : ℝ) (U : ℕ) :
    reference w₀ (history O A Y n ω) r U = reference w₀ (history O A Y r ω) r U := by
  unfold reference
  simp only [IsWellSampled, count_history_eq hrn, pseudoMean_history hrn, leader_history hrn]
  congr
  funext c
  congr

lemma testKinf_history {n r : ℕ} (hrn : r ≤ n) (w₀ : ℝ) (U : ℕ) (c : α) :
    testKinf w₀ (history O A Y n ω) r U c = testKinf w₀ (history O A Y r ω) r U c := by
  unfold testKinf
  rw [reference_history hrn, pseudoKinf_history hrn, pseudoMean_history hrn]

/-- The consistency threshold at the cutoffs `r' ≤ r ≤ n` of the history of length `n` is the
one of the history of length `r`. -/
lemma threshold_history {n r r' : ℕ} (hrn : r ≤ n) (hr'r : r' ≤ r) (w₀ L y' : ℝ) (U U' : ℕ) :
    threshold w₀ L y' (history O A Y n ω) r r' U U' =
      threshold w₀ L y' (history O A Y r ω) r r' U U' := by
  unfold threshold
  have h1 : ∀ c, testKinf w₀ (history O A Y n ω) r' U' c =
      testKinf w₀ (history O A Y r ω) r' U' c := fun c ↦ by
    rw [testKinf_history (hr'r.trans hrn), testKinf_history hr'r]
  have h2 : leader w₀ (history O A Y n ω) r' = leader w₀ (history O A Y r ω) r' := by
    rw [leader_history (hr'r.trans hrn), leader_history hr'r]
  simp only [IsWellSampled, count_history_eq hrn, h1, h2]
  congr
  funext c
  congr

/-- The paced target at the cutoff `r ≤ n` of the history of length `n` is the one of the history
of length `r` (for the same threshold and the same `log t`). -/
lemma target_history {n r : ℕ} (hrn : r ≤ n) (w₀ thr ω' y logt : ℝ) (U Unext : ℕ) (c : α) :
    target w₀ thr ω' y logt (history O A Y n ω) r U Unext c =
      target w₀ thr ω' y logt (history O A Y r ω) r U Unext c := by
  unfold target
  rw [testKinf_history hrn, count_history_eq hrn]

/-- Along a run, the IMED index of the round `n ≥ r` is `N_c(n) K̃(c) + y log N_c(n)`, with the
current count `N_c(n) = pullCount A c n` and the divergence `K̃(c)` frozen at the cutoff `r`. -/
lemma imedIndex_history {n r : ℕ} (hrn : r ≤ n) (w₀ y : ℝ) (c : α) :
    imedIndex w₀ y (history O A Y n ω) r c =
      (((pullCount A c n ω : ℝ≥0∞) * imedKinf w₀ (history O A Y r ω) r c : ℝ≥0∞) : EReal) +
        ((y * Real.log (pullCount A c n ω) : ℝ) : EReal) := by
  unfold imedIndex
  rw [imedKinf_history hrn, ← pullCount_eq_pullCount']

/-- Along a run, the IMED index is nondecreasing in the round, for `y ≥ 0` (the hypothesis (mono)
of the water-level lemma `lem:W`). -/
lemma imedIndex_history_mono {n n' r : ℕ} (hrn : r ≤ n) (hnn' : n ≤ n') (w₀ : ℝ) {y : ℝ}
    (hy : 0 ≤ y) (c : α) :
    imedIndex w₀ y (history O A Y n ω) r c ≤ imedIndex w₀ y (history O A Y n' ω) r c := by
  rw [imedIndex_history hrn, imedIndex_history (hrn.trans hnn')]
  have hN : pullCount A c n ω ≤ pullCount A c n' ω := pullCount_mono _ hnn' _
  refine add_le_add ?_ ?_
  · refine EReal.coe_ennreal_le_coe_ennreal_iff.mpr ?_
    gcongr
  · refine EReal.coe_le_coe_iff.mpr (mul_le_mul_of_nonneg_left ?_ hy)
    exact log_natCast_le_log_natCast hN

/-- At a round `n` of an IMED phase (`n` in batch `ℓ + 1`, `ℓ ≥ 1`, and `n + 1 ≤ s_ℓ`), HY pulls
the IMED arm with `y_ℓ = x_ℓ²` and the statistics at `t_ℓ`. -/
lemma next_of_imedPhase (w₀ β : ℝ) (ωs θ γ : ℕ → ℝ) {K : ℕ} (g : Grid K) {n ℓ : ℕ}
    (hb : g.batchOf n = ℓ + 1) (hℓ : ℓ ≠ 0) (himed : n + 1 ≤ g.imedEnd θ ℓ)
    (h : Hist Unit α ℝ n) :
    next w₀ β ωs θ γ g n h = imedArm w₀ (g.ratio ℓ ^ 2) h (g.t ℓ) := by
  unfold next
  rw [hb, Nat.add_sub_cancel, ite_eq_right hℓ, ite_eq_left himed]

/-- [INC-P000, proof of Lemma `lem:service`, (Q1)] The paced target is nondecreasing in `log t`
(for `(1 + ω) y ≥ 0`). -/
lemma target_mono_logt {w₀ thr ω' y logt logt' : ℝ} (hωy : 0 ≤ (1 + ω') * y)
    (hlt : logt ≤ logt') {n : ℕ} (h : Hist Unit α ℝ n) (r U Unext : ℕ) (c : α) :
    target w₀ thr ω' y logt h r U Unext c ≤ target w₀ thr ω' y logt' h r U Unext c := by
  unfold target
  split_ifs
  · exact le_rfl
  · gcongr
  · exact le_rfl

/-- [INC-P000, proof of Lemma `lem:service`, (Q1)] The paced target is at most
`K - 1 + U_(ℓ+1)`. -/
lemma target_le {w₀ thr ω' y logt : ℝ} {n : ℕ} (h : Hist Unit α ℝ n) (r U Unext : ℕ) (c : α) :
    target w₀ thr ω' y logt h r U Unext c ≤ Fintype.card α - 1 + Unext := by
  unfold target
  refine Nat.add_le_add_left ?_ _
  split_ifs <;> simp

/-- [INC-P000, proof of Lemma `lem:service`, Step (b2), one arm of HY] The paced target of HY
grows slowly after `σ ≥ 2` with `σ log σ ≥ 2k U_(ℓ+1)`: for `σ ≤ u ≤ t`,
`2k (n_c(t) - n_c(u)) ≤ 2k + (t - u)`, where `n_c(t)` is the target with `log t`. It is constant
if `c` is ambiguous or `K̂(c) = ∞`, and otherwise `K - 1 + min(U_(ℓ+1), ⌈f log t⌉)`. -/
lemma two_mul_target_sub_le {w₀ thr ω' y : ℝ} (hωy : 0 ≤ (1 + ω') * y) {n : ℕ}
    (h : Hist Unit α ℝ n) (r U Unext : ℕ) (c : α) {k σ : ℕ} (hk : 1 ≤ k) (hσ : 2 ≤ σ)
    (hσU : 2 * k * Unext ≤ σ * Real.log σ) {u t : ℕ} (hσu : σ ≤ u) (hut : u ≤ t) :
    2 * k * (target w₀ thr ω' y (Real.log t) h r U Unext c -
      target w₀ thr ω' y (Real.log u) h r U Unext c) ≤ 2 * k + (t - u) := by
  unfold target
  split_ifs with hrej htop
  · simp
  · have hf : 0 ≤ (1 + ω') * y / (testKinf w₀ h r U c).toReal :=
      div_nonneg hωy ENNReal.toReal_nonneg
    have e : ∀ x : ℝ, (1 + ω') * y * x / (testKinf w₀ h r U c).toReal =
        (1 + ω') * y / (testKinf w₀ h r U c).toReal * x := fun x ↦ by ring
    simp_rw [e]
    have := two_mul_min_ceil_sub_le hf hk hσ hσU hσu hut (U := Unext)
    rwa [Nat.add_sub_add_left]
  · simp

/-- At a round `n` of a paced phase (`n` in batch `ℓ + 1`, `ℓ ≥ 1`, and `n + 1 > s_ℓ`), HY pulls
the paced arm with the threshold `h_ℓ`, `y_ℓ = x_ℓ²`, `log t = log (n + 1)` and the statistics
at `t_ℓ`. -/
lemma next_of_pacedPhase (w₀ β : ℝ) (ωs θ γ : ℕ → ℝ) {K : ℕ} (g : Grid K) {n ℓ : ℕ}
    (hb : g.batchOf n = ℓ + 1) (hℓ : ℓ ≠ 0) (hpaced : ¬ n + 1 ≤ g.imedEnd θ ℓ)
    (h : Hist Unit α ℝ n) :
    next w₀ β ωs θ γ g n h = pacedArm w₀
      ((1 - γ ℓ) * g.ratio (ℓ - 1) ^ 2 * (if ℓ = 1 then g.logEnd 1 else
        threshold w₀ (g.logEnd ℓ) (g.ratio (ℓ - 1) ^ 2) h (g.t ℓ) (g.t (ℓ - 1))
          (g.netSize β ℓ) (g.netSize β (ℓ - 1))))
      (ωs ℓ) (g.ratio ℓ ^ 2) (Real.log (n + 1)) h (g.t ℓ) (g.netSize β ℓ)
      (g.netSize β (ℓ + 1)) := by
  unfold next
  rw [hb, Nat.add_sub_cancel, ite_eq_right hℓ, ite_eq_right hpaced]

/-- The threshold `h_ℓ` of the paced phase of batch `ℓ + 1` along a run, frozen at `t_ℓ`. -/
lemma pacedThr_history (w₀ β : ℝ) (γ : ℕ → ℝ) {K : ℕ} (g : Grid K) {n ℓ : ℕ}
    (hn : g.t ℓ ≤ n) :
    (1 - γ ℓ) * g.ratio (ℓ - 1) ^ 2 * (if ℓ = 1 then g.logEnd 1 else
        threshold w₀ (g.logEnd ℓ) (g.ratio (ℓ - 1) ^ 2) (history O A Y n ω) (g.t ℓ)
          (g.t (ℓ - 1)) (g.netSize β ℓ) (g.netSize β (ℓ - 1))) =
      (1 - γ ℓ) * g.ratio (ℓ - 1) ^ 2 * (if ℓ = 1 then g.logEnd 1 else
        threshold w₀ (g.logEnd ℓ) (g.ratio (ℓ - 1) ^ 2) (history O A Y (g.t ℓ) ω) (g.t ℓ)
          (g.t (ℓ - 1)) (g.netSize β ℓ) (g.netSize β (ℓ - 1))) := by
  rw [threshold_history hn (g.strictMono.monotone (Nat.sub_le ℓ 1))]

end HY

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] {K : ℕ}

/-- Along almost every run of `HY(w₀, β, ω, ϑ, γ)`, every action is HY's rule applied to the
history of the previous rounds. -/
lemma hyAlg_ae_action_eq (w₀ β : ℝ) (ωs θ γ : ℕ → ℝ) (g : Grid K)
    (env : Environment Unit α ℝ) :
    ∀ᵐ ω ∂(trajMeasure (hyAlg w₀ β ωs θ γ g : Algorithm Unit α ℝ) env), ∀ n,
      IT.action n ω = HY.next w₀ β ωs θ γ g n (history IT.obs IT.action IT.feedback n ω) :=
  (IT.isAlgEnvSeq_trajMeasure (hyAlg w₀ β ωs θ γ g) env).action_ae_all_eq_deterministic

/-- [INC-P000, the hypothesis (min) of Lemma `lem:W`, along a run] Along almost every run of HY,
at every round `n` of an IMED phase of batch `ℓ + 1` (`ℓ ≥ 1`), the pulled arm minimises the IMED
index `J_ℓ(·, n + 1)` computed with the statistics frozen at `t_ℓ`. -/
lemma hyAlg_ae_imedIndex_action_le (w₀ β : ℝ) (ωs θ γ : ℕ → ℝ) (g : Grid K)
    (env : Environment Unit α ℝ) :
    ∀ᵐ ω ∂(trajMeasure (hyAlg w₀ β ωs θ γ g : Algorithm Unit α ℝ) env), ∀ n ℓ,
      g.batchOf n = ℓ + 1 → ℓ ≠ 0 → n + 1 ≤ g.imedEnd θ ℓ → ∀ c,
        HY.imedIndex w₀ (g.ratio ℓ ^ 2) (history IT.obs IT.action IT.feedback n ω) (g.t ℓ)
            (IT.action n ω) ≤
          HY.imedIndex w₀ (g.ratio ℓ ^ 2) (history IT.obs IT.action IT.feedback n ω) (g.t ℓ) c := by
  filter_upwards [hyAlg_ae_action_eq w₀ β ωs θ γ g env] with ω hω
  intro n ℓ hb hℓ himed c
  rw [hω n, HY.next_of_imedPhase w₀ β ωs θ γ g hb hℓ himed]
  exact HY.imedIndex_imedArm_le c

/-- [INC-P000, Lemma `lem:W`(ii), Step 2, for HY] Along almost every run of HY, for every batch
`ℓ + 1` (`ℓ ≥ 1`) whose IMED phase `(t_ℓ, s]`, `s = min(s_ℓ, t_(ℓ+1))`, is nonempty and in which
every count at `t_ℓ` is at least `1`, the IMED index at the end of the batch satisfies
`J_ℓ(c', t_(ℓ+1) + 1) ≥ y_ℓ log ((s - t_ℓ) / K)` for every arm `c'`: the water level of the
batch, `Λ = min_c J_ℓ(c, t_(ℓ+1) + 1) / y_ℓ`, is at least `log ((s - t_ℓ) / K)`. -/
lemma hyAlg_ae_log_le_imedIndex (w₀ β : ℝ) (ωs θ γ : ℕ → ℝ) (g : Grid K)
    (env : Environment Unit α ℝ) :
    ∀ᵐ ω ∂(trajMeasure (hyAlg w₀ β ωs θ γ g : Algorithm Unit α ℝ) env), ∀ ℓ, ℓ ≠ 0 →
      (∀ c, 1 ≤ pullCount IT.action c (g.t ℓ) ω) →
      g.t ℓ < min (g.imedEnd θ ℓ) (g.t (ℓ + 1)) → ∀ c',
        ((g.ratio ℓ ^ 2 * Real.log (((min (g.imedEnd θ ℓ) (g.t (ℓ + 1)) - g.t ℓ : ℕ) : ℝ) /
            Fintype.card α) : ℝ) : EReal) ≤
          HY.imedIndex w₀ (g.ratio ℓ ^ 2)
            (history IT.obs IT.action IT.feedback (g.t (ℓ + 1)) ω) (g.t ℓ) c' := by
  filter_upwards [hyAlg_ae_imedIndex_action_le w₀ β ωs θ γ g env] with ω hω
  intro ℓ hℓ hN1 hrs c'
  set s := min (g.imedEnd θ ℓ) (g.t (ℓ + 1)) with hs
  set y := g.ratio ℓ ^ 2 with hy
  have hy0 : 0 ≤ y := sq_nonneg _
  have h := log_div_card_le_index (A := IT.action) (ω := ω)
    (I := fun c t ↦ HY.imedIndex w₀ y (history IT.obs IT.action IT.feedback (t - 1) ω) (g.t ℓ) c)
    (r := g.t ℓ) (s := s) (T := g.t (ℓ + 1)) hrs (min_le_right _ _) hy0
    (fun c t t' hrt htt' _ ↦
      HY.imedIndex_history_mono (by omega) (by omega) w₀ hy0 c)
    (fun t hrt hts c'' ↦ by
      have hts' : t ≤ g.t (ℓ + 1) := hts.trans (min_le_right _ _)
      have hb : g.batchOf (t - 1) = ℓ + 1 := g.batchOf_eq_iff.mpr ⟨by omega, by omega⟩
      have himed : t - 1 + 1 ≤ g.imedEnd θ ℓ := by
        have := hts.trans (min_le_left _ _)
        omega
      exact hω (t - 1) ℓ hb hℓ himed c'')
    (fun c t hrt _ ↦ by
      rw [HY.imedIndex_history (by omega)]
      exact le_add_of_nonneg_left (EReal.coe_ennreal_nonneg _))
    hN1 c'
  simpa using h

/-- [INC-P000, Lemma `lem:W`, Step 1, for HY] (W2) at the IMED rounds, along almost every run of
HY: an arm pulled at a round `n` of the IMED phase of batch `ℓ + 1` (`ℓ ≥ 1`) has
`y_ℓ log N_c(t_ℓ) ≤ J_ℓ(c', t_(ℓ+1) + 1)` for every arm `c'`, i.e. `log N_c(t_ℓ) ≤ Λ`. -/
lemma hyAlg_ae_log_pullCount_le_imedIndex (w₀ β : ℝ) (ωs θ γ : ℕ → ℝ) (g : Grid K)
    (env : Environment Unit α ℝ) :
    ∀ᵐ ω ∂(trajMeasure (hyAlg w₀ β ωs θ γ g : Algorithm Unit α ℝ) env), ∀ ℓ n, ℓ ≠ 0 →
      g.batchOf n = ℓ + 1 → n + 1 ≤ g.imedEnd θ ℓ → ∀ c',
        ((g.ratio ℓ ^ 2 * Real.log (pullCount IT.action (IT.action n ω) (g.t ℓ) ω) : ℝ) :
            EReal) ≤
          HY.imedIndex w₀ (g.ratio ℓ ^ 2)
            (history IT.obs IT.action IT.feedback (g.t (ℓ + 1)) ω) (g.t ℓ) c' := by
  filter_upwards [hyAlg_ae_imedIndex_action_le w₀ β ωs θ γ g env] with ω hω
  intro ℓ n hℓ hb himed c'
  have hbn := g.batchOf_eq_iff.mp hb
  set s := min (g.imedEnd θ ℓ) (g.t (ℓ + 1)) with hs
  set y := g.ratio ℓ ^ 2 with hy
  have hy0 : 0 ≤ y := sq_nonneg _
  have h := log_pullCount_le_index (A := IT.action) (ω := ω)
    (I := fun c t ↦ HY.imedIndex w₀ y (history IT.obs IT.action IT.feedback (t - 1) ω) (g.t ℓ) c)
    (r := g.t ℓ) (s := s) (T := g.t (ℓ + 1)) (min_le_right _ _) hy0
    (fun c t t' hrt htt' _ ↦
      HY.imedIndex_history_mono (by omega) (by omega) w₀ hy0 c)
    (fun t hrt hts c'' ↦ by
      have hts' : t ≤ g.t (ℓ + 1) := hts.trans (min_le_right _ _)
      have hb' : g.batchOf (t - 1) = ℓ + 1 := g.batchOf_eq_iff.mpr ⟨by omega, by omega⟩
      have himed' : t - 1 + 1 ≤ g.imedEnd θ ℓ := by
        have := hts.trans (min_le_left _ _)
        omega
      exact hω (t - 1) ℓ hb' hℓ himed' c'')
    (fun c t hrt _ ↦ by
      rw [HY.imedIndex_history (by omega)]
      exact le_add_of_nonneg_left (EReal.coe_ennreal_nonneg _))
    (t := n + 1) (by omega) (le_min himed (by omega)) c'
  simpa using h

/-- [INC-P000, the hypotheses (rule) and (idle) of Lemma `lem:service`, along a run] Along almost
every run of HY, at every round `n` of the paced phase of batch `ℓ + 1` (`ℓ ≥ 1`), with the
leader `ĉ_ℓ` and the targets `n_{ℓ,c}(n + 1)` computed from the statistics frozen at `t_ℓ`: a
pulled arm other than `ĉ_ℓ` is below its target, and if `ĉ_ℓ` is pulled, no other arm is. -/
lemma hyAlg_ae_paced_rule (w₀ β : ℝ) (ωs θ γ : ℕ → ℝ) (g : Grid K)
    (env : Environment Unit α ℝ) :
    ∀ᵐ ω ∂(trajMeasure (hyAlg w₀ β ωs θ γ g : Algorithm Unit α ℝ) env), ∀ ℓ n, ℓ ≠ 0 →
      g.batchOf n = ℓ + 1 → ¬ n + 1 ≤ g.imedEnd θ ℓ →
      (IT.action n ω ≠ HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) →
        pullCount IT.action (IT.action n ω) n ω <
          HY.target w₀ ((1 - γ ℓ) * g.ratio (ℓ - 1) ^ 2 * (if ℓ = 1 then g.logEnd 1 else
            HY.threshold w₀ (g.logEnd ℓ) (g.ratio (ℓ - 1) ^ 2)
              (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) (g.t (ℓ - 1))
              (g.netSize β ℓ) (g.netSize β (ℓ - 1))))
            (ωs ℓ) (g.ratio ℓ ^ 2) (Real.log (n + 1))
            (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) (g.netSize β ℓ)
            (g.netSize β (ℓ + 1)) (IT.action n ω)) ∧
      (IT.action n ω = HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) →
        ∀ c, c ≠ HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) →
          HY.target w₀ ((1 - γ ℓ) * g.ratio (ℓ - 1) ^ 2 * (if ℓ = 1 then g.logEnd 1 else
            HY.threshold w₀ (g.logEnd ℓ) (g.ratio (ℓ - 1) ^ 2)
              (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) (g.t (ℓ - 1))
              (g.netSize β ℓ) (g.netSize β (ℓ - 1))))
            (ωs ℓ) (g.ratio ℓ ^ 2) (Real.log (n + 1))
            (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) (g.netSize β ℓ)
            (g.netSize β (ℓ + 1)) c ≤ pullCount IT.action c n ω) := by
  filter_upwards [hyAlg_ae_action_eq w₀ β ωs θ γ g env] with ω hω
  intro ℓ n hℓ hb hpaced
  have hn : g.t ℓ ≤ n := (g.batchOf_eq_iff.mp hb).1
  have hA := hω n
  rw [HY.next_of_pacedPhase w₀ β ωs θ γ g hb hℓ hpaced, HY.pacedThr_history w₀ β γ g hn] at hA
  have hlead := HY.leader_history (O := IT.obs) (A := IT.action) (Y := IT.feedback) (ω := ω)
    hn w₀
  have htgt : ∀ thr c, HY.target w₀ thr (ωs ℓ) (g.ratio ℓ ^ 2) (Real.log (n + 1))
      (history IT.obs IT.action IT.feedback n ω) (g.t ℓ) (g.netSize β ℓ) (g.netSize β (ℓ + 1)) c =
      HY.target w₀ thr (ωs ℓ) (g.ratio ℓ ^ 2) (Real.log (n + 1))
      (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) (g.netSize β ℓ)
        (g.netSize β (ℓ + 1)) c := fun thr c ↦ HY.target_history hn _ _ _ _ _ _ _ c
  constructor
  · intro hne
    rw [hA] at hne ⊢
    rw [← hlead] at hne
    have := HY.pullCount'_pacedArm_lt_target hne
    rw [← pullCount_eq_pullCount', htgt] at this
    exact this
  · intro heq c hc
    rw [hA, ← hlead] at heq
    rw [← hlead] at hc
    have := HY.target_le_pullCount'_of_pacedArm_eq heq hc
    rw [← pullCount_eq_pullCount', htgt] at this
    exact this

/-- [INC-P000, Lemma `lem:service`(b), along a run] Along almost every run of HY, in the paced
phase `(σ, T]` of batch `ℓ + 1` (`ℓ ≥ 1`, `σ = s_ℓ`, `T = t_(ℓ+1)`), with the leader `ĉ_ℓ`, the
threshold `h_ℓ` and the targets `n_c(t) = n_{ℓ,c}(t)` frozen at `t_ℓ` (given here as `L`, `thr`
and `tgt`), if `ϑ_ℓ ≥ 0`, `(1 + ω_ℓ) y_ℓ ≥ 0` and the arrivals are slow (Step (b2)), then the
backlog after every round `t ∈ [σ, T]` satisfies
`∑_{c ≠ ĉ_ℓ} (n_c(t) - N_c(t))⁺ ≤ max((K - 1) B - (t - σ), K - 1)`, `B = K - 1 + U_(ℓ+1)`. -/
lemma hyAlg_ae_backlog_le (w₀ β : ℝ) (ωs θ γ : ℕ → ℝ) (g : Grid K)
    (env : Environment Unit α ℝ) :
    ∀ᵐ ω ∂(trajMeasure (hyAlg w₀ β ωs θ γ g : Algorithm Unit α ℝ) env), ∀ ℓ, ℓ ≠ 0 →
      0 ≤ θ ℓ → 0 ≤ (1 + ωs ℓ) * g.ratio ℓ ^ 2 → ∀ (L : α) (thr : ℝ) (tgt : α → ℕ → ℕ),
      L = HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) →
      thr = (1 - γ ℓ) * g.ratio (ℓ - 1) ^ 2 * (if ℓ = 1 then g.logEnd 1 else
        HY.threshold w₀ (g.logEnd ℓ) (g.ratio (ℓ - 1) ^ 2)
          (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) (g.t (ℓ - 1))
          (g.netSize β ℓ) (g.netSize β (ℓ - 1))) →
      (∀ c t, tgt c t = HY.target w₀ thr (ωs ℓ) (g.ratio ℓ ^ 2) (Real.log t)
        (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) (g.netSize β ℓ)
        (g.netSize β (ℓ + 1)) c) →
      (∀ u t, g.imedEnd θ ℓ ≤ u → u ≤ t → t ≤ g.t (ℓ + 1) →
        2 * ∑ c ∈ Finset.univ.erase L, (tgt c t - tgt c u) ≤
          2 * (Finset.univ.erase L).card + (t - u)) →
      ∀ t, g.imedEnd θ ℓ ≤ t → t ≤ g.t (ℓ + 1) →
        ∑ c ∈ Finset.univ.erase L, (tgt c t - pullCount IT.action c t ω) ≤
          max ((Finset.univ.erase L).card * (Fintype.card α - 1 + g.netSize β (ℓ + 1)) -
            (t - g.imedEnd θ ℓ)) (Finset.univ.erase L).card := by
  filter_upwards [hyAlg_ae_paced_rule w₀ β ωs θ γ g env] with ω hω
  intro ℓ hℓ hθ hωy L thr tgt hL hthr htgt harr t hσt htT
  have hσ : g.t ℓ ≤ g.imedEnd θ ℓ := g.t_le_imedEnd hθ
  have htℓ : 2 ≤ g.t ℓ := g.two_le_t (by omega)
  -- the round `n = t - 1` of the paced phase
  have hround : ∀ t, g.imedEnd θ ℓ < t → t ≤ g.t (ℓ + 1) →
      g.batchOf (t - 1) = ℓ + 1 ∧ ¬ t - 1 + 1 ≤ g.imedEnd θ ℓ ∧
      Real.log (((t - 1 : ℕ) : ℝ) + 1) = Real.log t := by
    intro t ht1 ht2
    refine ⟨g.batchOf_eq_iff.mpr ⟨by omega, by omega⟩, by omega, ?_⟩
    rw [Nat.cast_sub (by omega), Nat.cast_one, sub_add_cancel]
  refine backlog_le (A := IT.action) (ω := ω) (Finset.univ.erase L) (n := tgt)
    (σ := g.imedEnd θ ℓ) (T := g.t (ℓ + 1)) (B := Fintype.card α - 1 + g.netSize β (ℓ + 1))
    ?_ ?_ ?_ ?_ harr hσt htT
  · -- monotone targets
    intro c _ u hu v hv huv
    rw [htgt, htgt]
    refine HY.target_mono_logt hωy (Real.log_le_log ?_ (by exact_mod_cast huv)) _ _ _ _ c
    have : 2 ≤ u := htℓ.trans (hσ.trans hu.1)
    exact_mod_cast (show 0 < u by omega)
  · -- capped targets
    intro c _ u _ _
    rw [htgt]
    exact HY.target_le _ _ _ _ c
  · -- (rule)
    intro t ht1 ht2 hmem
    obtain ⟨hb, hpaced, hlog⟩ := hround t ht1 ht2
    have hne : IT.action (t - 1) ω ≠ L := Finset.ne_of_mem_erase hmem
    rw [hL] at hne
    have h1 := (hω ℓ (t - 1) hℓ hb hpaced).1 hne
    rw [htgt, hthr, ← hlog]
    exact h1
  · -- (idle)
    intro t ht1 ht2 hnot c hc
    obtain ⟨hb, hpaced, hlog⟩ := hround t ht1 ht2
    have heq : IT.action (t - 1) ω = L := by
      by_contra hne
      exact hnot (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩)
    rw [hL] at heq
    have hcL : c ≠ HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) := by
      rw [← hL]
      exact Finset.ne_of_mem_erase hc
    have h2 := (hω ℓ (t - 1) hℓ hb hpaced).2 heq c hcL
    rw [htgt, hthr, ← hlog]
    exact h2

/-- [INC-P000, Lemma `lem:service`(b), along a run, with Step (b2)] Along almost every run of HY,
with `K ≥ 2` arms, in the paced phase `(σ, T]` of batch `ℓ + 1` (`ℓ ≥ 1`, `σ = s_ℓ ≥ 2`,
`T = t_(ℓ+1)`) with the paper's condition `s_ℓ log s_ℓ ≥ 2(K - 1) U_(ℓ+1)`, `ϑ_ℓ ≥ 0` and
`(1 + ω_ℓ) y_ℓ ≥ 0`, the backlog after every round `t ∈ [σ, T]` is at most
`max((K - 1)(K - 1 + U_(ℓ+1)) - (t - σ), K - 1)`; the leader, the threshold and the targets frozen
at `t_ℓ` are given as `L`, `thr` and `tgt`, as in `hyAlg_ae_backlog_le`. -/
lemma hyAlg_ae_backlog_le_of_le (w₀ β : ℝ) (ωs θ γ : ℕ → ℝ) (g : Grid K)
    (env : Environment Unit α ℝ) (hK : 2 ≤ Fintype.card α) :
    ∀ᵐ ω ∂(trajMeasure (hyAlg w₀ β ωs θ γ g : Algorithm Unit α ℝ) env), ∀ ℓ, ℓ ≠ 0 →
      0 ≤ θ ℓ → 0 ≤ (1 + ωs ℓ) * g.ratio ℓ ^ 2 → 2 ≤ g.imedEnd θ ℓ →
      (2 * (Fintype.card α - 1 : ℕ) * g.netSize β (ℓ + 1) : ℝ) ≤
        g.imedEnd θ ℓ * Real.log (g.imedEnd θ ℓ) →
      ∀ (L : α) (thr : ℝ) (tgt : α → ℕ → ℕ),
      L = HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) →
      thr = (1 - γ ℓ) * g.ratio (ℓ - 1) ^ 2 * (if ℓ = 1 then g.logEnd 1 else
        HY.threshold w₀ (g.logEnd ℓ) (g.ratio (ℓ - 1) ^ 2)
          (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) (g.t (ℓ - 1))
          (g.netSize β ℓ) (g.netSize β (ℓ - 1))) →
      (∀ c t, tgt c t = HY.target w₀ thr (ωs ℓ) (g.ratio ℓ ^ 2) (Real.log t)
        (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) (g.netSize β ℓ)
        (g.netSize β (ℓ + 1)) c) →
      ∀ t, g.imedEnd θ ℓ ≤ t → t ≤ g.t (ℓ + 1) →
        ∑ c ∈ Finset.univ.erase L, (tgt c t - pullCount IT.action c t ω) ≤
          max ((Fintype.card α - 1) * (Fintype.card α - 1 + g.netSize β (ℓ + 1)) -
            (t - g.imedEnd θ ℓ)) (Fintype.card α - 1) := by
  filter_upwards [hyAlg_ae_backlog_le w₀ β ωs θ γ g env] with ω hω
  intro ℓ hℓ hθ hωy hσ2 hσU L thr tgt hL hthr htgt t hσt htT
  have hcard : (Finset.univ.erase L).card = Fintype.card α - 1 :=
    Finset.card_erase_of_mem (Finset.mem_univ L)
  set k := Fintype.card α - 1 with hk
  have hk1 : 1 ≤ k := by omega
  have harr : ∀ u t, g.imedEnd θ ℓ ≤ u → u ≤ t → t ≤ g.t (ℓ + 1) →
      2 * ∑ c ∈ Finset.univ.erase L, (tgt c t - tgt c u) ≤
        2 * (Finset.univ.erase L).card + (t - u) := by
    intro u t hu hut _
    rw [hcard]
    have hper : ∀ c ∈ Finset.univ.erase L, 2 * k * (tgt c t - tgt c u) ≤ 2 * k + (t - u) := by
      intro c _
      rw [htgt, htgt]
      exact HY.two_mul_target_sub_le hωy _ _ _ _ c hk1 hσ2 (by exact_mod_cast hσU) hu hut
    have hsum : k * (2 * ∑ c ∈ Finset.univ.erase L, (tgt c t - tgt c u)) ≤
        k * (2 * k + (t - u)) := by
      calc k * (2 * ∑ c ∈ Finset.univ.erase L, (tgt c t - tgt c u))
          = ∑ c ∈ Finset.univ.erase L, 2 * k * (tgt c t - tgt c u) := by
            rw [Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun c _ ↦ by ring
        _ ≤ ∑ _c ∈ Finset.univ.erase L, (2 * k + (t - u)) := Finset.sum_le_sum hper
        _ = k * (2 * k + (t - u)) := by rw [Finset.sum_const, hcard, smul_eq_mul]
    exact Nat.le_of_mul_le_mul_left hsum (by omega)
  have := hω ℓ hℓ hθ hωy L thr tgt hL hthr htgt harr t hσt htT
  rwa [hcard] at this

/-- [INC-P000, Definition `def:hy-vocab`, "every arm is observed"] Along almost every run of HY on
a grid for `K = card α` arms, batch 1 pulls every arm, so every count at a batch end `t_ℓ`,
`ℓ ≥ 1`, is at least `1`. -/
lemma hyAlg_ae_one_le_pullCount (w₀ β : ℝ) (ωs θ γ : ℕ → ℝ) (g : Grid (Fintype.card α))
    (env : Environment Unit α ℝ) :
    ∀ᵐ ω ∂(trajMeasure (hyAlg w₀ β ωs θ γ g : Algorithm Unit α ℝ) env), ∀ ℓ, 1 ≤ ℓ → ∀ c,
      1 ≤ pullCount IT.action c (g.t ℓ) ω := by
  filter_upwards [hyAlg_ae_action_eq w₀ β ωs θ γ g env] with ω hω
  intro ℓ hℓ c
  obtain ⟨n, hn, hnext⟩ := hy_exists_next_eq w₀ β ωs θ γ g c
  have hA : IT.action n ω = c := (hω n).trans (hnext _)
  have h1 : pullCount IT.action c (n + 1) ω = pullCount IT.action c n ω + 1 := by
    rw [pullCount_add_one, ite_eq_left hA]
  have h2 : pullCount IT.action c (n + 1) ω ≤ pullCount IT.action c (g.t ℓ) ω :=
    pullCount_mono _ ((Nat.succ_le_of_lt hn).trans (g.strictMono.monotone hℓ)) _
  omega

/-- [INC-P000, Lemma `lem:W`(ii), Step 2, for HY] `hyAlg_ae_log_le_imedIndex` without the
hypothesis on the counts at `t_ℓ` (every arm is pulled in batch 1): along almost every run of HY
on a grid for `K` arms, for every batch `ℓ + 1` (`ℓ ≥ 1`) whose IMED phase `(t_ℓ, s]`,
`s = min(s_ℓ, t_(ℓ+1))`, is nonempty, `J_ℓ(c', t_(ℓ+1) + 1) ≥ y_ℓ log ((s - t_ℓ) / K)` for every
arm `c'`. -/
lemma hyAlg_ae_log_le_imedIndex' (w₀ β : ℝ) (ωs θ γ : ℕ → ℝ) (g : Grid (Fintype.card α))
    (env : Environment Unit α ℝ) :
    ∀ᵐ ω ∂(trajMeasure (hyAlg w₀ β ωs θ γ g : Algorithm Unit α ℝ) env), ∀ ℓ, ℓ ≠ 0 →
      g.t ℓ < min (g.imedEnd θ ℓ) (g.t (ℓ + 1)) → ∀ c',
        ((g.ratio ℓ ^ 2 * Real.log (((min (g.imedEnd θ ℓ) (g.t (ℓ + 1)) - g.t ℓ : ℕ) : ℝ) /
            Fintype.card α) : ℝ) : EReal) ≤
          HY.imedIndex w₀ (g.ratio ℓ ^ 2)
            (history IT.obs IT.action IT.feedback (g.t (ℓ + 1)) ω) (g.t ℓ) c' := by
  filter_upwards [hyAlg_ae_log_le_imedIndex w₀ β ωs θ γ g env,
    hyAlg_ae_one_le_pullCount w₀ β ωs θ γ g env] with ω h1 h2
  intro ℓ hℓ hrs c'
  exact h1 ℓ hℓ (h2 ℓ (Nat.one_le_iff_ne_zero.mpr hℓ)) hrs c'

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- For an instance of `𝒫` (rewards in `[0, 1]`), the rewards of almost every run of every learner
are in `[0, 1]`: the reward of round `n` has the conditional law `ν_(A_n)`. -/
lemma ae_feedback_mem_Icc {alg : Algorithm Unit α ℝ} {ν : ProbabilityTheory.Kernel α ℝ}
    [ProbabilityTheory.IsMarkovKernel ν] (hν : ν ∈ unitBandits α) :
    ∀ᵐ ω ∂(trajMeasure alg (Environment.bandit ν)), ∀ n,
      IT.feedback n ω ∈ Set.Icc (0 : ℝ) 1 := by
  rw [MeasureTheory.ae_all_iff]
  intro n
  have hlaw := ((IT.isAlgEnvSeq_trajMeasure alg (Environment.bandit ν)).hasCondDistrib_feedback
    n).hasLaw_comp
  have hmem : ∀ᵐ y ∂((Environment.bandit ν).feedback n ∘ₘ
      (trajMeasure alg (Environment.bandit ν)).map
        (fun ω ↦ ((history IT.obs IT.action IT.feedback n ω, IT.obs n ω), IT.action n ω))),
      y ∈ Set.Icc (0 : ℝ) 1 := by
    refine MeasureTheory.Measure.ae_comp_of_ae_ae measurableSet_Icc
      (MeasureTheory.ae_of_all _ fun x ↦ ?_)
    rw [feedback_bandit, ProbabilityTheory.Kernel.prodMkLeft_apply]
    exact (hν.1 x.2).2
  rw [← hlaw.map_eq] at hmem
  exact MeasureTheory.ae_of_ae_map hlaw.aemeasurable hmem

/-- [INC-P000, Lemma `lem:imedround`, consequence, along a run] Along almost every run of HY
(`w₀ ≥ 0`, on a grid for `K` arms) on an instance of `𝒫`, for a batch `ℓ + 1` (`ℓ ≥ 1`) and an arm
`c` other than the leader `ĉ_ℓ` with IMED divergence `K̃_ℓ(c) ≥ D > 0` (both frozen at `t_ℓ`),
every round `t'` of the batch in its IMED phase (`t_ℓ ≤ t' ≤ s_ℓ`, `t' ≤ t_(ℓ+1)`) has
`N_c(t') ≤ max(N_c(t_ℓ), 1 + y_ℓ log t' / D)`. -/
lemma hyAlg_ae_pullCount_le_max (w₀ β : ℝ) (hw₀ : 0 ≤ w₀) (ωs θ γ : ℕ → ℝ)
    (g : Grid (Fintype.card α)) {ν : Kernel α ℝ} [IsMarkovKernel ν] (hν : ν ∈ unitBandits α) :
    ∀ᵐ ω ∂(trajMeasure (hyAlg w₀ β ωs θ γ g : Algorithm Unit α ℝ) (Environment.bandit ν)),
      ∀ ℓ, ℓ ≠ 0 → ∀ c, c ≠ HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) →
      ∀ D : ℝ, 0 < D →
      D ≤ (HY.imedKinf w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) c).toReal →
      ∀ t', g.t ℓ ≤ t' → t' ≤ g.imedEnd θ ℓ → t' ≤ g.t (ℓ + 1) →
        (pullCount IT.action c t' ω : ℝ) ≤
          max (pullCount IT.action c (g.t ℓ) ω : ℝ) (1 + g.ratio ℓ ^ 2 * Real.log t' / D) := by
  filter_upwards [hyAlg_ae_action_eq w₀ β ωs θ γ g (Environment.bandit ν),
    ae_feedback_mem_Icc (alg := hyAlg w₀ β ωs θ γ g) hν,
    hyAlg_ae_one_le_pullCount w₀ β ωs θ γ g (Environment.bandit ν)] with ω hω hfb hN1
  intro ℓ hℓ c hc D hD hDK t' ht'1 ht'2 ht'3
  have hℓ1 : 1 ≤ ℓ := Nat.one_le_iff_ne_zero.mpr hℓ
  have hy1 : 1 ≤ g.ratio ℓ ^ 2 := by
    rcases Nat.lt_or_ge ℓ 2 with h | h
    · rw [show ℓ = 1 by omega, g.ratio_one]
      norm_num
    · have := g.one_lt_ratio h
      nlinarith
  have hy0 : 0 < g.ratio ℓ ^ 2 := by linarith
  have htℓ : 2 ≤ g.t ℓ := g.two_le_t hℓ1
  have hg : Monotone fun k : ℕ ↦ g.ratio ℓ ^ 2 * Real.log ((k : ℝ) + 1) := by
    intro k k' hkk'
    refine mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) ?_) hy0.le
    exact_mod_cast Nat.add_le_add_right hkk' 1
  have h := pullCount_le_max_of_forall (A := IT.action) (ω := ω) (c := c) hD hg ht'1
    (fun k hk1 hk2 hAk ↦ by
      -- the round `k` is an IMED round of batch `ℓ + 1`
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
        have := hN1 ℓ hℓ1 (HY.leader w₀ (history IT.obs IT.action IT.feedback k ω) (g.t ℓ))
        have : (1 : ℝ) ≤ pullCount IT.action
            (HY.leader w₀ (history IT.obs IT.action IT.feedback k ω) (g.t ℓ)) (g.t ℓ) ω := by
          exact_mod_cast this
        linarith
      have hne : HY.imedArm w₀ (g.ratio ℓ ^ 2) (history IT.obs IT.action IT.feedback k ω)
          (g.t ℓ) ≠ HY.leader w₀ (history IT.obs IT.action IT.feedback k ω) (g.t ℓ) := by
        rw [← hA, hAk, hlead]
        exact hc
      have hNk : 1 ≤ pullCount' k (history IT.obs IT.action IT.feedback k ω)
          (HY.imedArm w₀ (g.ratio ℓ ^ 2) (history IT.obs IT.action IT.feedback k ω) (g.t ℓ)) := by
        rw [← hA, hAk, ← pullCount_eq_pullCount']
        exact (hN1 ℓ hℓ1 c).trans (pullCount_mono _ hk1 _)
      have hlt := HY.mul_toReal_imedKinf_add_lt hw₀ hy0 hfbk hpos (by omega) hne hNk
      rw [← hA, hAk, ← pullCount_eq_pullCount', HY.imedKinf_history hk1] at hlt
      have hNk' : (1 : ℝ) ≤ pullCount IT.action c k ω := by
        exact_mod_cast (hN1 ℓ hℓ1 c).trans (pullCount_mono _ hk1 _)
      have hlogN : 0 ≤ g.ratio ℓ ^ 2 * Real.log (pullCount IT.action c k ω) :=
        mul_nonneg hy0.le (Real.log_nonneg hNk')
      have hmul : (pullCount IT.action c k ω : ℝ) * D ≤ (pullCount IT.action c k ω : ℝ) *
          (HY.imedKinf w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) c).toReal :=
        mul_le_mul_of_nonneg_left hDK (by linarith)
      linarith)
  have hcast : g.ratio ℓ ^ 2 * Real.log (((t' - 1 : ℕ) : ℝ) + 1) = g.ratio ℓ ^ 2 * Real.log t' := by
    rw [Nat.cast_sub (by omega), Nat.cast_one, sub_add_cancel]
  rw [hcast] at h
  exact h

/-- [INC-P000, Lemma `lem:W`(i)–(ii), along a run] Along almost every run of HY on a grid for `K`
arms, for a batch `ℓ + 1` (`ℓ ≥ 1`) that is not activated (`t_(ℓ+1) ≤ s_ℓ`) or whose IMED phase
is long (`s_ℓ - t_ℓ ≥ K t_ℓ`, the third condition defining `ℓ_W`), every arm `c` pulled at a
round `n` of the batch has `y_ℓ log N_c(t_ℓ) ≤ J_ℓ(c', t_(ℓ+1) + 1)` for every arm `c'`: (W2),
`log N_c(t_ℓ) ≤ Λ`. At the paced rounds every arm has `N_c(t_ℓ) ≤ t_ℓ` and `Λ ≥ L_ℓ`. -/
lemma hyAlg_ae_W2 (w₀ β : ℝ) (ωs θ γ : ℕ → ℝ) (g : Grid (Fintype.card α))
    (env : Environment Unit α ℝ) :
    ∀ᵐ ω ∂(trajMeasure (hyAlg w₀ β ωs θ γ g : Algorithm Unit α ℝ) env), ∀ ℓ, ℓ ≠ 0 →
      (g.t (ℓ + 1) ≤ g.imedEnd θ ℓ ∨ Fintype.card α * g.t ℓ ≤ g.imedEnd θ ℓ - g.t ℓ) →
      ∀ n, g.batchOf n = ℓ + 1 → ∀ c',
        ((g.ratio ℓ ^ 2 * Real.log (pullCount IT.action (IT.action n ω) (g.t ℓ) ω) : ℝ) :
            EReal) ≤
          HY.imedIndex w₀ (g.ratio ℓ ^ 2)
            (history IT.obs IT.action IT.feedback (g.t (ℓ + 1)) ω) (g.t ℓ) c' := by
  filter_upwards [hyAlg_ae_log_pullCount_le_imedIndex w₀ β ωs θ γ g env,
    hyAlg_ae_log_le_imedIndex' w₀ β ωs θ γ g env] with ω h1 h2
  intro ℓ hℓ hcond n hb c'
  have hbn := g.batchOf_eq_iff.mp hb
  by_cases himed : n + 1 ≤ g.imedEnd θ ℓ
  · exact h1 ℓ n hℓ hb himed c'
  -- a paced round: the batch is activated, so its IMED phase is long
  have hact : g.imedEnd θ ℓ < g.t (ℓ + 1) := by omega
  have hlong : Fintype.card α * g.t ℓ ≤ g.imedEnd θ ℓ - g.t ℓ := hcond.resolve_left (by omega)
  have hK : 0 < Fintype.card α := Fintype.card_pos
  have htℓ : 2 ≤ g.t ℓ := g.two_le_t (Nat.one_le_iff_ne_zero.mpr hℓ)
  have hmin : min (g.imedEnd θ ℓ) (g.t (ℓ + 1)) = g.imedEnd θ ℓ := min_eq_left hact.le
  have hrs : g.t ℓ < min (g.imedEnd θ ℓ) (g.t (ℓ + 1)) := by
    rw [hmin]
    have : Fintype.card α * g.t ℓ ≥ 2 := le_trans htℓ (Nat.le_mul_of_pos_left _ hK)
    omega
  have hW := h2 ℓ hℓ hrs c'
  rw [hmin] at hW
  refine le_trans ?_ hW
  refine EReal.coe_le_coe_iff.mpr (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
  -- `log N_c(t_ℓ) ≤ log t_ℓ ≤ log ((s_ℓ - t_ℓ) / K)`
  have hN : Real.log (pullCount IT.action (IT.action n ω) (g.t ℓ) ω) ≤ Real.log (g.t ℓ) :=
    log_natCast_le_log_natCast (pullCount_le _ _ _)
  refine hN.trans (Real.log_le_log (by exact_mod_cast (show 0 < g.t ℓ by omega)) ?_)
  have hKr : (0 : ℝ) < Fintype.card α := by exact_mod_cast hK
  rw [le_div_iff₀ hKr]
  have : (Fintype.card α * g.t ℓ : ℕ) ≤ g.imedEnd θ ℓ - g.t ℓ := hlong
  have : ((Fintype.card α * g.t ℓ : ℕ) : ℝ) ≤ ((g.imedEnd θ ℓ - g.t ℓ : ℕ) : ℝ) := by
    exact_mod_cast this
  push_cast at this
  linarith

end Incognita.BatchedBandits
