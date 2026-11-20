/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.LawTransferAlgorithm
public import Incognita.TransferBandits.Means
public import Incognita.TransferBandits.Checks

/-! # Checks of the definitions of [INC-P002]

Witnesses, known cases and exclusions (AGENTS.md §6.4) for the definitions of
`Incognita.TransferBandits.LawDrift` and `Incognita.TransferBandits.LawTransferAlgorithm`.

## Main statements

The Dirac vector at `y₀ ∈ S` is Mathlib's `Pi.single y₀ 1`.

* `single_mem_probVecs` (witness), `lawVec_mem_probVecs` (known case: the vector of a
  probability measure carried by `S`), `zero_not_mem_probVecs` (exclusion).
* `vecKL_self` (witness: `KL(r, r) = 0`), `vecKL_single` (known case:
  `KL(δ_{y₀}, q) = log (1 / q(y₀))`), `vecKL_eq_top` (exclusion: `KL(r, q) = ∞` when
  `q(y) = 0 < r(y)`).
* `vecKs_eq_zero` (witness), `vecKs_eq_of_isKLProj` and `vecKs_single_zero` (known cases:
  `K_S(δ_0, ℓ) = log (1 / (1 - ℓ/x_max))`), `vecKs_single_zero_pos` (exclusion).
* `ipm_self` (witness), `ipm_meanClass` (known case: the mean gap), `ipm_meanClass_single_ne_zero`
  (exclusion: the mean gap separates two Dirac masses).
* `tvClass_isTestClass` (witness), `ipm_tvClass` (known case: `d_TV(q, q') = ∑ (q - q')_+`,
  lem:ipm (c)), `ipm_tvClass_single` (two Dirac masses are at distance `1`).
* `ksClass_isTestClass` (witness), `ipm_ksClass` (known case: `sup_s |F_q(s) - F_{q'}(s)|`, the
  Kolmogorov distance), `ipm_ksClass_single_pos` (exclusion: it separates two Dirac masses).
* `w1Class_isTestClass` (witness), `ipm_w1Class_single` (known case: `W₁(δ_y, δ_z) = |y - z|`),
  `indicator_not_mem_w1Class` (exclusion: the indicator of a point is not `1`-Lipschitz).
* `hasMeanProperty_meanClass` (witness), `hasMeanProperty_tvClass` (known case: the total
  variation has the mean property on `S ⊆ [0,1]`), `not_hasMeanProperty_zero` (exclusion: the class
  `{0}` does not have it).
* `deterministic_mem_supportBandits` (witness), `supportBandits_subset_unitBandits` (known case:
  instances on `S ⊆ [0,1]` are instances of [INC-P003]), `const_dirac_not_mem_supportBandits`
  (exclusion).
* `self_mem_lawDriftClass` (witness), `mem_lawDriftClass_meanClass_iff` (known case: for the
  mean gap, `Θ` is the two-sided drift condition of [INC-P003]), `lawDriftClass_eq_empty`
  (exclusion: no pair for a zero bound); `integral_id_eq_vecMean` (`P[id] = m(lawVec S P)`).
* `isLawConsistent_of_isConsistent_one` (known case: the class `𝒞_𝟏` of [INC-P003] is in every
  `Cons(N')`), `not_isLawConsistent_constArm` (exclusion: the learner that always pulls one arm);
  the witness is `Incognita.P002.isLawConsistent_klucb` (the source-ignoring KL-UCB, in
  `Incognita/P002/Witnesses.lean`).
* `isKLProj_self` (witness, slack case `ℓ ≤ m(ρ)`), `isKLProj_single_zero` (witness, binding case:
  the projection of `δ_0` at a level `ℓ ∈ [0, x_max]` is `(1 - ℓ/x_max) δ_0 + (ℓ/x_max) δ_{x_max}`),
  `not_isKLProj_zero` (exclusion).
* `isLeast_driftConstant_single_zero` (witness: the infimum defining `D_a(0)` is attained at
  `1/K_0`), `driftConstant_single_zero` (known case: `D_a(0) = 1/K_S(ν_a, μ⋆)`, the constant of
  KL-UCB, for `ν_a = δ_0`), `driftConstant_eq_zero_of_altPairs_eq_empty` (known case: no
  alternative, the constant is `0`), `driftConstant_single_zero_pos` (exclusion: the constant is
  not identically `0`); `armConstant_zero_of_eq_dirac` and `armConstant_zero_pos_of_eq_dirac`, the
  same on an arm of a pair of instances.
* `programme_le` (witness), `programme_zero` (known case: `J_a(x, 0; μ) = x K_S(ν_a, μ)`, the
  programme of KL-UCB), `programme_eq_top` (exclusion: `J_a = ∞` without alternative pairs).
* `reachGain_nonneg` (witness), `reachGain_meanClass` (known case: for the mean gap,
  `ω(q') = min (l, x_max - m(q'))`), `reachGain_single_max` (exclusion: `ω(δ_{x_max}) = 0`).
* `thresholdKL_le` (witness), `thresholdKL_eq_zero` (known case), `vecKs_le_thresholdKL_meanClass`
  and `thresholdKL_meanClass_single_zero_pos` (exclusion: `G > 0` for `ν'_a = δ_0`).
* `klucbLawTransfer_policy_of_lt` (known case: the first `K` rounds pull each arm once),
  `lawIndex_zero` and `statIndex_of_eq_zero` (known case: without source data the index is the
  KL-UCB index on `S`), `vecMean_le_lawIndex` (witness for the index: it is at least the
  empirical mean), `lawIndex_eq_bot` (exclusion: `-∞` for a negative drift bound),
  `klucbLawTransfer_policy_of_le` (witness: the later rounds draw uniformly among the maximisers
  of the index), `klucbLawTransfer_ne_constArm` (exclusion: it is not a
  constant-arm learner).
* `one_sub_le_vecKL` (`KL(r, q) ≥ 1 - q(supp r)`), `vecKs_pos_of_support_le` and
  `apply_le_one_sub_vecMean_div` (`q(0) ≤ 1 - m(q)/x_max`), used by the witnesses.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal Topology

namespace Incognita.TransferBandits

variable {S : Finset ℝ}

/-! ### Probability vectors -/

/-- Witness: a Dirac vector is a probability vector. -/
lemma single_mem_probVecs (y₀ : S) : Pi.single y₀ (1 : ℝ) ∈ probVecs S := by
  refine ⟨fun y ↦ ?_, Fintype.sum_pi_single' y₀ 1⟩
  rw [Pi.single_apply]
  split_ifs <;> norm_num

/-- Exclusion: the zero vector is not a probability vector. -/
lemma zero_not_mem_probVecs : (0 : S → ℝ) ∉ probVecs S := by
  rintro ⟨-, h⟩
  simp at h

/-- Known case: the vector of a probability measure carried by `S` is a probability vector. -/
lemma lawVec_mem_probVecs {P : Measure ℝ} [IsProbabilityMeasure P] (hP : P (↑S : Set ℝ)ᶜ = 0) :
    lawVec S P ∈ probVecs S := by
  refine ⟨fun y ↦ ENNReal.toReal_nonneg, ?_⟩
  have hS : P (↑S : Set ℝ) = 1 := by
    rw [← prob_compl_eq_zero_iff S.measurableSet]
    exact hP
  have h : ∑ y ∈ S, P {y} = 1 := by rw [sum_measure_singleton, hS]
  unfold lawVec
  rw [← ENNReal.toReal_sum (fun y _ ↦ measure_ne_top P _)]
  rw [Finset.sum_coe_sort S (fun y ↦ P {y}), h, ENNReal.toReal_one]

/-! ### The Kullback–Leibler divergence -/

/-- Witness: `KL(r, r) = 0` for a probability vector `r`. -/
lemma vecKL_self {r : S → ℝ} : vecKL r r = 0 := by
  unfold vecKL
  split_ifs with hc
  swap
  · exact absurd (fun y h ↦ h) hc
  have : ∀ y, (if 0 < r y then r y * Real.log (r y / r y) else 0) = 0 := by
    intro y
    split_ifs with h
    · rw [div_self h.ne', Real.log_one, mul_zero]
    · rfl
  simp only [this, Finset.sum_const_zero, ENNReal.ofReal_zero]

/-- Exclusion: `KL(r, q) = ∞` when `q(y) = 0 < r(y)` for some `y`. -/
lemma vecKL_eq_top {r q : S → ℝ} {y : S} (hr : 0 < r y) (hq : q y = 0) : vecKL r q = ∞ := by
  have h : ¬ ∀ y, 0 < r y → 0 < q y := fun h ↦ (h y hr).ne' hq
  unfold vecKL
  simp only [h, ↓reduceIte]

/-- Known case: `KL(δ_{y₀}, q) = log (1 / q(y₀))` when `q(y₀) > 0`. -/
lemma vecKL_single {q : S → ℝ} {y₀ : S} (hq : 0 < q y₀) :
    vecKL (Pi.single y₀ 1) q = ENNReal.ofReal (Real.log (1 / q y₀)) := by
  have hc : ∀ y, 0 < (Pi.single y₀ (1 : ℝ) : S → ℝ) y → 0 < q y := by
    intro y hy
    by_cases h : y = y₀
    · rw [h]; exact hq
    · simp [h] at hy
  unfold vecKL
  split_ifs
  congr 1
  rw [Finset.sum_eq_single y₀]
  · simp
  · intro y _ hy
    simp [hy]
  · simp

/-! ### Integral probability metrics -/

/-- Witness: `d_𝓕(q, q) = 0`. -/
lemma ipm_self (𝓕 : Set (S → ℝ)) (q : S → ℝ) : ipm 𝓕 q q = 0 := by
  simp [ipm]

lemma vecMean_sub (q q' : S → ℝ) :
    vecMean q - vecMean q' = ∑ y : S, (y : ℝ) * (q y - q' y) := by
  unfold vecMean
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  ring

/-- Known case: for the test function `y ↦ y`, `d_𝓕` is the mean gap `|m(q) - m(q')|`. -/
lemma ipm_meanClass (q q' : S → ℝ) :
    ipm (meanClass S) q q' = |vecMean q - vecMean q'| := by
  have : Unique (meanClass S) := Set.uniqueSingleton _
  have hd : ((default : meanClass S) : S → ℝ) = fun y : S ↦ (y : ℝ) :=
    Set.mem_singleton_iff.mp (default : meanClass S).2
  rw [ipm, ciSup_unique, vecMean_sub, hd]

/-- The mean of `x δ_{y₀}` is `x y₀`. -/
lemma vecMean_single (y₀ : S) (x : ℝ) : vecMean (Pi.single y₀ x) = x * y₀ := by
  unfold vecMean
  rw [Finset.sum_eq_single y₀ (fun y _ hy ↦ by simp [hy]) (by simp),
    Pi.single_eq_same]

lemma vecMean_add (q q' : S → ℝ) : vecMean (q + q') = vecMean q + vecMean q' := by
  simp only [vecMean, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- Exclusion: the mean gap between the Dirac masses at two distinct points is not `0`. -/
lemma ipm_meanClass_single_ne_zero {y₀ y₁ : S} (h : y₀ ≠ y₁) :
    ipm (meanClass S) (Pi.single y₀ 1) (Pi.single y₁ 1) ≠ 0 := by
  rw [ipm_meanClass, vecMean_single, vecMean_single, one_mul, one_mul, abs_ne_zero, sub_ne_zero]
  exact fun h' ↦ h (Subtype.ext h')

/-! ### Instances on `S` and the class `Θ` -/

variable {α : Type*} [MeasurableSpace α]

/-- Witness: a deterministic instance with values in `S` is an instance on `S`. -/
lemma deterministic_mem_supportBandits [Countable α] [MeasurableSingletonClass α] (f : α → S) :
    Kernel.deterministic (fun a ↦ (f a : ℝ)) (measurable_of_countable _) ∈ supportBandits S α := by
  refine ⟨inferInstance, fun a ↦ ?_⟩
  rw [Kernel.deterministic_apply, Measure.dirac_apply' _ S.measurableSet.compl]
  simp

/-- Exclusion: a Dirac mass outside `S` is not an instance on `S`. -/
lemma const_dirac_not_mem_supportBandits [Nonempty α] {x : ℝ} (hx : x ∉ S) :
    Kernel.const α (Measure.dirac x) ∉ supportBandits S α := by
  rintro ⟨-, h⟩
  have := h (Classical.arbitrary α)
  rw [Kernel.const_apply, Measure.dirac_apply' _ S.measurableSet.compl] at this
  simp [hx] at this

/-- Known case: the instances on `S ⊆ [0,1]` are instances `𝒫^K` of [INC-P003]. -/
lemma supportBandits_subset_unitBandits (hS : ∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) :
    supportBandits S α ⊆ unitBandits α := by
  rintro ν ⟨hν, h⟩
  refine ⟨hν, fun a ↦ ?_⟩
  rw [ae_iff]
  refine measure_mono_null (fun x hx ↦ ?_) (h a)
  intro hxS
  exact hx (hS x hxS)

/-- Witness: `(ν, ν) ∈ Θ` for an instance `ν` on `S` and positive bounds. -/
lemma self_mem_lawDriftClass {𝓕 : Set (S → ℝ)} {L : α → ℝ}
    (hL : ∀ k, 0 < L k) {ν : Kernel α ℝ} (hν : ν ∈ supportBandits S α) :
    (ν, ν) ∈ lawDriftClass 𝓕 L :=
  ⟨hν, hν, fun k ↦ by simpa [ipm_self] using hL k⟩

lemma ipm_nonneg (𝓕 : Set (S → ℝ)) (q q' : S → ℝ) : 0 ≤ ipm 𝓕 q q' :=
  Real.iSup_nonneg fun _ ↦ abs_nonneg _

/-- Exclusion: with a zero bound on some arm, `Θ` is empty. -/
lemma lawDriftClass_eq_empty (𝓕 : Set (S → ℝ)) {L : α → ℝ} {k : α} (hk : L k = 0) :
    lawDriftClass 𝓕 L = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun p hp ↦ ?_
  have := hp.2.2 k
  rw [hk] at this
  exact (ipm_nonneg 𝓕 _ _).not_gt this

/-- The mean of a probability measure carried by `S` is the mean of its vector:
`P[id] = ∑_y P{y} y`. -/
lemma integral_id_eq_vecMean {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : P (↑S : Set ℝ)ᶜ = 0) : P[id] = vecMean (lawVec S P) := by
  have hae : ∀ᵐ x ∂P, x ∈ (↑S : Set ℝ) := by
    rw [ae_iff]
    exact hP
  have h1 : ∫ x, id x ∂P = ∫ x in (↑S : Set ℝ), id x ∂P := by
    rw [Measure.restrict_eq_self_of_ae_mem hae]
  have hint : IntegrableOn id (↑S : Set ℝ) P := by
    rw [← Set.biUnion_of_singleton (↑S : Set ℝ)]
    exact (integrableOn_finset_iUnion (s := S)).mpr fun y _ ↦ integrableOn_singleton
  rw [h1, setIntegral_finset S hint]
  unfold vecMean lawVec
  rw [← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  simp [measureReal_def]

/-- Known case: for the mean gap, `Θ` is the set of pairs of instances on `S` with the two-sided
drift condition `|μ_k - μ'_k| < L_k` of [INC-P003]. -/
lemma mem_lawDriftClass_meanClass_iff {L : α → ℝ} {ν ν' : Kernel α ℝ} :
    (ν, ν') ∈ lawDriftClass (meanClass S) L ↔
      ν ∈ supportBandits S α ∧ ν' ∈ supportBandits S α ∧ TwoSidedDriftBound L ν ν' := by
  constructor
  · rintro ⟨hν, hν', h⟩
    have := hν.1
    have := hν'.1
    refine ⟨hν, hν', fun k ↦ ?_⟩
    rw [integral_id_eq_vecMean (hν.2 k), integral_id_eq_vecMean (hν'.2 k), ← ipm_meanClass]
    exact h k
  · rintro ⟨hν, hν', h⟩
    have := hν.1
    have := hν'.1
    refine ⟨hν, hν', fun k ↦ ?_⟩
    rw [ipm_meanClass, ← integral_id_eq_vecMean (hν.2 k), ← integral_id_eq_vecMean (hν'.2 k)]
    exact h k

/-! ### Consistency -/

/-- Known case: a learner of the class `𝒞_𝟏` of [INC-P003] (consistent on all pairs of `𝒫^K`
and all source strategies) belongs to `Cons(N')` for every `N'`, when `S ⊆ [0,1]`. -/
lemma isLawConsistent_of_isConsistent_one (hS : ∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1)
    {𝓕 : Set (S → ℝ)} {L : α → ℝ} (N' : ℕ → α → ℕ) {π : TransferAlgorithm α}
    (hπ : IsConsistent (fun _ ↦ 1) π) : IsLawConsistent 𝓕 L N' π := by
  intro ν ν' hνν' k hk c hc
  have hν := supportBandits_subset_unitBandits hS hνν'.1
  have hν' := supportBandits_subset_unitBandits hS hνν'.2.1
  have hex : ∃ b, (ν k)[id] < (ν b)[id] := by
    by_contra h
    simp only [not_exists, not_lt] at h
    have : Nonempty α := ⟨k⟩
    exact (ciSup_le h).not_gt hk
  exact hπ ν ν' ⟨hν, hν', fun a ↦ abs_mean_sub_mean_le_one hν hν' a⟩
    (fun T ↦ constSize (N' T)) (fun T ↦ isSizeRule_constSize _) k hex c hc

/-! ### The constant -/

/-- Witness: the constant is nonnegative. -/
lemma driftConstant_nonneg (𝓕 : Set (S → ℝ)) (l : ℝ) (r r' : S → ℝ) (μ c : ℝ) :
    0 ≤ driftConstant 𝓕 l r r' μ c :=
  Real.sInf_nonneg fun _ hx ↦ hx.1.le

/-- Known case: without alternative pairs (for example `μ⋆ > max S`), the programme is `∞` and
the constant is `0`: no pull is needed. -/
lemma driftConstant_eq_zero_of_altPairs_eq_empty {𝓕 : Set (S → ℝ)} {l : ℝ} {r r' : S → ℝ}
    {μ : ℝ} (h : altPairs 𝓕 l μ = ∅) (c : ℝ) : driftConstant 𝓕 l r r' μ c = 0 := by
  have hset : {x : ℝ | 0 < x ∧ 1 ≤ programme 𝓕 l r r' μ x c} = Set.Ioi 0 := by
    ext x
    simp [programme, h]
  rw [driftConstant, hset, csInf_Ioi]

/-! ### The algorithm -/

/-- Known case: at the rounds `n < K`, KL-UCB-`d`-Transfer pulls the arm
`(Fintype.equivFin α).symm n`, whatever the source data and the history (each arm once). -/
lemma klucbLawTransfer_policy_of_lt [Fintype α] [Nonempty α] [MeasurableSingletonClass α]
    (𝓕 : Set (S → ℝ)) (L : α → ℝ) {n : ℕ} (hn : n < Fintype.card α)
    (x : Source α × (Fin n → α × ℝ)) :
    (klucbLawTransfer 𝓕 L).policy n x = Measure.dirac ((Fintype.equivFin α).symm ⟨n, hn⟩) := by
  simp only [klucbLawTransfer, Kernel.comap_apply]
  change lawPolicyMeasure 𝓕 L n _ = _
  simp [lawPolicyMeasure, hn]

/-- Witness: at the rounds `n ≥ K`, KL-UCB-`d`-Transfer draws its arm uniformly among the maximisers
of the index computed from the counts of the source data and of the history. -/
lemma klucbLawTransfer_policy_of_le [Fintype α] [Nonempty α] [MeasurableSingletonClass α]
    (𝓕 : Set (S → ℝ)) (L : α → ℝ) {n : ℕ} (hn : Fintype.card α ≤ n)
    (x : Source α × (Fin n → α × ℝ)) :
    (klucbLawTransfer 𝓕 L).policy n x =
      uniformOn {k | ∀ j,
        statIndex 𝓕 L n (lawStat S n x) j ≤ statIndex 𝓕 L n (lawStat S n x) k} := by
  simp only [klucbLawTransfer, Kernel.comap_apply]
  change lawPolicyMeasure 𝓕 L n _ = _
  simp [lawPolicyMeasure, not_lt.mpr hn]

/-- Exclusion: with at least two arms, KL-UCB-`d`-Transfer is not a constant-arm learner (it pulls
two different arms at rounds `0` and `1`). -/
lemma klucbLawTransfer_ne_constArm [Fintype α] [Nonempty α] [MeasurableSingletonClass α]
    (hK : 2 ≤ Fintype.card α) (𝓕 : Set (S → ℝ)) (L : α → ℝ) (a : α) :
    klucbLawTransfer 𝓕 L ≠ TransferAlgorithm.constArm a := by
  intro h
  have h0 := klucbLawTransfer_policy_of_lt 𝓕 L (n := 0) (by omega) ((0, 0), Fin.elim0)
  have h1 := klucbLawTransfer_policy_of_lt 𝓕 L (n := 1) (by omega) ((0, 0), fun _ ↦ (a, 0))
  rw [h] at h0 h1
  simp only [TransferAlgorithm.constArm, Kernel.const_apply, dirac_eq_dirac_iff] at h0 h1
  have := (Fintype.equivFin α).symm.injective (h0.symm.trans h1)
  simp at this

/-! ### Objects of the structure results -/

lemma vecMean_nonneg (hS : ∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) {q : S → ℝ} (hq : q ∈ probVecs S) :
    0 ≤ vecMean q :=
  Finset.sum_nonneg fun y _ ↦ mul_nonneg (hq.1 y) (hS y y.2).1

/-- On a support `S ⊆ (-∞, b]`, the mean of a probability vector is at most `b`. -/
lemma vecMean_le_of_le {b : ℝ} (hS : ∀ y ∈ S, y ≤ b) {q : S → ℝ} (hq : q ∈ probVecs S) :
    vecMean q ≤ b := by
  calc vecMean q ≤ ∑ y, q y * b :=
        Finset.sum_le_sum fun y _ ↦ mul_le_mul_of_nonneg_left (hS y y.2) (hq.1 y)
    _ = b := by rw [← Finset.sum_mul, hq.2, one_mul]

/-- Witness: a probability vector whose mean is at least `ℓ` is its own projection. -/
lemma isKLProj_self {r : S → ℝ} {ℓ : ℝ} (hr : r ∈ probVecs S) (h : ℓ ≤ vecMean r) :
    IsKLProj r ℓ r :=
  ⟨hr, h, fun q _ _ ↦ by rw [vecKL_self]; exact zero_le⟩

/-- Exclusion: the zero vector is not a projection (it is not a probability vector). -/
lemma not_isKLProj_zero (r : S → ℝ) (ℓ : ℝ) : ¬ IsKLProj r ℓ 0 :=
  fun h ↦ zero_not_mem_probVecs h.1

/-- Known case: the divergence to a projection is `K_S(ρ, ℓ)`. -/
lemma vecKs_eq_of_isKLProj {ρ Q : S → ℝ} {ℓ : ℝ} (hQ : IsKLProj ρ ℓ Q) :
    vecKs S ρ ℓ = vecKL ρ Q :=
  le_antisymm (iInf₂_le Q ⟨hQ.1, hQ.2.1⟩) (le_iInf₂ fun q hq ↦ hQ.2.2 q hq.1 hq.2)

/-- `K_S(r, ℓ) = 0` when `m(r) ≥ ℓ`. -/
lemma vecKs_eq_zero {r : S → ℝ} {ℓ : ℝ} (hr : r ∈ probVecs S) (h : ℓ ≤ vecMean r) :
    vecKs S r ℓ = 0 :=
  le_antisymm ((iInf₂_le r ⟨hr, h⟩).trans_eq vecKL_self) zero_le

/-- Witness: `ω_d(q') ≥ 0` (take `q = q'`). -/
lemma reachGain_nonneg (𝓕 : Set (S → ℝ)) (l : ℝ) {q' : S → ℝ} (hq' : q' ∈ probVecs S) :
    0 ≤ reachGain 𝓕 l q' := by
  rcases le_or_gt 0 l with hl | hl
  · exact Real.sSup_nonneg' ⟨0, ⟨q', hq', by rw [ipm_self]; exact hl, by ring⟩, le_rfl⟩
  · -- a negative budget admits no `q`, and `sSup ∅ = 0`
    have : {m | ∃ q ∈ probVecs S, ipm 𝓕 q q' ≤ l ∧ m = vecMean q - vecMean q'} = ∅ :=
      Set.eq_empty_of_forall_notMem fun _ ⟨q, _, hd, _⟩ ↦
        (ipm_nonneg 𝓕 q q').not_gt (hd.trans_lt hl)
    rw [reachGain, this, Real.sSup_empty]

/-- Known case: `G^d = 0` when `ν'_a` itself reaches `μ⋆`. -/
lemma thresholdKL_eq_zero {𝓕 : Set (S → ℝ)} {l : ℝ} {r' : S → ℝ} {μ : ℝ}
    (hr' : r' ∈ probVecs S) (h : μ ≤ vecMean r' + reachGain 𝓕 l r') :
    thresholdKL 𝓕 l r' μ = 0 :=
  le_antisymm ((iInf₂_le r' ⟨hr', h⟩).trans_eq vecKL_self) zero_le

/-- Witness: `G^d` is at most the divergence to any source law that reaches `μ⋆`. -/
lemma thresholdKL_le {𝓕 : Set (S → ℝ)} {l : ℝ} {r' q' : S → ℝ} {μ : ℝ}
    (hq' : q' ∈ probVecs S) (h : μ ≤ vecMean q' + reachGain 𝓕 l q') :
    thresholdKL 𝓕 l r' μ ≤ vecKL r' q' :=
  iInf₂_le q' ⟨hq', h⟩

/-- The vector of the Dirac mass at a point of `S` is the Dirac vector. -/
lemma lawVec_dirac (y₀ : S) : lawVec S (Measure.dirac (y₀ : ℝ)) = Pi.single y₀ 1 := by
  funext y
  simp only [lawVec, Measure.dirac_apply' _ (measurableSet_singleton _), Pi.single_apply,
    Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply]
  by_cases h : y = y₀
  · simp [h]
  · have : (y₀ : ℝ) ≠ y := fun h' ↦ h (Subtype.ext h'.symm)
    simp [h, this]

/-- On a support `S ⊆ (-∞, b]` containing `0`, a probability vector `q` gives the point `0` a mass
at most `1 - m(q)/b` (for `b = 0`, read `1 - m(q)/0 = 1`). -/
lemma apply_le_one_sub_vecMean_div {b : ℝ} (hS : ∀ y ∈ S, y ≤ b) {y₀ : S}
    (hy₀ : (y₀ : ℝ) = 0) {q : S → ℝ} (hq : q ∈ probVecs S) : q y₀ ≤ 1 - vecMean q / b := by
  have hb0 : 0 ≤ b := by have := hS y₀ y₀.2; rwa [hy₀] at this
  rcases hb0.eq_or_lt with rfl | hb
  · rw [div_zero, sub_zero, ← hq.2]
    exact Finset.single_le_sum (fun y _ ↦ hq.1 y) (Finset.mem_univ y₀)
  have h1 : vecMean q ≤ b * ∑ y, (q y - (Pi.single y₀ (q y₀) : S → ℝ) y) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun y _ ↦ ?_
    by_cases h : y = y₀
    · subst h
      simp [hy₀]
    · simp only [Pi.single_apply, h, ↓reduceIte, sub_zero]
      nlinarith [hS y y.2, hq.1 y]
  rw [Finset.sum_sub_distrib, hq.2, Fintype.sum_pi_single'] at h1
  have : vecMean q / b ≤ 1 - q y₀ := by
    rw [div_le_iff₀ hb]
    linarith
  linarith

/-- `KL(δ_{y₀}, Q) ≤ KL(δ_{y₀}, q)` when `q(y₀) ≤ Q(y₀)`. -/
lemma vecKL_single_le_of_le {y₀ : S} {q Q : S → ℝ} (hle : q y₀ ≤ Q y₀) :
    vecKL (Pi.single y₀ 1) Q ≤ vecKL (Pi.single y₀ 1) q := by
  by_cases h0 : 0 < q y₀
  · rw [vecKL_single (h0.trans_le hle), vecKL_single h0]
    exact ENNReal.ofReal_le_ofReal (Real.log_le_log (one_div_pos.mpr (h0.trans_le hle))
      (one_div_le_one_div_of_le h0 hle))
  · have : vecKL (Pi.single y₀ 1) q = ∞ := by
      unfold vecKL
      split_ifs with h
      · exact absurd (h y₀ (by simp)) h0
      · rfl
    rw [this]
    exact le_top

/-- `K_S(δ_0, ℓ) ≥ log (1 / (1 - ℓ/b))` on a support `S ⊆ (-∞, b]` containing `0`, for
`ℓ < b`. -/
lemma le_vecKs_single_zero {b : ℝ} (hS : ∀ y ∈ S, y ≤ b) {y₀ : S}
    (hy₀ : (y₀ : ℝ) = 0) {ℓ : ℝ} (hℓ : ℓ < b) :
    ENNReal.ofReal (Real.log (1 / (1 - ℓ / b))) ≤ vecKs S (Pi.single y₀ 1) ℓ := by
  have hb0 : 0 ≤ b := by have := hS y₀ y₀.2; rwa [hy₀] at this
  rcases hb0.eq_or_lt with rfl | hb
  · simp
  refine le_iInf₂ fun q hq ↦ ?_
  have hle : q y₀ ≤ 1 - ℓ / b :=
    (apply_le_one_sub_vecMean_div hS hy₀ hq.1).trans (by gcongr; exact hq.2)
  have hpos : 0 < 1 - ℓ / b := by rw [sub_pos, div_lt_one hb]; exact hℓ
  have hQ : 0 < (fun _ : S ↦ 1 - ℓ / b) y₀ := hpos
  refine le_trans ?_ (vecKL_single_le_of_le (Q := fun _ ↦ 1 - ℓ / b) hle)
  rw [vecKL_single hQ]

/-- `K_S(δ_0, ℓ) > 0` for `ℓ ∈ (0, b)` on a support `S ⊆ (-∞, b]` containing `0`. -/
lemma vecKs_single_zero_pos {b : ℝ} (hS : ∀ y ∈ S, y ≤ b) {y₀ : S}
    (hy₀ : (y₀ : ℝ) = 0) {ℓ : ℝ} (hℓ0 : 0 < ℓ) (hℓ : ℓ < b) :
    0 < vecKs S (Pi.single y₀ 1) ℓ := by
  have hb : 0 < b := hℓ0.trans hℓ
  have h1 : 0 < 1 - ℓ / b := by rw [sub_pos, div_lt_one hb]; exact hℓ
  have h2 : 1 - ℓ / b < 1 := by linarith [div_pos hℓ0 hb]
  exact (ENNReal.ofReal_pos.mpr (Real.log_pos (one_lt_one_div h1 h2))).trans_le
    (le_vecKs_single_zero hS hy₀ hℓ)

/-- Witness of `IsKLProj` in the binding case: on a support `S ⊆ (-∞, b]` containing `0` and `b`,
for `ℓ ∈ [0, b]`, the projection of `δ_0` on `{q ∈ 𝒫_S : m(q) ≥ ℓ}` is
`(1 - ℓ/b) δ_0 + (ℓ/b) δ_b`: every `q` of mean at least `ℓ` has `q(0) ≤ 1 - ℓ/b`. -/
lemma isKLProj_single_zero {b : ℝ} (hS : ∀ y ∈ S, y ≤ b) {y₀ y₁ : S}
    (hy₀ : (y₀ : ℝ) = 0) (hy₁ : (y₁ : ℝ) = b) {ℓ : ℝ} (hℓ0 : 0 ≤ ℓ) (hℓb : ℓ ≤ b) :
    IsKLProj (Pi.single y₀ 1) ℓ (Pi.single y₀ (1 - ℓ / b) + Pi.single y₁ (ℓ / b)) := by
  rcases (hℓ0.trans hℓb).eq_or_lt with rfl | hb
  · -- `b = 0`: `ℓ = 0` and the projection is `δ_0` itself
    obtain rfl : ℓ = 0 := le_antisymm hℓb hℓ0
    simpa using isKLProj_self (single_mem_probVecs y₀) (by rw [vecMean_single, hy₀, mul_zero])
  have hne : y₀ ≠ y₁ := fun h ↦ by
    have := congrArg Subtype.val h
    rw [hy₀, hy₁] at this
    exact hb.ne this
  have ht0 : 0 ≤ ℓ / b := div_nonneg hℓ0 hb.le
  have ht1 : 0 ≤ 1 - ℓ / b := by rw [sub_nonneg, div_le_one hb]; exact hℓb
  have hQ0 : (Pi.single y₀ (1 - ℓ / b) + Pi.single y₁ (ℓ / b) : S → ℝ) y₀ = 1 - ℓ / b := by
    simp [hne]
  have hmean : vecMean (Pi.single y₀ (1 - ℓ / b) + Pi.single y₁ (ℓ / b)) = ℓ := by
    rw [vecMean_add, vecMean_single, vecMean_single, hy₀, hy₁]
    field_simp
    ring
  refine ⟨⟨fun y ↦ ?_, ?_⟩, hmean.ge, fun q hq hqℓ ↦ ?_⟩
  · simp only [Pi.add_apply, Pi.single_apply]
    split_ifs <;> linarith
  · simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib, Fintype.sum_pi_single', Fintype.sum_pi_single']
    ring
  · refine vecKL_single_le_of_le ?_
    rw [hQ0]
    exact (apply_le_one_sub_vecMean_div hS hy₀ hq).trans (by gcongr)

/-- The value `K_S(δ_0, ℓ) = log (1 / (1 - ℓ/b))` for `ℓ ∈ [0, b)`, read on the projection. -/
lemma vecKs_single_zero {b : ℝ} (hS : ∀ y ∈ S, y ≤ b) {y₀ y₁ : S}
    (hy₀ : (y₀ : ℝ) = 0) (hy₁ : (y₁ : ℝ) = b) {ℓ : ℝ} (hℓ0 : 0 ≤ ℓ) (hℓb : ℓ < b) :
    vecKs S (Pi.single y₀ 1) ℓ = ENNReal.ofReal (Real.log (1 / (1 - ℓ / b))) := by
  have hb : 0 < b := hℓ0.trans_lt hℓb
  have hne : y₀ ≠ y₁ := fun h ↦ by
    have := congrArg Subtype.val h
    rw [hy₀, hy₁] at this
    exact hb.ne this
  have hpos : 0 < 1 - ℓ / b := by rw [sub_pos, div_lt_one hb]; exact hℓb
  have hQ0 : (Pi.single y₀ (1 - ℓ / b) + Pi.single y₁ (ℓ / b) : S → ℝ) y₀ = 1 - ℓ / b := by
    simp [hne]
  rw [vecKs_eq_of_isKLProj (isKLProj_single_zero hS hy₀ hy₁ hℓ0 hℓb.le),
    vecKL_single (by rw [hQ0]; exact hpos), hQ0]

/-- Witness: for `ν_a = δ_0` on a support `S ⊆ (-∞, b]` containing `0` and `b`,
`μ⋆ = μ ∈ (0, b)` and `c = 0`, the least `x > 0` with `J_a(x, 0; μ) ≥ 1` is `1/K_S(δ_0, μ)`. -/
lemma isLeast_driftConstant_single_zero {b : ℝ} (hS : ∀ y ∈ S, y ≤ b)
    {y₀ y₁ : S} (hy₀ : (y₀ : ℝ) = 0) (hy₁ : (y₁ : ℝ) = b) {𝓕 : Set (S → ℝ)}
    {l : ℝ} (hl : 0 ≤ l) (r' : S → ℝ) {μ : ℝ} (hμ0 : 0 < μ) (hμb : μ < b) :
    IsLeast {x : ℝ | 0 < x ∧ 1 ≤ programme 𝓕 l (Pi.single y₀ 1) r' μ x 0}
      (1 / (vecKs S (Pi.single y₀ 1) μ).toReal) := by
  have hb : 0 < b := hμ0.trans hμb
  set κ := Real.log (1 / (1 - μ / b)) with hκ
  have hK : vecKs S (Pi.single y₀ 1) μ = ENNReal.ofReal κ :=
    vecKs_single_zero hS hy₀ hy₁ hμ0.le hμb
  have hκpos : 0 < κ := by
    have h1 : 0 < 1 - μ / b := by rw [sub_pos, div_lt_one hb]; exact hμb
    exact Real.log_pos (one_lt_one_div h1 (by linarith [div_pos hμ0 hb]))
  rw [hK, ENNReal.toReal_ofReal hκpos.le]
  -- the pair `(Q, Q)`, `Q` the projection of `δ_0` at level `μ`, is an alternative of
  -- divergence `κ`
  have hQp := isKLProj_single_zero hS hy₀ hy₁ hμ0.le hμb.le
  set Q : S → ℝ := Pi.single y₀ (1 - μ / b) + Pi.single y₁ (μ / b) with hQ
  have hKL : vecKL (Pi.single y₀ 1) Q = ENNReal.ofReal κ := by
    rw [← vecKs_eq_of_isKLProj hQp, hK]
  have hpair : (Q, Q) ∈ altPairs 𝓕 l μ :=
    ⟨hQp.1, hQp.1, hQp.2.1, by rw [ipm_self]; exact hl⟩
  refine ⟨⟨by positivity, le_iInf₂ fun p hp ↦ ?_⟩, ?_⟩
  · -- `x = 1/κ` reaches `1`
    have hk : ENNReal.ofReal κ ≤ vecKL (Pi.single y₀ 1) p.1 :=
      hK ▸ iInf₂_le p.1 ⟨hp.1, hp.2.2.1⟩
    calc (1 : ℝ≥0∞) = ENNReal.ofReal (1 / κ) * ENNReal.ofReal κ := by
          rw [← ENNReal.ofReal_mul (by positivity), one_div, inv_mul_cancel₀ hκpos.ne',
            ENNReal.ofReal_one]
      _ ≤ ENNReal.ofReal (1 / κ) * vecKL (Pi.single y₀ 1) p.1 := by gcongr
      _ ≤ _ := le_self_add
  · -- every `x` of the set is at least `1/κ`
    rintro x ⟨hx, h1⟩
    have hJ : programme 𝓕 l (Pi.single y₀ 1) r' μ x 0 ≤ ENNReal.ofReal (x * κ) := by
      refine (iInf₂_le (Q, Q) hpair).trans ?_
      rw [hKL, ENNReal.ofReal_zero, zero_mul, add_zero, ← ENNReal.ofReal_mul hx.le]
    have : 1 ≤ x * κ := by
      have := h1.trans hJ
      rwa [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff (by positivity)] at this
    rw [div_le_iff₀ hκpos]
    linarith

/-- Known case: for `ν_a = δ_0`, `μ⋆ = μ ∈ (0, x_max)` and `c = 0` (no source data), the constant is
`D_a(0) = 1/K_S(ν_a, μ⋆)`, the constant of KL-UCB on `S`. -/
lemma driftConstant_single_zero {b : ℝ} (hS : ∀ y ∈ S, y ≤ b) {y₀ y₁ : S}
    (hy₀ : (y₀ : ℝ) = 0) (hy₁ : (y₁ : ℝ) = b) {𝓕 : Set (S → ℝ)} {l : ℝ}
    (hl : 0 ≤ l) (r' : S → ℝ) {μ : ℝ} (hμ0 : 0 < μ) (hμb : μ < b) :
    driftConstant 𝓕 l (Pi.single y₀ 1) r' μ 0 = 1 / (vecKs S (Pi.single y₀ 1) μ).toReal :=
  (isLeast_driftConstant_single_zero hS hy₀ hy₁ hl r' hμ0 hμb).csInf_eq

/-- Exclusion: the constant is not identically `0`: `D_a(0) = 1/K_S(δ_0, μ) > 0` in the setting of
`driftConstant_single_zero`. -/
lemma driftConstant_single_zero_pos {b : ℝ} (hS : ∀ y ∈ S, y ≤ b) {y₀ y₁ : S}
    (hy₀ : (y₀ : ℝ) = 0) (hy₁ : (y₁ : ℝ) = b) {𝓕 : Set (S → ℝ)} {l : ℝ}
    (hl : 0 ≤ l) (r' : S → ℝ) {μ : ℝ} (hμ0 : 0 < μ) (hμb : μ < b) :
    0 < driftConstant 𝓕 l (Pi.single y₀ 1) r' μ 0 := by
  have h := isLeast_driftConstant_single_zero (𝓕 := 𝓕) hS hy₀ hy₁ hl r' hμ0 hμb
  rw [driftConstant, h.csInf_eq]
  exact h.1.1

/-- `KL(r, q) ≥ 1 - q(supp r)` for probability vectors (from `log x ≤ x - 1`). -/
lemma one_sub_le_vecKL {r q : S → ℝ} (hr : r ∈ probVecs S) :
    ENNReal.ofReal (1 - ∑ y, if 0 < r y then q y else 0) ≤ vecKL r q := by
  unfold vecKL
  split_ifs with hc
  · refine ENNReal.ofReal_le_ofReal ?_
    have h1 : ∑ y, (if 0 < r y then r y else 0) = 1 := by
      rw [← hr.2]
      refine Finset.sum_congr rfl fun y _ ↦ ?_
      split_ifs with h
      · rfl
      · exact (le_antisymm (not_lt.mp h) (hr.1 y)).symm
    have h2 : 1 - ∑ y, (if 0 < r y then q y else 0) =
        ∑ y, (if 0 < r y then r y - q y else 0) := by
      rw [← h1, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun y _ ↦ ?_
      split_ifs <;> ring
    rw [h2]
    refine Finset.sum_le_sum fun y _ ↦ ?_
    split_ifs with h
    · have hqy := hc y h
      have hlog := Real.log_le_sub_one_of_pos (div_pos hqy h)
      have e : Real.log (r y / q y) = - Real.log (q y / r y) := by
        rw [← Real.log_inv, inv_div]
      have e2 : r y * (q y / r y - 1) = q y - r y := by field_simp
      have := mul_le_mul_of_nonneg_left hlog h.le
      rw [e]
      linarith
    · exact le_rfl
  · exact le_top

/-- `K_S(r, ℓ) > 0` when the law `r` is carried by `(-∞, b]` and `b < ℓ`: every `q` of
mean at least `ℓ` gives mass at most `(1 - ℓ)/(1 - b)` to the support of `r`. -/
lemma vecKs_pos_of_support_le (hS : ∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) {r : S → ℝ}
    (hr : r ∈ probVecs S) {b ℓ : ℝ} (hb : b < ℓ)
    (hsupp : ∀ y, 0 < r y → (y : ℝ) ≤ b) : 0 < vecKs S r ℓ := by
  rcases lt_or_ge b 1 with hb1 | hb1
  swap
  · -- `ℓ > 1`: no law on `S ⊆ [0,1]` has mean `ℓ`, and `K_S = ∞`
    refine ENNReal.zero_lt_top.trans_le (le_iInf₂ fun q hq ↦ ?_)
    exact absurd (hq.2.trans (vecMean_le_of_le (fun y hy ↦ (hS y hy).2) hq.1)) (by linarith)
  have hpos : 0 < ENNReal.ofReal ((ℓ - b) / (1 - b)) :=
    ENNReal.ofReal_pos.2 (div_pos (by linarith) (by linarith))
  refine hpos.trans_le (le_iInf₂ fun q hq ↦ (ENNReal.ofReal_le_ofReal ?_).trans
    (one_sub_le_vecKL hr))
  set qA := ∑ y, if 0 < r y then q y else 0 with hqA
  have hmean : vecMean q ≤ b * qA + (1 - qA) := by
    have h1 : vecMean q ≤ ∑ y, (if 0 < r y then b * q y else q y) := by
      refine Finset.sum_le_sum fun y _ ↦ ?_
      split_ifs with h
      · rw [mul_comm b]
        exact mul_le_mul_of_nonneg_left (hsupp y h) (hq.1.1 y)
      · exact mul_le_of_le_one_right (hq.1.1 y) (hS y y.2).2
    have h2 : ∑ y, (if 0 < r y then b * q y else q y) = b * qA + (1 - qA) := by
      have : ∀ y, (if 0 < r y then b * q y else q y) =
          q y + (b - 1) * (if 0 < r y then q y else 0) := by
        intro y; split_ifs <;> ring
      simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum, hq.1.2, hqA]
      ring
    linarith
  have hℓ := hq.2
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-! ### Exclusion for `Cons(N')` -/

/-- Exclusion: the learner `constArm a`, which pulls the arm `a` at every round, is not in
`Cons(N')` as soon as there is a second arm `b` and `S` has two points `y₀ < y₁`: on the pair
`(ν, ν) ∈ Θ`, with `ν a = δ_{y₀}` and `ν k = δ_{y₁}` for `k ≠ a`, the arm `a` is suboptimal and
`E[N_a(T)] = T`, so with `c = 1` the ratio `E[N_a(T)] / T` tends to `1`, not to `0` (the argument of
`not_isConsistent_constArm` of [INC-P003]). -/
lemma not_isLawConsistent_constArm [MeasurableSingletonClass α] {𝓕 : Set (S → ℝ)}
    {L : α → ℝ} (hL : ∀ k, 0 < L k) (N' : ℕ → α → ℕ) {a b : α} (hab : a ≠ b)
    {y₀ y₁ : ℝ} (hy₀ : y₀ ∈ S) (hy₁ : y₁ ∈ S) (hy : y₀ < y₁) :
    ¬ IsLawConsistent 𝓕 L N' (TransferAlgorithm.constArm a) := by
  classical
  intro h
  let g : α → ℝ := fun k ↦ if k = a then y₀ else y₁
  let ν : Kernel α ℝ := Kernel.deterministic g
    (Measurable.ite (measurableSet_singleton a) measurable_const measurable_const)
  have hν : ν ∈ supportBandits S α := by
    refine ⟨inferInstance, fun k ↦ ?_⟩
    rw [Kernel.deterministic_apply, Measure.dirac_apply' _ S.measurableSet.compl]
    by_cases hk : k = a <;> simp [g, hk, hy₀, hy₁]
  have : IsMarkovKernel ν := hν.1
  have hmean : ∀ k, (ν k)[id] = g k := fun k ↦ by
    simp only [ν, Kernel.deterministic_apply, integral_dirac, id]
  have hbdd : BddAbove (Set.range fun k ↦ (ν k)[id]) := ⟨y₁, by
    rintro _ ⟨k, rfl⟩
    dsimp only
    rw [hmean]
    by_cases hk : k = a <;> simp [g, hk, hy.le]⟩
  have hsub : (ν a)[id] < bestMean ν := by
    refine lt_of_lt_of_le ?_ (le_ciSup hbdd b)
    rw [hmean a, hmean b]
    simpa [g, Ne.symm hab] using hy
  have ht := h ν ν (self_mem_lawDriftClass hL hν) a hsub 1 one_pos
  simp only [integral_onlineCount_constArm, Real.rpow_one] at ht
  have h1 : Tendsto (fun T : ℕ ↦ (T : ℝ) / T) atTop (𝓝 1) :=
    tendsto_const_nhds.congr' ((eventually_ne_atTop 0).mono fun T hT ↦
      (div_self (Nat.cast_ne_zero.mpr hT)).symm)
  exact one_ne_zero (tendsto_nhds_unique h1 ht)

/-! ### The increase `ω_d` and the threshold `G^d` -/

lemma vecMean_smul (x : ℝ) (q : S → ℝ) : vecMean (x • q) = x * vecMean q := by
  simp only [vecMean, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- `ω_d(q') ≤ u` as soon as every admissible `q` has `m(q) - m(q') ≤ u`, for `u ≥ 0`. -/
lemma reachGain_le {𝓕 : Set (S → ℝ)} {l u : ℝ} {q' : S → ℝ} (hu : 0 ≤ u)
    (h : ∀ q ∈ probVecs S, ipm 𝓕 q q' ≤ l → vecMean q - vecMean q' ≤ u) :
    reachGain 𝓕 l q' ≤ u :=
  Real.sSup_le (by rintro m ⟨q, hq, hd, rfl⟩; exact h q hq hd) hu

/-- Known case: for the mean gap, `ω(q') = min (l, x_max - m(q'))` (the paper's value in
prop:threshold (b)): the mean moves by at most `l`, and not above `x_max`; the mixture
`(1 - t) q' + t δ_{x_max}` reaches the bound. -/
lemma reachGain_meanClass {b : ℝ} (hS : ∀ y ∈ S, y ≤ b) {y₁ : S} (hy₁ : (y₁ : ℝ) = b) {l : ℝ}
    (hl : 0 ≤ l) {q' : S → ℝ} (hq' : q' ∈ probVecs S) :
    reachGain (meanClass S) l q' = min l (b - vecMean q') := by
  set g := min l (b - vecMean q') with hg
  have hbm : 0 ≤ b - vecMean q' := sub_nonneg.mpr (vecMean_le_of_le hS hq')
  have hg0 : 0 ≤ g := le_min hl hbm
  have hup : ∀ q ∈ probVecs S, ipm (meanClass S) q q' ≤ l → vecMean q - vecMean q' ≤ g := by
    intro q hq hd
    rw [ipm_meanClass] at hd
    exact le_min ((le_abs_self _).trans hd) (by linarith [vecMean_le_of_le hS hq])
  refine le_antisymm (reachGain_le hg0 hup) ?_
  -- the mixture `q = (1 - t) q' + t δ_{x_max}`, `t = g / (b - m(q'))`, has `m(q) - m(q') = g`
  set t := g / (b - vecMean q') with ht
  have ht0 : 0 ≤ t := div_nonneg hg0 hbm
  have ht1 : t ≤ 1 := div_le_one_of_le₀ (min_le_right _ _) hbm
  have htg : t * (b - vecMean q') = g := by
    rcases hbm.eq_or_lt with h | h
    · rw [← h, mul_zero, hg, ← h, min_eq_right hl]
    · exact div_mul_cancel₀ _ h.ne'
  set q : S → ℝ := (1 - t) • q' + t • Pi.single y₁ 1 with hq
  have hqm : vecMean q - vecMean q' = g := by
    rw [hq, vecMean_add, vecMean_smul, vecMean_smul, vecMean_single, hy₁, ← htg]
    ring
  have hqp : q ∈ probVecs S := by
    refine ⟨fun y ↦ ?_, ?_⟩
    · simp only [hq, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      have := hq'.1 y
      split_ifs <;> nlinarith
    · simp only [hq, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, hq'.2, Fintype.sum_pi_single']
      ring
  refine le_csSup ⟨g, ?_⟩ ⟨q, hqp, ?_, hqm.symm⟩
  · rintro m ⟨q, hq, hd, rfl⟩
    exact hup q hq hd
  · rw [ipm_meanClass, hqm, abs_of_nonneg hg0]
    exact min_le_left _ _

/-- Exclusion: from the Dirac mass at `x_max`, no increase of the mean is possible,
`ω_d(δ_{x_max}) = 0`, whatever the budget `l ≥ 0` (a definition that forgot the constraint
`q ∈ 𝒫_S` would give `l`; for `l < 0` no `q` is admissible and the value is `sSup ∅ = 0`). -/
lemma reachGain_single_max {b : ℝ} (hS : ∀ y ∈ S, y ≤ b) {y₁ : S} (hy₁ : (y₁ : ℝ) = b)
    (𝓕 : Set (S → ℝ)) (l : ℝ) :
    reachGain 𝓕 l (Pi.single y₁ 1) = 0 := by
  have hup : ∀ q ∈ probVecs S, ipm 𝓕 q (Pi.single y₁ 1) ≤ l →
      vecMean q - vecMean (Pi.single y₁ (1 : ℝ)) ≤ 0 := fun q hq _ ↦ by
    rw [vecMean_single, one_mul, hy₁, sub_nonpos]
    exact vecMean_le_of_le hS hq
  exact le_antisymm (reachGain_le le_rfl hup) (reachGain_nonneg 𝓕 l (single_mem_probVecs y₁))

/-- For the mean gap, `G ≥ K_S(ν'_a, μ⋆ - L_a)`: a source law that reaches `μ⋆` has mean at least
`μ⋆ - L_a`. -/
lemma vecKs_le_thresholdKL_meanClass {l : ℝ} (hl : 0 ≤ l) (r' : S → ℝ) (μ : ℝ) :
    vecKs S r' (μ - l) ≤ thresholdKL (meanClass S) l r' μ := by
  refine le_iInf₂ fun q' hq' ↦ iInf₂_le q' ⟨hq'.1, ?_⟩
  have : reachGain (meanClass S) l q' ≤ l := reachGain_le hl fun q _ hd ↦
    (le_abs_self _).trans ((ipm_meanClass q q') ▸ hd)
  linarith [hq'.2]

/-- Exclusion: `G^d` is not identically `0`: for the mean gap, `ν'_a = δ_0` on a support
`S ⊆ (-∞, b]` containing `0`, and `μ⋆ - L_a ∈ (0, b)`, `G > 0`. -/
lemma thresholdKL_meanClass_single_zero_pos {b : ℝ} (hS : ∀ y ∈ S, y ≤ b)
    {y₀ : S} (hy₀ : (y₀ : ℝ) = 0) {l μ : ℝ} (hl : 0 ≤ l) (hμ0 : 0 < μ - l) (hμb : μ - l < b) :
    0 < thresholdKL (meanClass S) l (Pi.single y₀ 1) μ :=
  (vecKs_single_zero_pos hS hy₀ hμ0 hμb).trans_le (vecKs_le_thresholdKL_meanClass hl _ μ)

/-! ### The index of the algorithm -/

/-- Known case: without source data (`N'_k = 0`), the index is the KL-UCB index on `S`,
`sup {m(q) : q ∈ 𝒫_S, n KL(ν̂_k, q) ≤ δ}`, whatever the empirical source law and the drift bound
`l ≥ 0` (the paper's "without source data it is KL-UCB on `S`"). -/
lemma lawIndex_zero {𝓕 : Set (S → ℝ)} {l : ℝ} (hl : 0 ≤ l) (n : ℕ)
    (r r' : S → ℝ) (δ : ℝ) :
    lawIndex 𝓕 l n r 0 r' δ = sSup ((fun q ↦ ((vecMean q : ℝ) : EReal)) ''
      {q | q ∈ probVecs S ∧ (n : ℝ≥0∞) * vecKL r q ≤ ENNReal.ofReal δ}) := by
  unfold lawIndex
  congr 1
  ext x
  constructor
  · rintro ⟨p, ⟨hp1, -, -, hK⟩, rfl⟩
    refine ⟨p.1, ⟨hp1, ?_⟩, rfl⟩
    simpa using hK
  · rintro ⟨q, ⟨hq, hK⟩, rfl⟩
    exact ⟨(q, q), ⟨hq, hq, by rw [ipm_self]; exact hl, by simpa using hK⟩, rfl⟩

/-- Witness: the index is at least the empirical mean when the empirical laws are within the
drift bound (the pair `(ν̂_k, ν̂'_k)` is feasible, of divergence `0`). -/
lemma vecMean_le_lawIndex {𝓕 : Set (S → ℝ)} {l : ℝ} (n n' : ℕ) {r r' : S → ℝ} (δ : ℝ)
    (hr : r ∈ probVecs S) (hr' : r' ∈ probVecs S) (hd : ipm 𝓕 r r' ≤ l) :
    ((vecMean r : ℝ) : EReal) ≤ lawIndex 𝓕 l n r n' r' δ :=
  le_sSup ⟨(r, r'), ⟨hr, hr', hd, by simp [vecKL_self]⟩, rfl⟩

/-- Exclusion: a negative drift bound leaves no feasible pair, and the index is `-∞`. -/
lemma lawIndex_eq_bot {𝓕 : Set (S → ℝ)} {l : ℝ} (hl : l < 0) (n : ℕ) (r : S → ℝ) (n' : ℕ)
    (r' : S → ℝ) (δ : ℝ) : lawIndex 𝓕 l n r n' r' δ = ⊥ := by
  unfold lawIndex
  rw [sSup_eq_bot]
  rintro _ ⟨p, hp, rfl⟩
  exact absurd hp.2.2.1 (not_le.mpr (hl.trans_le (ipm_nonneg _ _ _)))

omit [MeasurableSpace α] in
/-- Known case: an arm without source data (`N'_k = 0`) gets the KL-UCB index on `S` computed from
its own pulls. -/
lemma statIndex_of_eq_zero {𝓕 : Set (S → ℝ)} {L : α → ℝ} {k : α}
    (hL : 0 ≤ L k) (t : ℕ) {z : (α → ℕ) × (α → S → ℕ) × (α → ℕ) × (α → S → ℕ)}
    (hz : z.1 k = 0) :
    statIndex 𝓕 L t z k = sSup ((fun q ↦ ((vecMean q : ℝ) : EReal)) ''
      {q | q ∈ probVecs S ∧ (z.2.2.1 k : ℝ≥0∞) * vecKL (empVec (z.2.2.2 k) (z.2.2.1 k)) q ≤
        ENNReal.ofReal (explorationRate t)}) := by
  unfold statIndex
  rw [hz]
  exact lawIndex_zero hL _ _ _ _

/-! ### The test classes -/

/-- Under `IsTestClass`-type bounds, the family whose supremum is `d_𝓕(q, q')` is bounded by
`∑_y |q(y) - q'(y)|`. -/
lemma abs_sum_le_of_mem_Icc {f q q' : S → ℝ} (hf : ∀ y, f y ∈ Set.Icc 0 1) :
    |∑ y, f y * (q y - q' y)| ≤ ∑ y, |q y - q' y| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ ↦ ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (abs_le.mpr ⟨by linarith [(hf y).1], (hf y).2⟩)

lemma bddAbove_ipm {𝓕 : Set (S → ℝ)} (h𝓕 : ∀ f ∈ 𝓕, ∀ y, f y ∈ Set.Icc 0 1) (q q' : S → ℝ) :
    BddAbove (Set.range fun f : 𝓕 ↦ |∑ y, (f : S → ℝ) y * (q y - q' y)|) :=
  ⟨∑ y, |q y - q' y|, by rintro _ ⟨f, rfl⟩; exact abs_sum_le_of_mem_Icc (h𝓕 f f.2)⟩

/-- Witness: the total-variation class is a test class. -/
lemma tvClass_isTestClass : IsTestClass (tvClass S) :=
  ⟨⟨0, fun _ ↦ by simp⟩, fun _ hf ↦ hf⟩

/-- Known case: `d_TV(q, q') = ∑_y (q(y) - q'(y))_+` for vectors of the same mass (probability
vectors, for instance) [INC-P002, lem:ipm (c)]: the supremum is attained at the indicator of
`{q > q'}`. -/
lemma ipm_tvClass {q q' : S → ℝ} (h : ∑ y, q y = ∑ y, q' y) :
    ipm (tvClass S) q q' = ∑ y, max (q y - q' y) 0 := by
  have hD : ∑ y, (q y - q' y) = 0 := by rw [Finset.sum_sub_distrib, h, sub_self]
  have hup : ∀ f : S → ℝ, (∀ y, f y ∈ Set.Icc 0 1) →
      |∑ y, f y * (q y - q' y)| ≤ ∑ y, max (q y - q' y) 0 := by
    intro f hf
    refine abs_le.mpr ⟨?_, Finset.sum_le_sum fun y _ ↦ ?_⟩
    · have h1 : ∑ y, f y * (q' y - q y) ≤ ∑ y, max (q' y - q y) 0 :=
        Finset.sum_le_sum fun y _ ↦ by
          rcases le_total 0 (q' y - q y) with h | h
          · rw [max_eq_left h]; exact mul_le_of_le_one_left h (hf y).2
          · rw [max_eq_right h]; exact mul_nonpos_of_nonneg_of_nonpos (hf y).1 h
      have h2 : ∑ y, max (q' y - q y) 0 = ∑ y, max (q y - q' y) 0 := by
        have : ∀ y, max (q' y - q y) 0 = max (q y - q' y) 0 - (q y - q' y) := fun y ↦ by
          rcases le_total 0 (q y - q' y) with h | h
          · rw [max_eq_left h, max_eq_right (by linarith)]; ring
          · rw [max_eq_right h, max_eq_left (by linarith)]; ring
        rw [Finset.sum_congr rfl fun y _ ↦ this y, Finset.sum_sub_distrib, hD, sub_zero]
      have h3 : ∑ y, f y * (q' y - q y) = - ∑ y, f y * (q y - q' y) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun y _ ↦ by ring
      linarith
    · rcases le_total 0 (q y - q' y) with h | h
      · rw [max_eq_left h]; exact mul_le_of_le_one_left h (hf y).2
      · rw [max_eq_right h]; exact mul_nonpos_of_nonneg_of_nonpos (hf y).1 h
  have : Nonempty (tvClass S) := tvClass_isTestClass.1.to_subtype
  refine le_antisymm (ciSup_le fun f ↦ hup f f.2) ?_
  -- the indicator of `{q > q'}`
  let f₀ : S → ℝ := fun y ↦ if 0 < q y - q' y then 1 else 0
  have hf₀ : f₀ ∈ tvClass S := fun y ↦ by simp only [f₀]; split_ifs <;> simp
  refine le_ciSup_of_le (bddAbove_ipm (fun _ hf ↦ hf) q q') ⟨f₀, hf₀⟩ ?_
  have : ∑ y, f₀ y * (q y - q' y) = ∑ y, max (q y - q' y) 0 :=
    Finset.sum_congr rfl fun y _ ↦ by
      simp only [f₀]
      split_ifs with h
      · rw [one_mul, max_eq_left h.le]
      · rw [zero_mul, max_eq_right (not_lt.mp h)]
  rw [this]
  exact le_abs_self _

/-- Exclusion for the total variation: two distinct Dirac masses are at distance `1`. -/
lemma ipm_tvClass_single {y₀ y₁ : S} (h : y₀ ≠ y₁) :
    ipm (tvClass S) (Pi.single y₀ 1) (Pi.single y₁ 1) = 1 := by
  rw [ipm_tvClass ((single_mem_probVecs y₀).2.trans (single_mem_probVecs y₁).2.symm),
    Finset.sum_eq_single y₀
      (fun y _ hy ↦ by
        rw [Pi.single_eq_of_ne hy, zero_sub]
        exact max_eq_right (neg_nonpos.mpr ((single_mem_probVecs y₁).1 y))) (by simp)]
  simp [h.symm]

/-- Witness of the mean property: the mean gap has it. -/
lemma hasMeanProperty_meanClass : HasMeanProperty (meanClass S) :=
  fun q _ q' _ ↦ (ipm_meanClass q q').ge

/-- Known case: on `S ⊆ [0,1]`, the total variation has the mean property (`y ↦ y` is a test
function of `[0,1]^S`). -/
lemma hasMeanProperty_tvClass (hS : ∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) :
    HasMeanProperty (tvClass S) := by
  intro q _ q' _
  rw [vecMean_sub]
  exact le_ciSup_of_le (bddAbove_ipm (fun _ hf ↦ hf) q q')
    ⟨fun y ↦ (y : ℝ), fun y ↦ hS y y.2⟩ le_rfl

/-- Exclusion: the class `{0}` has no mean property as soon as `S` has two points (it does not see
the mean gap of two Dirac masses). -/
lemma not_hasMeanProperty_zero {y₀ y₁ : S} (h : y₀ ≠ y₁) :
    ¬ HasMeanProperty ({0} : Set (S → ℝ)) := by
  intro hM
  have h1 := hM _ (single_mem_probVecs y₀) _ (single_mem_probVecs y₁)
  have h0 : ipm ({0} : Set (S → ℝ)) (Pi.single y₀ 1) (Pi.single y₁ 1) = 0 := by
    have : Unique ({0} : Set (S → ℝ)) := Set.uniqueSingleton _
    have hd : ((default : ({0} : Set (S → ℝ))) : S → ℝ) = 0 :=
      Set.mem_singleton_iff.mp (default : ({0} : Set (S → ℝ))).2
    rw [ipm, ciSup_unique, hd]
    simp
  rw [h0, vecMean_single, vecMean_single, one_mul, one_mul, abs_nonpos_iff, sub_eq_zero] at h1
  exact h (Subtype.ext h1)

/-- Witness: the Kolmogorov class is a test class. -/
lemma ksClass_isTestClass : IsTestClass (ksClass S) := by
  refine ⟨⟨_, 0, rfl⟩, ?_⟩
  rintro _ ⟨s, rfl⟩ y
  dsimp only
  split_ifs <;> simp

/-- Known case: `d_KS(q, q') = sup_s |F_q(s) - F_{q'}(s)|`, the Kolmogorov distance of the
distribution functions `F_q(s) = q((-∞, s])`. -/
lemma ipm_ksClass (q q' : S → ℝ) :
    ipm (ksClass S) q q' = ⨆ s : ℝ,
      |∑ y ∈ Finset.univ.filter (fun y : S ↦ (y : ℝ) ≤ s), q y -
        ∑ y ∈ Finset.univ.filter (fun y : S ↦ (y : ℝ) ≤ s), q' y| := by
  rw [ipm, ksClass, iSup_range' (fun f : S → ℝ ↦ |∑ y, f y * (q y - q' y)|)]
  refine iSup_congr fun s ↦ ?_
  rw [← Finset.sum_sub_distrib, Finset.sum_filter]
  refine congrArg _ (Finset.sum_congr rfl fun y _ ↦ ?_)
  split_ifs <;> simp

/-- Exclusion: the Kolmogorov distance separates two distinct Dirac masses. -/
lemma ipm_ksClass_single_pos {y₀ y₁ : S} (h : y₀ ≠ y₁) :
    0 < ipm (ksClass S) (Pi.single y₀ 1) (Pi.single y₁ 1) := by
  wlog hlt : (y₀ : ℝ) < y₁ generalizing y₀ y₁
  · have hlt' : (y₁ : ℝ) < y₀ :=
      lt_of_le_of_ne (not_lt.mp hlt) fun e ↦ h (Subtype.ext e.symm)
    have := this h.symm hlt'
    rwa [ipm, ← iSup_congr fun f ↦ ?_] at this
    rw [← abs_neg, ← Finset.sum_neg_distrib]
    exact congrArg _ (Finset.sum_congr rfl fun y _ ↦ by ring)
  -- the indicator of `(-∞, y₀]`
  let f : S → ℝ := fun y ↦ if (y : ℝ) ≤ y₀ then 1 else 0
  have hf : f ∈ ksClass S := ⟨y₀, rfl⟩
  have hsum : ∑ y, f y * ((Pi.single y₀ (1 : ℝ) : S → ℝ) y - (Pi.single y₁ (1 : ℝ) : S → ℝ) y) =
      1 := by
    rw [Finset.sum_eq_single y₀]
    · simp [f, h.symm]
    · intro y _ hy
      by_cases hy1 : y = y₁
      · subst hy1
        have hfy : f y = 0 := by simp only [f, not_le.mpr hlt, ↓reduceIte]
        rw [hfy, zero_mul]
      · simp [hy, hy1]
    · simp
  exact one_pos.trans_le (le_ciSup_of_le (bddAbove_ipm ksClass_isTestClass.2 _ _) ⟨f, hf⟩
    (by rw [hsum, abs_one]))

/-- Witness: the Wasserstein class is a test class (it contains `0`). -/
lemma w1Class_isTestClass : IsTestClass (w1Class S) := by
  refine ⟨⟨0, fun _ ↦ by simp, fun _ _ ↦ by simp⟩, fun f hf ↦ ?_⟩
  exact hf.1

/-- Known case: on `S ⊆ [0,1]`, `W₁(δ_y, δ_z) = |y - z|`: a `1`-Lipschitz test function moves by
at most `|y - z|`, and `y ↦ y` is one. -/
lemma ipm_w1Class_single (hS : ∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) (y₀ y₁ : S) :
    ipm (w1Class S) (Pi.single y₀ 1) (Pi.single y₁ 1) = |(y₀ : ℝ) - y₁| := by
  have hsum : ∀ f : S → ℝ,
      ∑ y, f y * ((Pi.single y₀ (1 : ℝ) : S → ℝ) y - (Pi.single y₁ (1 : ℝ) : S → ℝ) y) =
        f y₀ - f y₁ := by
    intro f
    simp only [mul_sub, Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have : Nonempty (w1Class S) := w1Class_isTestClass.1.to_subtype
  refine le_antisymm (ciSup_le fun f ↦ ?_) ?_
  · rw [hsum]
    exact f.2.2 y₀ y₁
  · refine le_ciSup_of_le (bddAbove_ipm w1Class_isTestClass.2 _ _)
      ⟨fun y ↦ (y : ℝ), fun y ↦ hS y y.2, fun _ _ ↦ le_rfl⟩ ?_
    rw [hsum]

/-- Exclusion: the indicator of a point `y₀` is not `1`-Lipschitz when another point `y₁` of `S`
is at distance less than `1` (so `W₁` is not the total variation). -/
lemma indicator_not_mem_w1Class {y₀ y₁ : S} (h : y₀ ≠ y₁) (hd : |(y₀ : ℝ) - y₁| < 1) :
    (Pi.single y₀ 1 : S → ℝ) ∉ w1Class S := by
  intro hf
  have := hf.2 y₀ y₁
  simp [h.symm] at this
  linarith

/-! ### The programme and the constant of an arm -/

/-- Witness: `J_a(x, c; μ)` is at most the value of any alternative pair. -/
lemma programme_le {𝓕 : Set (S → ℝ)} {l : ℝ} {r r' : S → ℝ} {μ : ℝ} (x c : ℝ)
    {p : (S → ℝ) × (S → ℝ)} (hp : p ∈ altPairs 𝓕 l μ) :
    programme 𝓕 l r r' μ x c ≤ ENNReal.ofReal x * vecKL r p.1 + ENNReal.ofReal c * vecKL r' p.2 :=
  iInf₂_le p hp

/-- Known case: without source data (`c = 0`), `J_a(x, 0; μ) = x K_S(ν_a, μ)`, the programme of
KL-UCB (the second law of a pair is free, and `q' = q` is admissible). -/
lemma programme_zero {𝓕 : Set (S → ℝ)} {l : ℝ} (hl : 0 ≤ l)
    (r r' : S → ℝ) (μ : ℝ) {x : ℝ} (hx : 0 < x) :
    programme 𝓕 l r r' μ x 0 = ENNReal.ofReal x * vecKs S r μ := by
  have hx0 : ENNReal.ofReal x ≠ 0 := (ENNReal.ofReal_pos.2 hx).ne'
  refine le_antisymm ?_ (le_iInf₂ fun p hp ↦ ?_)
  · rw [vecKs, ENNReal.mul_iInf_of_ne hx0 ENNReal.ofReal_ne_top]
    refine le_iInf fun q ↦ ?_
    rw [ENNReal.mul_iInf_of_ne hx0 ENNReal.ofReal_ne_top]
    refine le_iInf fun hq ↦ (programme_le x 0 (p := (q, q))
      ⟨hq.1, hq.1, hq.2, by rw [ipm_self]; exact hl⟩).trans ?_
    rw [ENNReal.ofReal_zero, zero_mul, add_zero]
  · calc ENNReal.ofReal x * vecKs S r μ ≤ ENNReal.ofReal x * vecKL r p.1 := by
          gcongr
          exact iInf₂_le p.1 ⟨hp.1, hp.2.2.1⟩
      _ = ENNReal.ofReal x * vecKL r p.1 + ENNReal.ofReal 0 * vecKL r' p.2 := by
          rw [ENNReal.ofReal_zero, zero_mul, add_zero]

/-- Exclusion: without alternative pairs (for example `μ > max S`), `J_a = ∞`. -/
lemma programme_eq_top {𝓕 : Set (S → ℝ)} {l : ℝ} {r r' : S → ℝ} {μ : ℝ}
    (h : altPairs 𝓕 l μ = ∅) (x c : ℝ) : programme 𝓕 l r r' μ x c = ∞ := by
  simp [programme, h]

/-- Known case: an arm `a` with `ν_a = δ_0`, on a support `S ⊆ (-∞, b]` containing `0` and
`b > 0`, with `μ⋆ ∈ (0, b)`, has `D_a(0) = 1/K_S(ν_a, μ⋆)`, the constant of KL-UCB. -/
lemma armConstant_zero_of_eq_dirac {b : ℝ} (hS : ∀ y ∈ S, y ≤ b) {y₀ y₁ : S}
    (hy₀ : (y₀ : ℝ) = 0) (hy₁ : (y₁ : ℝ) = b) {𝓕 : Set (S → ℝ)} {L : α → ℝ}
    {ν ν' : Kernel α ℝ} {a : α} (hL : 0 ≤ L a) (hνa : ν a = Measure.dirac (y₀ : ℝ))
    (hμ0 : 0 < bestMean ν) (hμb : bestMean ν < b) :
    armConstant 𝓕 L ν ν' a 0 = 1 / (vecKs S (lawVec S (ν a)) (bestMean ν)).toReal := by
  rw [armConstant, hνa, lawVec_dirac]
  exact driftConstant_single_zero hS hy₀ hy₁ hL _ hμ0 hμb

/-- Exclusion: the constant of an arm is not identically `0` (`D_a(0) > 0` in the setting of
`armConstant_zero_of_eq_dirac`). -/
lemma armConstant_zero_pos_of_eq_dirac {b : ℝ} (hS : ∀ y ∈ S, y ≤ b) {y₀ y₁ : S}
    (hy₀ : (y₀ : ℝ) = 0) (hy₁ : (y₁ : ℝ) = b) {𝓕 : Set (S → ℝ)} {L : α → ℝ}
    {ν ν' : Kernel α ℝ} {a : α} (hL : 0 ≤ L a) (hνa : ν a = Measure.dirac (y₀ : ℝ))
    (hμ0 : 0 < bestMean ν) (hμb : bestMean ν < b) :
    0 < armConstant 𝓕 L ν ν' a 0 := by
  rw [armConstant, hνa, lawVec_dirac]
  exact driftConstant_single_zero_pos hS hy₀ hy₁ hL _ hμ0 hμb

end Incognita.TransferBandits
