/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.Consistency
public import Incognita.BatchedBandits.KInf
public import LMLExplore.Identification.Task.RealLaws

/-! # Relations between the information models, the grids and consistency

The basic relations of [INC-P006, Theorem `thm:main`], in the generality of the definitions
(any action and feedback types, any `K`): the information models `𝓜_k` are nested and strictly
nested, `𝓜_⊤` is the set of families of batched learners, refining a grid preserves batching and
coarsening it preserves consistency at the batch ends, and on the sequential grid `𝖲_s` both
notions reduce to their sequential counterparts.

## Main statements

* `InfoModel.mono`: `𝓜_k ⊆ 𝓜_k'` for `k ≤ k'`.
* `exists_infoModel_and_not_infoModel`: `𝓜_k' ⊄ 𝓜_k` for `k < k'` (two distinct actions).
* `infoModel_top_iff`: a family is in `𝓜_⊤` iff each of its learners is batched on its grid.
* `isBatched_iff_exists_infoModel_top`: a learner is batched on `g` iff it is the component at
  `g` of a family in `𝓜_⊤`.
* `IsBatched.of_isFiner`: a learner batched on `g'` is batched on every grid finer than `g'`.
* `IsConsistentAtBatchEnds.of_isFiner`: consistency at the batch ends of `g` passes to every grid
  `g'` coarser than `g`.
* `isBatched_sequential_iff`: batched on `𝖲_s` iff the rewards are ignored in the rounds `< s`.
* `isConsistentAtBatchEnds_sequential_iff`: consistent at the batch ends of `𝖲_s` iff
  (sequentially) consistent.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Bandits Filter

open scoped Topology

namespace Incognita.BatchedBandits

section InfoModel

variable {𝓐 𝓨 : Type*} [MeasurableSpace 𝓐] [MeasurableSpace 𝓨] {K : ℕ}

/-- The information models are nested: `𝓜_k ⊆ 𝓜_k'` for `k ≤ k'` [INC-P006, Theorem
`thm:main`(i)]. Agreement of the grids on `t 1, …, t (ℓ + k')` implies agreement on
`t 1, …, t (ℓ + k)`. -/
lemma InfoModel.mono {k k' : ℕ∞} (hkk' : k ≤ k') {π : Grid K → Algorithm Unit 𝓐 𝓨}
    (h : InfoModel k π) : InfoModel k' π :=
  ⟨h.isBatched, fun g g' ℓ n hg hg' ht ↦ h.policy_eq g g' ℓ n hg hg' fun j hj hjk ↦
    ht j hj (hjk.trans (by gcongr))⟩

/-- Two grids with the same ends `t j` for every `j ≥ 1` are equal (both have `t 0 = 0`). -/
lemma Grid.eq_of_forall_one_le_t_eq {g g' : Grid K} (h : ∀ j, 1 ≤ j → g.t j = g'.t j) :
    g = g' := by
  refine Grid.ext (funext fun j ↦ ?_)
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [g.t_zero, g'.t_zero]
  · exact h j hj

/-- `𝓜_⊤` is the set of families of batched learners: condition (b) of `InfoModel ⊤` only compares
a grid with itself. -/
lemma infoModel_top_iff {π : Grid K → Algorithm Unit 𝓐 𝓨} :
    InfoModel ⊤ π ↔ ∀ g, IsBatched (π g) g := by
  refine ⟨fun h ↦ h.isBatched, fun h ↦ ⟨h, fun g g' ℓ n _ _ ht ↦ ?_⟩⟩
  rw [Grid.eq_of_forall_one_le_t_eq fun j hj ↦ ht j hj (by simp)]

/-- A learner is batched on `g` iff it is the component at `g` of a family in `𝓜_⊤`
[INC-P006, Theorem `thm:main`(i)]. For the direct implication, the family plays the learner on `g`
and the constant learner `Const_a` (batched on every grid) on the other grids; this needs an
action `a`. -/
lemma isBatched_iff_exists_infoModel_top [Nonempty 𝓐] {alg : Algorithm Unit 𝓐 𝓨} {g : Grid K} :
    IsBatched alg g ↔ ∃ π : Grid K → Algorithm Unit 𝓐 𝓨, InfoModel ⊤ π ∧ π g = alg := by
  classical
  refine ⟨fun h ↦ ?_, fun ⟨π, hπ, hg⟩ ↦ hg ▸ hπ.isBatched g⟩
  obtain ⟨a⟩ := ‹Nonempty 𝓐›
  refine ⟨fun g' ↦ if g' = g then alg else Algorithm.const (Measure.dirac a),
    infoModel_top_iff.mpr fun g' ↦ ?_, by simp⟩
  by_cases hg : g' = g
  · subst hg
    simpa only [ite_true] using h
  · simpa only [hg, ite_false] using isBatched_const (Measure.dirac a) g'

/-- The inclusion `𝓜_k ⊆ 𝓜_k'` is strict for `k < k'` [INC-P006, Theorem `thm:main`(i)]: with
`k = m` finite, the parity learner `Par^{(m)}` is in `𝓜_{m+1} ⊆ 𝓜_k'` and not in `𝓜_m`. -/
lemma exists_infoModel_and_not_infoModel [MeasurableSingletonClass 𝓐] {c₁ c₂ : 𝓐}
    (hc : c₁ ≠ c₂) {k k' : ℕ∞} (hkk' : k < k') :
    ∃ π : Grid K → Algorithm Unit 𝓐 𝓨, InfoModel k' π ∧ ¬ InfoModel k π := by
  obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp hkk'.ne_top
  refine ⟨fun g ↦ parityAlg m c₁ c₂ g, (infoModel_parityAlg m c₁ c₂).mono ?_,
    not_infoModel_parityAlg m hc⟩
  rw [Nat.cast_add, Nat.cast_one]
  exact Order.add_one_le_of_lt hkk'

end InfoModel

section Grids

variable {𝓐 𝓨 : Type*} [MeasurableSpace 𝓐] [MeasurableSpace 𝓨] {K : ℕ}

/-- If `g` is finer than `g'`, the end of the batch before the batch of a round `n` in `g'` is at
most the end of the batch before the batch of `n` in `g`: the batches of `g` start later. -/
lemma Grid.t_batchOf_sub_one_le_of_isFiner {g g' : Grid K} (hgg' : g.IsFiner g') (n : ℕ) :
    g'.t (g'.batchOf n - 1) ≤ g.t (g.batchOf n - 1) := by
  obtain ⟨m, hm⟩ := hgg' (Set.mem_range_self (g'.batchOf n - 1))
  rw [← hm]
  have hlt : g.t m < g.t (g.batchOf n) :=
    (hm ▸ g'.t_batchOf_sub_one_le n).trans_lt (g.lt_t_batchOf n)
  exact g.strictMono.monotone (by have := g.strictMono.lt_iff_lt.mp hlt; omega)

/-- Refining a grid preserves batching [INC-P006, Theorem `thm:main`(ii)]: a learner batched on
`g'` is batched on every grid `g` finer than `g'`. -/
lemma IsBatched.of_isFiner {g g' : Grid K} (hgg' : g.IsFiner g') {alg : Algorithm Unit 𝓐 𝓨}
    (h : IsBatched alg g') : IsBatched alg g :=
  fun n ↦ (h n).mono (Grid.t_batchOf_sub_one_le_of_isFiner hgg' n)

/-- On the sequential grid `𝖲_s`, a learner is batched iff its policies ignore the rewards in the
rounds `n < s` (the first batch) [INC-P006, Theorem `thm:main`(iii)]: from the round `s` on, the
batch before that of `n` ends at `n`, and every policy sees the rewards of its own history. -/
lemma isBatched_sequential_iff {s : ℕ} (hs : max 2 K ≤ s) {alg : Algorithm Unit 𝓐 𝓨} :
    IsBatched alg (Grid.sequential s hs) ↔ ∀ n < s, SeesRewardsUpTo alg n 0 := by
  constructor
  · intro h n hn
    have := h n
    rwa [Grid.sequential_batchOf_of_lt hn, Nat.sub_self, Grid.t_zero] at this
  · intro h n
    rcases lt_or_ge n s with hn | hn
    · rw [Grid.sequential_batchOf_of_lt hn, Nat.sub_self, Grid.t_zero]
      exact h n hn
    · rw [Grid.sequential_batchOf hn, show n - s + 2 - 1 = n - s + 1 by omega,
        Grid.sequential_t (by omega), show s + (n - s + 1) - 1 = n by omega]
      exact seesRewardsUpTo_self alg n

end Grids

section Consistency

variable {α : Type*} [MeasurableSpace α] [DecidableEq α] {K : ℕ}

/-- Consistency at the batch ends passes from a grid `g` to every grid `g'` coarser than `g`
[INC-P006, Theorem `thm:main`(ii)]: the ends of `g'` form a subsequence `t (φ ℓ)` of the ends of
`g`, with `φ` strictly increasing. -/
lemma IsConsistentAtBatchEnds.of_isFiner {g g' : Grid K} (hgg' : g.IsFiner g')
    {E : Set (Kernel α ℝ)} {alg : Algorithm Unit α ℝ} (h : IsConsistentAtBatchEnds alg g E) :
    IsConsistentAtBatchEnds alg g' E := by
  choose φ hφ using fun ℓ ↦ hgg' (Set.mem_range_self ℓ)
  have hmono : StrictMono φ := fun a b hab ↦
    g.strictMono.lt_iff_lt.mp (by rw [hφ, hφ]; exact g'.strictMono hab)
  intro ν hν _ c hc p hp
  refine ((h ν hν c hc p hp).comp hmono.tendsto_atTop).congr fun ℓ ↦ ?_
  simp only [Function.comp_apply, hφ]

/-- On the sequential grid `𝖲_s`, consistency at the batch ends implies (sequential)
consistency [INC-P006, Theorem `thm:main`(iii)]: every horizon `T ≥ s` is a batch end of `𝖲_s`,
and the expected regret is `∑_c Δ_c E[N_c(T)]`. -/
lemma IsConsistentAtBatchEnds.isConsistent_of_sequential [Finite α]
    [MeasurableSingletonClass α] {s : ℕ} (hs : max 2 K ≤ s) {E : Set (Kernel α ℝ)}
    {alg : Algorithm Unit α ℝ} (h : IsConsistentAtBatchEnds alg (Grid.sequential s hs) E) :
    LMLExplore.Bandits.IsConsistent alg E := by
  have := Fintype.ofFinite α
  refine (LMLExplore.Bandits.isConsistent_def _ _).mpr fun ν hν _ p hp ↦ ?_
  have hψ : Tendsto (fun n : ℕ ↦ n - s + 1) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b ↦ ⟨b + s, fun n hn ↦ by omega⟩
  have hc : ∀ c ∈ Finset.univ, Tendsto (fun n : ℕ ↦ gap ν c * ((∫ ω,
      (pullCount IT.action c n ω : ℝ) ∂(trajMeasure alg (Environment.bandit ν))) / (n : ℝ) ^ p))
      atTop (𝓝 0) := by
    intro c _
    rcases (gap_nonneg (ν := ν) (a := c)).eq_or_lt with h0 | hpos
    · simp only [← h0, zero_mul]
      exact tendsto_const_nhds
    · rw [← mul_zero (gap ν c)]
      refine Tendsto.const_mul _ (((h ν hν c hpos p hp).comp hψ).congr' ?_)
      filter_upwards [eventually_ge_atTop s] with n hn
      simp only [Function.comp_apply]
      rw [Grid.sequential_t (by omega), show s + (n - s + 1) - 1 = n by omega]
  have hsum := tendsto_finsetSum _ hc
  rw [Finset.sum_const_zero] at hsum
  refine hsum.congr fun n ↦ ?_
  rw [integral_regret_eq_sum_gap_mul_integral_pullCount (fun n ↦ IT.measurable_action n),
    Finset.sum_div]
  simp_rw [mul_div_assoc]

/-- On the sequential grid `𝖲_s`, a learner is consistent at the batch ends on `E` iff it is
(sequentially) consistent on `E` [INC-P006, Theorem `thm:main`(iii)]. The hypothesis `E ⊆ 𝒫` of
the paper is not needed. -/
lemma isConsistentAtBatchEnds_sequential_iff [Finite α] [MeasurableSingletonClass α] {s : ℕ}
    (hs : max 2 K ≤ s) {E : Set (Kernel α ℝ)} {alg : Algorithm Unit α ℝ} :
    IsConsistentAtBatchEnds alg (Grid.sequential s hs) E ↔ LMLExplore.Bandits.IsConsistent alg E :=
  ⟨fun h ↦ h.isConsistent_of_sequential hs, fun h ↦ h.isConsistentAtBatchEnds _⟩

end Consistency

/-! ### Relations found by gardening

`garden` records each relation below in `catalogue/relations.toml`. -/

namespace Relations

variable {𝓐 𝓨 : Type*} [MeasurableSpace 𝓐] [MeasurableSpace 𝓨] {K : ℕ}

/-- **Implication** [INC-P006, Theorem `thm:main`(ii) and (iii), first claims]: refining a grid
preserves batching (`IsBatched.of_isFiner`), and on `𝖲_s` batching means ignoring the rewards in
the rounds `< s` (`isBatched_sequential_iff`). Together they give the known case
`IsBatched.seesRewardsUpTo_zero`, with the same hypotheses: `𝖲_{t 1}` is finer than `g`, so a
learner batched on `g` ignores the rewards in the rounds `< t 1`, the first batch of `g`. -/
lemma isBatched_seesRewardsUpTo_zero_of_isBatched_sequential_iff {alg : Algorithm Unit 𝓐 𝓨}
    {g : Grid K} (h : IsBatched alg g) {n : ℕ} (hn : n < g.t 1) : SeesRewardsUpTo alg n 0 :=
  (isBatched_sequential_iff g.le_t_one).mp (h.of_isFiner (Grid.sequential_isFiner le_rfl)) n hn

section KInf

open LMLExplore LMLExplore.Identification
open scoped ENNReal unitInterval

/-- **Implication** [INC-P006, Proposition `prop:kinf`, (iii) implies (v)]: the bounds
`2 (μ - p)² ≤ kl(p, μ) ≤ 𝒦_inf(P, μ) ≤ log ((1 - p) / (1 - μ))`, `𝒦_inf(P, μ) < ∞`, for every law
`P` on `[0, 1]` of mean `p ≤ μ < 1` (item (iii), taken here as the hypothesis `h3`, in the form of
the frozen statement `Incognita.Statements.P006.kinf_bounds`) give item (v) at `P = ν_a`,
`μ = m⋆`: `0 < 2 Δ_a² ≤ K_a ≤ log ((1 - m_a) / (1 - m⋆)) < ∞` for `ν ∈ 𝒫` and a suboptimal arm `a`.
Same constants (`2`, the same logarithm), hypotheses no stronger (`m_a ≤ m⋆ < 1` on `𝒫`). The
proof of the frozen (v), `Incognita.P006.kinf_bounds_of_gap_pos`, already goes this way; here the
implication is stated with (iii) as a hypothesis, so it does not depend on how (iii) is proved. -/
lemma kinf_bounds_of_gap_pos_of_kinf_bounds
    (h3 : ∀ {P : Measure ℝ}, P ∈ unitLaws → ∀ {μ : ℝ}, ∫ x, id x ∂P ≤ μ → μ < 1 →
      ENNReal.ofReal (2 * (μ - ∫ x, id x ∂P) ^ 2) ≤ klBer (∫ x, id x ∂P) μ ∧
        klBer (∫ x, id x ∂P) μ ≤ LMLExplore.Bandits.dInf unitLaws P μ ∧
        LMLExplore.Bandits.dInf unitLaws P μ ≤
          ENNReal.ofReal (Real.log ((1 - ∫ x, id x ∂P) / (1 - μ))) ∧
        LMLExplore.Bandits.dInf unitLaws P μ ≠ ⊤)
    {α : Type*} [Finite α] [MeasurableSpace α] {ν : Kernel α ℝ} (hν : ν ∈ unitBandits α) {a : α}
    (ha : 0 < gap ν a) :
    0 < ENNReal.ofReal (2 * gap ν a ^ 2) ∧
      ENNReal.ofReal (2 * gap ν a ^ 2) ≤
        LMLExplore.Bandits.dInf unitLaws (ν a) (⨆ b, ∫ x, id x ∂(ν b)) ∧
      LMLExplore.Bandits.dInf unitLaws (ν a) (⨆ b, ∫ x, id x ∂(ν b)) ≤
        ENNReal.ofReal
          (Real.log ((1 - ∫ x, id x ∂(ν a)) / (1 - ⨆ b, ∫ x, id x ∂(ν b)))) ∧
      LMLExplore.Bandits.dInf unitLaws (ν a) (⨆ b, ∫ x, id x ∂(ν b)) ≠ ⊤ := by
  have hle : ∫ x, id x ∂(ν a) ≤ ⨆ b, ∫ x, id x ∂(ν b) :=
    le_ciSup (Finite.bddAbove_range fun b ↦ ∫ x, id x ∂(ν b)) a
  obtain ⟨h1, h2, h3, h4⟩ := h3 (hν.1 a) hle hν.2
  exact ⟨ENNReal.ofReal_pos.2 (by positivity), h1.trans h2, h3, h4⟩

/-- **Implication** [INC-P006, Proposition `prop:kinf`(i), general form
`dInf_unitLaws_eq_top_of_one_le`] gives LMLExplore's
`LMLExplore.Bandits.dInf_range_bernoulliMeasure_of_one_le` [LS, Table 16.1] (to be checked), with
the same hypotheses (any `P`, `m ≥ 1`): the Bernoulli laws are laws on `[0, 1]`, and `dInf` is
antitone in the class (`dInf_anti`), so `∞ = 𝒦_inf(P, m) ≤ d_inf^{Ber}(P, m)`. -/
lemma dInf_range_bernoulliMeasure_of_one_le_of_dInf_unitLaws_eq_top_of_one_le (P : Measure ℝ)
    {m : ℝ} (hm : 1 ≤ m) :
    LMLExplore.Bandits.dInf (Set.range fun q : I ↦ Ber((1 : ℝ), 0, q)) P m = ∞ :=
  top_le_iff.1 ((dInf_unitLaws_eq_top_of_one_le P hm).symm.le.trans
    (dInf_anti (Set.range_subset_iff.2 bernoulliMeasure_mem_unitLaws) P m))

/-- **Same object**: the set `𝓜 = unitLaws` of laws on `[0, 1]` [INC-P006, Definition
`def:instance`] is LMLExplore's `unitIntervalLaws`, a set of `ProbabilityMeasure ℝ`, seen in
`Measure ℝ`. -/
lemma unitLaws_eq_image_unitIntervalLaws :
    unitLaws = ProbabilityMeasure.toMeasure '' unitIntervalLaws := by
  ext Q
  constructor
  · intro hQ
    exact ⟨⟨Q, hQ.1⟩, mem_unitIntervalLaws_iff.2 hQ.2, rfl⟩
  · rintro ⟨Q', hQ', rfl⟩
    exact ⟨inferInstance, mem_unitIntervalLaws_iff.1 hQ'⟩

/-- LMLExplore's transportation cost `K⁺(P, μ)` over the laws on `[0, 1]` (competitors of mean
`≥ μ`) is at most `𝒦_inf(P, μ) = dInf unitLaws P μ` (competitors of mean `> μ`). -/
lemma kInfUpper_unitIntervalLaws_le_dInf_unitLaws (P : ProbabilityMeasure ℝ) (μ : ℝ) :
    kInfUpper ProbabilityMeasure.toMeasure unitIntervalLaws (fun Q ↦ (Q : Measure ℝ)[id]) P μ ≤
      LMLExplore.Bandits.dInf unitLaws (P : Measure ℝ) μ :=
  LMLExplore.Bandits.le_dInf_iff.2 fun Q hQ hm ↦
    kInfUpper_le (κ := ProbabilityMeasure.toMeasure) (m := fun Q ↦ (Q : Measure ℝ)[id])
      (y := (⟨Q, hQ.1⟩ : ProbabilityMeasure ℝ)) (mem_unitIntervalLaws_iff.2 hQ.2) hm.le

/-- **Duplicate**: `klBer_le_dInf_unitLaws` [INC-P006, Proposition `prop:kinf`(iii), lower bound]
repeats the computation of LMLExplore's `klBer_le_kInfUpper_of_subset_unitIntervalLaws` (data
processing to the reward, `klBer_integral_le_klDiv`, then the monotonicity of `kl(p, ·)`); proved
again, with the same type, from it and `kInfUpper_unitIntervalLaws_le_dInf_unitLaws`. -/
lemma klBer_le_dInf_unitLaws_of_klBer_le_kInfUpper {P : Measure ℝ} (hP : P ∈ unitLaws) {μ : ℝ}
    (hpμ : P[id] ≤ μ) : klBer P[id] μ ≤ LMLExplore.Bandits.dInf unitLaws P μ :=
  (klBer_le_kInfUpper_of_subset_unitIntervalLaws (P := ⟨P, hP.1⟩) subset_rfl
    (mem_unitIntervalLaws_iff.2 hP.2) hpμ).trans
    (kInfUpper_unitIntervalLaws_le_dInf_unitLaws ⟨P, hP.1⟩ μ)

end KInf

end Relations

end Incognita.BatchedBandits
