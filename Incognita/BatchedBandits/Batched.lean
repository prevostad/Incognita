/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.Grid
public import LeanMachineLearning.SequentialLearning.Algorithms.RandomSampling.Basic
public import LeanMachineLearning.SequentialLearning.Deterministic

/-! # Batched learners and information models

A learner is an LML algorithm `alg : Algorithm Unit 𝓐 𝓨` (no observation): its policy at the
round `n` (rounds from `0`) is a Markov kernel `alg.policy n` from the histories of the `n` rounds
`0, …, n - 1` to the actions [INC-P006, Definition `def:learner`; the paper's `π_t` is
`alg.policy (t - 1)`].

The closest notions in the literature: batched learners on a grid chosen by the learner [PRCS16],
and batch-aware and batch-oblivious learners on a grid imposed by the environment [QW26] (the
information models `𝓜_⊤` and `𝓜_0` respectively).

## Main definitions

* `Incognita.BatchedBandits.SeesRewardsUpTo alg n r`: the policy of the round `n` depends on the
  history only through the actions and the rewards of the rounds `< r` (the paper's "`π_{n+1}`
  sees the rewards up to `r`", Definition `def:batched`; it **ignores the rewards** for `r = 0`).
* `Incognita.BatchedBandits.IsBatched alg g`: `alg` is batched on the grid `g`: during batch
  `ℓ + 1` it sees only the rewards of the rounds `< t ℓ` [INC-P006, Definition `def:batched`].
* `Incognita.BatchedBandits.InfoModel k π`: the family of learners `π : Grid K → Algorithm …`, one
  per grid, belongs to the information model `𝓜_k`, `k : ℕ∞` [INC-P006, Definition
  `def:infomodel`].
* `Incognita.BatchedBandits.reactAlg c₁ c₂`, `Incognita.BatchedBandits.parityAlg k c₁ c₂ g`: the
  learners `React` and `Par^{(k),g}` of [INC-P006, Definition `def:exlearners`]. The learner
  `Const_c` is LML's `Algorithm.const (Measure.dirac c)`.
* `Incognita.BatchedBandits.firstRewardAlg c₁ c₂ g`: a learner batched on `g` that uses the
  rewards (after the first batch it pulls `c₂` or `c₁` according to the reward of the round `0`).

## Main statements

* `seesRewardsUpTo_const`, `isBatched_const`: a learner that ignores the history is batched on
  every grid; `infoModel_const`: the grid-independent family of such a learner is in every `𝓜_k`.
* `seesRewardsUpTo_self`: every policy sees all the rewards of its history (sequential learners).
* `IsBatched.seesRewardsUpTo_zero`: in the first batch a batched learner ignores the rewards.
* `isBatched_firstRewardAlg`, `not_seesRewardsUpTo_zero_firstRewardAlg`,
  `infoModel_firstRewardAlg`: a batched learner that does not ignore the rewards, whose family is
  in `𝓜_0`.
* `infoModel_const_iff`: a family that does not depend on the grid is in `𝓜_k` if and only if its
  learner is batched on every grid (grid-oblivious, "doubly anytime" learners).
* `not_isBatched_reactAlg`: `React`, which reacts at round `1` to the reward of round `0`, is
  batched on no grid; `not_infoModel_parityAlg`: `Par^{(k)}`, which reads `t (ℓ + 1 + k)` during
  batch `ℓ + 1`, is not in `𝓜_k`; `infoModel_parityAlg`: it is in `𝓜_{k+1}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning

namespace Incognita.BatchedBandits

variable {𝓐 𝓨 : Type*} [MeasurableSpace 𝓐] [MeasurableSpace 𝓨] {K : ℕ}

/-- The policy of the round `n` (rounds from `0`) **sees the rewards up to `r`**
[INC-P006, Definition `def:batched`]: it takes the same value on two histories of the rounds
`0, …, n - 1` that have the same actions and the same rewards at the rounds `i < r`. In the paper's
1-based rounds, this is "`π_{n+1}` sees the rewards up to `r`" (the rewards `y_s`, `s ≤ r`). For
`r = 0` the policy **ignores the rewards**. -/
def SeesRewardsUpTo (alg : Algorithm Unit 𝓐 𝓨) (n r : ℕ) : Prop :=
  ∀ h h' : Hist Unit 𝓐 𝓨 n, (∀ i, (h i).action = (h' i).action) →
    (∀ i : Fin n, (i : ℕ) < r → (h i).feedback = (h' i).feedback) →
    alg.policy n (h, ()) = alg.policy n (h', ())

/-- A learner is **batched** on a grid `g` [INC-P006, Definition `def:batched`]: at every round `n`
(rounds from `0`), its policy sees the rewards up to the end `t (b - 1)` of the batch before the
batch `b = g.batchOf n` of `n`, that is, during batch `ℓ + 1` it uses the rewards of the rounds
`< t ℓ` only, its own past actions and its internal randomisation. -/
def IsBatched (alg : Algorithm Unit 𝓐 𝓨) (g : Grid K) : Prop :=
  ∀ n, SeesRewardsUpTo alg n (g.t (g.batchOf n - 1))

/-- A family `π : Grid K → Algorithm Unit 𝓐 𝓨` of learners, one per grid, belongs to the
**information model** `𝓜_k`, `k : ℕ∞` [INC-P006, Definition `def:infomodel`] if
(a) every `π g` is batched on `g`, and
(b) for all grids `g, g'`, every `ℓ` and every round `n` in batch `ℓ + 1` of both `g` and `g'`, if
`g` and `g'` have the same ends `t j` for `1 ≤ j ≤ ℓ + k`, then `π g` and `π g'` have the same
policy at the round `n`.
For `k = ⊤` the hypothesis of (b) forces `g = g'`, so `𝓜_⊤` is the set of families of batched
learners; `𝓜_0` knows nothing of the grid ahead. -/
structure InfoModel (k : ℕ∞) (π : Grid K → Algorithm Unit 𝓐 𝓨) : Prop where
  /-- (a) Each learner of the family is batched on its grid. -/
  isBatched : ∀ g, IsBatched (π g) g
  /-- (b) During batch `ℓ + 1`, the policy depends on the grid only through `t 1, …, t (ℓ + k)`. -/
  policy_eq : ∀ (g g' : Grid K) (ℓ n : ℕ), g.batchOf n = ℓ + 1 → g'.batchOf n = ℓ + 1 →
    (∀ j : ℕ, 1 ≤ j → (j : ℕ∞) ≤ ℓ + k → g.t j = g'.t j) → (π g).policy n = (π g').policy n

/-! ### Basic facts -/

lemma SeesRewardsUpTo.mono {alg : Algorithm Unit 𝓐 𝓨} {n r r' : ℕ} (h : SeesRewardsUpTo alg n r)
    (hrr' : r ≤ r') : SeesRewardsUpTo alg n r' :=
  fun h₁ h₂ ha hy ↦ h h₁ h₂ ha fun i hi ↦ hy i (hi.trans_le hrr')

/-- **Known case**: every policy sees all the rewards of its own history, the rounds `< n`: a
learner with no constraint is a sequential learner. -/
lemma seesRewardsUpTo_self (alg : Algorithm Unit 𝓐 𝓨) (n : ℕ) : SeesRewardsUpTo alg n n := by
  intro h h' ha hy
  congr 2
  funext i
  have hobs : (h i).obs = (h' i).obs := rfl
  rw [← Round.mk_obs_action_feedback (h i), ← Round.mk_obs_action_feedback (h' i), hobs, ha i,
    hy i i.2]

/-- **Witness**: a learner that samples its action from a fixed law ignores the history. -/
lemma seesRewardsUpTo_const (μ : Measure 𝓐) [IsProbabilityMeasure μ] (n r : ℕ) :
    SeesRewardsUpTo (Algorithm.const μ : Algorithm Unit 𝓐 𝓨) n r :=
  fun _ _ _ _ ↦ rfl

/-- A learner whose policies all ignore the rewards is batched on every grid. -/
lemma isBatched_of_forall_seesRewardsUpTo_zero {alg : Algorithm Unit 𝓐 𝓨}
    (h : ∀ n, SeesRewardsUpTo alg n 0) (g : Grid K) : IsBatched alg g :=
  fun n ↦ (h n).mono (Nat.zero_le _)

/-- **Witness** [INC-P006, Proposition `prop:witnesses`(c)]: `Const` (and every learner sampling
from a fixed law) is batched on every grid. -/
lemma isBatched_const (μ : Measure 𝓐) [IsProbabilityMeasure μ] (g : Grid K) :
    IsBatched (Algorithm.const μ : Algorithm Unit 𝓐 𝓨) g :=
  isBatched_of_forall_seesRewardsUpTo_zero (seesRewardsUpTo_const μ · 0) g

/-- Batched learners in the `ℓ`-form: during batch `ℓ + 1`, the policy sees the rewards up to
`t ℓ`. -/
lemma isBatched_iff {alg : Algorithm Unit 𝓐 𝓨} {g : Grid K} :
    IsBatched alg g ↔ ∀ ℓ n, g.t ℓ ≤ n → n < g.t (ℓ + 1) → SeesRewardsUpTo alg n (g.t ℓ) := by
  constructor
  · intro h ℓ n h1 h2
    have hb := (g.batchOf_eq_iff).mpr ⟨h1, h2⟩
    simpa [hb] using h n
  · intro h n
    have h1 := g.one_le_batchOf n
    have hb : g.batchOf n = (g.batchOf n - 1) + 1 := by omega
    exact h _ n (g.t_batchOf_sub_one_le n) (by rw [← hb]; exact g.lt_t_batchOf n)

/-- **Known case**: in the first batch, the rounds `n < t 1`, a batched learner ignores the
rewards. -/
lemma IsBatched.seesRewardsUpTo_zero {alg : Algorithm Unit 𝓐 𝓨} {g : Grid K}
    (h : IsBatched alg g) {n : ℕ} (hn : n < g.t 1) : SeesRewardsUpTo alg n 0 := by
  have := isBatched_iff.mp h 0 n (by simp) hn
  rwa [g.t_zero] at this

/-- During the rounds `n < t (j + 1)`, a batched learner sees at most the rewards of the rounds
`< t j` (the case `j = 0` is `IsBatched.seesRewardsUpTo_zero`). -/
lemma IsBatched.seesRewardsUpTo_of_lt {alg : Algorithm Unit 𝓐 𝓨} {g : Grid K}
    (h : IsBatched alg g) {n j : ℕ} (hn : n < g.t (j + 1)) : SeesRewardsUpTo alg n (g.t j) := by
  refine (h n).mono (g.strictMono.monotone ?_)
  have h1 := g.t_batchOf_sub_one_le n
  have h2 : g.batchOf n - 1 < j + 1 := g.strictMono.lt_iff_lt.mp (h1.trans_lt hn)
  omega

/-- **Witness** [INC-P006, Proposition `prop:witnesses`(d)]: the family that plays the same learner
`Const` on every grid is in every information model, in particular in `𝓜_0`. -/
lemma infoModel_const (μ : Measure 𝓐) [IsProbabilityMeasure μ] (k : ℕ∞) :
    InfoModel k (fun _ : Grid K ↦ (Algorithm.const μ : Algorithm Unit 𝓐 𝓨)) :=
  ⟨fun g ↦ isBatched_const μ g, fun _ _ _ _ _ _ _ ↦ rfl⟩

/-- **Known case**: a family that does not depend on the grid (a grid-oblivious learner) is in
`𝓜_k` if and only if its learner is batched on every grid. -/
lemma infoModel_const_iff {alg : Algorithm Unit 𝓐 𝓨} {k : ℕ∞} :
    InfoModel k (fun _ : Grid K ↦ alg) ↔ ∀ g : Grid K, IsBatched alg g :=
  ⟨fun h ↦ h.isBatched, fun h ↦ ⟨h, fun _ _ _ _ _ _ _ ↦ rfl⟩⟩

/-! ### The learner `React`: batched on no grid -/

/-- The action of `React` at the round `n` (rounds from `0`): `c₂` at the round `1` if the reward
of the round `0` is below `1 / 2`, and `c₁` otherwise. -/
noncomputable def reactNext (c₁ c₂ : 𝓐) (n : ℕ) (h : Hist Unit 𝓐 ℝ n × Unit) : 𝓐 :=
  if hn : n = 1 then (if (h.1 ⟨0, by omega⟩).feedback < 1 / 2 then c₂ else c₁) else c₁

lemma measurable_reactNext (c₁ c₂ : 𝓐) (n : ℕ) : Measurable (reactNext c₁ c₂ n) := by
  unfold reactNext
  by_cases hn : n = 1
  · subst hn
    simp only [dite_true]
    refine Measurable.ite ?_ measurable_const measurable_const
    exact measurableSet_lt (Round.measurable_feedback.comp
      ((measurable_pi_apply _).comp measurable_fst)) measurable_const
  · simp only [hn, dite_false]
    exact measurable_const

/-- The learner `React` [INC-P006, Definition `def:exlearners`, rounds from `0`]: it pulls `c₁`,
except at the round `1` (the paper's round `2`), where it pulls `c₂` if the reward of the round `0`
is below `1 / 2`. -/
noncomputable def reactAlg (c₁ c₂ : 𝓐) : Algorithm Unit 𝓐 ℝ :=
  Algorithm.deterministic (reactNext c₁ c₂) (measurable_reactNext c₁ c₂)

/-- **Exclusion** [INC-P006, Proposition `prop:witnesses`(c)]: `React` reacts at the round `1` to
the reward of the round `0`, inside the first batch (`t 1 ≥ 2`): it is batched on no grid. -/
lemma not_isBatched_reactAlg [MeasurableSingletonClass 𝓐] {c₁ c₂ : 𝓐} (hc : c₁ ≠ c₂)
    (g : Grid K) : ¬ IsBatched (reactAlg c₁ c₂) g := by
  intro h
  have h1 : SeesRewardsUpTo (reactAlg c₁ c₂) 1 0 :=
    h.seesRewardsUpTo_zero (lt_of_lt_of_le one_lt_two g.two_le_t_one)
  have := h1 (fun _ ↦ ((), c₁, 1)) (fun _ ↦ ((), c₁, 0)) (fun _ ↦ rfl)
    (fun i hi ↦ absurd hi (Nat.not_lt_zero _))
  simp only [reactAlg, Algorithm.deterministic_policy, Kernel.deterministic_apply, reactNext,
    dite_true, Round.feedback_mk] at this
  norm_num at this
  exact hc ((dirac_eq_dirac_iff).mp this)

/-! ### A batched learner that uses the rewards: in `𝓜_0` -/

/-- The action of the learner `firstRewardAlg c₁ c₂ g` at the round `n`: `c₁` during the first
batch (`n < t 1`); afterwards, `c₂` if the reward of the round `0` is below `1 / 2`, and `c₁`
otherwise. -/
noncomputable def firstRewardNext (c₁ c₂ : 𝓐) (g : Grid K) (n : ℕ) (h : Hist Unit 𝓐 ℝ n × Unit) :
    𝓐 :=
  if hn : g.t 1 ≤ n then
    (if (h.1 ⟨0, lt_of_lt_of_le (lt_of_lt_of_le zero_lt_two g.two_le_t_one) hn⟩).feedback < 1 / 2
      then c₂ else c₁)
  else c₁

lemma measurable_firstRewardNext (c₁ c₂ : 𝓐) (g : Grid K) (n : ℕ) :
    Measurable (firstRewardNext c₁ c₂ g n) := by
  unfold firstRewardNext
  by_cases hn : g.t 1 ≤ n
  · simp only [hn, dite_true]
    refine Measurable.ite ?_ measurable_const measurable_const
    exact measurableSet_lt (Round.measurable_feedback.comp
      ((measurable_pi_apply _).comp measurable_fst)) measurable_const
  · simp only [hn, dite_false]
    exact measurable_const

/-- A deterministic learner, batched on the grid `g`, that uses the rewards: it pulls `c₁` during
the first batch, then `c₂` or `c₁` according to the reward of the round `0` (which it sees from the
end `t 1` of the first batch on). It plays the role of the paper's frozen leader `FL^g`
[INC-P006, Definition `def:exlearners`] as a witness of `IsBatched` and `𝓜_0` that does not ignore
the rewards. -/
noncomputable def firstRewardAlg (c₁ c₂ : 𝓐) (g : Grid K) : Algorithm Unit 𝓐 ℝ :=
  Algorithm.deterministic (firstRewardNext c₁ c₂ g) (measurable_firstRewardNext c₁ c₂ g)

/-- **Witness** of `IsBatched`: `firstRewardAlg c₁ c₂ g` is batched on `g`. -/
lemma isBatched_firstRewardAlg (c₁ c₂ : 𝓐) (g : Grid K) :
    IsBatched (firstRewardAlg c₁ c₂ g) g := by
  intro n h h' _ hy
  simp only [firstRewardAlg, Algorithm.deterministic_policy, Kernel.deterministic_apply]
  congr 1
  unfold firstRewardNext
  by_cases hn : g.t 1 ≤ n
  · simp only [hn, dite_true]
    have hb : 2 ≤ g.batchOf n := by
      by_contra hb
      have h1 : g.batchOf n = 0 + 1 := by have := g.one_le_batchOf n; omega
      have := (g.batchOf_eq_iff.mp h1).2
      rw [zero_add] at this
      omega
    have ht : 0 < g.t (g.batchOf n - 1) :=
      lt_of_lt_of_le (by have := g.two_le_t_one; omega)
        (g.strictMono.monotone (by omega : 1 ≤ g.batchOf n - 1))
    rw [hy ⟨0, _⟩ ht]
  · simp only [hn, dite_false]

/-- **Witness**: `firstRewardAlg c₁ c₂ g` does not ignore the rewards at the round `t 1` (the
paper's round `t_1 + 1`), as the paper says of `FL^g`
[INC-P006, Proposition `prop:witnesses`(c)]. -/
lemma not_seesRewardsUpTo_zero_firstRewardAlg [MeasurableSingletonClass 𝓐] {c₁ c₂ : 𝓐}
    (hc : c₁ ≠ c₂) (g : Grid K) : ¬ SeesRewardsUpTo (firstRewardAlg c₁ c₂ g) (g.t 1) 0 := by
  intro h
  have := h (fun _ ↦ ((), c₁, 1)) (fun _ ↦ ((), c₁, 0)) (fun _ ↦ rfl)
    (fun i hi ↦ absurd hi (Nat.not_lt_zero _))
  simp only [firstRewardAlg, Algorithm.deterministic_policy, Kernel.deterministic_apply,
    firstRewardNext, le_rfl, dite_true, Round.feedback_mk] at this
  norm_num at this
  exact hc (dirac_eq_dirac_iff.mp this)

/-- **Witness** of `InfoModel` [INC-P006, Proposition `prop:witnesses`(d), with this learner in
place of `FL`]: the family `g ↦ firstRewardAlg c₁ c₂ g` is in `𝓜_0`: during batch `ℓ + 1` it uses
the grid only through `t 1` when `ℓ ≥ 1`, and not at all when `ℓ = 0`. -/
lemma infoModel_firstRewardAlg (c₁ c₂ : 𝓐) :
    InfoModel (0 : ℕ∞) (fun g : Grid K ↦ firstRewardAlg c₁ c₂ g) := by
  refine ⟨fun g ↦ isBatched_firstRewardAlg c₁ c₂ g, ?_⟩
  intro g g' ℓ n hg hg' ht
  have hiff : g.t 1 ≤ n ↔ g'.t 1 ≤ n := by
    rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
    · have h1 := (g.batchOf_eq_iff.mp hg).2
      have h2 := (g'.batchOf_eq_iff.mp hg').2
      rw [zero_add] at h1 h2
      omega
    · rw [ht 1 le_rfl (by simpa using (show (1 : ℕ∞) ≤ ℓ by exact_mod_cast hℓ))]
  ext x : 1
  simp only [firstRewardAlg, Algorithm.deterministic_policy, Kernel.deterministic_apply]
  congr 1
  unfold firstRewardNext
  by_cases hn : g.t 1 ≤ n
  · simp only [hn, hiff.mp hn, dite_true]
  · simp only [hn, (not_congr hiff).mp hn, dite_false]

/-! ### The parity learners `Par^{(k)}`: in `𝓜_{k+1}`, not in `𝓜_k` -/

/-- The learner `Par^{(k),g}` [INC-P006, Definition `def:exlearners`]: at a round of batch `b`, it
pulls `c₁` if `t (b + k)` is even and `c₂` otherwise. It ignores the history. -/
noncomputable def parityAlg (k : ℕ) (c₁ c₂ : 𝓐) (g : Grid K) : Algorithm Unit 𝓐 𝓨 :=
  Algorithm.deterministic (fun n _ ↦ if Even (g.t (g.batchOf n + k)) then c₁ else c₂)
    (fun _ ↦ measurable_const)

@[simp]
lemma parityAlg_policy (k : ℕ) (c₁ c₂ : 𝓐) (g : Grid K) (n : ℕ) :
    (parityAlg k c₁ c₂ g : Algorithm Unit 𝓐 𝓨).policy n =
      Kernel.const _ (Measure.dirac (if Even (g.t (g.batchOf n + k)) then c₁ else c₂)) := by
  ext x : 1
  simp [parityAlg, Kernel.deterministic_apply]

/-- **Witness** [INC-P006, Proposition `prop:witnesses`(d)]: `Par^{(k)} ∈ 𝓜_{k+1}`. -/
lemma infoModel_parityAlg (k : ℕ) (c₁ c₂ : 𝓐) :
    InfoModel (k + 1 : ℕ) (fun g : Grid K ↦ (parityAlg k c₁ c₂ g : Algorithm Unit 𝓐 𝓨)) := by
  refine ⟨fun g ↦ isBatched_of_forall_seesRewardsUpTo_zero
    (fun n h h' _ _ ↦ by simp [parityAlg_policy]) g, ?_⟩
  intro g g' ℓ n hg hg' ht
  rw [parityAlg_policy, parityAlg_policy, hg, hg',
    ht (ℓ + 1 + k) (by omega) (by push_cast; rw [add_assoc, add_comm (1 : ℕ∞)])]

/-- The grid that agrees with the sequential grid `𝖲_s` up to `t k` and is shifted by one from
`t (k + 1)` on: `t j = s + j - 1` for `1 ≤ j ≤ k` and `t j = s + j` for `j > k`. -/
def shiftedGrid (s k : ℕ) (hs : max 2 K ≤ s) : Grid K where
  t j := if j = 0 then 0 else if j ≤ k then s + j - 1 else s + j
  t_zero := rfl
  strictMono := strictMono_nat_of_lt_succ fun j ↦ by
    have : 2 ≤ s := (le_max_left 2 K).trans hs
    -- the field `t` of the structure literal, at `j` and `j + 1`
    change (if j = 0 then 0 else if j ≤ k then s + j - 1 else s + j) <
      (if j + 1 = 0 then 0 else if j + 1 ≤ k then s + (j + 1) - 1 else s + (j + 1))
    split_ifs <;> first | contradiction | omega
  le_t_one := by
    have : 2 ≤ s := (le_max_left 2 K).trans hs
    -- the field `t` of the structure literal, at `1`
    change max 2 K ≤ (if 1 = 0 then 0 else if 1 ≤ k then s + 1 - 1 else s + 1)
    split_ifs <;> first | contradiction | omega

/-- The batch ends of `shiftedGrid s k`. -/
lemma shiftedGrid_t (s k : ℕ) (hs : max 2 K ≤ s) (j : ℕ) :
    (shiftedGrid s k hs).t j = if j = 0 then 0 else if j ≤ k then s + j - 1 else s + j := rfl

/-- The batch ends of `shiftedGrid s k` up to `k` are those of `𝖲_s`: `t j = s + j - 1` for
`1 ≤ j ≤ k`. -/
lemma shiftedGrid_t_of_le {s k : ℕ} (hs : max 2 K ≤ s) {j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) :
    (shiftedGrid s k hs).t j = s + j - 1 := by
  simp [shiftedGrid, show j ≠ 0 by omega, hjk]

/-- The batch ends of `shiftedGrid s k` after `k` are shifted by one: `t j = s + j` for `j > k`. -/
lemma shiftedGrid_t_of_lt {s k : ℕ} (hs : max 2 K ≤ s) {j : ℕ} (hkj : k < j) :
    (shiftedGrid s k hs).t j = s + j := by
  simp [shiftedGrid, show j ≠ 0 by omega, show ¬ j ≤ k by omega]

/-- **Exclusion** [INC-P006, Proposition `prop:witnesses`(d)]: `Par^{(k)} ∉ 𝓜_k`. At the round `0`
the grids `𝖲_s` and `shiftedGrid s k` (with `s = max 2 K`) agree on `t 1, …, t k`, but their ends
`t (k + 1)` are `s + k` and `s + k + 1`, of different parities. -/
lemma not_infoModel_parityAlg [MeasurableSingletonClass 𝓐] (k : ℕ) {c₁ c₂ : 𝓐} (hc : c₁ ≠ c₂) :
    ¬ InfoModel (k : ℕ) (fun g : Grid K ↦ (parityAlg k c₁ c₂ g : Algorithm Unit 𝓐 𝓨)) := by
  intro h
  set s := max 2 K with hs_def
  have hs : max 2 K ≤ s := le_rfl
  have h2s : 2 ≤ s := le_max_left 2 K
  set g := Grid.sequential (K := K) s hs
  set g' := shiftedGrid (K := K) s k hs
  have hb : g.batchOf 0 = 0 + 1 := g.batchOf_eq_iff.mpr ⟨by simp, by
    rw [Grid.sequential_t le_rfl]; omega⟩
  have hb' : g'.batchOf 0 = 0 + 1 := g'.batchOf_eq_iff.mpr ⟨by simp, by
    rw [shiftedGrid_t]
    split_ifs <;> first | contradiction | omega⟩
  have ht : ∀ j : ℕ, 1 ≤ j → (j : ℕ∞) ≤ 0 + (k : ℕ∞) → g.t j = g'.t j := by
    intro j hj hjk
    have hjk' : j ≤ k := by exact_mod_cast (zero_add (k : ℕ∞)) ▸ hjk
    rw [Grid.sequential_t hj, shiftedGrid_t_of_le hs hj hjk']
  have hpol := h.policy_eq g g' 0 0 hb hb' ht
  rw [parityAlg_policy, parityAlg_policy, hb, hb'] at hpol
  have hd := congrArg (fun κ ↦ κ (default, ())) hpol
  simp only [Kernel.const_apply] at hd
  have hgt : g.t (0 + 1 + k) = s + k := by rw [Grid.sequential_t (by omega)]; omega
  have hgt' : g'.t (0 + 1 + k) = s + k + 1 := by rw [shiftedGrid_t_of_lt hs (by omega)]; omega
  rw [hgt, hgt'] at hd
  rcases Nat.even_or_odd (s + k) with he | ho
  · have hne : ¬ Even (s + k + 1) := by rw [Nat.not_even_iff_odd]; exact he.add_one
    rw [ite_eq_left he, ite_eq_right hne] at hd
    exact hc ((dirac_eq_dirac_iff).mp hd)
  · have hne : ¬ Even (s + k) := Nat.not_even_iff_odd.mpr ho
    have he : Even (s + k + 1) := ho.add_one
    rw [ite_eq_right hne, ite_eq_left he] at hd
    exact hc ((dirac_eq_dirac_iff).mp hd).symm

end Incognita.BatchedBandits
