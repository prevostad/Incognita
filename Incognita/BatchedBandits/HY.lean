/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.Batched
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.MeasureTheory.Function.Floor
public import LeanMachineLearning.ForMathlib.MeasureTheory.Order.MeasurableArg
public import LeanMachineLearning.SequentialLearning.FiniteActions

/-! # The algorithm HY

The learner `HY(w₀, β, ω, ϑ, γ)` of [INC-P000, Definition `def:hy`], as a deterministic LML
algorithm `Algorithm Unit α ℝ` on a grid `g`, with the default parameters `ω^dy`, `ϑ`, `γ` of the
same definition. Its IMED phase uses the IMED index of [HT15, Section 2, Algorithm 1], with a
weight `y` on the logarithm, computed with the statistics frozen at the last batch end and the
current counts.

**Rounds are numbered from `0`** (LML, [INC-P006]). The paper's round `t ∈ (t_ℓ, t_{ℓ+1}]` is the
round `n = t - 1 ∈ [t_ℓ, t_{ℓ+1})` here, that is `g.batchOf n = ℓ + 1`. The policy of the round `n`
sees the history `h` of the rounds `0, …, n - 1` (the paper's rounds `1, …, t - 1`), so:
* the paper's current count `N_c(t - 1)` is `pullCount' n h c`;
* the paper's count `N_c(t_ℓ)` at the last batch end is `HY.count h (t ℓ) c`, the number of pulls
  of `c` in the rounds `< t ℓ`, and the statistics of the rewards of `c` observed at `t_ℓ` are those
  of the rounds `< t ℓ`;
* the paper's `log t` is `log (n + 1)`, and the IMED phase `t ≤ s_ℓ` is `n + 1 ≤ s_ℓ`.

## The statistics at a batch end

For a history `h`, a cutoff `r` (a batch end `t_j`) and an arm `c`:
* `HY.count h r c` is `N_c(t_j)`, `HY.pseudoMean w₀ h r c` is `m̃_c(t_j) = N_c m̂_c / (N_c + w₀)`;
* `HY.pseudoKinf w₀ h r c μ` is `𝒦_inf(ν̃_c(t_j), μ)` for the pseudo-empirical law
  `ν̃_c = (N_c ν̂_c + w₀ δ_0) / (N_c + w₀)`, by the dual formula of
  [INC-P000, Definition `def:kinf`] (the dual formula of 𝒦_inf is [HT10, Theorem 8]):
  for `μ < 1`, the supremum over `λ ∈ [0, 1 / (1 - μ))` of
  `E_{ν̃_c}[log (1 - λ (X - μ))] = (∑_{i} log (1 - λ (X_i - μ)) + w₀ log (1 + λ μ)) / (N_c + w₀)`,
  and, for `μ ≥ 1` (the paper's `μ = 1`), `0` if the mean of `ν̃_c` is `1` and `∞` otherwise. The
  supremum is taken over the **rational** `λ`, as the paper allows for an empirical law ("the
  supremum can be taken over rational `λ`, so `𝒦_inf` is a measurable function of the sample"):
  for rewards in `[0, 1]` the function of `λ` is continuous on `[0, 1 / (1 - μ))`, so the two
  suprema agree. Values in `ℝ≥0∞` (the value at `λ = 0` is `0`, so truncating at `0` changes
  nothing).
* `HY.leader` is the leader `ĉ` (an arm of largest `m̃_c`), `HY.reference` the reference `r` (an arm
  of largest `m̃_c` among the well-sampled arms `N_c ≥ U / 2`, the leader if there is none),
  `HY.imedKinf` the IMED divergences `K̃(c) = 𝒦_inf(ν̃_c, m̃⋆)` and `HY.testKinf` the test
  divergences `K̂(c) = 𝒦_inf(ν̃_c, μ̂)`.

**Tie rules.** The paper fixes the tie rules without using them. Here a maximiser or minimiser of a
finite family of values is LML's `argmax` / `argmin`, a fixed function of the family of values; the
IMED phase plays the leader whenever it is a minimiser, as the paper requires; the "first arm in a
fixed order" of the paced rule is the arm of smallest index in the enumeration
`Fintype.equivFin α`, and batch 1 pulls the arms in turn in that enumeration.

## Main definitions

* `Incognita.BatchedBandits.Grid.netSize β g j`: `U_j` (`U_1 = 1`, `U_{ℓ+1} = ⌈L_ℓ ^ β⌉`).
* `Incognita.BatchedBandits.Grid.imedEnd θ g ℓ`: `s_ℓ = ⌊t_ℓ ^ (1 + θ_ℓ)⌋`.
* `Incognita.BatchedBandits.Grid.hyOmega`, `Grid.hyTheta`, `Grid.hyGamma`: the default parameters
  `ω^dy_ℓ = 2 ^ (-k_ℓ)`, `ϑ_ℓ` and `γ_ℓ`.
* `Incognita.BatchedBandits.HY.imedIndex`, `HY.imedArm`: the IMED index
  `J(c) = N_c(t - 1) K̃(c) + y log N_c(t - 1)` and the arm of the IMED phase.
* `Incognita.BatchedBandits.HY.threshold`: the consistency threshold `Λ̂_ℓ` of the test.
* `Incognita.BatchedBandits.HY.target`, `HY.pacedArm`: the paced targets `n_{ℓ,c}(t)` and the arm
  of the paced phase.
* `Incognita.BatchedBandits.HY.next w₀ β ω θ γ g n h`: the arm pulled by HY at the round `n`.
* `Incognita.BatchedBandits.hyAlg w₀ β ω θ γ g`: the algorithm `HY(w₀, β, ω, ϑ, γ)` on the grid `g`.
* `Incognita.BatchedBandits.hy w₀ β g`: HY with the default `ω^dy`, `ϑ`, `γ` of the grid `g`.

## Main statements

* `HY.measurable_next`: the arm pulled is a measurable function of the history.
* `HY.next_of_lt_t_one`, `hy_exists_next_eq`: batch 1 pulls the arms in turn, so HY pulls every arm
  in batch 1 (it is not a constant learner).
* `HY.pseudoKinf_eq_zero_of_le_pseudoMean`: known case, `𝒦_inf(ν̃, μ) = 0` when the mean of `ν̃` is
  at least `μ`; `HY.pseudoKinf_ne_zero_example`: one observation `0` and `μ = 1/2` give a positive
  divergence.
* `Grid.hyOmega_mem`, `Grid.hyTheta_mem`, `Grid.hyGamma_mem`, `Grid.hyOmega_antitone`: the default
  parameters have the ranges that Definition `def:hy` requires;
  `Grid.hyOmega_hyGamma_of_logEnd_le_one` gives their values while `L_ℓ ≤ 1`.
* `Grid.netSize_one`, `Grid.netSize_succ`, `Grid.one_le_netSize`, `Grid.imedEnd_zero`,
  `Grid.t_le_imedEnd`: `U_1 = 1`, `U_{ℓ+1} = ⌈L_ℓ ^ β⌉`, `U_j ≥ 1`, and `t_ℓ ≤ s_ℓ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Finset

open scoped ENNReal

namespace Incognita.BatchedBandits

variable {K : ℕ}

/-! ### Quantities of the grid -/

namespace Grid

/-- The net size `U_j` of [INC-P000, Definition `def:hy`]: `U_1 = 1` and `U_{ℓ+1} = ⌈L_ℓ ^ β⌉` for
`ℓ ≥ 1` (at `j = 0`, which the paper does not use, it is `1`). -/
noncomputable def netSize (β : ℝ) (g : Grid K) (j : ℕ) : ℕ :=
  if j ≤ 1 then 1 else ⌈g.logEnd (j - 1) ^ β⌉₊

/-- The end `s_ℓ = ⌊t_ℓ ^ (1 + ϑ_ℓ)⌋` of the IMED phase of batch `ℓ + 1` (paper's rounds)
[INC-P000, Definition `def:hy`]. -/
noncomputable def imedEnd (θ : ℕ → ℝ) (g : Grid K) (ℓ : ℕ) : ℕ :=
  ⌊(g.t ℓ : ℝ) ^ (1 + θ ℓ)⌋₊

/-- The default margins `ω^dy_ℓ = 2 ^ (-k_ℓ)`, `k_ℓ = ⌊(1/4) log₂ max(L_ℓ, 1)⌋`
[INC-P000, Definition `def:hy`, default parameters]. -/
noncomputable def hyOmega (g : Grid K) (ℓ : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ ⌊(1 / 4 : ℝ) * Real.logb 2 (max (g.logEnd ℓ) 1)⌋₊

/-- The default activation exponents `ϑ_ℓ = 1 / log log t_ℓ` if `t_ℓ ≥ e^e`, and `1` otherwise
[INC-P000, Definition `def:hy`, default parameters]. -/
noncomputable def hyTheta (g : Grid K) (ℓ : ℕ) : ℝ :=
  if Real.exp (Real.exp 1) ≤ (g.t ℓ : ℝ) then 1 / Real.log (Real.log (g.t ℓ)) else 1

/-- The default consistency margins `γ_ℓ = min(1/2, max(L_ℓ, 1) ^ (-1/4))`
[INC-P000, Definition `def:hy`, default parameters]. -/
noncomputable def hyGamma (g : Grid K) (ℓ : ℕ) : ℝ :=
  min (1 / 2) (max (g.logEnd ℓ) 1 ^ (-(1 / 4 : ℝ)))

end Grid

/-! ### The statistics of a history at a batch end -/

namespace HY

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}

/-- `1` if the round `i` is before the cutoff `r` and pulled the arm `c`, `0` otherwise. -/
noncomputable def ind (h : Hist Unit α ℝ n) (r : ℕ) (c : α) (i : Fin n) : ℝ :=
  if (i : ℕ) < r ∧ (h i).action = c then 1 else 0

/-- The count `N_c(r)` at a cutoff `r`: the number of rounds `i < r` of the history that pulled `c`
(the paper's `N_c(t_j)` for `r = t_j`). -/
noncomputable def count (h : Hist Unit α ℝ n) (r : ℕ) (c : α) : ℕ :=
  ∑ i : Fin n, if (i : ℕ) < r ∧ (h i).action = c then 1 else 0

/-- The pseudo-mean `m̃_c = N_c m̂_c / (N_c + w₀)`: the sum of the rewards of `c` in the rounds
`< r`, divided by `N_c + w₀` [INC-P000, Definition `def:hy`, (1)]. -/
noncomputable def pseudoMean (w₀ : ℝ) (h : Hist Unit α ℝ n) (r : ℕ) (c : α) : ℝ :=
  (∑ i, ind h r c i * (h i).feedback) / (count h r c + w₀)

/-- `E_{ν̃_c}[log (1 - λ (X - μ))]` for the pseudo-empirical law
`ν̃_c = (N_c ν̂_c + w₀ δ_0) / (N_c + w₀)` of the rewards of `c` in the rounds `< r`. -/
noncomputable def pseudoLogMean (w₀ : ℝ) (h : Hist Unit α ℝ n) (r : ℕ) (c : α) (q μ : ℝ) : ℝ :=
  ((∑ i, ind h r c i * Real.log (1 - q * ((h i).feedback - μ))) + w₀ * Real.log (1 + q * μ)) /
    (count h r c + w₀)

/-- The divergence `𝒦_inf(ν̃_c, μ)` of the pseudo-empirical law of `c` at the cutoff `r`, by the
dual formula of [INC-P000, Definition `def:kinf`]: for `μ < 1`, the supremum over the rational
`λ ∈ [0, 1 / (1 - μ))` of `E_{ν̃_c}[log (1 - λ (X - μ))]`; for `μ ≥ 1` (the paper's `μ = 1`), `0`
if the mean `m̃_c` of `ν̃_c` is `1` and `∞` otherwise. -/
noncomputable def pseudoKinf (w₀ : ℝ) (h : Hist Unit α ℝ n) (r : ℕ) (c : α) (μ : ℝ) : ℝ≥0∞ :=
  if μ < 1 then
    ⨆ q : ℚ, if 0 ≤ (q : ℝ) ∧ (q : ℝ) * (1 - μ) < 1 then
      ENNReal.ofReal (pseudoLogMean w₀ h r c q μ) else 0
  else if pseudoMean w₀ h r c = 1 then 0 else ⊤

/-! ### Measurability -/

section Measurability

variable [MeasurableSpace α] [MeasurableSingletonClass α]

omit [Fintype α] [DecidableEq α] in
/-- A function of the history and of an arm chosen measurably from the history is measurable. -/
lemma measurable_comp_arm [Countable α] {X γ : Type*} [MeasurableSpace X] [MeasurableSpace γ]
    {F : α → X → γ} (hF : ∀ c, Measurable (F c)) {G : X → α} (hG : Measurable G) :
    Measurable fun x ↦ F (G x) x :=
  (measurable_from_prod_countable_right (f := fun p : α × X ↦ F p.1 p.2) hF).comp
    (hG.prodMk measurable_id)

omit [Fintype α] [DecidableEq α] in
lemma measurableSet_round (r : ℕ) (c : α) (i : Fin n) :
    MeasurableSet {h : Hist Unit α ℝ n | (i : ℕ) < r ∧ (h i).action = c} := by
  by_cases hi : (i : ℕ) < r
  · simp only [hi, true_and]
    exact (measurableSet_singleton c).preimage
      (Round.measurable_action.comp (measurable_pi_apply i))
  · simp [hi]

omit [Fintype α] in
lemma measurable_ind (r : ℕ) (c : α) (i : Fin n) :
    Measurable fun h : Hist Unit α ℝ n ↦ ind h r c i :=
  Measurable.ite (measurableSet_round r c i) measurable_const measurable_const

omit [Fintype α] in
lemma measurable_count (r : ℕ) (c : α) : Measurable fun h : Hist Unit α ℝ n ↦ count h r c :=
  Finset.measurable_sum _ fun i _ ↦
    Measurable.ite (measurableSet_round r c i) measurable_const measurable_const

omit [Fintype α] [DecidableEq α] [MeasurableSingletonClass α] in
lemma measurable_feedback_apply (i : Fin n) :
    Measurable fun h : Hist Unit α ℝ n ↦ (h i).feedback :=
  Round.measurable_feedback.comp (measurable_pi_apply i)

omit [Fintype α] in
lemma measurable_pseudoMean (w₀ : ℝ) (r : ℕ) (c : α) :
    Measurable fun h : Hist Unit α ℝ n ↦ pseudoMean w₀ h r c := by
  unfold pseudoMean
  refine Measurable.div (Finset.measurable_sum _ fun i _ ↦
    (measurable_ind r c i).mul (measurable_feedback_apply i)) ?_
  exact (measurable_from_nat.comp (measurable_count r c)).add measurable_const

omit [Fintype α] in
lemma measurable_pseudoLogMean (w₀ : ℝ) (r : ℕ) (c : α) (q : ℝ) :
    Measurable fun p : Hist Unit α ℝ n × ℝ ↦ pseudoLogMean w₀ p.1 r c q p.2 := by
  unfold pseudoLogMean
  refine Measurable.div (Measurable.add (Finset.measurable_sum _ fun i _ ↦
    ((measurable_ind r c i).comp measurable_fst).mul ?_) ?_) ?_
  · exact Real.measurable_log.comp (measurable_const.sub (measurable_const.mul
      (((measurable_feedback_apply i).comp measurable_fst).sub measurable_snd)))
  · exact measurable_const.mul (Real.measurable_log.comp
      (measurable_const.add (measurable_const.mul measurable_snd)))
  · exact ((measurable_from_nat.comp (measurable_count r c)).comp measurable_fst).add
      measurable_const

omit [Fintype α] in
lemma measurable_pseudoKinf_prod (w₀ : ℝ) (r : ℕ) (c : α) :
    Measurable fun p : Hist Unit α ℝ n × ℝ ↦ pseudoKinf w₀ p.1 r c p.2 := by
  unfold pseudoKinf
  refine Measurable.ite (measurableSet_lt measurable_snd measurable_const) ?_ ?_
  · refine Measurable.iSup fun q ↦ Measurable.ite ?_ ?_ measurable_const
    · by_cases hq : 0 ≤ (q : ℝ)
      · simp only [hq, true_and]
        exact measurableSet_lt (measurable_const.mul (measurable_const.sub measurable_snd))
          measurable_const
      · simp [hq]
    · exact ENNReal.measurable_ofReal.comp (measurable_pseudoLogMean w₀ r c q)
  · exact Measurable.ite (measurableSet_eq_fun ((measurable_pseudoMean w₀ r c).comp measurable_fst)
      measurable_const) measurable_const measurable_const

omit [Fintype α] in
lemma measurable_pseudoKinf (w₀ : ℝ) (r : ℕ) (c : α) {μ : Hist Unit α ℝ n → ℝ}
    (hμ : Measurable μ) : Measurable fun h ↦ pseudoKinf w₀ h r c (μ h) :=
  (measurable_pseudoKinf_prod w₀ r c).comp (measurable_id.prodMk hμ)

end Measurability

variable [Nonempty α]

/-- The leader `ĉ` at the cutoff `r`: an arm of largest pseudo-mean (LML's `argmax`)
[INC-P000, Definition `def:hy`, (2)]. -/
noncomputable def leader (w₀ : ℝ) (h : Hist Unit α ℝ n) (r : ℕ) : α :=
  argmax fun c ↦ pseudoMean w₀ h r c

/-- The arm `c` is well sampled at the cutoff `r` for the net size `U`: `N_c ≥ U / 2`. -/
def IsWellSampled (h : Hist Unit α ℝ n) (r U : ℕ) (c : α) : Prop := U ≤ 2 * count h r c

open Classical in
/-- The reference `r`: an arm of largest pseudo-mean among the well-sampled arms, and the leader if
no arm is well sampled [INC-P000, Definition `def:hy`, (3)]. -/
noncomputable def reference (w₀ : ℝ) (h : Hist Unit α ℝ n) (r U : ℕ) : α :=
  if ∃ c, IsWellSampled h r U c then
    argmax fun c ↦ if IsWellSampled h r U c then (pseudoMean w₀ h r c : EReal) else ⊥
  else leader w₀ h r

/-- The IMED divergence `K̃(c) = 𝒦_inf(ν̃_c, m̃⋆)`, `m̃⋆` the pseudo-mean of the leader
[INC-P000, Definition `def:hy`, (2)]. -/
noncomputable def imedKinf (w₀ : ℝ) (h : Hist Unit α ℝ n) (r : ℕ) (c : α) : ℝ≥0∞ :=
  pseudoKinf w₀ h r c (pseudoMean w₀ h r (leader w₀ h r))

/-- The test divergence `K̂(c) = 𝒦_inf(ν̃_c, μ̂)`, `μ̂` the pseudo-mean of the reference
[INC-P000, Definition `def:hy`, (3)]. -/
noncomputable def testKinf (w₀ : ℝ) (h : Hist Unit α ℝ n) (r U : ℕ) (c : α) : ℝ≥0∞ :=
  pseudoKinf w₀ h r c (pseudoMean w₀ h r (reference w₀ h r U))

/-! ### One round of HY -/

/-- The IMED index `J(c) = N_c(t - 1) K̃(c) + y log N_c(t - 1)` with the current count
`N_c(t - 1) = pullCount' n h c`, in `EReal` (`0 · ∞ = 0`, `N · ∞ = ∞` for `N ≥ 1`). -/
noncomputable def imedIndex (w₀ y : ℝ) (h : Hist Unit α ℝ n) (r : ℕ) (c : α) : EReal :=
  (((pullCount' n h c : ℝ≥0∞) * imedKinf w₀ h r c : ℝ≥0∞) : EReal) +
    ((y * Real.log (pullCount' n h c) : ℝ) : EReal)

open Classical in
/-- The arm of the IMED phase: the leader if it minimises `J`, otherwise LML's `argmin` of `J`. -/
noncomputable def imedArm (w₀ y : ℝ) (h : Hist Unit α ℝ n) (r : ℕ) : α :=
  if ∀ c, imedIndex w₀ y h r (leader w₀ h r) ≤ imedIndex w₀ y h r c then leader w₀ h r
  else argmin fun c ↦ imedIndex w₀ y h r c

open Classical in
/-- The consistency threshold `Λ̂_ℓ` of the test of batch `ℓ + 1` [INC-P000, Definition `def:hy`,
(4)], for `ℓ ≥ 2`: `min(L_ℓ, min_{c ∈ Q_ℓ} [N_c K̂_{ℓ-1}(c) / y_{ℓ-1} + log N_c])`, with
`Q_ℓ` the arms not well sampled at `t_ℓ` other than the previous leader `ĉ_{ℓ-1}`, `N_c = N_c(t_ℓ)`
and `min ∅ = ∞`. The arguments are the cutoffs `r = t_ℓ`, `r' = t_{ℓ-1}`, the net sizes `U = U_ℓ`,
`U' = U_{ℓ-1}`, `L = L_ℓ` and `y' = y_{ℓ-1}`. -/
noncomputable def threshold (w₀ L y' : ℝ) (h : Hist Unit α ℝ n) (r r' U U' : ℕ) : ℝ :=
  (min (ENNReal.ofReal L) (⨅ c, if ¬ IsWellSampled h r U c ∧ c ≠ leader w₀ h r' then
    (count h r c : ℝ≥0∞) * testKinf w₀ h r' U' c / ENNReal.ofReal y' +
      ENNReal.ofReal (Real.log (count h r c)) else ⊤)).toReal

open Classical in
/-- The paced target `n_{ℓ,c}(t)` [INC-P000, Definition `def:hy`, (5)-(6)]: `K - 1 + U_{ℓ+1}` if `c`
is ambiguous, `K - 1 + min(U_{ℓ+1}, ⌈(1 + ω_ℓ) y_ℓ log t / K̂_ℓ(c)⌉)` if `c` is rejected
(the ceiling term is `0` when `K̂_ℓ(c) = ∞`),
where `c` is rejected if `K̂_ℓ(c) > 0` and `N_c K̂_ℓ(c) ≥ h_ℓ`. Arguments: `thr = h_ℓ`, `ω = ω_ℓ`,
`y = y_ℓ`, `logt = log t`, `r = t_ℓ`, `U = U_ℓ` (for `K̂_ℓ`), `Unext = U_{ℓ+1}`. -/
noncomputable def target (w₀ thr ω y logt : ℝ) (h : Hist Unit α ℝ n) (r U Unext : ℕ) (c : α) : ℕ :=
  Fintype.card α - 1 +
    if 0 < testKinf w₀ h r U c ∧ ENNReal.ofReal thr ≤ (count h r c : ℝ≥0∞) * testKinf w₀ h r U c
    then min Unext
      (if testKinf w₀ h r U c = ⊤ then 0
        else ⌈(1 + ω) * y * logt / (testKinf w₀ h r U c).toReal⌉₊)
    else Unext

open Classical in
/-- The arm of the paced phase [INC-P000, Definition `def:hy`, (7)]: the first arm `c ≠ ĉ_ℓ` (in the
enumeration `Fintype.equivFin α`) whose current count is below its target, and the leader `ĉ_ℓ` if
there is none. The first such arm is the unique maximiser of `c ↦ -(index of c)` on these arms. -/
noncomputable def pacedArm (w₀ thr ω y logt : ℝ) (h : Hist Unit α ℝ n) (r U Unext : ℕ) : α :=
  if ∃ c, c ≠ leader w₀ h r ∧ pullCount' n h c < target w₀ thr ω y logt h r U Unext c then
    argmax fun c ↦ if c ≠ leader w₀ h r ∧ pullCount' n h c < target w₀ thr ω y logt h r U Unext c
      then ((-((Fintype.equivFin α c : ℕ) : ℝ) : ℝ) : EReal) else ⊥
  else leader w₀ h r

/-- The arm pulled by `HY(w₀, β, ω, ϑ, γ)` on the grid `g` at the round `n` (rounds from `0`), from
the history `h` of the rounds `0, …, n - 1` [INC-P000, Definition `def:hy`]. With
`ℓ = g.batchOf n - 1` (so `t ℓ ≤ n < t (ℓ + 1)`):
* batch 1 (`ℓ = 0`): the arm of index `n mod K` in the enumeration `Fintype.equivFin α` (the arms
  in turn);
* `ℓ ≥ 1`, IMED phase (`n + 1 ≤ s_ℓ`): `imedArm` with `y_ℓ = x_ℓ ^ 2` and the statistics at `t ℓ`;
* `ℓ ≥ 1`, paced phase (`n + 1 > s_ℓ`): `pacedArm` with `h_ℓ = (1 - γ_ℓ) y_{ℓ-1} Λ̂_ℓ`,
  `Λ̂_1 = L_1`, and `log t = log (n + 1)`. -/
noncomputable def next (w₀ β : ℝ) (ω θ γ : ℕ → ℝ) (g : Grid K) (n : ℕ) (h : Hist Unit α ℝ n) : α :=
  if g.batchOf n - 1 = 0 then
    (Fintype.equivFin α).symm ⟨n % Fintype.card α, Nat.mod_lt _ Fintype.card_pos⟩
  else if n + 1 ≤ g.imedEnd θ (g.batchOf n - 1) then
    imedArm w₀ (g.ratio (g.batchOf n - 1) ^ 2) h (g.t (g.batchOf n - 1))
  else
    pacedArm w₀
      ((1 - γ (g.batchOf n - 1)) * g.ratio (g.batchOf n - 1 - 1) ^ 2 *
        (if g.batchOf n - 1 = 1 then g.logEnd 1 else
          threshold w₀ (g.logEnd (g.batchOf n - 1)) (g.ratio (g.batchOf n - 1 - 1) ^ 2) h
            (g.t (g.batchOf n - 1)) (g.t (g.batchOf n - 1 - 1)) (g.netSize β (g.batchOf n - 1))
            (g.netSize β (g.batchOf n - 1 - 1))))
      (ω (g.batchOf n - 1)) (g.ratio (g.batchOf n - 1) ^ 2) (Real.log (n + 1)) h
      (g.t (g.batchOf n - 1)) (g.netSize β (g.batchOf n - 1)) (g.netSize β (g.batchOf n - 1 + 1))

section Measurability

variable [MeasurableSpace α] [MeasurableSingletonClass α]

lemma measurable_leader (w₀ : ℝ) (r : ℕ) : Measurable fun h : Hist Unit α ℝ n ↦ leader w₀ h r :=
  measurable_argmax.comp (Measurable.of_eval fun c ↦ measurable_pseudoMean w₀ r c)

omit [Fintype α] [Nonempty α] in
lemma measurableSet_isWellSampled (r U : ℕ) (c : α) :
    MeasurableSet {h : Hist Unit α ℝ n | IsWellSampled h r U c} :=
  measurableSet_le measurable_const (measurable_const.mul (measurable_count r c))

lemma measurable_reference (w₀ : ℝ) (r U : ℕ) :
    Measurable fun h : Hist Unit α ℝ n ↦ reference w₀ h r U := by
  unfold reference
  refine Measurable.ite ?_ ?_ (measurable_leader w₀ r)
  · simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion fun c ↦ measurableSet_isWellSampled r U c
  · refine measurable_argmax.comp (Measurable.of_eval fun c ↦ ?_)
    exact Measurable.ite (measurableSet_isWellSampled r U c)
      (measurable_coe_real_ereal.comp (measurable_pseudoMean w₀ r c)) measurable_const

lemma measurable_imedKinf (w₀ : ℝ) (r : ℕ) (c : α) :
    Measurable fun h : Hist Unit α ℝ n ↦ imedKinf w₀ h r c :=
  measurable_pseudoKinf w₀ r c
    (measurable_comp_arm (fun c ↦ measurable_pseudoMean w₀ r c) (measurable_leader w₀ r))

lemma measurable_testKinf (w₀ : ℝ) (r U : ℕ) (c : α) :
    Measurable fun h : Hist Unit α ℝ n ↦ testKinf w₀ h r U c :=
  measurable_pseudoKinf w₀ r c
    (measurable_comp_arm (fun c ↦ measurable_pseudoMean w₀ r c) (measurable_reference w₀ r U))

omit [Fintype α] [Nonempty α] in
lemma measurable_pullCount'_nat (c : α) : Measurable fun h : Hist Unit α ℝ n ↦ pullCount' n h c :=
  measurable_pullCount' n c

lemma measurable_imedIndex (w₀ y : ℝ) (r : ℕ) (c : α) :
    Measurable fun h : Hist Unit α ℝ n ↦ imedIndex w₀ y h r c := by
  unfold imedIndex
  refine Measurable.add ?_ ?_
  · exact measurable_coe_ennreal_ereal.comp
      ((measurable_from_nat.comp (measurable_pullCount'_nat c)).mul (measurable_imedKinf w₀ r c))
  · exact measurable_coe_real_ereal.comp (measurable_const.mul
      (Real.measurable_log.comp (measurable_from_nat.comp (measurable_pullCount'_nat c))))

lemma measurable_imedArm (w₀ y : ℝ) (r : ℕ) :
    Measurable fun h : Hist Unit α ℝ n ↦ imedArm w₀ y h r := by
  unfold imedArm
  refine Measurable.ite ?_ (measurable_leader w₀ r)
    (measurable_argmin.comp (Measurable.of_eval fun c ↦ measurable_imedIndex w₀ y r c))
  simp only [Set.ofPred_forall]
  refine MeasurableSet.iInter fun c ↦ measurableSet_le ?_ (measurable_imedIndex w₀ y r c)
  exact measurable_comp_arm (fun c ↦ measurable_imedIndex w₀ y r c) (measurable_leader w₀ r)

lemma measurable_threshold (w₀ L y' : ℝ) (r r' U U' : ℕ) :
    Measurable fun h : Hist Unit α ℝ n ↦ threshold w₀ L y' h r r' U U' := by
  unfold threshold
  refine ENNReal.measurable_toReal.comp (Measurable.min measurable_const ?_)
  refine Measurable.iInf fun c ↦ Measurable.ite ?_ ?_ measurable_const
  · exact (measurableSet_isWellSampled r U c).compl.inter
      (measurableSet_eq_fun measurable_const (measurable_leader w₀ r')).compl
  · refine Measurable.add (Measurable.div_const ?_ _) ?_
    · exact (measurable_from_nat.comp (measurable_count r c)).mul (measurable_testKinf w₀ r' U' c)
    · exact ENNReal.measurable_ofReal.comp
        (Real.measurable_log.comp (measurable_from_nat.comp (measurable_count r c)))

lemma measurable_target (w₀ ω y logt : ℝ) (r U Unext : ℕ) (c : α) {T : Hist Unit α ℝ n → ℝ}
    (hT : Measurable T) :
    Measurable fun h : Hist Unit α ℝ n ↦ target w₀ (T h) ω y logt h r U Unext c := by
  unfold target
  refine measurable_const.add (Measurable.ite ?_ (Measurable.min measurable_const ?_)
    measurable_const)
  · exact (measurableSet_lt measurable_const (measurable_testKinf w₀ r U c)).inter
      (measurableSet_le (ENNReal.measurable_ofReal.comp hT)
        ((measurable_from_nat.comp (measurable_count r c)).mul (measurable_testKinf w₀ r U c)))
  · refine Measurable.ite (measurableSet_eq_fun (measurable_testKinf w₀ r U c) measurable_const)
      measurable_const ?_
    exact Nat.measurable_ceil.comp (measurable_const.div
      (ENNReal.measurable_toReal.comp (measurable_testKinf w₀ r U c)))

lemma measurableSet_demand (w₀ ω y logt : ℝ) (r U Unext : ℕ) (c : α) {T : Hist Unit α ℝ n → ℝ}
    (hT : Measurable T) :
    MeasurableSet {h : Hist Unit α ℝ n | c ≠ leader w₀ h r ∧
      pullCount' n h c < target w₀ (T h) ω y logt h r U Unext c} := by
  exact (measurableSet_eq_fun measurable_const (measurable_leader w₀ r)).compl.inter
    (measurableSet_lt (measurable_pullCount'_nat c) (measurable_target w₀ ω y logt r U Unext c hT))

lemma measurable_pacedArm (w₀ ω y logt : ℝ) (r U Unext : ℕ) {T : Hist Unit α ℝ n → ℝ}
    (hT : Measurable T) :
    Measurable fun h : Hist Unit α ℝ n ↦ pacedArm w₀ (T h) ω y logt h r U Unext := by
  unfold pacedArm
  refine Measurable.ite ?_ ?_ (measurable_leader w₀ r)
  · simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion fun c ↦ measurableSet_demand w₀ ω y logt r U Unext c hT
  · refine measurable_argmax.comp (Measurable.of_eval fun c ↦ ?_)
    exact Measurable.ite (measurableSet_demand w₀ ω y logt r U Unext c hT) measurable_const
      measurable_const

lemma measurable_next (w₀ β : ℝ) (ω θ γ : ℕ → ℝ) (g : Grid K) (n : ℕ) :
    Measurable fun h : Hist Unit α ℝ n ↦ next w₀ β ω θ γ g n h := by
  unfold next
  split_ifs
  · exact measurable_const
  · exact measurable_imedArm _ _ _
  · exact measurable_pacedArm _ _ _ _ _ _ _ measurable_const
  · exact measurable_pacedArm _ _ _ _ _ _ _
      (measurable_const.mul (measurable_threshold _ _ _ _ _ _ _))

end Measurability

/-! ### Checks of the statistics -/

omit [Fintype α] [Nonempty α] in
/-- **Known case** [INC-P000, Definition `def:kinf`; Lemma `lem:kinf`]: `𝒦_inf(ν̃, μ) = 0` when the
mean of the pseudo-empirical law `ν̃` is at least the level `μ < 1`, for rewards at most `1`, a
pseudo-count `w₀ ≥ 0` and a positive total weight `N + w₀`. -/
lemma pseudoKinf_eq_zero_of_le_pseudoMean {w₀ : ℝ} (hw₀ : 0 ≤ w₀) {h : Hist Unit α ℝ n} {r : ℕ}
    {c : α} {μ : ℝ} (hμ : μ < 1) (hy : ∀ i, (h i).feedback ≤ 1)
    (hpos : 0 < (count h r c : ℝ) + w₀) (hle : μ ≤ pseudoMean w₀ h r c) :
    pseudoKinf w₀ h r c μ = 0 := by
  -- Every term of the dual formula is `≤ -λ (m̃ - μ) ≤ 0`, since `log x ≤ x - 1`.
  rw [pseudoKinf, ite_eq_left hμ]
  refine le_antisymm (iSup_le fun q ↦ ?_) bot_le
  split_ifs with hq
  swap
  · exact le_rfl
  rw [ENNReal.ofReal_eq_zero.mpr]
  rw [pseudoLogMean, div_nonpos_iff]
  refine Or.inr ⟨?_, hpos.le⟩
  have hcount : (count h r c : ℝ) = ∑ i, ind h r c i := by
    simp only [count, ind]
    push_cast
    rfl
  have hterm : ∀ i, ind h r c i * Real.log (1 - q * ((h i).feedback - μ)) ≤
      ind h r c i * (-(q * ((h i).feedback - μ))) := by
    intro i
    have hind : 0 ≤ ind h r c i := by unfold ind; split_ifs <;> norm_num
    refine mul_le_mul_of_nonneg_left ?_ hind
    have hpos' : 0 < 1 - q * ((h i).feedback - μ) := by
      have : (q : ℝ) * ((h i).feedback - μ) ≤ q * (1 - μ) :=
        mul_le_mul_of_nonneg_left (by linarith [hy i]) hq.1
      linarith [hq.2]
    linarith [Real.log_le_sub_one_of_pos hpos']
  have hw : w₀ * Real.log (1 + q * μ) ≤ w₀ * (q * μ) := by
    refine mul_le_mul_of_nonneg_left ?_ hw₀
    have : 0 < 1 + (q : ℝ) * μ := by nlinarith [hq.1]
    linarith [Real.log_le_sub_one_of_pos this]
  have hmean : μ * ((count h r c : ℝ) + w₀) ≤ ∑ i, ind h r c i * (h i).feedback := by
    rw [pseudoMean, le_div_iff₀ hpos] at hle
    exact hle
  have hlin : ∀ i, ind h r c i * (-(q * ((h i).feedback - μ))) =
      -(q : ℝ) * (ind h r c i * (h i).feedback) + q * μ * ind h r c i := fun i ↦ by ring
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ hterm i
  simp_rw [hlin, Finset.sum_add_distrib, ← Finset.mul_sum, ← hcount] at hsum
  have hq0 := hq.1
  nlinarith

omit [Fintype α] [Nonempty α] in
/-- **Exclusion**: one observation `0` of the arm `c`, no pseudo-count and the level `μ = 1/2`
give a positive divergence (the dual formula at `λ = 1` is `log (3/2) > 0`): `pseudoKinf` is not
identically `0`. -/
lemma pseudoKinf_ne_zero_example (c : α) :
    pseudoKinf 0 (fun _ : Fin 1 ↦ ((), c, (0 : ℝ))) 1 c (1 / 2) ≠ 0 := by
  rw [pseudoKinf, ite_eq_left (by norm_num)]
  refine (ENNReal.iSup_eq_zero.not).mpr fun h ↦ ?_
  have h1 := h 1
  rw [ite_eq_left (by norm_num), ENNReal.ofReal_eq_zero] at h1
  have : pseudoLogMean 0 (fun _ : Fin 1 ↦ ((), c, (0 : ℝ))) 1 c (1 : ℚ) (1 / 2) =
      Real.log (3 / 2) := by
    simp [pseudoLogMean, ind, count]
    norm_num
  rw [this] at h1
  exact absurd h1 (not_le.mpr (Real.log_pos (by norm_num)))

end HY

/-! ### The algorithm -/

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α]

/-- The algorithm `HY(w₀, β, ω, ϑ, γ)` on the grid `g` [INC-P000, Definition `def:hy`]: the
deterministic LML algorithm whose action at the round `n` is `HY.next w₀ β ω θ γ g n h` for the
history `h` of the rounds `0, …, n - 1` (it uses no observation). The parameters are a pseudo-count
`w₀`, a net exponent `β`, and the sequences `ω_ℓ`, `ϑ_ℓ`, `γ_ℓ`; the paper requires `w₀ ≥ 0`,
`β ≥ 2`, `ω_ℓ ∈ (0, 1]` non-increasing, `ϑ_ℓ ∈ (0, 1]`, `γ_ℓ ∈ (0, 1/2]`, functions of
`t_1, …, t_ℓ` (the statements carry these hypotheses). -/
noncomputable def hyAlg (w₀ β : ℝ) (ω θ γ : ℕ → ℝ) (g : Grid K) : Algorithm Unit α ℝ :=
  Algorithm.deterministic (fun n x ↦ HY.next w₀ β ω θ γ g n x.1)
    fun n ↦ (HY.measurable_next w₀ β ω θ γ g n).comp measurable_fst

/-- `HY(w₀, β, ω^dy, ϑ, γ)` on the grid `g`, with the default margins, activation exponents and
consistency margins of [INC-P000, Definition `def:hy`] (`Grid.hyOmega`, `Grid.hyTheta`,
`Grid.hyGamma`), which depend on the grid only through `t_ℓ`. With `w₀ = 1` and `β = 2` it is HY
with all its default parameters. -/
noncomputable def hy (w₀ β : ℝ) (g : Grid K) : Algorithm Unit α ℝ :=
  hyAlg w₀ β g.hyOmega g.hyTheta g.hyGamma g

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **Known case** [INC-P000, Definition `def:hy`, batch 1]: during the first batch (`n < t 1`),
HY pulls the arm of index `n mod K` (the arms in turn), whatever the history. -/
lemma HY.next_of_lt_t_one (w₀ β : ℝ) (ω θ γ : ℕ → ℝ) (g : Grid K) {n : ℕ} (hn : n < g.t 1)
    (h : Hist Unit α ℝ n) :
    HY.next w₀ β ω θ γ g n h =
      (Fintype.equivFin α).symm ⟨n % Fintype.card α, Nat.mod_lt _ Fintype.card_pos⟩ := by
  have hb : g.batchOf n = 0 + 1 := g.batchOf_eq_iff.mpr ⟨by rw [g.t_zero]; exact Nat.zero_le n, hn⟩
  rw [HY.next, ite_eq_left (by rw [hb])]

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **Witness and exclusion**: on a grid for `K = card α` arms, HY pulls every arm `c` at some round
of the first batch (the round of index `c` in the enumeration, which is `< K ≤ t 1`): it is not a
constant learner. -/
lemma hy_exists_next_eq (w₀ β : ℝ) (ω θ γ : ℕ → ℝ) (g : Grid (Fintype.card α)) (c : α) :
    ∃ n, n < g.t 1 ∧ ∀ h : Hist Unit α ℝ n, HY.next w₀ β ω θ γ g n h = c := by
  refine ⟨Fintype.equivFin α c, lt_of_lt_of_le (Fintype.equivFin α c).2 g.card_le_t_one,
    fun h ↦ ?_⟩
  rw [HY.next_of_lt_t_one w₀ β ω θ γ g (lt_of_lt_of_le (Fintype.equivFin α c).2 g.card_le_t_one)]
  rw [Equiv.symm_apply_eq]
  ext
  simp [Nat.mod_eq_of_lt (Fintype.equivFin α c).2]

/-! ### The default parameters -/

namespace Grid

variable (g : Grid K)

/-- The default margins are in `(0, 1]` [INC-P000, Definition `def:hy`]. -/
lemma hyOmega_mem (ℓ : ℕ) : g.hyOmega ℓ ∈ Set.Ioc (0 : ℝ) 1 :=
  ⟨pow_pos (by norm_num) _, pow_le_one₀ (by norm_num) (by norm_num)⟩

/-- The default margins are non-increasing in `ℓ ≥ 1` [INC-P000, Definition `def:hy`]. -/
lemma hyOmega_antitone {ℓ ℓ' : ℕ} (hℓ : 1 ≤ ℓ) (hℓℓ' : ℓ ≤ ℓ') : g.hyOmega ℓ' ≤ g.hyOmega ℓ := by
  refine pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.floor_mono ?_)
  refine mul_le_mul_of_nonneg_left (Real.logb_le_logb_of_le (by norm_num)
    (lt_of_lt_of_le one_pos (le_max_right _ _)) (max_le_max_right 1 ?_)) (by norm_num)
  unfold logEnd
  gcongr
  · exact_mod_cast (show 0 < g.t ℓ by have := g.two_le_t hℓ; omega)
  · exact_mod_cast g.strictMono.monotone hℓℓ'

/-- The default activation exponents are in `(0, 1]` [INC-P000, Definition `def:hy`]. -/
lemma hyTheta_mem (ℓ : ℕ) : g.hyTheta ℓ ∈ Set.Ioc (0 : ℝ) 1 := by
  unfold hyTheta
  split_ifs with h
  · have he : 1 < Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    have hlog : Real.exp 1 ≤ Real.log (g.t ℓ) := by
      rw [Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos _) h)]
      exact h
    have hll : 1 ≤ Real.log (Real.log (g.t ℓ)) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      exact hlog
    exact ⟨by positivity, by rw [div_le_one (by linarith)]; exact hll⟩
  · exact ⟨one_pos, le_rfl⟩

/-- **Known case**: on a batch end `t_ℓ < e^e` the default activation exponent is `1`. -/
lemma hyTheta_of_lt {ℓ : ℕ} (h : (g.t ℓ : ℝ) < Real.exp (Real.exp 1)) : g.hyTheta ℓ = 1 := by
  simp [hyTheta, not_le.mpr h]

/-- The default consistency margins are in `(0, 1/2]` [INC-P000, Definition `def:hy`]. -/
lemma hyGamma_mem (ℓ : ℕ) : g.hyGamma ℓ ∈ Set.Ioc (0 : ℝ) (1 / 2) :=
  ⟨lt_min (by norm_num) (Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (le_max_right _ _)) _),
    min_le_left _ _⟩

/-- **Known case**: `U_1 = 1` [INC-P000, Definition `def:hy`]. -/
lemma netSize_one (β : ℝ) : g.netSize β 1 = 1 := by simp [netSize]

/-- **Known case**: `U_{ℓ+1} = ⌈L_ℓ ^ β⌉` for `ℓ ≥ 1` [INC-P000, Definition `def:hy`]. -/
lemma netSize_succ (β : ℝ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    g.netSize β (ℓ + 1) = ⌈g.logEnd ℓ ^ β⌉₊ := by
  simp [netSize, show ¬ ℓ + 1 ≤ 1 by omega]

/-- **Witness**: the net sizes are positive (`L_ℓ > 0` for `ℓ ≥ 1`). -/
lemma one_le_netSize (β : ℝ) (j : ℕ) : 1 ≤ g.netSize β j := by
  unfold netSize
  split_ifs with hj
  · exact le_rfl
  · exact Nat.one_le_iff_ne_zero.mpr fun h0 ↦ by
      rw [Nat.ceil_eq_zero] at h0
      exact absurd h0 (not_le.mpr (Real.rpow_pos_of_pos (g.logEnd_pos (by omega)) β))

/-- **Known case**: with the exponent `ϑ_ℓ = 0` the IMED phase would end at `t_ℓ`. -/
lemma imedEnd_zero (ℓ : ℕ) : g.imedEnd (fun _ ↦ 0) ℓ = g.t ℓ := by
  simp [imedEnd]

/-- **Witness**: for `ϑ_ℓ ≥ 0` the IMED phase ends at `s_ℓ ≥ t_ℓ`. -/
lemma t_le_imedEnd {θ : ℕ → ℝ} {ℓ : ℕ} (hθ : 0 ≤ θ ℓ) : g.t ℓ ≤ g.imedEnd θ ℓ := by
  unfold imedEnd
  rcases Nat.eq_zero_or_pos (g.t ℓ) with h0 | hpos
  · rw [h0]
    exact Nat.zero_le _
  refine Nat.le_floor ?_
  calc ((g.t ℓ : ℕ) : ℝ) = (g.t ℓ : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ (g.t ℓ : ℝ) ^ (1 + θ ℓ) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hpos) (by linarith)

/-- **Known case**: while `L_ℓ ≤ 1` the default parameters are `ω = 1`, `γ = 1/2`. -/
lemma hyOmega_hyGamma_of_logEnd_le_one {ℓ : ℕ} (h : g.logEnd ℓ ≤ 1) :
    g.hyOmega ℓ = 1 ∧ g.hyGamma ℓ = 1 / 2 := by
  norm_num [hyOmega, hyGamma, max_eq_right h]

end Grid

end Incognita.BatchedBandits
