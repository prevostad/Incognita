/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.Instances
public import Incognita.BatchedBandits.Relations
public import Incognita.TransferBandits.Consistency
public import Incognita.TransferBandits.Checks
public import Incognita.TransferBandits.SourceKL
public import Incognita.TransferBandits.SizeRules
public import Incognita.TransferBandits.LMLHistory
public import Incognita.ForLML.InformationTheory.KullbackLeibler.Bernoulli

/-! # Relations between the consistency notions of TransferBandits and BatchedBandits

Relations between the bandit consistency of
[INC-P003, Definition `def:consistency`] (`IsConsistentOnUnit`), the classical consistency of
LMLExplore (`LMLExplore.Bandits.IsConsistent`, in terms of the expected regret) and the
consistency at the batch ends of [INC-P006, Definition `def:consistent`]
(`Incognita.BatchedBandits.IsConsistentAtBatchEnds`), and between the two classes of instances
`𝒫^K` [INC-P003, Definition `def:instance`] and `𝒫` [INC-P006, Definition `def:instance`].

## Main statements

* `Relations.mem_unitBandits_iff_forall_mem_unitLaws`: `ν ∈ 𝒫^K` iff every law `ν a` is in the set
  `unitLaws` of BatchedBandits.
* `Relations.batchedBandits_unitBandits_eq_inter`: `𝒫 = 𝒫^K ∩ {m⋆ < 1}`; the two classes are not the
  same object (an instance with an arm `δ_1` is in `𝒫^K` and not in `𝒫`).
* `Relations.isConsistentOnUnit_iff_isConsistentAtBatchEnds_sequential`: a learner is consistent
  on `𝒫^K` in the sense of P003 iff it is consistent at the batch ends of `𝖲_s` on `𝒫^K`, for any
  `s`.
* `Relations.isConsistentOnUnit_iff_bandits_isConsistent`: P003's pull-count consistency on
  `𝒫^K` is LMLExplore's regret-based consistency on `𝒫^K` (finitely many arms).
* `LMLExplore.Bandits.IsConsistent.isConsistentOnUnit`: LMLExplore's regret-based consistency on
  the bandits with rewards in `[0, 1]` gives P003's pull-count consistency on `𝒫^K`, from the
  BatchedBandits lemma `LMLExplore.Bandits.IsConsistent.isConsistentAtBatchEnds`
  (`Δ_a E[N_a(T)] ≤ E[R_T]`); the former names
  `Relations.isConsistentOnUnit_of_isConsistent_of_isConsistentAtBatchEnds` and
  `Incognita.P003.isConsistentOnUnit_of_isConsistent` are deprecated aliases of it.
* `Relations.isConsistentOnUnit_klucb`: LMLExplore's KL-UCB is consistent on `𝒫^K` in the sense
  of P003.
* `Relations.isConsistentAtBatchEnds_of_isConsistentOnUnit`: a learner consistent on `𝒫^K` in the
  sense of P003 is consistent at the batch ends of every grid on `𝒫`.

Implications between the nodes of [INC-P003], each from the frozen statement of the stronger node
taken as a hypothesis:

* `Relations.priorCounts_isSizeRule_of_stoppedCounts_isSizeRule`: `prop:stopped-games` (a) gives
  `lem:prior-game` (b).
* `Relations.lookahead_not_isSizeRule_of_lookahead_divergence`: `thm:main` (b) gives
  `lem:lookahead`.
* `Relations.fundamental_inequality_of_divergence_decomposition`: `thm:main` (a) gives
  `cor:fundamental`.
* `Relations.isConsistent_one_of_isConsistent_anti_of_drift_all_pairs`: `prop:drift` (d) and
  `prop:classes` (a) give `prop:classes` (b).

Same objects:

* `Relations.onlineCount_eq_pullCount'`: the pull counts `N_a(T)` of an online history are LML's
  `pullCount'`.
* `Relations.exists_priorStrategy_state_eq_hist`,
  `Relations.exists_priorStrategy_counts_eq_pullCount`: a bandit algorithm played in LML's array
  model is a prior bandit game of [INC-P003, `def:prior-game`] (pointwise, the indices of the
  stacks exchanged); the converse fails pointwise.
* `Relations.isSizeRule_pullCount_arrayModel`: hence the pull counts of LML's array model after `T'`
  rounds form a size rule.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Learning Bandits Filter

open scoped Topology ENNReal unitInterval

namespace Incognita.TransferBandits.Relations

variable {α : Type*} [MeasurableSpace α]

/-- **Same object**: an instance of `𝒫^K` [INC-P003, Definitions `def:laws` and `def:instance`] is a
kernel whose laws are all in the set `𝓜 = unitLaws` of the laws on `[0, 1]` of BatchedBandits
[INC-P006, Definition `def:instance`]. -/
lemma mem_unitBandits_iff_forall_mem_unitLaws {ν : Kernel α ℝ} :
    ν ∈ unitBandits α ↔ ∀ a, ν a ∈ Incognita.BatchedBandits.unitLaws :=
  ⟨fun h a ↦ ⟨h.1.isProbabilityMeasure a, h.2 a⟩, fun h ↦ ⟨⟨fun a ↦ (h a).1⟩, fun a ↦ (h a).2⟩⟩

/-- The class `𝒫` of BatchedBandits [INC-P006, Definition `def:instance`] is the class `𝒫^K` of
TransferBandits [INC-P003, Definitions `def:laws` and `def:instance`] restricted to the instances
whose largest mean is below `1`. -/
lemma batchedBandits_unitBandits_eq_inter :
    Incognita.BatchedBandits.unitBandits α = unitBandits α ∩ {ν | (⨆ a, (ν a)[id]) < 1} := by
  ext ν
  simp only [Incognita.BatchedBandits.unitBandits, Incognita.BatchedBandits.unitLaws, unitBandits,
    Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h, hm⟩
    exact ⟨⟨⟨fun a ↦ (h a).1⟩, fun a ↦ (h a).2⟩, hm⟩
  · rintro ⟨⟨hM, h⟩, hm⟩
    exact ⟨fun a ↦ ⟨hM.isProbabilityMeasure a, h a⟩, hm⟩

@[deprecated (since := "2026-11-19")]
alias batchedUnitBandits_eq_inter := batchedBandits_unitBandits_eq_inter

/-- `𝒫 ⊆ 𝒫^K`. -/
lemma batchedBandits_unitBandits_subset :
    Incognita.BatchedBandits.unitBandits α ⊆ unitBandits α := by
  rw [batchedBandits_unitBandits_eq_inter]
  exact Set.inter_subset_left

@[deprecated (since := "2026-11-19")]
alias batchedUnitBandits_subset := batchedBandits_unitBandits_subset

/-- With finitely many arms, an arm is suboptimal in the sense of P003 (some arm has a larger mean)
iff its gap is positive, the sense of P006 and of LML. -/
lemma gap_pos_iff_exists_lt [Finite α] {ν : Kernel α ℝ} {a : α} :
    0 < gap ν a ↔ ∃ b, (ν a)[id] < (ν b)[id] := by
  have : Nonempty α := ⟨a⟩
  rw [gap, sub_pos]
  exact lt_ciSup_iff (Finite.bddAbove_range _)

variable [DecidableEq α]

/-- **Same object** [INC-P003, Definition `def:consistency`; INC-P006, Definition
`def:consistent`]: a learner is consistent on `𝒫^K` in the sense of P003 (pull counts at every
horizon) iff it is consistent at the batch ends of the sequential grid `𝖲_s` on `𝒫^K`. The batch
ends of `𝖲_s` are `s, s + 1, …`, and a limit along every horizon is a limit along the horizons
`≥ s`. -/
lemma isConsistentOnUnit_iff_isConsistentAtBatchEnds_sequential [Finite α] {K s : ℕ}
    (hs : max 2 K ≤ s) {alg : Algorithm Unit α ℝ} :
    IsConsistentOnUnit alg ↔ Incognita.BatchedBandits.IsConsistentAtBatchEnds alg
      (Incognita.BatchedBandits.Grid.sequential s hs) (unitBandits α) := by
  constructor
  · intro h ν hν _ c hc p hp
    exact (h ν hν.2 c (gap_pos_iff_exists_lt.mp hc) p hp).comp
      (Incognita.BatchedBandits.Grid.sequential s hs).strictMono.tendsto_atTop
  · intro h ν _ hν a ha c hc
    have hψ : Tendsto (fun n : ℕ ↦ n - s + 1) atTop atTop :=
      tendsto_atTop_atTop.mpr fun b ↦ ⟨b + s, fun n hn ↦ by omega⟩
    refine ((h ν ⟨inferInstance, hν⟩ a (gap_pos_iff_exists_lt.mpr ha) c hc).comp hψ).congr' ?_
    filter_upwards [eventually_ge_atTop s] with n hn
    simp only [Function.comp_apply]
    rw [Incognita.BatchedBandits.Grid.sequential_t (by omega),
      show s + (n - s + 1) - 1 = n by omega]

/-- **Same object** [INC-P003, Definition `def:consistency`; LS, Definition 16.1]: with finitely
many arms, P003's consistency on `𝒫^K` (pull counts) is LMLExplore's consistency on `𝒫^K`
(expected regret). Proved through the sequential grid `𝖲_2` and [INC-P006, Theorem
`thm:main`(iii)] (`Incognita.BatchedBandits.isConsistentAtBatchEnds_sequential_iff`, which does not
assume `E ⊆ 𝒫`). -/
lemma isConsistentOnUnit_iff_bandits_isConsistent [Finite α] [MeasurableSingletonClass α]
    {alg : Algorithm Unit α ℝ} :
    IsConsistentOnUnit alg ↔ LMLExplore.Bandits.IsConsistent alg (unitBandits α) :=
  (isConsistentOnUnit_iff_isConsistentAtBatchEnds_sequential (K := 0) le_rfl).trans
    (Incognita.BatchedBandits.isConsistentAtBatchEnds_sequential_iff _)

@[deprecated (since := "2026-11-19")]
alias isConsistentOnUnit_iff_isConsistent := isConsistentOnUnit_iff_bandits_isConsistent

/-- Pull-count consistency on `𝒫^K` [INC-P003, Definition `def:consistency`] follows from
LMLExplore's regret-based consistency over the bandits with rewards in `[0, 1]`, through the
BatchedBandits lemma `LMLExplore.Bandits.IsConsistent.isConsistentAtBatchEnds`
(`Δ_a E[N_a(T)] ≤ E[R_T]`); on `𝖲_2` the batch ends are every horizon `T ≥ 2`. -/
lemma _root_.LMLExplore.Bandits.IsConsistent.isConsistentOnUnit [Finite α]
    [MeasurableSingletonClass α] {alg : Algorithm Unit α ℝ}
    (h : LMLExplore.Bandits.IsConsistent alg {ν : Kernel α ℝ | ∀ a, ∀ᵐ x ∂(ν a), x ∈ Set.Icc 0 1}) :
    IsConsistentOnUnit alg :=
  (isConsistentOnUnit_iff_isConsistentAtBatchEnds_sequential (K := 0) le_rfl).mpr
    ((h.isConsistentAtBatchEnds _).mono fun _ hν ↦ hν.2)

@[deprecated (since := "2026-11-19")]
alias isConsistentOnUnit_of_isConsistent_of_isConsistentAtBatchEnds :=
  LMLExplore.Bandits.IsConsistent.isConsistentOnUnit

/-- LMLExplore's KL-UCB [CGMMS13] is consistent on `𝒫^K` in the sense of pull counts
[INC-P003, Definition `def:consistency`]. -/
lemma isConsistentOnUnit_klucb [Fintype α] [Nonempty α] [StandardBorelSpace α]
    [MeasurableSingletonClass α] : IsConsistentOnUnit (LMLExplore.Bandits.klucb (α := α)) :=
  LMLExplore.Bandits.KLUCB.isConsistent.isConsistentOnUnit

/-- A learner consistent on `𝒫^K` in the sense of P003 [INC-P003, Definition `def:consistency`] is
consistent at the batch ends of every grid on `𝒫` [INC-P006, Definition `def:consistent`]. -/
lemma isConsistentAtBatchEnds_of_isConsistentOnUnit [Finite α] [MeasurableSingletonClass α]
    {alg : Algorithm Unit α ℝ} (h : IsConsistentOnUnit alg) {K : ℕ}
    (g : Incognita.BatchedBandits.Grid K) :
    Incognita.BatchedBandits.IsConsistentAtBatchEnds alg g
      (Incognita.BatchedBandits.unitBandits α) :=
  ((isConsistentOnUnit_iff_bandits_isConsistent.mp h).isConsistentAtBatchEnds g).mono
    batchedBandits_unitBandits_subset

/-! ### Implications between the nodes of P003

Each lemma takes a frozen statement of [INC-P003] as a hypothesis, in the form of its frozen type
at the arms `α` (the hypothesis `2 ≤ Fintype.card α` included), and derives another node, with the
same hypotheses. -/

/-- **Implication** [INC-P003, Proposition `prop:stopped-games` (a) ⇒ Lemma `lem:prior-game` (b)]:
the stopped counts of a prior game form a size rule with `|N'| ≤ T'` (the frozen statement
`Incognita.Statements.P003.stoppedCounts_isSizeRule`, hypothesis `h`); at the constant stopping
time `τ ≡ T'` they are the counts of the prior game over `T'` rounds, so these form a size rule
with `N'_k ≤ |N'| ≤ T'` (`Incognita.Statements.P003.priorCounts_isSizeRule`). -/
lemma priorCounts_isSizeRule_of_stoppedCounts_isSizeRule [Fintype α]
    (hK : 2 ≤ Fintype.card α)
    (h : 2 ≤ Fintype.card α → ∀ (g : PriorStrategy α) {T' : ℕ} {τ : SourceSpace α → ℕ},
      g.IsStoppingTime T' τ →
        IsSizeRule (g.stoppedCounts τ) ∧ ∀ ω, ∑ a, g.stoppedCounts τ ω a ≤ T')
    (g : PriorStrategy α) (T' : ℕ) :
    IsSizeRule (g.counts T') ∧ ∀ ω a, g.counts T' ω a ≤ T' := by
  have h' := h hK g (PriorStrategy.isStoppingTime_const g T')
  refine ⟨h'.1, fun ω a ↦ ?_⟩
  calc g.counts T' ω a ≤ ∑ b, g.counts T' ω b :=
        Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)
    _ ≤ T' := h'.2 ω

/-- **Implication** [INC-P003, Theorem `thm:main` (b) ⇒ Lemma `lem:lookahead`]: the frozen
statement `Incognita.Statements.P003.lookahead_divergence` (hypothesis `h`) contains the claim of
`lem:lookahead` (`Incognita.Statements.P003.lookahead_not_isSizeRule`: the look-ahead map is a
measurable, bounded size map and not a size rule) as its first three conjuncts; its hypotheses hold
on every finite type of arms, at `p = 1/4`, `q = 1/2`, the learner that always pulls `a₁`, `T = 0`,
`ν = δ_0` and the Bernoulli sources `ν' = Ber(1/4)^K`, `ν₂'` equal to `ν'` except
`ν₂'_{a₁} = Ber(1/2)`. -/
lemma lookahead_not_isSizeRule_of_lookahead_divergence [Fintype α]
    [MeasurableSingletonClass α] (hK : 2 ≤ Fintype.card α) (a₁ : α)
    (h : 2 ≤ Fintype.card α → ∀ (a₁ : α) {p q : I}, (p : ℝ) ∈ Set.Ioo 0 1 →
      (q : ℝ) ∈ Set.Ioo 0 1 → p ≠ q → ∀ (π : TransferAlgorithm α) (T : ℕ) {ν ν' ν₂' : Kernel α ℝ},
      ν ∈ unitBandits α → ν' ∈ unitBandits α → ν' a₁ = Ber((1 : ℝ), 0, p) →
      ν₂' a₁ = Ber((1 : ℝ), 0, q) → (∀ a, a ≠ a₁ → ν₂' a = ν' a) →
      Measurable (lookahead a₁) ∧ (∃ M : ℕ, ∀ ω a, lookahead a₁ ω a ≤ M) ∧
        ¬ IsSizeRule (lookahead a₁) ∧
        klDiv (gameMeasure ν' (lookahead a₁) ν π T) (gameMeasure ν₂' (lookahead a₁) ν π T) =
          2 * klDiv (Ber((1 : ℝ), 0, p)) (Ber((1 : ℝ), 0, q)) ∧
        ∑ a, (∫⁻ x, (sourceCount a x.1 : ℝ≥0∞) ∂(gameMeasure ν' (lookahead a₁) ν π T)) *
            klDiv (ν' a) (ν₂' a) +
          ∑ a, (∫⁻ x, (onlineCount a x.2 : ℝ≥0∞) ∂(gameMeasure ν' (lookahead a₁) ν π T)) *
            klDiv (ν a) (ν a) =
          ENNReal.ofReal (2 - p) * klDiv (Ber((1 : ℝ), 0, p)) (Ber((1 : ℝ), 0, q)) ∧
        ENNReal.ofReal (2 - p) * klDiv (Ber((1 : ℝ), 0, p)) (Ber((1 : ℝ), 0, q)) <
          2 * klDiv (Ber((1 : ℝ), 0, p)) (Ber((1 : ℝ), 0, q))) :
    Measurable (lookahead a₁) ∧ (∃ M : ℕ, ∀ ω a, lookahead a₁ ω a ≤ M) ∧
      ¬ IsSizeRule (lookahead a₁) := by
  let p : I := ⟨1 / 4, by norm_num, by norm_num⟩
  let q : I := ⟨1 / 2, by norm_num, by norm_num⟩
  have hpq : p ≠ q := fun hpq ↦ by
    have := congrArg Subtype.val hpq
    norm_num [p, q] at this
  obtain ⟨h1, h2, h3, -⟩ := h hK a₁ (p := p) (q := q) (by norm_num [p]) (by norm_num [q]) hpq
    (TransferAlgorithm.constArm a₁) 0 (ν := Kernel.const α (Measure.dirac 0))
    (ν' := LMLExplore.Bandits.bernoulliBandit fun _ ↦ p)
    (ν₂' := LMLExplore.Bandits.bernoulliBandit fun a ↦ if a = a₁ then q else p)
    (const_dirac_mem_unitBandits ⟨le_rfl, zero_le_one⟩) (bernoulliBandit_mem_unitBandits _)
    (LMLExplore.Bandits.bernoulliBandit_apply _ _)
    (by simp [LMLExplore.Bandits.bernoulliBandit_apply])
    (fun a ha ↦ by simp [LMLExplore.Bandits.bernoulliBandit_apply, ha])
  exact ⟨h1, h2, h3⟩

omit [DecidableEq α] in
/-- **Implication** [INC-P003, Theorem `thm:main` (a) ⇒ Corollary `cor:fundamental`]: the
divergence decomposition (the frozen statement `Incognita.Statements.P003.divergence_decomposition`,
hypothesis `h`), with the data-processing inequality `kl(E_P[Z], E_{P₂}[Z]) ≤ KL(P, P₂)` for `Z`
with values in `[0, 1]` [GMS19, Lemma 1] and `E_P[N'_k] = E_{ν'}[N'_k]`, gives the fundamental
inequality (`Incognita.Statements.P003.fundamental_inequality`), same hypotheses, same terms. -/
lemma fundamental_inequality_of_divergence_decomposition [Fintype α]
    (hK : 2 ≤ Fintype.card α)
    (h : 2 ≤ Fintype.card α → ∀ {N : SourceSpace α → α → ℕ}, IsSizeRule N →
      ∀ (π : TransferAlgorithm α) (T : ℕ) {ν ν' ν₂ ν₂' : Kernel α ℝ}, ν ∈ unitBandits α →
      ν' ∈ unitBandits α → ν₂ ∈ unitBandits α → ν₂' ∈ unitBandits α →
      (∀ a, ∫⁻ ω, (N ω a : ℝ≥0∞) ∂(sourceMeasure ν') < ∞) →
      klDiv (gameMeasure ν' N ν π T) (gameMeasure ν₂' N ν₂ π T) =
        ∑ a, (∫⁻ x, (sourceCount a x.1 : ℝ≥0∞) ∂(gameMeasure ν' N ν π T)) *
            klDiv (ν' a) (ν₂' a) +
          ∑ a, (∫⁻ x, (onlineCount a x.2 : ℝ≥0∞) ∂(gameMeasure ν' N ν π T)) *
            klDiv (ν a) (ν₂ a))
    {N : SourceSpace α → α → ℕ} (hN : IsSizeRule N) (π : TransferAlgorithm α) (T : ℕ)
    {ν ν' ν₂ ν₂' : Kernel α ℝ} (hν : ν ∈ unitBandits α) (hν' : ν' ∈ unitBandits α)
    (hν₂ : ν₂ ∈ unitBandits α) (hν₂' : ν₂' ∈ unitBandits α)
    (hfin : ∀ a, ∫⁻ ω, (N ω a : ℝ≥0∞) ∂(sourceMeasure ν') < ∞)
    {Z : Source α × (Fin T → α × ℝ) → ℝ} (hZ : Measurable Z) (hZ01 : ∀ x, Z x ∈ Set.Icc 0 1) :
    klDiv (Ber((1 : ℝ), 0, Set.projIcc 0 1 zero_le_one (∫ x, Z x ∂(gameMeasure ν' N ν π T))))
        (Ber((1 : ℝ), 0, Set.projIcc 0 1 zero_le_one (∫ x, Z x ∂(gameMeasure ν₂' N ν₂ π T)))) ≤
      ∑ a, (∫⁻ ω, (N ω a : ℝ≥0∞) ∂(sourceMeasure ν')) * klDiv (ν' a) (ν₂' a) +
      ∑ a, (∫⁻ x, (onlineCount a x.2 : ℝ≥0∞) ∂(gameMeasure ν' N ν π T)) * klDiv (ν a) (ν₂ a) := by
  have : IsMarkovKernel ν := hν.1
  have : IsMarkovKernel ν' := hν'.1
  have : IsMarkovKernel ν₂ := hν₂.1
  have : IsMarkovKernel ν₂' := hν₂'.1
  refine (klDiv_bernoulliMeasure_integral_le _ _ hZ hZ01).trans (le_of_eq ?_)
  rw [h hK hN π T hν hν' hν₂ hν₂' hfin]
  congr 1
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [lintegral_sourceCount_gameMeasure hN.measurable ν' ν π T a]

omit [DecidableEq α] in
/-- **Implication** [INC-P003, Proposition `prop:drift` (d) and Proposition `prop:classes` (a) ⇒
Proposition `prop:classes` (b)]: from `𝒫_L = 𝒫^K × 𝒫^K` for `L ≥ 𝟏` (first claim of the frozen
statement `Incognita.Statements.P003.drift_all_pairs`, hypothesis `hall`), the class `𝒞_L`, which
depends on `L` only through `𝒫_L`, is `𝒞_𝟏` for `L ≥ 𝟏` and is the class over every pair; with
`𝒞_{L'} ⊂ 𝒞_L` for `L ≤ L'` (`Incognita.Statements.P003.isConsistent_anti`, hypothesis `hanti`)
at `L' = max L 𝟏`, `⋂_L 𝒞_L = 𝒞_𝟏` (`Incognita.Statements.P003.isConsistent_one`). -/
lemma isConsistent_one_of_isConsistent_anti_of_drift_all_pairs [Fintype α]
    (hK : 2 ≤ Fintype.card α)
    (hanti : 2 ≤ Fintype.card α → ∀ {L L' : α → ℝ}, (∀ a, 0 < L a) → (∀ a, 0 < L' a) →
      (∀ a, L a ≤ L' a) → {π : TransferAlgorithm α | IsConsistent L' π} ⊆ {π | IsConsistent L π})
    (hall : 2 ≤ Fintype.card α → ∀ {L : α → ℝ}, (∀ a, 0 < L a) →
      (meanBand L = unitBandits α ×ˢ unitBandits α ↔ ∀ a, 1 ≤ L a) ∧
        ((∀ ν ν' : Kernel α ℝ, ν ∈ unitBandits α → ν' ∈ unitBandits α → DriftBound L ν ν') ↔
          ∀ a, 1 < L a))
    (π : TransferAlgorithm α) :
    (∀ L : α → ℝ, (∀ a, 1 ≤ L a) → (IsConsistent L π ↔ IsConsistent (fun _ ↦ 1) π)) ∧
      ((∀ L : α → ℝ, (∀ a, 0 < L a) → IsConsistent L π) ↔ IsConsistent (fun _ ↦ 1) π) ∧
      (IsConsistent (fun _ ↦ 1) π ↔
        ∀ ν ν' : Kernel α ℝ, ν ∈ unitBandits α → ν' ∈ unitBandits α →
          ∀ ρ : ℕ → SourceSpace α → α → ℕ, IsSourceStrategy ρ →
            ∀ a, (∃ b, (ν a)[id] < (ν b)[id]) → ∀ c : ℝ, 0 < c →
              Tendsto (fun T : ℕ ↦
                  (∫ p, (onlineCount a p.2 : ℝ) ∂(gameMeasure ν' (ρ T) ν π T)) / (T : ℝ) ^ c)
                atTop (𝓝 0)) := by
  have hband : ∀ L : α → ℝ, (∀ a, 1 ≤ L a) → meanBand L = unitBandits α ×ˢ unitBandits α :=
    fun L hL ↦ ((hall hK fun a ↦ one_pos.trans_le (hL a)).1).mpr hL
  have h1 : ∀ L : α → ℝ, (∀ a, 1 ≤ L a) → (IsConsistent L π ↔ IsConsistent (fun _ ↦ 1) π) :=
    fun L hL ↦ by simp only [IsConsistent, hband L hL, hband (fun _ ↦ 1) fun _ ↦ le_rfl]
  refine ⟨h1, ⟨fun h ↦ h _ fun _ ↦ one_pos, fun h L hL ↦ ?_⟩, ?_⟩
  · exact hanti hK hL (fun a ↦ one_pos.trans_le (le_max_right (L a) 1))
      (fun a ↦ le_max_left (L a) 1) ((h1 (fun a ↦ max (L a) 1) fun a ↦ le_max_right _ _).mpr h)
  · simp only [IsConsistent, hband (fun _ ↦ 1) fun _ ↦ le_rfl, Set.mem_prod, and_imp]

omit [MeasurableSpace α] in
/-- **Same object**: the number `N_a(T)` of pulls of `a` in an online history
[INC-P003, Definition `def:game`] (`onlineCount`) is LML's `pullCount'` of the history seen as an
LML history with trivial observations. -/
lemma onlineCount_eq_pullCount' {T : ℕ} (a : α) (h : Fin T → α × ℝ) :
    onlineCount a h = pullCount' T (pairsHist h) a := by
  rw [onlineCount_eq_sum, pullCount'_eq_sum]
  rfl

/-! ### Prior games and LML's array model

LML's array model `Bandits.ArrayModel` [LS, Section 4.6] plays a bandit algorithm on stacks of
rewards: at round `n` the action is `algFunction alg n (history) (ω.1 n)`, the image of the
history and of the `n`-th uniform variable, and its reward is the next unread value of the stack
of the action. On the source space of [INC-P003, Definition `def:source-space`], with the indices
of the stacks exchanged (the map of `sourceMeasure_eq_map_arrayMeasure`), this is a prior bandit
game [INC-P003, Definition `def:prior-game`]. The converse fails pointwise: the strategy of a prior
game may read the whole randomisation at every round, LML's array model reads `ω.1 n` at round
`n` only. -/

/-- LML's array model of a bandit algorithm `alg` is a prior bandit game
[INC-P003, Definition `def:prior-game`]: some strategy `g` has, at every point `ω` of the source
space and after every number `r` of rounds, the history of `alg` in the array model at the point
`(ω.1, (j, b) ↦ ω.2 b j)`. -/
lemma exists_priorStrategy_state_eq_hist [Nonempty α] [StandardBorelSpace α]
    (alg : Algorithm Unit α ℝ) :
    ∃ g : PriorStrategy α, ∀ (ω : SourceSpace α) (r : ℕ),
      (g.state ω r).2 = histPairs (Bandits.ArrayModel.hist alg (ω.1, fun j b ↦ ω.2 b j) r) := by
  let g : PriorStrategy α :=
    ⟨fun r p ↦ Bandits.ArrayModel.algFunction alg r (pairsHist p.2) (p.1 r),
      fun r ↦ (Bandits.ArrayModel.measurable_algFunction alg r).comp
        (((measurable_pairsHist r).comp measurable_snd).prodMk
          ((measurable_pi_apply r).comp measurable_fst))⟩
  refine ⟨g, fun ω r ↦ ?_⟩
  induction r with
  | zero => funext i; exact i.elim0
  | succ r ih =>
    have hcount : ∀ a, (g.state ω r).1 a =
        pullCount' r (Bandits.ArrayModel.hist alg (ω.1, fun j b ↦ ω.2 b j) r) a := fun a ↦ by
      rw [PriorStrategy.state_fst_eq_card, ih]
      rfl
    have hact : g.act r (ω.1, (g.state ω r).2) = Bandits.ArrayModel.algFunction alg r
        (Bandits.ArrayModel.hist alg (ω.1, fun j b ↦ ω.2 b j) r) (ω.1 r) := by
      rw [ih]
      rfl
    rw [PriorStrategy.state_succ, Bandits.ArrayModel.hist_add_one]
    simp only [MeasurableEquiv.finSuccProd_symm_apply]
    rw [hact, hcount, ih]
    funext i
    refine Fin.lastCases ?_ (fun k ↦ ?_) i <;> simp [histPairs]

/-- The pull counts of a bandit algorithm in LML's array model are the counts of a prior bandit
game [INC-P003, Definition `def:prior-game`], at every point of the source space (with the indices
of the stacks exchanged) and every horizon `T'`. -/
lemma exists_priorStrategy_counts_eq_pullCount [Nonempty α]
    [StandardBorelSpace α] (alg : Algorithm Unit α ℝ) :
    ∃ g : PriorStrategy α, ∀ (T' : ℕ) (ω : SourceSpace α) (a : α),
      g.counts T' ω a =
        pullCount (Bandits.ArrayModel.action alg) a T' (ω.1, fun j b ↦ ω.2 b j) := by
  obtain ⟨g, hg⟩ := exists_priorStrategy_state_eq_hist alg
  refine ⟨g, fun T' ω a ↦ ?_⟩
  rw [PriorStrategy.counts, PriorStrategy.state_fst_eq_card, hg,
    Bandits.ArrayModel.pullCount_action_eq]
  rfl

/-- The pull counts after `T'` rounds of a bandit algorithm in LML's array model, read on the
source space with the indices of the stacks exchanged, form a size rule
[INC-P003, Definition `def:size-rule`]: by `exists_priorStrategy_counts_eq_pullCount`, they are
the counts of a prior game, which are its stopped counts at `τ ≡ T'` and read only the values of
the box of the counts (the argument of [INC-P003, Lemma `lem:prior-game` (b)]). -/
lemma isSizeRule_pullCount_arrayModel [Finite α] [MeasurableSingletonClass α]
    [Nonempty α] [StandardBorelSpace α] (alg : Algorithm Unit α ℝ) (T' : ℕ) :
    IsSizeRule fun (ω : SourceSpace α) (a : α) ↦
      pullCount (Bandits.ArrayModel.action alg) a T' (ω.1, fun j b ↦ ω.2 b j) := by
  obtain ⟨g, hg⟩ := exists_priorStrategy_counts_eq_pullCount alg
  have heq : (fun (ω : SourceSpace α) (a : α) ↦
      pullCount (Bandits.ArrayModel.action alg) a T' (ω.1, fun j b ↦ ω.2 b j)) =
        g.stoppedCounts fun _ ↦ T' := funext fun ω ↦ funext fun a ↦ (hg T' ω a).symm
  rw [heq]
  exact isSizeRule_of_eqOn_box (g.measurable_stoppedCounts (g.isStoppingTime_const T'))
    fun _ _ _ h1 h2 h ↦ g.stoppedCounts_eq_of_eqOn_box (g.isStoppingTime_const T') h1 h2 h

end Incognita.TransferBandits.Relations
