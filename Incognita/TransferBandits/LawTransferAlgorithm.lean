/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.LawDrift
public import Incognita.TransferBandits.LMLHistory
public import Mathlib.Probability.UniformOn

/-! # The algorithm KL-UCB-`d`-Transfer

The learner of [INC-P002, def:algo] (paper `P002-transfer-drift-between-laws`), as a transfer
learner of [INC-P003] (`TransferAlgorithm α`).

## Conventions

* Rounds are indexed from `0`: the kernel of round `n` is the paper's choice of `A_{n+1}`, from
  the source data and the history of the `n` first rounds.
* At the rounds `n < K` (the paper's rounds `t = n + 1 = 1, …, K`) the learner pulls the arm
  `(Fintype.equivFin α).symm n`: the paper's "pull arm `t`", for the enumeration of the arms given
  by `Fintype.equivFin α`.
* At the rounds `n ≥ K` it computes, with the history of `t = n` rounds (the paper's "end of round
  `t ≥ K`"), the index `U_k(t)` of every arm and pulls an arm drawn uniformly among the maximisers
  of the index (the paper's ties broken uniformly at random with `V_t`).
* The index is the supremum in `EReal` of the means of the feasible target laws, so that
  `sup ∅ = -∞` (the paper's `max ∅ := -∞`); the paper shows the maximum is attained when the set
  is nonempty (lem:index), so the supremum is the paper's maximum.
* The learner reads the history and the source data only through counts: for every arm `k` and
  point `y ∈ S`, the number of source values of arm `k` equal to `y`, the number of pulls of `k`,
  and the number of pulls of `k` with reward `y`. The empirical laws are these counts divided by
  the sizes; when `N'_k = 0` the source law is the zero vector, which plays no role since its
  term is `N'_k · KL = 0` (the paper's convention "`N'_k KL(ν̂'_k, q') := 0` when `N'_k = 0`"). On
  the event that every observed value lies in `S` (of full measure for instances on `S`), these
  are the paper's empirical laws. This makes the kernels measurable: they factor through a
  countable set of statistics.

## Main definitions

* `explorationRate t`: `δ_t = log (t ∨ 3) + log log (t ∨ 3)`.
* `lawIndex 𝓕 l n r n' r' δ`: the index (eq:index) for `N_k(t) = n`, `ν̂_k(t) = r`, `N'_k = n'`,
  `ν̂'_k = r'`, `L_k = l` and `δ_t = δ`.
* `lawStat n x`: the counts read by the learner at round `n`.
* `klucbLawTransfer 𝓕 L`: KL-UCB-`d`-Transfer, with `d = d_𝓕` and the bounds `L`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace Incognita.TransferBandits

/-- The exploration rate `δ_t = log (t ∨ 3) + log log (t ∨ 3)` [INC-P002, eq:rate]. -/
noncomputable def explorationRate (t : ℕ) : ℝ :=
  Real.log (max (t : ℝ) 3) + Real.log (Real.log (max (t : ℝ) 3))

/-- The index of [INC-P002, eq:index]: the supremum, in `EReal`, of the means `m(q)` over the pairs
`(q, q') ∈ 𝒫_S²` with `d_𝓕(q, q') ≤ l` and `n KL(r, q) + n' KL(r', q') ≤ δ`, where `n = N_k(t)`,
`r = ν̂_k(t)`, `n' = N'_k`, `r' = ν̂'_k`, `l = L_k` and `δ = δ_t`. The products are in `ℝ≥0∞`, so
that `0 · KL = 0`, and `sup ∅ = ⊥ = -∞`. -/
noncomputable def lawIndex {S : Finset ℝ} (𝓕 : Set (S → ℝ)) (l : ℝ) (n : ℕ) (r : S → ℝ)
    (n' : ℕ) (r' : S → ℝ) (δ : ℝ) : EReal :=
  sSup ((fun p : (S → ℝ) × (S → ℝ) ↦ ((vecMean p.1 : ℝ) : EReal)) ''
    {p | p.1 ∈ probVecs S ∧ p.2 ∈ probVecs S ∧ ipm 𝓕 p.1 p.2 ≤ l ∧
      (n : ℝ≥0∞) * vecKL r p.1 + (n' : ℝ≥0∞) * vecKL r' p.2 ≤ ENNReal.ofReal δ})

/-- The empirical vector `y ↦ cnt(y) / m` of counts `cnt` out of `m` values. -/
noncomputable def empVec {S : Finset ℝ} (cnt : S → ℕ) (m : ℕ) : S → ℝ :=
  fun y ↦ (cnt y : ℝ) / m

variable {α : Type*} [MeasurableSpace α]

/-- The statistics of the source data and of the history of `n` rounds read by
KL-UCB-`d`-Transfer: the sizes `N'_k`, the numbers of source values of arm `k` equal to `y`, the
numbers of pulls `N_k(n)` (`onlineCount`) and the numbers of pulls of `k` with reward `y`. -/
noncomputable def lawStat (S : Finset ℝ) (n : ℕ) (x : Source α × (Fin n → α × ℝ)) :
    (α → ℕ) × (α → S → ℕ) × (α → ℕ) × (α → S → ℕ) := by
  classical
  exact (fun k ↦ sourceCount k x.1,
    fun k y ↦ ∑ j ∈ Finset.range (x.1.1 k), if x.1.2 k j = y then 1 else 0,
    fun k ↦ onlineCount k x.2,
    fun k y ↦ ∑ i, if (x.2 i).1 = k ∧ (x.2 i).2 = y then 1 else 0)

/-- The index `U_k(t)` of every arm `k` computed from the statistics `z = lawStat S t x` at the end
of round `t` [INC-P002, def:algo]. -/
noncomputable def statIndex {S : Finset ℝ} (𝓕 : Set (S → ℝ)) (L : α → ℝ) (t : ℕ)
    (z : (α → ℕ) × (α → S → ℕ) × (α → ℕ) × (α → S → ℕ)) (k : α) : EReal :=
  lawIndex 𝓕 (L k) (z.2.2.1 k) (empVec (z.2.2.2 k) (z.2.2.1 k)) (z.1 k)
    (empVec (z.2.1 k) (z.1 k)) (explorationRate t)

/-- The law of the arm pulled at round `n` (0-based) by KL-UCB-`d`-Transfer, given the statistics
`z`: the arm `(Fintype.equivFin α).symm n` if `n < K`, otherwise the uniform law on the maximisers
of the index `statIndex 𝓕 L n z`. -/
noncomputable def lawPolicyMeasure [Fintype α] {S : Finset ℝ} (𝓕 : Set (S → ℝ)) (L : α → ℝ)
    (n : ℕ) (z : (α → ℕ) × (α → S → ℕ) × (α → ℕ) × (α → S → ℕ)) : Measure α :=
  if h : n < Fintype.card α then Measure.dirac ((Fintype.equivFin α).symm ⟨n, h⟩)
  else uniformOn {k | ∀ j, statIndex 𝓕 L n z j ≤ statIndex 𝓕 L n z k}

lemma measurable_lawStat [Finite α] [MeasurableSingletonClass α] (S : Finset ℝ) (n : ℕ) :
    Measurable (lawStat (α := α) S n) := by
  classical
  unfold lawStat
  refine Measurable.prodMk (measurable_fst.fst) (Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_))
  · refine Measurable.of_eval fun k ↦ Measurable.of_eval fun y ↦ ?_
    have h : Measurable fun s : Source α ↦
        ∑ j ∈ Finset.range (s.1 k), if s.2 k j = (y : ℝ) then 1 else 0 := by
      refine measurable_from_prod_countable_right fun m ↦ ?_
      dsimp only
      refine Finset.measurable_sum (M := ℕ) _ fun j _ ↦
        Measurable.ite ?_ measurable_const measurable_const
      exact (measurableSet_singleton (y : ℝ)).preimage
        ((measurable_pi_apply j).comp (measurable_pi_apply k))
    exact h.comp measurable_fst
  · exact measurable_pi_iff.2 fun k ↦ (measurable_onlineCount k).comp measurable_snd
  · refine Measurable.of_eval fun k ↦ Measurable.of_eval fun y ↦ ?_
    refine Finset.measurable_sum (M := ℕ) _ fun i _ ↦
      Measurable.ite ?_ measurable_const measurable_const
    exact ((measurableSet_singleton k).preimage
      (measurable_fst.comp ((measurable_pi_apply i).comp measurable_snd))).inter
      ((measurableSet_singleton (y : ℝ)).preimage
      (measurable_snd.comp ((measurable_pi_apply i).comp measurable_snd)))

lemma isProbabilityMeasure_lawPolicyMeasure [Fintype α] [Nonempty α] [MeasurableSingletonClass α]
    {S : Finset ℝ} (𝓕 : Set (S → ℝ)) (L : α → ℝ) (n : ℕ)
    (z : (α → ℕ) × (α → S → ℕ) × (α → ℕ) × (α → S → ℕ)) :
    IsProbabilityMeasure (lawPolicyMeasure 𝓕 L n z) := by
  unfold lawPolicyMeasure
  split_ifs with h
  · infer_instance
  · obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ (statIndex 𝓕 L n z)
      Finset.univ_nonempty
    exact isProbabilityMeasure_uniformOn (Set.toFinite _) ⟨k, fun j ↦ hk j (Finset.mem_univ j)⟩

/-- **KL-UCB-`d`-Transfer** [INC-P002, def:algo], for the integral probability metric `d = d_𝓕`
and the drift bounds `L`: at the rounds `n < K` it pulls the arm `(Fintype.equivFin α).symm n`;
at every later round `n` it pulls an arm drawn uniformly among the maximisers of the index
`U_k(n)` of eq:index, computed from the source data and the history of the `n` first rounds. -/
noncomputable def klucbLawTransfer [Fintype α] [Nonempty α] [MeasurableSingletonClass α]
    {S : Finset ℝ} (𝓕 : Set (S → ℝ)) (L : α → ℝ) : TransferAlgorithm α where
  policy n := (Kernel.ofFunOfCountable (lawPolicyMeasure 𝓕 L n)).comap (lawStat S n)
    (measurable_lawStat S n)
  isMarkovKernel_policy n := ⟨fun x ↦ by
    rw [Kernel.comap_apply]
    exact isProbabilityMeasure_lawPolicyMeasure 𝓕 L n _⟩

end Incognita.TransferBandits
