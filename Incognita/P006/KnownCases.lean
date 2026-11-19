/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.Relations
public import Incognita.P006.KInf
public import Incognita.P006.Main
public import LMLExplore.Bandits.AsymptoticOptimality

/-! # P006: the verified statements on known cases

Checks of [INC-P006] on cases with a known answer: the frozen statements of the paper, used
through their proofs `Incognita.P006.<name>` (whose types are exactly those of
`Incognita.Statements.P006.<name>`), are instantiated on cases whose answer is known independently,
and the instances are proved.

* `isConsistentAtBatchEnds_of_isConsistent`: [INC-P006, Theorem `thm:main`(ii) and (iii)]: a
  learner sequentially consistent on `E ⊆ 𝒫` is consistent at the batch ends of every grid on `E`.
* `isConsistentAtBatchEnds_klucb`, `isConsistentAtBatchEnds_ucbF`: [INC-P006, Theorem `thm:main`(ii)
  and (iii)] on two learners that LMLExplore proves sequentially consistent, KL-UCB on the bandits
  with rewards in `[0, 1]` [CGMMS13] and the asymptotically optimal UCB of [LS, Algorithm 6]
  (to be checked) with `σ² = 1 / 4` (Hoeffding's lemma): both are consistent at the batch ends of
  every grid on `𝒫`. This is the consistency half of [INC-P006, Corollary `cor:ucb`], stated there
  for `UCB1`, for these two learners instead, on every grid.
* `kinf_dirac_zero`: [INC-P006, Proposition `prop:kinf`(iv)] at `p = 0`, `Ber(0) = δ_0`:
  `𝒦_inf(δ_0, μ) = kl(0, μ) = log (1 / (1 - μ))` for `0 ≤ μ < 1`. With item (iii) this shows
  that the upper bound `log ((1 - p) / (1 - μ))` of (iii) is attained
  (`kinf_bounds_upper_eq_of_dirac_zero`).
* `kinf_self_eq_zero`: (iii) at the boundary `μ = m(P) < 1`: `𝒦_inf(P, m(P)) = 0`, the value
  that (ii) gives below the mean (the competitors of mean `> m(P)` exclude `P` itself).
* `kinf_bernoulliBandit`: (iv) and (v) on a Bernoulli bandit: `K_a = kl(p_a, p⋆)`, which is also
  LMLExplore's `d_inf` over the Bernoulli laws alone, the constant of the Lai–Robbins bound for
  Bernoulli bandits [LS, Table 16.1] (to be checked); and (v) then gives
  `2 Δ_a² ≤ kl(p_a, p⋆) ≤ log ((1 - p_a) / (1 - p⋆))`.
* `kinf_bernoulli_eq_kInfUpper`: (iv) against LMLExplore's independent computation of the
  transportation cost `K⁺` (competitors of mean `≥ μ`) at the Bernoulli laws
  (`LMLExplore.Identification.kInfUpper_unitIntervalLaws_bernoulliMeasure`): the two costs
  agree, `kl(p, μ)`, for `p ≤ μ < 1`.
* `klBer_le_ofReal_log`: (iii) and (iv) together give `kl(p, μ) ≤ log ((1 - p) / (1 - μ))` for
  `0 ≤ p ≤ μ < 1`, the elementary inequality (`p log (p / μ) ≤ 0`); the lower bound of one item
  and the upper bound of the other are consistent.

## References

* [CGMMS13] O. Cappé, A. Garivier, O.-A. Maillard, R. Munos and G. Stoltz, *Kullback–Leibler upper
  confidence bounds for optimal sequential allocation*, Annals of Statistics, 2013 (as cited by
  LMLExplore, `LMLExplore.Bandits.KLUCB.isConsistent`).
* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Filter LMLExplore LMLExplore.Bandits
  LMLExplore.Identification
open scoped ENNReal unitInterval

namespace Incognita.P006.KnownCases

open Incognita.BatchedBandits

section Consistency

variable {α : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- [INC-P006, Theorem `thm:main`(ii) and (iii), consistency] A sequentially consistent learner on
`E ⊆ 𝒫` is consistent at the batch ends of every grid `g` on `E`: by (iii) it is consistent at the
batch ends of `𝖲_{t_1}`, which is finer than `g`, and (ii) passes to `g`. -/
lemma isConsistentAtBatchEnds_of_isConsistent (hK : 2 ≤ Fintype.card α)
    {E : Set (Kernel α ℝ)} (hE : E ⊆ unitBandits α) {alg : Algorithm Unit α ℝ}
    (h : IsConsistent alg E) (g : Grid (Fintype.card α)) : IsConsistentAtBatchEnds alg g E :=
  Incognita.P006.isConsistentAtBatchEnds_of_isFiner hK (Grid.sequential_isFiner le_rfl) hE
    ((Incognita.P006.isConsistentAtBatchEnds_sequential_iff hK g.le_t_one hE alg).2 h)

variable [Nonempty α] [StandardBorelSpace α]

/-- **Known case** [INC-P006, Theorem `thm:main`(ii) and (iii)] on KL-UCB: LMLExplore's
`KLUCB.isConsistent` [CGMMS13] (consistency on the bandits with rewards in `[0, 1]`) makes it
consistent at the batch ends of every grid on `𝒫`. -/
theorem isConsistentAtBatchEnds_klucb (hK : 2 ≤ Fintype.card α) (g : Grid (Fintype.card α)) :
    IsConsistentAtBatchEnds klucb g (unitBandits α) :=
  isConsistentAtBatchEnds_of_isConsistent hK subset_rfl
    (KLUCB.isConsistent.mono fun _ hν a ↦ (hν.1 a).2) g

/-- **Known case** [INC-P006, Theorem `thm:main`(ii) and (iii)] on the asymptotically optimal UCB
`ucbF (1 / 4)` [LS, Algorithm 6] (to be checked): a law on `[0, 1]` is `1 / 4`-sub-Gaussian
(Hoeffding's lemma), so LMLExplore's `UCBF.isConsistent` makes it consistent at the batch ends of
every grid on `𝒫`. -/
theorem isConsistentAtBatchEnds_ucbF (hK : 2 ≤ Fintype.card α) (g : Grid (Fintype.card α)) :
    IsConsistentAtBatchEnds (ucbF (1 / 4)) g (unitBandits α) := by
  refine isConsistentAtBatchEnds_of_isConsistent hK subset_rfl
    ((UCBF.isConsistent (by norm_num)).mono fun ν hν a ↦ ?_) g
  have := (hν.1 a).1
  exact hasSubgaussianMGF_of_mem_Icc_zero_one aemeasurable_id (hν.1 a).2

end Consistency

section KInf

/-- `kl(0, μ) = log (1 / (1 - μ))` for `0 ≤ μ < 1`, from the closed form of `kl`. -/
lemma klBer_zero_left {μ : ℝ} (h0 : 0 ≤ μ) (h1 : μ < 1) :
    klBer 0 μ = ENNReal.ofReal (Real.log (1 / (1 - μ))) := by
  rcases h0.eq_or_lt with rfl | hpos
  · simp [klBer_self]
  · rw [klBer_eq_ofReal_klBerReal ⟨le_rfl, zero_le_one⟩ ⟨h0, h1.le⟩ (klBer_ne_top ⟨hpos, h1⟩)]
    rw [klBerReal_def]
    simp [Real.log_inv]

/-- **Known case** [INC-P006, Proposition `prop:kinf`(iv)] at `p = 0`: `Ber(0) = δ_0` and
`𝒦_inf(δ_0, μ) = kl(0, μ) = log (1 / (1 - μ))` for `0 ≤ μ < 1`. -/
theorem kinf_dirac_zero {μ : ℝ} (h0 : 0 ≤ μ) (h1 : μ < 1) :
    dInf unitLaws (Measure.dirac 0) μ = ENNReal.ofReal (Real.log (1 / (1 - μ))) := by
  have h := Incognita.P006.kinf_bernoulli (p := 0) (by simpa using h0) h1
  rw [bernoulliMeasure_zero] at h
  rw [h]
  simpa using klBer_zero_left h0 h1

/-- **Known case**: the upper bound of [INC-P006, Proposition `prop:kinf`(iii)] is attained at
`P = δ_0`, for every `0 ≤ μ < 1`: `𝒦_inf(δ_0, μ) = log ((1 - m(δ_0)) / (1 - μ))`. -/
theorem kinf_bounds_upper_eq_of_dirac_zero {μ : ℝ} (h0 : 0 ≤ μ) (h1 : μ < 1) :
    dInf unitLaws (Measure.dirac 0) μ =
      ENNReal.ofReal (Real.log ((1 - ∫ x, id x ∂(Measure.dirac (0 : ℝ))) / (1 - μ))) := by
  rw [kinf_dirac_zero h0 h1]
  simp

/-- **Known case** [INC-P006, Proposition `prop:kinf`(iii)] at the boundary `μ = m(P) < 1`:
`𝒦_inf(P, m(P)) = 0`, since the upper bound is `log 1 = 0`. -/
theorem kinf_self_eq_zero {P : Measure ℝ} (hP : P ∈ unitLaws) (hp : ∫ x, id x ∂P < 1) :
    dInf unitLaws P (∫ x, id x ∂P) = 0 := by
  have h := (Incognita.P006.kinf_bounds hP le_rfl hp).2.2.1
  rw [div_self (sub_pos.2 hp).ne', Real.log_one, ENNReal.ofReal_zero] at h
  exact nonpos_iff_eq_zero.1 h

/-- **Known case** [INC-P006, Proposition `prop:kinf`(iv) and (v)] on a Bernoulli bandit with
means `p_b < 1` and a suboptimal arm `a`: `K_a = kl(p_a, p⋆)` with `p⋆ = max_b p_b`; it is also
LMLExplore's `d_inf` over the Bernoulli laws only, the constant of the Lai–Robbins bound for
Bernoulli bandits [LS, Table 16.1] (to be checked); and
`2 Δ_a² ≤ kl(p_a, p⋆) ≤ log ((1 - p_a) / (1 - p⋆))`. -/
theorem kinf_bernoulliBandit {α : Type*} [Finite α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : α → I) (hp : ∀ a, (p a : ℝ) < 1) {a : α}
    (ha : 0 < Bandits.gap (bernoulliBandit p) a) :
    dInf unitLaws (bernoulliBandit p a) (⨆ b, ∫ x, id x ∂(bernoulliBandit p b)) =
        klBer (p a) (⨆ b, (p b : ℝ)) ∧
      dInf (Set.range fun q : I ↦ Ber((1 : ℝ), 0, q)) (bernoulliBandit p a)
          (⨆ b, ∫ x, id x ∂(bernoulliBandit p b)) = klBer (p a) (⨆ b, (p b : ℝ)) ∧
      ENNReal.ofReal (2 * Bandits.gap (bernoulliBandit p) a ^ 2) ≤ klBer (p a) (⨆ b, (p b : ℝ)) ∧
      klBer (p a) (⨆ b, (p b : ℝ)) ≤
        ENNReal.ofReal (Real.log ((1 - p a) / (1 - ⨆ b, (p b : ℝ)))) := by
  have hν := bernoulliBandit_mem_unitBandits p hp
  have hmax : (⨆ b, ∫ x, id x ∂(bernoulliBandit p b)) = ⨆ b, (p b : ℝ) := by
    simp only [integral_id_bernoulliBandit]
  have hle : (p a : ℝ) ≤ ⨆ b, (p b : ℝ) :=
    le_ciSup (Finite.bddAbove_range fun b ↦ (p b : ℝ)) a
  have hlt : ⨆ b, (p b : ℝ) < 1 := hmax ▸ hν.2
  have h4 := Incognita.P006.kinf_bernoulli hle hlt
  obtain ⟨-, h5l, h5u, -⟩ := Incognita.P006.kinf_bounds_of_gap_pos hν ha
  rw [hmax, bernoulliBandit_apply, h4] at h5l h5u
  have hm : ∫ x, id x ∂Ber((1 : ℝ), 0, p a) = (p a : ℝ) :=
    TauCeti.Probability.integral_id_bernoulliMeasure _
  rw [hm] at h5u
  refine ⟨?_, ?_, h5l, h5u⟩
  · rw [hmax, bernoulliBandit_apply, h4]
  · rw [hmax, bernoulliBandit_apply, dInf_range_bernoulliMeasure hle hlt]

/-- **Known case** [INC-P006, Proposition `prop:kinf`(iv)] against LMLExplore's independent
computation of the transportation cost `K⁺` over the laws on `[0, 1]` at the Bernoulli laws
(`kInfUpper_unitIntervalLaws_bernoulliMeasure`): for `p ≤ μ < 1`, `𝒦_inf(Ber(p), μ)`
(competitors of mean `> μ`) equals `K⁺(Ber(p), μ)` (competitors of mean `≥ μ`), both `kl(p, μ)`. -/
theorem kinf_bernoulli_eq_kInfUpper {p : I} {μ : ℝ} (hpμ : (p : ℝ) ≤ μ) (hμ : μ < 1) :
    dInf unitLaws Ber((1 : ℝ), 0, p) μ =
      kInfUpper ProbabilityMeasure.toMeasure unitIntervalLaws (fun Q ↦ (Q : Measure ℝ)[id])
        ⟨Ber((1 : ℝ), 0, p), inferInstance⟩ μ := by
  rw [Incognita.P006.kinf_bernoulli hpμ hμ,
    kInfUpper_unitIntervalLaws_bernoulliMeasure hpμ hμ.le]

/-- **Lower against upper bound** [INC-P006, Proposition `prop:kinf`(iii) and (iv)]: at `P = Ber(p)`
the value `kl(p, μ)` of (iv) is below the upper bound of (iii), `kl(p, μ) ≤ log ((1 - p) / (1 - μ))`
for `p ≤ μ < 1`: the two items are consistent (the inequality is the elementary
`p log (p / μ) ≤ 0`). -/
theorem klBer_le_ofReal_log {p : I} {μ : ℝ} (hpμ : (p : ℝ) ≤ μ) (hμ : μ < 1) :
    klBer p μ ≤ ENNReal.ofReal (Real.log ((1 - p) / (1 - μ))) := by
  have hmean : ∫ x, id x ∂Ber((1 : ℝ), 0, p) = (p : ℝ) :=
    TauCeti.Probability.integral_id_bernoulliMeasure _
  have h3 := (Incognita.P006.kinf_bounds (bernoulliMeasure_mem_unitLaws p)
    (hmean.trans_le hpμ) hμ).2.2.1
  rw [hmean, Incognita.P006.kinf_bernoulli hpμ hμ] at h3
  exact h3

end KInf

end Incognita.P006.KnownCases
