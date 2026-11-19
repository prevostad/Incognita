/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.LowerBound.Assembly
public import Incognita.BatchedBandits.TwoBatchesAhead

/-! # The lower bounds `x² / 𝒦_inf` on a convergent grid

The lower bounds of [INC-P000, Theorem `thm:lower`(ii)–(iii)] on a grid with `x_ℓ → x > 0`, from
the lower bound two batches ahead (`eventually_lt_integral_pullCount_div_log_t_add_two`) and the
assembly lemmas of `Incognita.BatchedBandits.LowerBound.Assembly`.

## Main statements

* `eventually_lt_integral_pullCount_div_log_t_of_isBigO`: if `E_ν[N_a(t_ℓ)] = O(log t_ℓ)`, then
  `liminf_ℓ E_ν[N_a(t_ℓ)] / log t_ℓ ≥ x² / 𝒦_inf(ν_a, m⋆)`.
* `eventually_lt_regret_div_log_t_of_forall`: per-arm lower bounds give the regret lower bound.
* `frequently_lt_regret_div_log_t_of_not_isBigO`: if the counts of a suboptimal arm are not
  logarithmic, the regret has `limsup ℜ(t_ℓ) / log t_ℓ = ∞`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Bandits Filter Real Finset

open scoped Topology

namespace Incognita.BatchedBandits

variable {α : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
  {K : ℕ}

omit [Fintype α] in
/-- **The lower bound `x² / 𝒦_inf` under logarithmic counts** [INC-P000, Theorem `thm:lower`(ii),
second claim, and Case A of its proof]: on a grid with `x_ℓ → x > 0`, for a learner batched on
it and consistent at its batch ends on `𝒫`, `ν ∈ 𝒫` and `gap ν a > 0`, if
`E_ν[N_a(t_ℓ)] = O(log t_ℓ)` then `liminf_ℓ E_ν[N_a(t_ℓ)] / log t_ℓ ≥ x² / 𝒦_inf(ν_a, m⋆)`. -/
lemma eventually_lt_integral_pullCount_div_log_t_of_isBigO [Finite α] (g : Grid K) {x : ℝ}
    (hx : 0 < x)
    (hg : Tendsto g.ratio atTop (𝓝 x)) {alg : Algorithm Unit α ℝ} (hb : IsBatched alg g)
    (hc : IsConsistentAtBatchEnds alg g (unitBandits α)) {ν : Kernel α ℝ} [IsMarkovKernel ν]
    (hν : ν ∈ unitBandits α) {a : α} (ha : 0 < gap ν a)
    (hO : Asymptotics.IsBigO atTop
      (fun ℓ ↦ ∫ ω, (pullCount IT.action a (g.t ℓ) ω : ℝ)
        ∂(trajMeasure alg (Environment.bandit ν))) (fun ℓ ↦ Real.log (g.t ℓ))) :
    ∀ c < x ^ 2 * (1 / (LMLExplore.Bandits.dInf unitLaws (ν a)
        (⨆ b, ∫ y, id y ∂(ν b))).toReal),
      ∀ᶠ ℓ in atTop, c < (∫ ω, (pullCount IT.action a (g.t ℓ) ω : ℝ)
          ∂(trajMeasure alg (Environment.bandit ν))) / Real.log (g.t ℓ) := by
  obtain ⟨C, hC⟩ := hO.bound
  have hlog : ∃ C', ∀ᶠ ℓ in atTop, (∫ ω, (pullCount IT.action a (g.t (ℓ + 1)) ω : ℝ)
      ∂(trajMeasure alg (Environment.bandit ν))) ≤ C' * Real.log (g.t (ℓ + 2)) := by
    refine ⟨max C 0, ?_⟩
    filter_upwards [(tendsto_add_atTop_nat 1).eventually hC] with ℓ hℓ
    have hlog1 : 0 < Real.log (g.t (ℓ + 1)) := g.logEnd_pos (ℓ := ℓ + 1) (by omega)
    have hle : Real.log (g.t (ℓ + 1)) ≤ Real.log (g.t (ℓ + 2)) :=
      Real.log_le_log (by exact_mod_cast (show 0 < g.t (ℓ + 1) by
        have := g.two_le_t (ℓ := ℓ + 1) (by omega); omega))
        (by exact_mod_cast g.strictMono.monotone (Nat.le_succ (ℓ + 1)))
    rw [Real.norm_of_nonneg (integral_nonneg fun _ ↦ Nat.cast_nonneg _),
      Real.norm_of_nonneg hlog1.le] at hℓ
    calc _ ≤ C * Real.log (g.t (ℓ + 1)) := hℓ
      _ ≤ max C 0 * Real.log (g.t (ℓ + 1)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hlog1.le
      _ ≤ max C 0 * Real.log (g.t (ℓ + 2)) :=
          mul_le_mul_of_nonneg_left hle (le_max_right _ _)
  exact eventually_lt_div_log_t_of_eventually_lt_div_log_t_add_two g hx hg
    (fun ℓ ↦ integral_nonneg fun _ ↦ Nat.cast_nonneg _)
    (eventually_lt_integral_pullCount_div_log_t_add_two g hb hc hν ha hlog)

omit [MeasurableSingletonClass α] in
/-- **The regret from the counts** [INC-P000, Theorem `thm:lower`(iii)]: if every suboptimal arm
`c` has `liminf_ℓ E_ν[N_c(t_ℓ)] / log t_ℓ ≥ L_c`, then
`liminf_ℓ ℜ(t_ℓ) / log t_ℓ ≥ ∑_{c : Δ_c > 0} Δ_c L_c`, with `ℜ(t) = ∑_c Δ_c E_ν[N_c(t)]`. -/
lemma eventually_lt_regret_div_log_t_of_forall (g : Grid K) {alg : Algorithm Unit α ℝ}
    {ν : Kernel α ℝ} [IsMarkovKernel ν] {L : α → ℝ}
    (h : ∀ c, 0 < gap ν c → ∀ b < L c, ∀ᶠ ℓ in atTop,
      b < (∫ ω, (pullCount IT.action c (g.t ℓ) ω : ℝ)
        ∂(trajMeasure alg (Environment.bandit ν))) / Real.log (g.t ℓ)) :
    ∀ c' < ∑ c ∈ Finset.univ.filter (fun c ↦ 0 < gap ν c), gap ν c * L c,
      ∀ᶠ ℓ in atTop, c' < (∑ c, gap ν c * ∫ ω, (pullCount IT.action c (g.t ℓ) ω : ℝ)
          ∂(trajMeasure alg (Environment.bandit ν))) / Real.log (g.t ℓ) := by
  intro c' hc'
  set S := Finset.univ.filter (fun c ↦ 0 < gap ν c)
  have hsum := eventually_lt_sum_mul S (w := fun c ↦ gap ν c) (L := L)
    (u := fun c ℓ ↦ (∫ ω, (pullCount IT.action c (g.t ℓ) ω : ℝ)
      ∂(trajMeasure alg (Environment.bandit ν))) / Real.log (g.t ℓ))
    (fun c hcS ↦ (Finset.mem_filter.mp hcS).2)
    (fun c hcS ↦ h c (Finset.mem_filter.mp hcS).2) c' hc'
  filter_upwards [hsum] with ℓ hℓ
  have hsplit : (∑ c, gap ν c * ∫ ω, (pullCount IT.action c (g.t ℓ) ω : ℝ)
      ∂(trajMeasure alg (Environment.bandit ν))) / Real.log (g.t ℓ) =
      ∑ c ∈ S, gap ν c * ((∫ ω, (pullCount IT.action c (g.t ℓ) ω : ℝ)
        ∂(trajMeasure alg (Environment.bandit ν))) / Real.log (g.t ℓ)) := by
    rw [Finset.sum_div, ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun c ↦ 0 < gap ν c)]
    have h0 : ∑ c ∈ Finset.univ.filter (fun c ↦ ¬ 0 < gap ν c),
        gap ν c * (∫ ω, (pullCount IT.action c (g.t ℓ) ω : ℝ)
          ∂(trajMeasure alg (Environment.bandit ν))) / Real.log (g.t ℓ) = 0 := by
      refine Finset.sum_eq_zero fun c hcS ↦ ?_
      have : gap ν c = 0 := le_antisymm (not_lt.mp (Finset.mem_filter.mp hcS).2) gap_nonneg
      simp [this]
    rw [h0, add_zero]
    exact Finset.sum_congr rfl fun c _ ↦ by ring
  rw [hsplit]
  exact hℓ

omit [MeasurableSingletonClass α] in
/-- **Case B for the regret** [INC-P000, Theorem `thm:main`, regret, `limsup`]: if a suboptimal
arm `c` has counts that are not `O(log t_ℓ)`, then `limsup_ℓ ℜ(t_ℓ) / log t_ℓ = ∞`. -/
lemma frequently_lt_regret_div_log_t_of_not_isBigO (g : Grid K) {alg : Algorithm Unit α ℝ}
    {ν : Kernel α ℝ} [IsMarkovKernel ν] {c : α} (hgap : 0 < gap ν c)
    (hO : ¬ Asymptotics.IsBigO atTop
      (fun ℓ ↦ ∫ ω, (pullCount IT.action c (g.t ℓ) ω : ℝ)
        ∂(trajMeasure alg (Environment.bandit ν))) (fun ℓ ↦ Real.log (g.t ℓ))) (c' : ℝ) :
    ∃ᶠ ℓ in atTop, c' < (∑ b, gap ν b * ∫ ω, (pullCount IT.action b (g.t ℓ) ω : ℝ)
        ∂(trajMeasure alg (Environment.bandit ν))) / Real.log (g.t ℓ) := by
  have hB := frequently_lt_div_log_t_of_not_isBigO g
    (fun ℓ ↦ integral_nonneg fun _ ↦ Nat.cast_nonneg _) hO (c' / gap ν c)
  refine (hB.and_eventually (eventually_ge_atTop 1)).mono fun ℓ ⟨hℓ, hℓ1⟩ ↦ ?_
  have hlog := g.logEnd_pos hℓ1
  unfold Grid.logEnd at hlog
  rw [div_lt_iff₀ hgap] at hℓ
  calc c' < (∫ ω, (pullCount IT.action c (g.t ℓ) ω : ℝ)
        ∂(trajMeasure alg (Environment.bandit ν))) / Real.log (g.t ℓ) * gap ν c := hℓ
    _ = gap ν c * (∫ ω, (pullCount IT.action c (g.t ℓ) ω : ℝ)
        ∂(trajMeasure alg (Environment.bandit ν))) / Real.log (g.t ℓ) := by ring
    _ ≤ _ := by
        refine div_le_div_of_nonneg_right ?_ hlog.le
        exact Finset.single_le_sum (f := fun b ↦ gap ν b * ∫ ω,
          (pullCount IT.action b (g.t ℓ) ω : ℝ) ∂(trajMeasure alg (Environment.bandit ν)))
          (fun b _ ↦ mul_nonneg gap_nonneg (integral_nonneg fun _ ↦ Nat.cast_nonneg _))
          (Finset.mem_univ c)

end Incognita.BatchedBandits
