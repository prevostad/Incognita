/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.LowerBound
public import Incognita.BatchedBandits.HY.InfoModel

/-! # Assembling the upper bound of P000

The deterministic steps of the proof of [INC-P000, Theorem `thm:upper`] (Subsection
`sec:app-proofupper`) that come after the non-asymptotic upper bounds (Propositions `prop:dyA`
and `prop:fixedC`): an upper bound `limsup_ℓ E_ν[N_a(t_ℓ)] / log t_ℓ ≤ x² / 𝒦_inf(ν_a, m⋆)` for
every instance of `𝒫` and every suboptimal arm gives consistency, then (with the lower bound of
Theorem `thm:lower`) the limit of the counts, then the limit of the regret. The `limsup` bound is
written `∀ c > L, ∀ᶠ ℓ in atTop, u_ℓ / log t_ℓ < c`, the form dual to the `liminf` bounds of the
lower bound.

* `isBigO_log_t_of_eventually_div_lt`: a nonnegative sequence with `limsup u_ℓ / log t_ℓ < ∞` is
  `O(log t_ℓ)`.
* `isConsistentAtBatchEnds_of_isBigO`: logarithmic counts at the batch ends, for every instance
  of a class and every suboptimal arm, give consistency at the batch ends on that class.
* `tendsto_div_log_t_of_upper`: the `limsup` bound and the lower bound `x² / 𝒦_inf` of
  Theorem `thm:lower` give the limit of the counts, for a batched learner.
* `tendsto_regret_div_log_t_of_tendsto`: the limits of the counts give the limit of the regret.
* `hy_isConsistent_of_upper`, `hy_tendsto_count_of_upper`, `hy_tendsto_regret_of_upper`: the three
  frozen statements of Theorem `thm:upper` for HY, from the `limsup` bound for HY.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Bandits Filter Real Finset

open scoped Topology

namespace Incognita.BatchedBandits

variable {α : Type*} [MeasurableSpace α] [DecidableEq α] {K : ℕ}

/-- A nonnegative sequence `u` with `u_ℓ / log t_ℓ < C` eventually is `O(log t_ℓ)`. -/
lemma isBigO_log_t_of_eventually_div_lt (g : Grid K) {u : ℕ → ℝ} (hu0 : ∀ ℓ, 0 ≤ u ℓ) {C : ℝ}
    (hC : ∀ᶠ ℓ in atTop, u ℓ / Real.log (g.t ℓ) < C) :
    Asymptotics.IsBigO atTop u (fun ℓ ↦ Real.log (g.t ℓ)) := by
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [hC, eventually_ge_atTop 1] with ℓ hℓ hℓ1
  have hlog : 0 < Real.log (g.t ℓ) := g.logEnd_pos hℓ1
  rw [Real.norm_of_nonneg (hu0 ℓ), Real.norm_of_nonneg hlog.le]
  rw [div_lt_iff₀ hlog] at hℓ
  exact hℓ.le

/-- **Consistency from logarithmic counts** [INC-P000, proof of Theorem `thm:upper`,
"consistency"]: if, for every instance `ν` of a class `E` and every suboptimal arm `c`,
`E_ν[N_c(t_ℓ)] = O(log t_ℓ)`, then the learner is consistent at the batch ends on `E`, since
`log t = o(t ^ p)` for every `p > 0`. -/
lemma isConsistentAtBatchEnds_of_isBigO (g : Grid K) {alg : Algorithm Unit α ℝ}
    {E : Set (Kernel α ℝ)}
    (h : ∀ ν ∈ E, ∀ [IsMarkovKernel ν], ∀ c, 0 < gap ν c → Asymptotics.IsBigO atTop
      (fun ℓ ↦ ∫ ω, (pullCount IT.action c (g.t ℓ) ω : ℝ)
        ∂(trajMeasure alg (Environment.bandit ν))) (fun ℓ ↦ Real.log (g.t ℓ))) :
    IsConsistentAtBatchEnds alg g E := by
  intro ν hν _ c hc p hp
  have ht : Tendsto (fun ℓ ↦ (g.t ℓ : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp g.strictMono.tendsto_atTop
  have hlog : Asymptotics.IsLittleO atTop (fun ℓ ↦ Real.log (g.t ℓ))
      (fun ℓ ↦ (g.t ℓ : ℝ) ^ p) :=
    (isLittleO_log_rpow_atTop hp).comp_tendsto ht
  exact ((h ν hν c hc).trans_isLittleO hlog).tendsto_div_nhds_zero

/-- **Consistency from the `limsup` bound** [INC-P000, proof of Theorem `thm:upper`,
"consistency"]: a learner whose counts satisfy
`limsup_ℓ E_ν[N_c(t_ℓ)] / log t_ℓ ≤ x² / 𝒦_inf(ν_c, m⋆)` for every `ν ∈ 𝒫` and every suboptimal
arm `c` is consistent at the batch ends on `𝒫`. -/
lemma isConsistentAtBatchEnds_of_upper (g : Grid K) {x : ℝ}
    {alg : Algorithm Unit α ℝ}
    (hup : ∀ ν ∈ unitBandits α, ∀ [IsMarkovKernel ν], ∀ a, 0 < gap ν a →
      ∀ c > x ^ 2 / (LMLExplore.Bandits.dInf unitLaws (ν a) (⨆ b, ∫ y, id y ∂(ν b))).toReal,
        ∀ᶠ ℓ in atTop, (∫ ω, (pullCount IT.action a (g.t ℓ) ω : ℝ)
          ∂(trajMeasure alg (Environment.bandit ν))) / Real.log (g.t ℓ) < c) :
    IsConsistentAtBatchEnds alg g (unitBandits α) :=
  isConsistentAtBatchEnds_of_isBigO g fun ν hν _ c hc ↦
    isBigO_log_t_of_eventually_div_lt g (fun _ ↦ integral_nonneg fun _ ↦ Nat.cast_nonneg _)
      (hup ν hν c hc _ (lt_add_one _))

/-- **The limit of the counts from the `limsup` bound** [INC-P000, proof of Theorem `thm:upper`,
"lower bound"]: on a grid with `x_ℓ → x ≥ 1`, a learner batched on it whose counts satisfy the
`limsup` bound of `isConsistentAtBatchEnds_of_upper` is consistent at the batch ends on `𝒫`, and
then Theorem `thm:lower` (with the logarithmic counts) gives
`lim_ℓ E_ν[N_a(t_ℓ)] / log t_ℓ = x² / 𝒦_inf(ν_a, m⋆)`. -/
lemma tendsto_div_log_t_of_upper [Finite α] [MeasurableSingletonClass α] (g : Grid K) {x : ℝ}
    (hx : 1 ≤ x) (hg : Tendsto g.ratio atTop (𝓝 x)) {alg : Algorithm Unit α ℝ}
    (hb : IsBatched alg g)
    (hup : ∀ ν ∈ unitBandits α, ∀ [IsMarkovKernel ν], ∀ a, 0 < gap ν a →
      ∀ c > x ^ 2 / (LMLExplore.Bandits.dInf unitLaws (ν a) (⨆ b, ∫ y, id y ∂(ν b))).toReal,
        ∀ᶠ ℓ in atTop, (∫ ω, (pullCount IT.action a (g.t ℓ) ω : ℝ)
          ∂(trajMeasure alg (Environment.bandit ν))) / Real.log (g.t ℓ) < c)
    {ν : Kernel α ℝ} [IsMarkovKernel ν] (hν : ν ∈ unitBandits α) {a : α} (ha : 0 < gap ν a) :
    Tendsto (fun ℓ ↦ (∫ ω, (pullCount IT.action a (g.t ℓ) ω : ℝ)
        ∂(trajMeasure alg (Environment.bandit ν))) / Real.log (g.t ℓ)) atTop
      (𝓝 (x ^ 2 / (LMLExplore.Bandits.dInf unitLaws (ν a) (⨆ b, ∫ y, id y ∂(ν b))).toReal)) := by
  have hc := isConsistentAtBatchEnds_of_upper g hup
  refine tendsto_order.2 ⟨fun c hcx ↦ ?_, fun c hcx ↦ hup ν hν a ha c hcx⟩
  have hO := isBigO_log_t_of_eventually_div_lt g
    (fun _ ↦ integral_nonneg fun _ ↦ Nat.cast_nonneg _) (hup ν hν a ha _ (lt_add_one _))
  exact eventually_lt_integral_pullCount_div_log_t_of_isBigO g (by linarith) hg hb hc hν ha hO c
    (by rwa [mul_one_div])

/-- **The limit of the regret from the limits of the counts** [INC-P000, proof of
Theorem `thm:upper`, "regret"]: if every suboptimal arm `c` has
`E_ν[N_c(t_ℓ)] / log t_ℓ → L_c`, then `ℜ(t_ℓ) / log t_ℓ → ∑_{c : Δ_c > 0} Δ_c L_c`, with
`ℜ(t) = ∑_c Δ_c E_ν[N_c(t)]`. -/
lemma tendsto_regret_div_log_t_of_tendsto [Fintype α] (g : Grid K)
    {alg : Algorithm Unit α ℝ} {ν : Kernel α ℝ} [IsMarkovKernel ν] {L : α → ℝ}
    (h : ∀ c, 0 < gap ν c → Tendsto (fun ℓ ↦ (∫ ω, (pullCount IT.action c (g.t ℓ) ω : ℝ)
        ∂(trajMeasure alg (Environment.bandit ν))) / Real.log (g.t ℓ)) atTop (𝓝 (L c))) :
    Tendsto (fun ℓ ↦ (∑ c, gap ν c * ∫ ω, (pullCount IT.action c (g.t ℓ) ω : ℝ)
        ∂(trajMeasure alg (Environment.bandit ν))) / Real.log (g.t ℓ)) atTop
      (𝓝 (∑ c ∈ Finset.univ.filter (fun c ↦ 0 < gap ν c), gap ν c * L c)) := by
  set S := Finset.univ.filter (fun c ↦ 0 < gap ν c)
  have hsum : Tendsto (fun ℓ ↦ ∑ c ∈ S, gap ν c * ((∫ ω, (pullCount IT.action c (g.t ℓ) ω : ℝ)
      ∂(trajMeasure alg (Environment.bandit ν))) / Real.log (g.t ℓ))) atTop
      (𝓝 (∑ c ∈ S, gap ν c * L c)) :=
    tendsto_finsetSum S fun c hcS ↦ (h c (Finset.mem_filter.mp hcS).2).const_mul _
  refine hsum.congr fun ℓ ↦ ?_
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

/-! ### The three statements of Theorem `thm:upper` for HY, from the `limsup` bound -/

section HY

variable [Fintype α] [MeasurableSingletonClass α] [Nonempty α]

/-- [INC-P000, Theorem `thm:upper`, consistency, from the upper bound] If HY satisfies
`limsup_ℓ E_ν[N_a(t_ℓ)] / log t_ℓ ≤ x² / 𝒦_inf(ν_a, m⋆)` for every `ν ∈ 𝒫` and every suboptimal
arm `a`, it is consistent at the batch ends on `𝒫`. -/
lemma hy_isConsistent_of_upper (g : Grid (Fintype.card α)) {x w₀ β : ℝ}
    (hup : ∀ ν ∈ unitBandits α, ∀ [IsMarkovKernel ν], ∀ a, 0 < gap ν a →
      ∀ c > x ^ 2 / (LMLExplore.Bandits.dInf unitLaws (ν a) (⨆ b, ∫ y, id y ∂(ν b))).toReal,
        ∀ᶠ ℓ in atTop, (∫ ω, (pullCount IT.action a (g.t ℓ) ω : ℝ)
          ∂(trajMeasure (hy w₀ β g : Algorithm Unit α ℝ) (Environment.bandit ν))) /
            Real.log (g.t ℓ) < c) :
    IsConsistentAtBatchEnds (hy w₀ β g : Algorithm Unit α ℝ) g (unitBandits α) :=
  isConsistentAtBatchEnds_of_upper g hup

/-- [INC-P000, Theorem `thm:upper`, counts, from the upper bound] Under the hypothesis of
`hy_isConsistent_of_upper`, on a grid with `x_ℓ → x ≥ 1`,
`E_ν[N_a(t_ℓ)] / log t_ℓ → x² / 𝒦_inf(ν_a, m⋆)` under HY, for every `ν ∈ 𝒫` and every suboptimal
arm `a`. -/
lemma hy_tendsto_count_of_upper (g : Grid (Fintype.card α)) {x : ℝ} (hx : 1 ≤ x)
    (hg : Tendsto g.ratio atTop (𝓝 x)) {w₀ β : ℝ}
    (hup : ∀ ν ∈ unitBandits α, ∀ [IsMarkovKernel ν], ∀ a, 0 < gap ν a →
      ∀ c > x ^ 2 / (LMLExplore.Bandits.dInf unitLaws (ν a) (⨆ b, ∫ y, id y ∂(ν b))).toReal,
        ∀ᶠ ℓ in atTop, (∫ ω, (pullCount IT.action a (g.t ℓ) ω : ℝ)
          ∂(trajMeasure (hy w₀ β g : Algorithm Unit α ℝ) (Environment.bandit ν))) /
            Real.log (g.t ℓ) < c)
    {ν : Kernel α ℝ} [IsMarkovKernel ν] (hν : ν ∈ unitBandits α) {a : α} (ha : 0 < gap ν a) :
    Tendsto (fun ℓ ↦ (∫ ω, (pullCount IT.action a (g.t ℓ) ω : ℝ)
        ∂(trajMeasure (hy w₀ β g : Algorithm Unit α ℝ) (Environment.bandit ν))) /
          Real.log (g.t ℓ)) atTop
      (𝓝 (x ^ 2 / (LMLExplore.Bandits.dInf unitLaws (ν a) (⨆ b, ∫ y, id y ∂(ν b))).toReal)) :=
  tendsto_div_log_t_of_upper g hx hg (isBatched_hyAlg _ _ _ _ _ g) hup hν ha

/-- [INC-P000, Theorem `thm:upper`, regret, from the upper bound] Under the hypothesis of
`hy_isConsistent_of_upper`, on a grid with `x_ℓ → x ≥ 1`,
`ℜ(t_ℓ) / log t_ℓ → C_x = x² ∑_{c : Δ_c > 0} Δ_c / 𝒦_inf(ν_c, m⋆)` under HY, for every
`ν ∈ 𝒫`. -/
lemma hy_tendsto_regret_of_upper (g : Grid (Fintype.card α)) {x : ℝ} (hx : 1 ≤ x)
    (hg : Tendsto g.ratio atTop (𝓝 x)) {w₀ β : ℝ}
    (hup : ∀ ν ∈ unitBandits α, ∀ [IsMarkovKernel ν], ∀ a, 0 < gap ν a →
      ∀ c > x ^ 2 / (LMLExplore.Bandits.dInf unitLaws (ν a) (⨆ b, ∫ y, id y ∂(ν b))).toReal,
        ∀ᶠ ℓ in atTop, (∫ ω, (pullCount IT.action a (g.t ℓ) ω : ℝ)
          ∂(trajMeasure (hy w₀ β g : Algorithm Unit α ℝ) (Environment.bandit ν))) /
            Real.log (g.t ℓ) < c)
    {ν : Kernel α ℝ} [IsMarkovKernel ν] (hν : ν ∈ unitBandits α) :
    Tendsto (fun ℓ ↦ (∑ c, gap ν c * ∫ ω, (pullCount IT.action c (g.t ℓ) ω : ℝ)
        ∂(trajMeasure (hy w₀ β g : Algorithm Unit α ℝ) (Environment.bandit ν))) /
          Real.log (g.t ℓ)) atTop
      (𝓝 (x ^ 2 * ∑ c ∈ Finset.univ.filter (fun c ↦ 0 < gap ν c),
        gap ν c / (LMLExplore.Bandits.dInf unitLaws (ν c) (⨆ b, ∫ y, id y ∂(ν b))).toReal)) := by
  have h := tendsto_regret_div_log_t_of_tendsto g
    (L := fun c ↦ x ^ 2 / (LMLExplore.Bandits.dInf unitLaws (ν c) (⨆ b, ∫ y, id y ∂(ν b))).toReal)
    fun c hc ↦ hy_tendsto_count_of_upper g hx hg hup hν hc
  convert h using 2
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ ↦ by ring

end HY

end Incognita.BatchedBandits
