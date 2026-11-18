/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.LowerBound

/-! # P000: the lower bounds

Proofs of six frozen statements of [INC-P000], each with exactly the type of
`Incognita.Statements.P000.<name>`:

* `one_batch_ahead` [INC-P000, Lemma `lem:onebatch`]: on every grid, every batched learner
  consistent on `𝒫` has `liminf_ℓ E_ν[N_a(t_ℓ)] / log t_(ℓ+1) ≥ 1 / 𝒦_inf(ν_a, m⋆)`;
* `lower_liminf_of_tendsto_ratio_one` [INC-P000, Theorem `thm:lower`(i)]: the same with
  `log t_ℓ` in the denominator;
* `lower_liminf`, `lower_limsup` [INC-P000, Theorem `thm:main`(a)]: on a grid with `x_ℓ → x ≥ 1`,
  `limsup_ℓ E_ν[N_a(t_ℓ)] / log t_ℓ ≥ x² / 𝒦_inf(ν_a, m⋆)`, and the `liminf` too when `x = 1` or
  the counts of `a` are logarithmic;
* `lower_regret_liminf`, `lower_regret_limsup` [INC-P000, Theorem `thm:lower`(iii) and
  Theorem `thm:main`, regret]: the same for the regret, with the constant `C_x`.

They are specialisations of the lemmas of `Incognita.BatchedBandits.OneBatchAhead` (one batch
ahead), `Incognita.BatchedBandits.TwoBatchesAhead` (two batches ahead, the factor `x²`) and
`Incognita.BatchedBandits.LowerBound` (the assembly). The hypothesis `K ≥ 2` is not used, nor, for
`lower_liminf_of_tendsto_ratio_one`, the convergence of the ratios to `1`: the bound holds on every
grid, as the paper remarks. Unused hypotheses are named `_hK`, `_hg` (the type is the frozen one up
to binder names).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Bandits

namespace Incognita.P000

/-- [INC-P000, Lemma `lem:onebatch`] For every grid, every batched learner consistent on `𝒫`,
every `ν ∈ 𝒫` and every sub-optimal arm `a`,
`liminf_ℓ E_ν[N_a(t_ℓ)] / log t_(ℓ+1) ≥ 1 / 𝒦_inf(ν_a, m⋆)`. The hypothesis `K ≥ 2` is not used. -/
theorem one_batch_ahead {α : Type*}
    [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (_hK : 2 ≤ Fintype.card α) (g : Incognita.BatchedBandits.Grid (Fintype.card α))
    (alg : Learning.Algorithm Unit α ℝ)
    (hb : Incognita.BatchedBandits.IsBatched alg g)
    (hc : Incognita.BatchedBandits.IsConsistentAtBatchEnds alg g
      (Incognita.BatchedBandits.unitBandits α))
    (ν : ProbabilityTheory.Kernel α ℝ)
    [ProbabilityTheory.IsMarkovKernel ν] (hν : ν ∈ Incognita.BatchedBandits.unitBandits α)
    {a : α} (ha : 0 < Bandits.gap ν a) :
    ∀ c < 1 / (LMLExplore.Bandits.dInf Incognita.BatchedBandits.unitLaws (ν a)
          (⨆ b, ∫ y, id y ∂(ν b))).toReal,
      ∀ᶠ ℓ in Filter.atTop, c < (∫ ω, (Learning.pullCount Learning.IT.action a (g.t ℓ) ω : ℝ)
          ∂(Learning.trajMeasure alg
            (Learning.Environment.bandit ν))) /
          Real.log (g.t (ℓ + 1)) :=
  Incognita.BatchedBandits.eventually_lt_integral_pullCount_div_log_t_succ g hb hc hν ha

/-- [INC-P000, Theorem `thm:lower`(i)] Let the grid be convergent with limit `x = 1`, let a batched
learner be consistent on `𝒫`, let `ν ∈ 𝒫` and let `a` be a sub-optimal arm. Then
`liminf_ℓ E_ν[N_a(t_ℓ)] / log t_ℓ ≥ 1 / 𝒦_inf(ν_a, m⋆)`. Neither `K ≥ 2` nor the convergence of
the ratios is used: the bound holds on every grid. -/
theorem lower_liminf_of_tendsto_ratio_one {α : Type*}
    [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (_hK : 2 ≤ Fintype.card α) (g : Incognita.BatchedBandits.Grid (Fintype.card α))
    (_hg : Filter.Tendsto g.ratio Filter.atTop (nhds 1))
    (alg : Learning.Algorithm Unit α ℝ)
    (hb : Incognita.BatchedBandits.IsBatched alg g)
    (hc : Incognita.BatchedBandits.IsConsistentAtBatchEnds alg g
      (Incognita.BatchedBandits.unitBandits α))
    (ν : ProbabilityTheory.Kernel α ℝ)
    [ProbabilityTheory.IsMarkovKernel ν] (hν : ν ∈ Incognita.BatchedBandits.unitBandits α)
    {a : α} (ha : 0 < Bandits.gap ν a) :
    ∀ c < 1 / (LMLExplore.Bandits.dInf Incognita.BatchedBandits.unitLaws (ν a)
          (⨆ b, ∫ y, id y ∂(ν b))).toReal,
      ∀ᶠ ℓ in Filter.atTop, c < (∫ ω, (Learning.pullCount Learning.IT.action a (g.t ℓ) ω : ℝ)
          ∂(Learning.trajMeasure alg
            (Learning.Environment.bandit ν))) /
          Real.log (g.t ℓ) :=
  Incognita.BatchedBandits.eventually_lt_integral_pullCount_div_log_t g hb hc hν ha

/-- [INC-P000, Theorem `thm:main`(a), second claim; Theorem `thm:lower`(i)–(ii)] On a grid with
`x_ℓ → x ≥ 1`, every batched learner consistent on `𝒫` such that `x = 1` or its counts of `a` are
logarithmic at the batch ends satisfies
`liminf_ℓ E_ν[N_a(t_ℓ)] / log t_ℓ ≥ x² / 𝒦_inf(ν_a, m⋆)`. For `x = 1`: one batch ahead, on
every grid; otherwise two batches ahead and `log t_(ℓ+2) / log t_ℓ → x²`. `K ≥ 2` is not used. -/
theorem lower_liminf {α : Type*}
    [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (_hK : 2 ≤ Fintype.card α) (g : Incognita.BatchedBandits.Grid (Fintype.card α))
    {x : ℝ} (hx : 1 ≤ x) (hg : Filter.Tendsto g.ratio Filter.atTop (nhds x))
    (alg : Learning.Algorithm Unit α ℝ)
    (hb : Incognita.BatchedBandits.IsBatched alg g)
    (hc : Incognita.BatchedBandits.IsConsistentAtBatchEnds alg g
      (Incognita.BatchedBandits.unitBandits α))
    (ν : ProbabilityTheory.Kernel α ℝ)
    [ProbabilityTheory.IsMarkovKernel ν] (hν : ν ∈ Incognita.BatchedBandits.unitBandits α)
    {a : α} (ha : 0 < Bandits.gap ν a)
    (hlog : x = 1 ∨ Asymptotics.IsBigO Filter.atTop
      (fun ℓ ↦ (∫ ω, (Learning.pullCount Learning.IT.action a (g.t ℓ) ω : ℝ)
          ∂(Learning.trajMeasure alg
            (Learning.Environment.bandit ν))))
      (fun ℓ ↦ Real.log (g.t ℓ))) :
    ∀ c < x ^ 2 / (LMLExplore.Bandits.dInf Incognita.BatchedBandits.unitLaws (ν a)
          (⨆ b, ∫ y, id y ∂(ν b))).toReal,
      ∀ᶠ ℓ in Filter.atTop, c < (∫ ω, (Learning.pullCount Learning.IT.action a (g.t ℓ) ω : ℝ)
          ∂(Learning.trajMeasure alg
            (Learning.Environment.bandit ν))) /
          Real.log (g.t ℓ) := by
  intro c hcx
  rcases hlog with rfl | hO
  · exact Incognita.BatchedBandits.eventually_lt_integral_pullCount_div_log_t g hb hc hν ha c
      (by simpa using hcx)
  · exact Incognita.BatchedBandits.eventually_lt_integral_pullCount_div_log_t_of_isBigO g
      (by linarith) hg hb hc hν ha hO c (by rwa [mul_one_div])

/-- [INC-P000, Theorem `thm:main`(a), first claim; Theorem `thm:lower`(i)–(ii)] On a grid with
`x_ℓ → x ≥ 1`, every batched learner consistent on `𝒫` satisfies
`limsup_ℓ E_ν[N_a(t_ℓ)] / log t_ℓ ≥ x² / 𝒦_inf(ν_a, m⋆)`: if the counts of `a` are logarithmic,
by `lower_liminf`; otherwise the `limsup` is infinite (Case B). `K ≥ 2` is not used. -/
theorem lower_limsup {α : Type*}
    [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (_hK : 2 ≤ Fintype.card α) (g : Incognita.BatchedBandits.Grid (Fintype.card α))
    {x : ℝ} (hx : 1 ≤ x) (hg : Filter.Tendsto g.ratio Filter.atTop (nhds x))
    (alg : Learning.Algorithm Unit α ℝ)
    (hb : Incognita.BatchedBandits.IsBatched alg g)
    (hc : Incognita.BatchedBandits.IsConsistentAtBatchEnds alg g
      (Incognita.BatchedBandits.unitBandits α))
    (ν : ProbabilityTheory.Kernel α ℝ)
    [ProbabilityTheory.IsMarkovKernel ν] (hν : ν ∈ Incognita.BatchedBandits.unitBandits α)
    {a : α} (ha : 0 < Bandits.gap ν a) :
    ∀ c < x ^ 2 / (LMLExplore.Bandits.dInf Incognita.BatchedBandits.unitLaws (ν a)
          (⨆ b, ∫ y, id y ∂(ν b))).toReal,
      ∃ᶠ ℓ in Filter.atTop, c < (∫ ω, (Learning.pullCount Learning.IT.action a (g.t ℓ) ω : ℝ)
          ∂(Learning.trajMeasure alg
            (Learning.Environment.bandit ν))) /
          Real.log (g.t ℓ) := by
  intro c hcx
  by_cases hO : Asymptotics.IsBigO Filter.atTop
      (fun ℓ ↦ (∫ ω, (Learning.pullCount Learning.IT.action a (g.t ℓ) ω : ℝ)
          ∂(Learning.trajMeasure alg (Learning.Environment.bandit ν))))
      (fun ℓ ↦ Real.log (g.t ℓ))
  · exact (lower_liminf _hK g hx hg alg hb hc ν hν ha (Or.inr hO) c hcx).frequently
  · exact Incognita.BatchedBandits.frequently_lt_div_log_t_of_not_isBigO g
      (fun ℓ ↦ integral_nonneg fun _ ↦ Nat.cast_nonneg _) hO c

/-- [INC-P000, Theorem `thm:lower`(iii)] On a grid with `x_ℓ → x ≥ 1`, every batched learner
consistent on `𝒫` such that `x = 1` or the counts of every suboptimal arm are logarithmic satisfies
`liminf_ℓ ℜ(t_ℓ) / log t_ℓ ≥ C_x = x² ∑_{c : Δ_c > 0} Δ_c / 𝒦_inf(ν_c, m⋆)`. `K ≥ 2` is not
used. -/
theorem lower_regret_liminf {α : Type*}
    [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (_hK : 2 ≤ Fintype.card α) (g : Incognita.BatchedBandits.Grid (Fintype.card α))
    {x : ℝ} (hx : 1 ≤ x) (hg : Filter.Tendsto g.ratio Filter.atTop (nhds x))
    (alg : Learning.Algorithm Unit α ℝ)
    (hb : Incognita.BatchedBandits.IsBatched alg g)
    (hc : Incognita.BatchedBandits.IsConsistentAtBatchEnds alg g
      (Incognita.BatchedBandits.unitBandits α))
    (ν : ProbabilityTheory.Kernel α ℝ)
    [ProbabilityTheory.IsMarkovKernel ν] (hν : ν ∈ Incognita.BatchedBandits.unitBandits α)
    (hlog : x = 1 ∨ ∀ c, 0 < Bandits.gap ν c → Asymptotics.IsBigO Filter.atTop
      (fun ℓ ↦ (∫ ω, (Learning.pullCount Learning.IT.action c (g.t ℓ) ω : ℝ)
          ∂(Learning.trajMeasure alg
            (Learning.Environment.bandit ν))))
      (fun ℓ ↦ Real.log (g.t ℓ))) :
    ∀ c' < x ^ 2 * ∑ c ∈ Finset.univ.filter (fun c ↦ 0 < Bandits.gap ν c),
        Bandits.gap ν c / (LMLExplore.Bandits.dInf Incognita.BatchedBandits.unitLaws (ν c)
          (⨆ b, ∫ y, id y ∂(ν b))).toReal,
      ∀ᶠ ℓ in Filter.atTop, c' < (∑ c, Bandits.gap ν c *
          ∫ ω, (Learning.pullCount Learning.IT.action c (g.t ℓ) ω : ℝ)
          ∂(Learning.trajMeasure alg
            (Learning.Environment.bandit ν))) /
          Real.log (g.t ℓ) := by
  intro c' hc'
  rcases hlog with rfl | hO
  · exact Incognita.BatchedBandits.eventually_lt_regret_div_log_t g hb hc hν c'
      (by simpa using hc')
  · refine Incognita.BatchedBandits.eventually_lt_regret_div_log_t_of_forall g
      (L := fun c ↦ x ^ 2 / (LMLExplore.Bandits.dInf Incognita.BatchedBandits.unitLaws (ν c)
        (⨆ b, ∫ y, id y ∂(ν b))).toReal)
      (fun c hgap b hb' ↦ lower_liminf _hK g hx hg alg hb hc ν hν hgap (Or.inr (hO c hgap)) b hb')
      c' ?_
    calc c' < _ := hc'
      _ = _ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun c _ ↦ by ring

/-- [INC-P000, Theorem `thm:main`, regret] On a grid with `x_ℓ → x ≥ 1`, every batched learner
consistent on `𝒫` satisfies `limsup_ℓ ℜ(t_ℓ) / log t_ℓ ≥ C_x`: if the counts of every suboptimal
arm are logarithmic, by `lower_regret_liminf`; otherwise the `limsup` is infinite. `K ≥ 2` is not
used. -/
theorem lower_regret_limsup {α : Type*}
    [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (_hK : 2 ≤ Fintype.card α) (g : Incognita.BatchedBandits.Grid (Fintype.card α))
    {x : ℝ} (hx : 1 ≤ x) (hg : Filter.Tendsto g.ratio Filter.atTop (nhds x))
    (alg : Learning.Algorithm Unit α ℝ)
    (hb : Incognita.BatchedBandits.IsBatched alg g)
    (hc : Incognita.BatchedBandits.IsConsistentAtBatchEnds alg g
      (Incognita.BatchedBandits.unitBandits α))
    (ν : ProbabilityTheory.Kernel α ℝ)
    [ProbabilityTheory.IsMarkovKernel ν] (hν : ν ∈ Incognita.BatchedBandits.unitBandits α) :
    ∀ c' < x ^ 2 * ∑ c ∈ Finset.univ.filter (fun c ↦ 0 < Bandits.gap ν c),
        Bandits.gap ν c / (LMLExplore.Bandits.dInf Incognita.BatchedBandits.unitLaws (ν c)
          (⨆ b, ∫ y, id y ∂(ν b))).toReal,
      ∃ᶠ ℓ in Filter.atTop, c' < (∑ c, Bandits.gap ν c *
          ∫ ω, (Learning.pullCount Learning.IT.action c (g.t ℓ) ω : ℝ)
          ∂(Learning.trajMeasure alg
            (Learning.Environment.bandit ν))) /
          Real.log (g.t ℓ) := by
  intro c' hc'
  by_cases hall : ∀ c, 0 < Bandits.gap ν c → Asymptotics.IsBigO Filter.atTop
      (fun ℓ ↦ (∫ ω, (Learning.pullCount Learning.IT.action c (g.t ℓ) ω : ℝ)
          ∂(Learning.trajMeasure alg (Learning.Environment.bandit ν))))
      (fun ℓ ↦ Real.log (g.t ℓ))
  · exact (lower_regret_liminf _hK g hx hg alg hb hc ν hν (Or.inr hall) c' hc').frequently
  · simp only [not_forall, exists_prop] at hall
    obtain ⟨c, hgap, hO⟩ := hall
    exact Incognita.BatchedBandits.frequently_lt_regret_div_log_t_of_not_isBigO g hgap hO c'

end Incognita.P000
