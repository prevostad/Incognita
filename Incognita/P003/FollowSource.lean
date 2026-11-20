/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.Checks
public import Incognita.ForMathlib.Probability.Distributions.Bernoulli

/-! # P003, prop:exclusion: following the source is not consistent

Proof of [INC-P003, prop:exclusion]: the learner `π^tr` (`TransferAlgorithm.followSource`) is in
no class `𝒞_L`, and it already fails on a pair `(ν, ν)` with deterministic source sizes.

The learner `π^tr` pulls at every round the arm `followSourceArm s` of the source data
(`ae_onlineKernel_followSource`), so `E[N_a(T)] = T · P(followSourceArm D = a)` under every size
map (`integral_onlineCount_followSource`).

* `followSource_not_isConsistent` (superseded by SC1): the Lean proof takes the deterministic sizes
  `n = 0`: then no arm has a source value, `π^tr` pulls the smallest arm `a₀` at every round, and on
  the instance `ν a₀ = δ_0`, `ν k = δ_1` (`k ≠ a₀`) the suboptimal arm `a₀` is pulled `T` times
  (`integral_onlineCount_followSource_zero`), so `E[N_{a₀}(T)] / T → 1`.
* `followSource_not_isConsistent_v2` (correction SC1, sizes positive on every arm): the sizes `1`
  and the instance `ν_b = Ber(1/2)` for one arm `b ≠ a₀`, `ν_k = δ_0` otherwise; when
  `X'_{b,1} = 0` every source empirical mean is `0` (`followSourceArm_sourceData_one`), so `π^tr`
  pulls the suboptimal arm `a₀` with probability at least `1/2`
  (`measure_zero_le_sourceLaw_followSourceArm`), and `E[N_{a₀}(T)] / T ≥ 1/2`. The paper's proof
  takes the sizes `1` and two Bernoulli arms, where the source picks the suboptimal arm with
  probability `1/9`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Incognita.TransferBandits Filter unitInterval

open scoped Topology

namespace Incognita.P003

section Helpers

variable {α : Type*} [Fintype α] [LinearOrder α] [Nonempty α] [MeasurableSpace α]

/-- Under the learner `π^tr`, almost every online history pulls the arm `followSourceArm s` at
every round. -/
lemma ae_onlineKernel_followSource [MeasurableSingletonClass α] (ν : Kernel α ℝ) :
    ∀ (T : ℕ) (s : Source α),
      ∀ᵐ h ∂(onlineKernel (TransferAlgorithm.followSource (α := α)) ν T s),
        ∀ i, (h i).1 = followSourceArm s :=
  TransferBandits.ae_onlineKernel_of_policy_eq_dirac followSourceArm (fun _ _ ↦ rfl) ν

/-- With no source value (`n = 0`), `π^tr` pulls the smallest arm at every round: under the game
with the size rule `constSize 0`, the expected number of pulls of the smallest arm over `T`
rounds is `T`, whatever the source law and the target. -/
lemma integral_onlineCount_followSource_zero [MeasurableSingletonClass α] (ν' ν : Kernel α ℝ)
    [IsMarkovKernel ν'] [IsMarkovKernel ν] (T : ℕ) :
    ∫ p, (onlineCount (Finset.univ.min' Finset.univ_nonempty) p.2 : ℝ)
        ∂(gameMeasure ν' (constSize 0) ν (TransferAlgorithm.followSource (α := α)) T) = T := by
  set a₀ : α := Finset.univ.min' Finset.univ_nonempty
  set P := gameMeasure ν' (constSize 0) ν (TransferAlgorithm.followSource (α := α)) T
  have hS : MeasurableSet
      {p : Source α × (Fin T → α × ℝ) | ∀ i, (p.2 i).1 = followSourceArm p.1} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i ↦ measurableSet_eq_fun
      (by fun_prop : Measurable fun p : Source α × (Fin T → α × ℝ) ↦ (p.2 i).1)
      (measurable_followSourceArm.comp measurable_fst)
  have hall : ∀ᵐ p ∂P, ∀ i, (p.2 i).1 = followSourceArm p.1 :=
    Measure.ae_compProd_of_ae_ae hS (ae_of_all _ fun s ↦ ae_onlineKernel_followSource ν T s)
  have hlaw : sourceLaw ν' (constSize (0 : α → ℕ)) = Measure.dirac (0, 0) := by
    have : sourceData (constSize (0 : α → ℕ)) = fun _ ↦ (0, 0) :=
      funext sourceData_constSize_zero
    rw [sourceLaw, this, Measure.map_const, measure_univ, one_smul]
  have hfst : ∀ᵐ p ∂P, p.1 = (0, 0) := by
    have hmap : P.map Prod.fst = Measure.dirac (0, 0) := by
      rw [← hlaw]
      exact Measure.fst_compProd (μ := sourceLaw ν' (constSize (0 : α → ℕ)))
        (κ := onlineKernel (TransferAlgorithm.followSource (α := α)) ν T)
    refine ae_of_ae_map (μ := P) (p := fun s : Source α ↦ s = (0, 0))
      measurable_fst.aemeasurable ?_
    rw [hmap, ae_dirac_eq]
    exact Filter.eventually_pure.mpr rfl
  have harm : followSourceArm ((0, 0) : Source α) = a₀ := by
    classical
    have hnot : ¬ ∀ k, 1 ≤ ((0, 0) : Source α).1 k := fun h ↦ by
      simpa using h (Classical.arbitrary α)
    unfold followSourceArm
    simp only [hnot, ite_false]
    rfl
  have h : ∀ᵐ p ∂P, (onlineCount a₀ p.2 : ℝ) = T := by
    filter_upwards [hall, hfst] with p hp hp1
    rw [hp1, harm] at hp
    simp [onlineCount, hp]
  rw [integral_congr_ae h]
  simp

/-- Under the game with any size map, the expected number of pulls of an arm `a` by `π^tr` over
`T` rounds is `T` times the probability that `π^tr` chooses `a` from the source data. -/
lemma integral_onlineCount_followSource [MeasurableSingletonClass α] (ν' ν : Kernel α ℝ)
    [IsMarkovKernel ν'] [IsMarkovKernel ν] (N : SourceSpace α → α → ℕ) (a : α) (T : ℕ) :
    ∫ p, (onlineCount a p.2 : ℝ)
        ∂(gameMeasure ν' N ν (TransferAlgorithm.followSource (α := α)) T) =
      T * (sourceLaw ν' N).real {s | followSourceArm s = a} := by
  classical
  set P := gameMeasure ν' N ν (TransferAlgorithm.followSource (α := α)) T
  have hS : MeasurableSet
      {p : Source α × (Fin T → α × ℝ) | ∀ i, (p.2 i).1 = followSourceArm p.1} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i ↦ measurableSet_eq_fun
      (by fun_prop : Measurable fun p : Source α × (Fin T → α × ℝ) ↦ (p.2 i).1)
      (measurable_followSourceArm.comp measurable_fst)
  have hall : ∀ᵐ p ∂P, ∀ i, (p.2 i).1 = followSourceArm p.1 :=
    Measure.ae_compProd_of_ae_ae hS (ae_of_all _ fun s ↦ ae_onlineKernel_followSource ν T s)
  have hA : MeasurableSet {s : Source α | followSourceArm s = a} :=
    measurable_followSourceArm (measurableSet_singleton a)
  have h : (fun p : Source α × (Fin T → α × ℝ) ↦ (onlineCount a p.2 : ℝ)) =ᵐ[P]
      (Prod.fst ⁻¹' {s | followSourceArm s = a}).indicator fun _ ↦ (T : ℝ) := by
    filter_upwards [hall] with p hp
    by_cases hpa : followSourceArm p.1 = a
    · simp [onlineCount, hp, hpa]
    · simp [onlineCount, hp, hpa]
  have hfst : P.map Prod.fst = sourceLaw ν' N := fst_gameMeasure N ν' ν _ T
  rw [integral_congr_ae h, integral_indicator_const _ (measurable_fst hA), smul_eq_mul, mul_comm,
    ← map_measureReal_apply measurable_fst hA, hfst]

omit [MeasurableSpace α] in
/-- With one source value per arm, all equal to `0`, every source empirical mean is `0`, and
`π^tr` pulls the smallest arm. -/
lemma followSourceArm_sourceData_one {ω : SourceSpace α} (hω : ∀ k, ω.2 k 0 = 0) :
    followSourceArm (sourceData (constSize 1) ω) = Finset.univ.min' Finset.univ_nonempty := by
  classical
  have hm : ∀ k, sourceMean (sourceData (constSize 1) ω) k = 0 := fun k ↦ by
    simp [sourceMean, sourceData, constSize, hω k]
  have h1 : ∀ k, 1 ≤ (sourceData (constSize 1) ω).1 k := fun k ↦ le_refl _
  unfold followSourceArm
  simp only [h1, implies_true, ite_true]
  rw [bestSourceArm_eq_iff]
  exact ⟨fun j ↦ by rw [hm, hm], fun i _ ↦ Finset.min'_le _ _ (Finset.mem_univ i)⟩

/-- With the sizes `1` on every arm and a source law `ν'` equal to `δ_0` on every arm but `b`,
`π^tr` pulls the smallest arm with probability at least `ν'_b({0})`: on the event
`{X'_{b,1} = 0}` every source empirical mean is `0` almost surely. -/
lemma measure_zero_le_sourceLaw_followSourceArm [MeasurableSingletonClass α] (ν' : Kernel α ℝ)
    [IsMarkovKernel ν'] {b : α} (hν' : ∀ k, k ≠ b → ν' k = Measure.dirac 0) :
    ν' b {0} ≤ sourceLaw ν' (constSize 1)
      {s | followSourceArm s = Finset.univ.min' Finset.univ_nonempty} := by
  have hS : MeasurableSet
      {s : Source α | followSourceArm s = Finset.univ.min' Finset.univ_nonempty} :=
    measurable_followSourceArm (measurableSet_singleton _)
  have hzero : ∀ᵐ ω ∂sourceMeasure ν', ∀ k, k ≠ b → ω.2 k 0 = 0 := by
    refine ae_all_iff.mpr fun k ↦ ?_
    by_cases hk : k = b
    · simp [hk]
    have h : ∀ᵐ x ∂(sourceMeasure ν').map (fun ω : SourceSpace α ↦ ω.2 k 0), x = 0 := by
      rw [map_eval_sourceMeasure, hν' k hk]
      exact (ae_dirac_iff (measurableSet_singleton 0)).mpr rfl
    filter_upwards [ae_of_ae_map (by fun_prop) h] with ω hω _ using hω
  rw [← map_eval_sourceMeasure ν' b 0, Measure.map_apply (by fun_prop) (measurableSet_singleton 0),
    sourceLaw, Measure.map_apply
      (measurable_sourceData (N := constSize (1 : α → ℕ)) measurable_const) hS]
  refine measure_mono_ae ?_
  filter_upwards [hzero] with ω hω hb0
  exact followSourceArm_sourceData_one fun k ↦ by
    by_cases hk : k = b
    · rw [hk]; exact hb0
    · exact hω k hk

end Helpers

/-- [INC-P003, prop:exclusion] The learner `π^tr` is in no class `𝒞_L`; it already fails on a pair
`(ν, ν)` with deterministic source sizes. The Lean proof takes the sizes `0`. The instance
argument `[Nonempty α]` is redundant given `hK`. -/
theorem followSource_not_isConsistent {α : Type*} [Fintype α] [LinearOrder α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (hK : 2 ≤ Fintype.card α) :
    (∀ L : α → ℝ, (∀ a, 0 < L a) → ¬ IsConsistent L (TransferAlgorithm.followSource (α := α))) ∧
      ∃ ν ∈ unitBandits α, ∃ n : α → ℕ, ∃ a, (∃ b, (ν a)[id] < (ν b)[id]) ∧ ∃ c : ℝ, 0 < c ∧
        ¬ Tendsto (fun T : ℕ ↦ (∫ p, (onlineCount a p.2 : ℝ) ∂(gameMeasure ν (constSize n) ν
            (TransferAlgorithm.followSource (α := α)) T)) / (T : ℝ) ^ c) atTop (𝓝 0) := by
  classical
  set a₀ : α := Finset.univ.min' Finset.univ_nonempty
  obtain ⟨b, hb⟩ : ∃ b, b ≠ a₀ := by
    by_contra! h
    have : Fintype.card α ≤ 1 := Fintype.card_le_one_iff.mpr fun x y ↦ (h x).trans (h y).symm
    omega
  let f : α → ℝ := fun k ↦ if k = a₀ then 0 else 1
  have hf : Measurable f := Measurable.ite (measurableSet_singleton a₀) measurable_const
    measurable_const
  let ν : Kernel α ℝ := Kernel.deterministic f hf
  have hν : ν ∈ unitBandits α := by
    refine ⟨inferInstance, fun k ↦ ?_⟩
    refine (ae_dirac_iff measurableSet_Icc).mpr ?_
    by_cases hk : k = a₀ <;> simp [f, hk]
  have hsub : ∃ c, (ν a₀)[id] < (ν c)[id] := ⟨b, by simp [ν, f, Kernel.deterministic_apply, hb]⟩
  have hfail : ¬ Tendsto (fun T : ℕ ↦ (∫ p, (onlineCount a₀ p.2 : ℝ) ∂(gameMeasure ν
      (constSize 0) ν (TransferAlgorithm.followSource (α := α)) T)) / (T : ℝ) ^ (1 : ℝ))
      atTop (𝓝 0) := by
    intro ht
    have hT : ∀ T : ℕ, ∫ p, (onlineCount a₀ p.2 : ℝ) ∂(gameMeasure ν (constSize 0) ν
        (TransferAlgorithm.followSource (α := α)) T) = T :=
      integral_onlineCount_followSource_zero ν ν
    simp only [hT, Real.rpow_one] at ht
    have h1 : Tendsto (fun T : ℕ ↦ (T : ℝ) / T) atTop (𝓝 1) :=
      tendsto_const_nhds.congr' ((eventually_ne_atTop 0).mono fun T hT ↦
        (div_self (Nat.cast_ne_zero.mpr hT)).symm)
    exact one_ne_zero (tendsto_nhds_unique h1 ht)
  refine ⟨fun L hL hcons ↦ hfail ?_, ν, hν, 0, a₀, hsub, 1, one_pos, hfail⟩
  exact hcons ν ν (mem_meanBand_self (fun a ↦ (hL a).le) hν) (fun _ ↦ constSize 0)
    (fun _ ↦ isSizeRule_constSize 0) a₀ hsub 1 one_pos

/-- [INC-P003, prop:exclusion] The learner `π^tr` is in no class `𝒞_L`; it already fails on a pair
`(ν, ν)` with deterministic source sizes, positive on every arm (correction SC1). The first claim
is that of `followSource_not_isConsistent`. For the second, the Lean proof takes the sizes `1` on
every arm, the smallest arm `a₀`, another arm `b` and the instance `ν_b = Ber(1/2)`, `ν_k = δ_0`
for `k ≠ b`: when the source value of `b` is `0` (probability `1/2`) every source empirical mean
is `0`, so `π^tr` pulls the suboptimal arm `a₀` at every round, and `E[N_{a₀}(T)] / T ≥ 1/2`
(`c = 1`). The paper's proof uses two Bernoulli arms and `c = 1/2` instead. The instance argument
`[Nonempty α]` is redundant given `hK`. -/
theorem followSource_not_isConsistent_v2 {α : Type*} [Fintype α] [LinearOrder α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (hK : 2 ≤ Fintype.card α) :
    (∀ L : α → ℝ, (∀ a, 0 < L a) → ¬ IsConsistent L (TransferAlgorithm.followSource (α := α))) ∧
      ∃ ν ∈ unitBandits α, ∃ n : α → ℕ, (∀ k, 1 ≤ n k) ∧ ∃ a, (∃ b, (ν a)[id] < (ν b)[id]) ∧
        ∃ c : ℝ, 0 < c ∧
        ¬ Tendsto (fun T : ℕ ↦ (∫ p, (onlineCount a p.2 : ℝ) ∂(gameMeasure ν (constSize n) ν
            (TransferAlgorithm.followSource (α := α)) T)) / (T : ℝ) ^ c) atTop (𝓝 0) := by
  classical
  refine ⟨(followSource_not_isConsistent hK).1, ?_⟩
  set a₀ : α := Finset.univ.min' Finset.univ_nonempty
  obtain ⟨b, hb⟩ : ∃ b, b ≠ a₀ := by
    by_contra! h
    have : Fintype.card α ≤ 1 := Fintype.card_le_one_iff.mpr fun x y ↦ (h x).trans (h y).symm
    omega
  let p : I := ⟨1 / 2, by norm_num, by norm_num⟩
  let ν : Kernel α ℝ := Kernel.piecewise (measurableSet_singleton b)
    (Kernel.const α Ber((1 : ℝ), 0, p)) (Kernel.const α (Measure.dirac 0))
  have hνb : ν b = Ber((1 : ℝ), 0, p) := by simp [ν, Kernel.piecewise_apply]
  have hνk : ∀ k, k ≠ b → ν k = Measure.dirac 0 := fun k hk ↦ by
    simp [ν, Kernel.piecewise_apply, hk]
  have hν : ν ∈ unitBandits α := by
    refine ⟨inferInstance, fun k ↦ ?_⟩
    by_cases hk : k = b
    · rw [hk, hνb]
      filter_upwards [ae_bernoulliMeasure_eq_zero_or_eq_one p] with x hx
      rcases hx with rfl | rfl <;> simp
    · rw [hνk k hk]
      exact (ae_dirac_iff measurableSet_Icc).mpr (by simp)
  have hsub : ∃ c, (ν a₀)[id] < (ν c)[id] := ⟨b, by
    rw [hνb, hνk a₀ hb.symm, integral_bernoulliMeasure]
    simp [p]⟩
  set q := (sourceLaw ν (constSize 1)).real {s | followSourceArm s = a₀}
  have hpos : 0 < q := by
    have hle := measure_zero_le_sourceLaw_followSourceArm ν hνk
    rw [hνb, bernoulliMeasure_apply_of_notMem_of_mem p (measurableSet_singleton 0)
      (by norm_num) rfl] at hle
    refine ENNReal.toReal_pos (lt_of_lt_of_le ?_ hle).ne' (measure_ne_top _ _)
    rw [ENNReal.coe_pos, ← NNReal.coe_pos, coe_toNNReal, coe_symm_eq]
    norm_num [p]
  have hT : ∀ T : ℕ, ∫ p, (onlineCount a₀ p.2 : ℝ) ∂(gameMeasure ν (constSize 1) ν
      (TransferAlgorithm.followSource (α := α)) T) = T * q :=
    integral_onlineCount_followSource ν ν _ a₀
  refine ⟨ν, hν, 1, fun _ ↦ le_refl _, a₀, hsub, 1, one_pos, fun ht ↦ ?_⟩
  simp only [hT, Real.rpow_one] at ht
  have hq : Tendsto (fun T : ℕ ↦ (T : ℝ) * q / T) atTop (𝓝 q) :=
    tendsto_const_nhds.congr' ((eventually_ne_atTop 0).mono fun T hT ↦
      (mul_div_cancel_left₀ q (Nat.cast_ne_zero.mpr hT)).symm)
  exact hpos.ne' (tendsto_nhds_unique ht hq).symm

end Incognita.P003
