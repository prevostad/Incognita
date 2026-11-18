/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.Checks

/-! # P003, prop:exclusion: following the source is not consistent

Proof of [INC-P003, prop:exclusion]: the learner `π^tr` (`TransferAlgorithm.followSource`) is in
no class `𝒞_L`, and it already fails on a pair `(ν, ν)` with deterministic source sizes.

The learner `π^tr` pulls at every round the arm `followSourceArm s` of the source data
(`ae_onlineKernel_followSource`). The Lean proof takes the deterministic sizes `n = 0`: then no arm
has a source value, `π^tr` pulls the smallest arm `a₀` at every round, and on the instance
`ν a₀ = δ_0`, `ν k = δ_1` (`k ≠ a₀`) the suboptimal arm `a₀` is pulled `T` times
(`integral_onlineCount_followSource_zero`), so `E[N_{a₀}(T)] / T → 1`. The paper's proof takes the
sizes `1` and Bernoulli laws, where the source picks the suboptimal arm with probability `1/9`;
both are pairs `(ν, ν)` of `𝒫^K` with deterministic sizes, as the statement asks.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Incognita.TransferBandits Filter

open scoped Topology

namespace Incognita.P003

section Helpers

variable {α : Type*} [Fintype α] [LinearOrder α] [Nonempty α] [MeasurableSpace α]

/-- Under the learner `π^tr`, almost every online history pulls the arm `followSourceArm s` at
every round. -/
lemma ae_onlineKernel_followSource [MeasurableSingletonClass α] (ν : Kernel α ℝ) :
    ∀ (T : ℕ) (s : Source α),
      ∀ᵐ h ∂(onlineKernel (TransferAlgorithm.followSource (α := α)) ν T s),
        ∀ i, (h i).1 = followSourceArm s
  | 0, _ => ae_of_all _ fun _ i ↦ i.elim0
  | T + 1, s => by
    have hmeas : MeasurableSet {h : Fin (T + 1) → α × ℝ | ∀ i, (h i).1 = followSourceArm s} := by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun i ↦
        (by fun_prop : Measurable fun h : Fin (T + 1) → α × ℝ ↦ (h i).1)
          (measurableSet_singleton _)
    rw [onlineKernel, Kernel.map_apply _ (MeasurableEquiv.measurable _),
      (MeasurableEquiv.measurableEmbedding _).ae_map_iff]
    refine Kernel.ae_compProd_of_ae_ae ((MeasurableEquiv.measurable _) hmeas) ?_
    filter_upwards [ae_onlineKernel_followSource ν T s] with h hh
    have hstep : ∀ᵐ x ∂(stepKernel (TransferAlgorithm.followSource (α := α)) ν T (s, h)),
        x.1 = followSourceArm s := by
      rw [stepKernel]
      refine Kernel.ae_compProd_of_ae_ae (measurable_fst (measurableSet_singleton _)) ?_
      change ∀ᵐ b ∂(Measure.dirac (followSourceArm s)), _
      rw [ae_dirac_eq]
      exact Filter.eventually_pure.mpr (ae_of_all _ fun _ ↦ rfl)
    filter_upwards [hstep] with x hx i
    rw [MeasurableEquiv.finSuccProd_symm_apply]
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa using hx
    · simpa using hh j

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


end Helpers

/-- [INC-P003, prop:exclusion] The learner `π^tr` is in no class `𝒞_L`; it already fails on a pair
`(ν, ν)` with deterministic source sizes. The Lean proof takes the sizes `0`. -/
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

end Incognita.P003
