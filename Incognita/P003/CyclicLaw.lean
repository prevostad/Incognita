/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.P003.Cyclic
public import Incognita.TransferBandits.Checks

/-! # P003, prop:stopped-games (c): no stopped prior game has the law of the cyclic map

Proof of [INC-P003, prop:stopped-games (c)], following the paper's proof. The cyclic map is a
classical example: its pattern is that of the stable function that is not sequential of
[Ber76, Proposition II.2.2], and for three independent Markov chains a cyclic stopping point is not
predictable [MV81, Section 5.2].

The events `{τ = 0}` and `{τ ≥ 1, A'_1 = k}` partition the source space and depend only on the
randomisation, so their probabilities do not depend on the source instance; each is bounded by the
probability of an event of the stopped counts (`N' = 0`, or `N'_k ≥ 1`) that the cyclic map gives
probability `0` under a well-chosen Dirac instance. The probabilities sum to `1`: a contradiction.

## Main statements

* `cyclicSize_not_stoppedCounts`: the frozen statement.

It uses `TransferBandits.map_eval_sourceMeasure` (`X'_{k,j}` has law `ν'_k` under `P'_{ν'}`),
`TransferBandits.map_fst_sourceMeasure`, and `PriorStrategy.state_fst_mono`,
`PriorStrategy.state_one_fst_act` (the counts of a prior game do not decrease, and after one round
the count of the first arm is `1`), whose former copies here are deprecated aliases.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Incognita.TransferBandits

open scoped unitInterval

namespace Incognita.P003

section Helpers

@[deprecated (since := "2026-11-19")] alias map_sourceMeasure_eval := map_eval_sourceMeasure

@[deprecated (since := "2026-11-19")]
alias map_fst_sourceMeasure := TransferBandits.map_fst_sourceMeasure

@[deprecated (since := "2026-11-19")] alias state_fst_mono := PriorStrategy.state_fst_mono

@[deprecated (since := "2026-11-19")] alias state_one_fst_act := PriorStrategy.state_one_fst_act

end Helpers

/-- [INC-P003, prop:stopped-games (c)] The cyclic map is a size rule with total at most `3`, and no
stopped prior game has its law under every source instance. The hypothesis
`3 ≤ Fintype.card α` is not used (distinct `a₁, a₂, a₃` suffice). -/
theorem cyclicSize_not_stoppedCounts {α : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (_hK : 3 ≤ Fintype.card α) {a₁ a₂ a₃ : α}
    (h₁₂ : a₁ ≠ a₂) (h₂₃ : a₂ ≠ a₃) (h₁₃ : a₁ ≠ a₃) :
    IsSizeRule (cyclicSize a₁ a₂ a₃) ∧ (∀ ω, ∑ a, cyclicSize a₁ a₂ a₃ ω a ≤ 3) ∧
      ¬ ∃ (T' : ℕ) (g : PriorStrategy α) (τ : SourceSpace α → ℕ), g.IsStoppingTime T' τ ∧
        ∀ ν' ∈ unitBandits α, (sourceMeasure ν').map (g.stoppedCounts τ) =
          (sourceMeasure ν').map (cyclicSize a₁ a₂ a₃) := by
  refine ⟨isSizeRule_cyclicSize h₁₂ h₂₃ h₁₃, sum_cyclicSize_le a₁ a₂ a₃, ?_⟩
  rintro ⟨T', g, τ, hτ, hlaw⟩
  set V : Measure (ℕ → I) := Measure.infinitePi fun _ : ℕ ↦ (volume : Measure I)
  -- The Dirac instances `ν^b`: `δ_1` on the arm `b`, `δ_0` elsewhere.
  let c : α → α → ℝ := fun b k ↦ if k = b then 1 else 0
  have hc : ∀ b, Measurable (c b) := fun b ↦
    Measurable.ite (measurableSet_singleton b) measurable_const measurable_const
  let νb : α → Kernel α ℝ := fun b ↦ Kernel.deterministic (c b) (hc b)
  have hνb : ∀ b, νb b ∈ unitBandits α := fun b ↦ by
    refine ⟨inferInstance, fun k ↦ (ae_dirac_iff measurableSet_Icc).mpr ?_⟩
    by_cases hk : k = b <;> simp [c, hk]
  have hae : ∀ b, ∀ᵐ ω ∂(sourceMeasure (νb b)), ∀ k, ω.2 k 0 = c b k := fun b ↦ by
    have : IsMarkovKernel (νb b) := (hνb b).1
    rw [ae_all_iff]
    intro k
    refine ae_of_ae_map (p := fun x : ℝ ↦ x = c b k) (by fun_prop) ?_
    rw [map_eval_sourceMeasure]
    change ∀ᵐ y ∂(Measure.dirac (c b k)), y = c b k
    rw [ae_dirac_eq]
    exact Filter.eventually_pure.mpr rfl
  -- The events of the randomisation.
  obtain ⟨S₀, hS₀, hτ₀⟩ := hτ.measurableSet_eq 0
  have hemb : Measurable fun u : ℕ → I ↦ (u, (fun i ↦ i.elim0 : Fin 0 → α × ℝ)) := by fun_prop
  set F₀ : Set (ℕ → I) := (fun u ↦ (u, (fun i ↦ i.elim0 : Fin 0 → α × ℝ))) ⁻¹' S₀
  have hF₀ : MeasurableSet F₀ := hemb hS₀
  have hτ0 : {ω : SourceSpace α | τ ω = 0} = Prod.fst ⁻¹' F₀ := by
    rw [← hτ₀]
    rfl
  have hact : Measurable fun u : ℕ → I ↦ g.act 0 (u, fun i ↦ i.elim0) :=
    (g.measurable_act 0).comp hemb
  set G : α → Set (ℕ → I) := fun k ↦ F₀ᶜ ∩ {u | g.act 0 (u, fun i ↦ i.elim0) = k}
  have hG : ∀ k, MeasurableSet (G k) := fun k ↦
    hF₀.compl.inter (hact (measurableSet_singleton k))
  have hSC := g.measurable_stoppedCounts hτ
  have hcyc := measurable_cyclicSize (α := α) a₁ a₂ a₃
  -- Probabilities of events of the randomisation do not depend on the instance.
  have hV : ∀ (ν' : Kernel α ℝ) [IsMarkovKernel ν'] (S : Set (ℕ → I)), MeasurableSet S →
      sourceMeasure ν' (Prod.fst ⁻¹' S) = V S := fun ν' _ S hS ↦ by
    rw [← Measure.map_apply measurable_fst hS, TransferBandits.map_fst_sourceMeasure]
  -- Transport of an event of the stopped counts to the cyclic map.
  have htrans : ∀ ν' ∈ unitBandits α, ∀ B : Set (α → ℕ), MeasurableSet B →
      sourceMeasure ν' (g.stoppedCounts τ ⁻¹' B) = sourceMeasure ν' (cyclicSize a₁ a₂ a₃ ⁻¹' B) :=
    fun ν' hν' B hB ↦ by
      rw [← Measure.map_apply hSC hB, ← Measure.map_apply hcyc hB, hlaw ν' hν']
  -- `V F₀ = 0`: on `{τ = 0}` the stopped counts are `0`, and the cyclic map is never `0`.
  have hF₀0 : V F₀ = 0 := by
    have : IsMarkovKernel (νb a₁) := (hνb a₁).1
    rw [← hV (νb a₁) F₀ hF₀, ← hτ0]
    refine le_antisymm ?_ bot_le
    calc sourceMeasure (νb a₁) {ω | τ ω = 0}
        ≤ sourceMeasure (νb a₁) (g.stoppedCounts τ ⁻¹' {0}) := by
          refine measure_mono fun ω hω ↦ ?_
          simp only [Set.mem_ofPred_eq] at hω
          simp only [Set.mem_preimage, Set.mem_singleton_iff, PriorStrategy.stoppedCounts]
          rw [hω]
          rfl
      _ = sourceMeasure (νb a₁) (cyclicSize a₁ a₂ a₃ ⁻¹' {0}) :=
          htrans _ (hνb a₁) _ (measurableSet_singleton 0)
      _ = 0 := by
          rw [Set.preimage_eq_empty, measure_empty]
          rw [Set.disjoint_singleton_left]
          rintro ⟨ω, hω⟩
          have h1 := congrFun hω a₁
          have h2 := congrFun hω a₂
          unfold cyclicSize at h1 h2
          split_ifs at h1 h2 <;>
            simp [h₁₂, h₁₃, h₂₃] at h1 h2
  -- `V (G k) = 0`: on `G k`, the stopped count of `k` is at least `1`.
  have hGle : ∀ (k : α) (ν' : Kernel α ℝ), ν' ∈ unitBandits α →
      V (G k) ≤ sourceMeasure ν' (cyclicSize a₁ a₂ a₃ ⁻¹' {n | 1 ≤ n k}) := fun k ν' hν' ↦ by
    have : IsMarkovKernel ν' := hν'.1
    rw [← hV ν' (G k) (hG k), ← htrans ν' hν' _ (measurableSet_le measurable_const
      (measurable_pi_apply k))]
    refine measure_mono fun ω hω ↦ ?_
    simp only [Set.mem_preimage, G, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq] at hω
    have hτ1 : 1 ≤ τ ω := by
      by_contra h0
      have : ω ∈ {ω : SourceSpace α | τ ω = 0} := by
        simp only [Set.mem_ofPred_eq]
        omega
      rw [hτ0] at this
      exact hω.1 this
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, PriorStrategy.stoppedCounts]
    rw [← hω.2, ← g.state_one_fst_act ω]
    exact g.state_fst_mono ω hτ1 _
  have hzero : ∀ k b, (∀ ω : SourceSpace α, (∀ i, ω.2 i 0 = c b i) →
      cyclicSize a₁ a₂ a₃ ω k = 0) → V (G k) = 0 := fun k b hb ↦ by
    have : IsMarkovKernel (νb b) := (hνb b).1
    refine le_antisymm ((hGle k (νb b) (hνb b)).trans (le_of_eq ?_)) bot_le
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae b] with ω hω
    simp [hb ω hω]
  have hGk : ∀ k, V (G k) = 0 := by
    intro k
    by_cases hk1 : k = a₁
    · rw [hk1]
      refine hzero a₁ a₂ fun ω hω ↦ ?_
      have e1 : ω.2 a₁ 0 = 0 := by rw [hω]; simp [c, h₁₂]
      have e2 : ω.2 a₂ 0 = 1 := by rw [hω]; simp [c]
      have e3 : ω.2 a₃ 0 = 0 := by rw [hω]; simp [c, Ne.symm h₂₃]
      unfold cyclicSize
      simp only [e1, e2, e3]
      norm_num [Pi.single_apply, h₁₂, h₁₃, h₂₃, Ne.symm h₁₂, Ne.symm h₁₃, Ne.symm h₂₃]
    by_cases hk2 : k = a₂
    · rw [hk2]
      refine hzero a₂ a₃ fun ω hω ↦ ?_
      have e1 : ω.2 a₁ 0 = 0 := by rw [hω]; simp [c, h₁₃]
      have e2 : ω.2 a₂ 0 = 0 := by rw [hω]; simp [c, h₂₃]
      have e3 : ω.2 a₃ 0 = 1 := by rw [hω]; simp [c]
      unfold cyclicSize
      simp only [e1, e2, e3]
      norm_num [Pi.single_apply, h₁₂, h₁₃, h₂₃, Ne.symm h₁₂, Ne.symm h₁₃, Ne.symm h₂₃]
    by_cases hk3 : k = a₃
    · rw [hk3]
      refine hzero a₃ a₁ fun ω hω ↦ ?_
      have e1 : ω.2 a₁ 0 = 1 := by rw [hω]; simp [c]
      have e2 : ω.2 a₂ 0 = 0 := by rw [hω]; simp [c, Ne.symm h₁₂]
      have e3 : ω.2 a₃ 0 = 0 := by rw [hω]; simp [c, Ne.symm h₁₃]
      unfold cyclicSize
      simp only [e1, e2, e3]
      norm_num [Pi.single_apply, h₁₂, h₁₃, h₂₃, Ne.symm h₁₂, Ne.symm h₁₃, Ne.symm h₂₃]
    · refine hzero k a₁ fun ω _ ↦ ?_
      unfold cyclicSize
      split_ifs <;> simp [hk1, hk2, hk3]
  -- The events cover the randomisation space.
  have hcover : (Set.univ : Set (ℕ → I)) ⊆ F₀ ∪ ⋃ k ∈ (Finset.univ : Finset α), G k := by
    intro u _
    by_cases hu : u ∈ F₀
    · exact Or.inl hu
    · exact Or.inr (Set.mem_biUnion (Finset.mem_univ (g.act 0 (u, fun i ↦ i.elim0)))
        ⟨hu, rfl⟩)
  have h1 : V Set.univ ≤ 0 := by
    calc V Set.univ ≤ V (F₀ ∪ ⋃ k ∈ (Finset.univ : Finset α), G k) := measure_mono hcover
      _ ≤ V F₀ + V (⋃ k ∈ (Finset.univ : Finset α), G k) := measure_union_le _ _
      _ ≤ V F₀ + ∑ k, V (G k) := by gcongr; exact measure_biUnion_finset_le _ _
      _ = 0 := by simp [hF₀0, hGk]
  rw [measure_univ] at h1
  exact one_ne_zero (le_antisymm h1 bot_le)

end Incognita.P003
