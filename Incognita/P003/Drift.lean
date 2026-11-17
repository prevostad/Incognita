/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.Checks

/-! # P003: the drift conditions and the classes `𝒞_L`

Proofs of [INC-P003, prop:drift (a)–(e)], [INC-P003, prop:classes (a)–(b)] and
[INC-P003, lem:prior-game (a)].

## Main statements

* `mean_mem_Icc`: the mean of a law of an instance of `𝒫^K` lies in `[0,1]`;
  `abs_mean_sub_mean_le_one`: two such means differ by at most `1`.
* `meanBand_mono`, `meanBand_eq_of_one_le`: `𝒫_L` grows with `L` and is every pair for `L ≥ 1`.
* `isConsistent_of_le`: `𝒞_{L'} ⊂ 𝒞_L` for `L ≤ L'`.
* The frozen statements `drift_of_twoSided`, `drift_of_mem_meanBand`, `drift_meanBand_inclusions`,
  `drift_all_pairs`, `drift_witness_exclusion`, `isConsistent_anti`, `isConsistent_one`,
  `constSize_isSizeRule`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Incognita.TransferBandits

open scoped Topology

namespace Incognita.P003

section Means

variable {α : Type*} [MeasurableSpace α]

/-- The mean of a law of an instance of `𝒫^K` lies in `[0,1]`. -/
lemma mean_mem_Icc {ν : Kernel α ℝ} (hν : ν ∈ unitBandits α) (a : α) :
    (ν a)[id] ∈ Set.Icc 0 1 := by
  have := hν.1
  have h := hν.2 a
  refine ⟨integral_nonneg_of_ae (h.mono fun x hx ↦ hx.1), ?_⟩
  calc (ν a)[id] ≤ ∫ _, (1 : ℝ) ∂(ν a) :=
        integral_mono_of_nonneg (h.mono fun x hx ↦ hx.1) (integrable_const 1)
          (h.mono fun x hx ↦ hx.2)
    _ = 1 := by simp

/-- Two means of laws of instances of `𝒫^K` differ by at most `1`. -/
lemma abs_mean_sub_mean_le_one {ν ν' : Kernel α ℝ} (hν : ν ∈ unitBandits α)
    (hν' : ν' ∈ unitBandits α) (a : α) : |(ν a)[id] - (ν' a)[id]| ≤ 1 := by
  have h := mean_mem_Icc hν a
  have h' := mean_mem_Icc hν' a
  exact abs_sub_le_iff.mpr ⟨by linarith [h.2, h'.1], by linarith [h.1, h'.2]⟩

/-- `𝒫_L` grows with `L`. -/
lemma meanBand_mono {L L' : α → ℝ} (hLL' : ∀ a, L a ≤ L' a) : meanBand L ⊆ meanBand L' :=
  fun _ hp ↦ ⟨hp.1, hp.2.1, fun a ↦ (hp.2.2 a).trans (hLL' a)⟩

/-- For `L ≥ 1`, `𝒫_L` is every pair of `𝒫^K × 𝒫^K`. -/
lemma meanBand_eq_of_one_le {L : α → ℝ} (hL : ∀ a, 1 ≤ L a) :
    meanBand L = unitBandits α ×ˢ unitBandits α := by
  ext p
  exact ⟨fun hp ↦ ⟨hp.1, hp.2.1⟩,
    fun hp ↦ ⟨hp.1, hp.2, fun a ↦ (abs_mean_sub_mean_le_one hp.1 hp.2 a).trans (hL a)⟩⟩

/-- `𝒞_{L'} ⊂ 𝒞_L` for `L ≤ L'`: the class only quantifies over the pairs of `𝒫_L`. -/
lemma isConsistent_of_le {L L' : α → ℝ} (hLL' : ∀ a, L a ≤ L' a) {π : TransferAlgorithm α}
    (hπ : IsConsistent L' π) : IsConsistent L π := by
  intro ν ν' hp
  exact hπ ν ν' (meanBand_mono hLL' hp)

/-- For `L ≥ 1`, `π ∈ 𝒞_L` iff the condition of def:consistency holds for every pair of
`𝒫^K × 𝒫^K`. -/
lemma isConsistent_iff_of_one_le {L : α → ℝ} (hL : ∀ a, 1 ≤ L a) (π : TransferAlgorithm α) :
    IsConsistent L π ↔
      ∀ ν ν' : Kernel α ℝ, ν ∈ unitBandits α → ν' ∈ unitBandits α →
        ∀ ρ : ℕ → SourceSpace α → α → ℕ, IsSourceStrategy ρ →
          ∀ a, (∃ b, (ν a)[id] < (ν b)[id]) → ∀ c : ℝ, 0 < c →
            Tendsto (fun T : ℕ ↦
                (∫ p, (onlineCount a p.2 : ℝ) ∂(gameMeasure ν' (ρ T) ν π T)) / (T : ℝ) ^ c)
              atTop (𝓝 0) := by
  have hmem : ∀ ν ν' : Kernel α ℝ, (ν, ν') ∈ meanBand L ↔ ν ∈ unitBandits α ∧ ν' ∈ unitBandits α :=
    fun ν ν' ↦ by rw [meanBand_eq_of_one_le hL]; rfl
  constructor
  · intro h ν ν' hν hν'
    exact h ν ν' ((hmem ν ν').mpr ⟨hν, hν'⟩)
  · intro h ν ν' hp
    exact h ν ν' ((hmem ν ν').mp hp).1 ((hmem ν ν').mp hp).2

end Means

/-- [INC-P003, prop:drift (a)] The two-sided strict drift condition implies `Drift_L` and
membership in `𝒫_L`. -/
theorem drift_of_twoSided {α : Type*} [Fintype α] [MeasurableSpace α]
    (_hK : 2 ≤ Fintype.card α) {L : α → ℝ} (_hL : ∀ a, 0 < L a)
    {ν ν' : Kernel α ℝ} (hν : ν ∈ unitBandits α) (hν' : ν' ∈ unitBandits α)
    (h : TwoSidedDriftBound L ν ν') :
    DriftBound L ν ν' ∧ (ν, ν') ∈ meanBand L :=
  ⟨fun a ↦ (le_abs_self _).trans_lt (h a), hν, hν', fun a ↦ (h a).le⟩

/-- [INC-P003, prop:drift (b)] Every pair of `𝒫_L` satisfies `Drift_{L'}` when `L' > L`
componentwise. -/
theorem drift_of_mem_meanBand {α : Type*} [Fintype α] [MeasurableSpace α]
    (_hK : 2 ≤ Fintype.card α) {L L' : α → ℝ} (_hL : ∀ a, 0 < L a) (hLL' : ∀ a, L a < L' a)
    {ν ν' : Kernel α ℝ} (h : (ν, ν') ∈ meanBand L) :
    DriftBound L' ν ν' :=
  fun a ↦ (le_abs_self _).trans_lt ((h.2.2 a).trans_lt (hLL' a))

/-- [INC-P003, prop:drift (c)] `{Drift_L} ⊂ 𝒫_L` iff `L ≥ 1`, `𝒫_L ⊂ {Drift_L}` iff `L > 1`, and
for `L < 1` neither inclusion holds. -/
theorem drift_meanBand_inclusions {α : Type*} [Fintype α] [MeasurableSpace α]
    (hK : 2 ≤ Fintype.card α) {L : α → ℝ} (hL : ∀ a, 0 < L a) :
    ((∀ ν ν' : Kernel α ℝ, ν ∈ unitBandits α → ν' ∈ unitBandits α →
        DriftBound L ν ν' → (ν, ν') ∈ meanBand L) ↔ ∀ a, 1 ≤ L a) ∧
      ((∀ ν ν' : Kernel α ℝ, (ν, ν') ∈ meanBand L → DriftBound L ν ν') ↔ ∀ a, 1 < L a) ∧
      ((∀ a, L a < 1) →
        (¬ ∀ ν ν' : Kernel α ℝ, ν ∈ unitBandits α → ν' ∈ unitBandits α →
            DriftBound L ν ν' → (ν, ν') ∈ meanBand L) ∧
          ¬ ∀ ν ν' : Kernel α ℝ, (ν, ν') ∈ meanBand L → DriftBound L ν ν') := by
  have hne : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  have h1 : (∀ ν ν' : Kernel α ℝ, ν ∈ unitBandits α → ν' ∈ unitBandits α →
        DriftBound L ν ν' → (ν, ν') ∈ meanBand L) ↔ ∀ a, 1 ≤ L a := by
    constructor
    · intro h a
      by_contra ha
      push Not at ha
      have hm := h (Kernel.const α (Measure.dirac 0)) (Kernel.const α (Measure.dirac 1))
        (const_dirac_mem_unitBandits (by norm_num)) (const_dirac_mem_unitBandits (by norm_num))
        (driftBound_const_dirac_iff.mpr fun b ↦ by linarith [hL b])
      have := ((mem_meanBand_const_dirac_iff (by norm_num) (by norm_num)).mp hm) a
      norm_num at this
      linarith
    · intro h ν ν' hν hν' _
      exact ⟨hν, hν', fun a ↦ (abs_mean_sub_mean_le_one hν hν' a).trans (h a)⟩
  have h2 : (∀ ν ν' : Kernel α ℝ, (ν, ν') ∈ meanBand L → DriftBound L ν ν') ↔
      ∀ a, 1 < L a := by
    constructor
    · intro h a
      by_contra ha
      push Not at ha
      obtain ⟨a₀, -, ha₀⟩ := Finset.exists_min_image Finset.univ L Finset.univ_nonempty
      have hx : L a₀ ∈ Set.Icc (0 : ℝ) 1 := ⟨(hL a₀).le, (ha₀ a (Finset.mem_univ a)).trans ha⟩
      have hd := h (Kernel.const α (Measure.dirac (L a₀))) (Kernel.const α (Measure.dirac 0))
        ((mem_meanBand_const_dirac_iff hx (by norm_num)).mpr fun b ↦ by
          simpa [abs_of_pos (hL a₀)] using ha₀ b (Finset.mem_univ b))
      have := (driftBound_const_dirac_iff.mp hd) a₀
      simp at this
    · intro h ν ν' hp a
      exact (le_abs_self _).trans_lt
        ((abs_mean_sub_mean_le_one hp.1 hp.2.1 a).trans_lt (h a))
  refine ⟨h1, h2, fun hL1 ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩⟩
  · obtain a := Classical.arbitrary α
    linarith [h1.mp h a, hL1 a]
  · obtain a := Classical.arbitrary α
    linarith [h2.mp h a, hL1 a]

/-- [INC-P003, prop:drift (d)] `𝒫_L` is every pair iff `L ≥ 1`; `Drift_L` holds for every pair iff
`L > 1`. -/
theorem drift_all_pairs {α : Type*} [Fintype α] [MeasurableSpace α]
    (_hK : 2 ≤ Fintype.card α) {L : α → ℝ} (_hL : ∀ a, 0 < L a) :
    (meanBand L = unitBandits α ×ˢ unitBandits α ↔ ∀ a, 1 ≤ L a) ∧
      ((∀ ν ν' : Kernel α ℝ, ν ∈ unitBandits α → ν' ∈ unitBandits α → DriftBound L ν ν') ↔
        ∀ a, 1 < L a) := by
  refine ⟨⟨fun h a ↦ ?_, meanBand_eq_of_one_le⟩, ⟨fun h a ↦ ?_, fun h ν ν' hν hν' a ↦ ?_⟩⟩
  · by_contra ha
    push Not at ha
    have hm : (Kernel.const α (Measure.dirac (1 : ℝ)), Kernel.const α (Measure.dirac (0 : ℝ))) ∈
        meanBand L := by
      rw [h]
      exact ⟨const_dirac_mem_unitBandits (by norm_num), const_dirac_mem_unitBandits (by norm_num)⟩
    have := ((mem_meanBand_const_dirac_iff (by norm_num) (by norm_num)).mp hm) a
    norm_num at this
    linarith
  · by_contra ha
    push Not at ha
    have := (driftBound_const_dirac_iff.mp
      (h _ _ (const_dirac_mem_unitBandits (x := 1) (by norm_num))
        (const_dirac_mem_unitBandits (x := 0) (by norm_num)))) a
    norm_num at this
    linarith
  · exact (le_abs_self _).trans_lt ((abs_mean_sub_mean_le_one hν hν' a).trans_lt (h a))

/-- [INC-P003, prop:drift (e)] Pairs with `ν' = ν` satisfy every condition; `(δ_1, δ_0)` is in
`𝒫_𝟏` and does not satisfy `Drift_𝟏`. -/
theorem drift_witness_exclusion {α : Type*} [Fintype α] [MeasurableSpace α]
    (hK : 2 ≤ Fintype.card α) {L : α → ℝ} (hL : ∀ a, 0 < L a) :
    (∀ ν ∈ unitBandits α, DriftBound L ν ν ∧ TwoSidedDriftBound L ν ν ∧ (ν, ν) ∈ meanBand L) ∧
      (Kernel.const α (Measure.dirac (1 : ℝ)), Kernel.const α (Measure.dirac (0 : ℝ))) ∈
          meanBand (fun _ ↦ 1) ∧
        ¬ DriftBound (fun _ ↦ 1) (Kernel.const α (Measure.dirac (1 : ℝ)))
          (Kernel.const α (Measure.dirac (0 : ℝ))) := by
  have hne : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  exact ⟨fun ν hν ↦ ⟨driftBound_self hL ν, twoSidedDriftBound_self hL ν,
      mem_meanBand_self (fun a ↦ (hL a).le) hν⟩,
    (mem_meanBand_const_dirac_iff (by norm_num) (by norm_num)).mpr fun _ ↦ by norm_num,
    not_driftBound_dirac_one_zero⟩

/-- [INC-P003, prop:classes (a)] If `L ≤ L'`, then `𝒞_{L'} ⊂ 𝒞_L`. -/
@[nolint unusedArguments]
theorem isConsistent_anti {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (_hK : 2 ≤ Fintype.card α) {L L' : α → ℝ}
    (_hL : ∀ a, 0 < L a) (_hL' : ∀ a, 0 < L' a) (hLL' : ∀ a, L a ≤ L' a) :
    {π : TransferAlgorithm α | IsConsistent L' π} ⊆ {π | IsConsistent L π} :=
  fun _ hπ ↦ isConsistent_of_le hLL' hπ

/-- [INC-P003, prop:classes (b)] `𝒞_L = 𝒞_𝟏` for `L ≥ 𝟏`; the intersection of the classes `𝒞_L`
is `𝒞_𝟏`, the class defined with every pair of instances. -/
@[nolint unusedArguments]
theorem isConsistent_one {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (_hK : 2 ≤ Fintype.card α) (π : TransferAlgorithm α) :
    (∀ L : α → ℝ, (∀ a, 1 ≤ L a) → (IsConsistent L π ↔ IsConsistent (fun _ ↦ 1) π)) ∧
      ((∀ L : α → ℝ, (∀ a, 0 < L a) → IsConsistent L π) ↔ IsConsistent (fun _ ↦ 1) π) ∧
      (IsConsistent (fun _ ↦ 1) π ↔
        ∀ ν ν' : Kernel α ℝ, ν ∈ unitBandits α → ν' ∈ unitBandits α →
          ∀ ρ : ℕ → SourceSpace α → α → ℕ, IsSourceStrategy ρ →
            ∀ a, (∃ b, (ν a)[id] < (ν b)[id]) → ∀ c : ℝ, 0 < c →
              Tendsto (fun T : ℕ ↦
                  (∫ p, (onlineCount a p.2 : ℝ) ∂(gameMeasure ν' (ρ T) ν π T)) / (T : ℝ) ^ c)
                atTop (𝓝 0)) := by
  have h1 : ∀ L : α → ℝ, (∀ a, 1 ≤ L a) → (IsConsistent L π ↔ IsConsistent (fun _ ↦ 1) π) :=
    fun L hL ↦ (isConsistent_iff_of_one_le hL π).trans
      (isConsistent_iff_of_one_le (fun _ ↦ le_rfl) π).symm
  refine ⟨h1, ⟨fun h ↦ h _ fun _ ↦ one_pos, fun h L _ ↦ ?_⟩,
    isConsistent_iff_of_one_le (fun _ ↦ le_rfl) π⟩
  exact isConsistent_of_le (L' := fun a ↦ max (L a) 1) (fun a ↦ le_max_left _ _)
    ((h1 _ fun a ↦ le_max_right _ _).mpr h)

/-- [INC-P003, lem:prior-game (a)] A constant size map is a size rule. -/
@[nolint unusedArguments]
theorem constSize_isSizeRule {α : Type*} [Fintype α] [MeasurableSpace α]
    (_hK : 2 ≤ Fintype.card α) (n : α → ℕ) :
    IsSizeRule (constSize n : SourceSpace α → α → ℕ) :=
  isSizeRule_constSize n

end Incognita.P003
