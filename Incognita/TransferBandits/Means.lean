/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.Consistency
public import LMLExplore.Analysis.Convex.Integral

/-! # Means of instances, the sets `𝒫_L` and the classes `𝒞_L`

Basic facts about `unitBandits`, `meanBand` and `IsConsistent` [INC-P003, def:drift and
def:consistency].

## Main statements

* `mean_mem_Icc`: the mean of a law of an instance of `𝒫^K` lies in `[0,1]`;
  `abs_mean_sub_mean_le_one`: two such means differ by at most `1`.
* `meanBand_mono`, `meanBand_eq_of_one_le`: `𝒫_L` grows with `L` and is every pair for `L ≥ 1`.
* `isConsistent_of_le`: `𝒞_{L'} ⊂ 𝒞_L` for `L ≤ L'`; `isConsistent_iff_of_one_le`: for `L ≥ 1`,
  `𝒞_L` is the class defined with every pair of `𝒫^K × 𝒫^K`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter

open scoped Topology

namespace Incognita.TransferBandits

variable {α : Type*} [MeasurableSpace α]

/-- The mean of a law of an instance of `𝒫^K` lies in `[0,1]` (LMLExplore's
`integral_id_mem_Icc_of_ae_mem_Icc`). -/
lemma mean_mem_Icc {ν : Kernel α ℝ} (hν : ν ∈ unitBandits α) (a : α) :
    (ν a)[id] ∈ Set.Icc 0 1 :=
  haveI := hν.1
  integral_id_mem_Icc_of_ae_mem_Icc (hν.2 a)

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

end Incognita.TransferBandits
