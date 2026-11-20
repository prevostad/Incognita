/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.StochasticBandits.GravesLai

/-! # The Graves–Lai constant of an unstructured class

The value of the Graves–Lai constant `C(ν; E)` [INC-P007, Definition `def:gl`] in two cases:
when the law of the optimal arm identifies the instance in `E` (then `C = 0`), and on an
unstructured class `∏_a D_a` (then `C = ∑_{a ≠ a⋆} Δ_a / 𝒦_inf(ν_a, m⋆; D_a)`).

Both proofs put the weight `∞` on the optimal arm `a⋆`: it costs nothing, since `Δ_{a⋆} = 0`, and
it meets the constraint of every alternative that moves the law of `a⋆`, whose divergence is then
positive (Gibbs' inequality, Mathlib's `klDiv_eq_zero_iff`). On an unstructured class, the
alternatives that move one suboptimal arm `a` give the lower bound `w_a ≥ 1 / 𝒦_inf(ν_a, m⋆; D_a)`
for every feasible weight; the weights `1 / 𝒦_inf + δ`, `δ > 0`, are feasible and give the upper
bound as `δ → 0`. The margin `δ` is needed when `𝒦_inf(ν_b, m⋆; D_b) = ∞` but an alternative raises
`b` above `m⋆` (at an infinite divergence): then the weight `0 = 1 / ∞` does not meet its
constraint, and every positive weight does.

## Main statements

* `gravesLai_eq_zero_of_identifies`: `C(ν; E) = 0` if every instance of `E` with the law of `a⋆`
  of `ν` is `ν` [INC-P007, Proposition `prop:gl-zero`].
* `le_gravesLai_productClass`, `gravesLai_productClass_le`, `gravesLai_productClass`: the value on
  an unstructured class [INC-P007, Theorem `thm:main`].
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Learning Bandits LMLExplore.Bandits
open Filter Finset

open scoped ENNReal NNReal Topology

namespace Incognita.StochasticBandits

variable {α : Type*} [MeasurableSpace α] [Fintype α] {E : Set (Kernel α ℝ)} {ν ν' : Kernel α ℝ}
  {aStar : α}

omit [Fintype α] in
/-- The unique optimal arm has the largest mean. -/
lemma iSup_integral_eq_of_unique [Finite α] (h : ∀ a ≠ aStar, 0 < gap ν a) :
    (⨆ b, (ν b)[id]) = (ν aStar)[id] := by
  have h0 := gap_eq_zero_of_unique h
  rwa [gap, sub_eq_zero] at h0

/-- A weight `∞` on an arm of gap `0` costs nothing: the cost of `w` updated to `∞` at `aStar` is
the cost of `w`. -/
lemma sum_update_top_mul_ofReal_gap [DecidableEq α] (w : α → ℝ≥0∞) (h : gap ν aStar = 0) :
    ∑ a, Function.update w aStar ⊤ a * ENNReal.ofReal (gap ν a) =
      ∑ a, w a * ENNReal.ofReal (gap ν a) := by
  refine sum_congr rfl fun a _ ↦ ?_
  rcases eq_or_ne a aStar with rfl | ha
  · simp [h]
  · rw [Function.update_of_ne ha]

/-- A weight `∞` on the arm `aStar` meets the constraint of every alternative `ν'` that changes the
law of `aStar`, since then `KL(ν_{aStar}, ν'_{aStar}) > 0`. -/
lemma one_le_sum_mul_klDiv_of_ne {w : α → ℝ≥0∞} (hw : w aStar = ⊤)
    [IsFiniteMeasure (ν aStar)] [IsFiniteMeasure (ν' aStar)] (hne : ν' aStar ≠ ν aStar) :
    1 ≤ ∑ a, w a * klDiv (ν a) (ν' a) := by
  have hkl : klDiv (ν aStar) (ν' aStar) ≠ 0 := fun h ↦ hne (klDiv_eq_zero_iff.mp h).symm
  calc 1 ≤ w aStar * klDiv (ν aStar) (ν' aStar) := by rw [hw, ENNReal.top_mul hkl]; exact le_top
    _ ≤ _ := single_le_sum (f := fun a ↦ w a * klDiv (ν a) (ν' a)) (fun _ _ ↦ zero_le)
        (mem_univ _)

/-- **The constant vanishes when the optimal arm identifies the instance** [INC-P007, Proposition
`prop:gl-zero`]: if every `ν' ∈ E` with `ν'_{a⋆} = ν_{a⋆}` is `ν`, then `C(ν; E) = 0`. The weight
`∞` on `a⋆` and `0` elsewhere is feasible, at cost `0`. Only the finiteness of the laws of `a⋆` is
used. -/
lemma gravesLai_eq_zero_of_identifies (haStar : ∀ a ≠ aStar, 0 < gap ν a)
    (hE : ∀ ν' ∈ E, IsFiniteMeasure (ν' aStar)) [IsFiniteMeasure (ν aStar)]
    (hid : ∀ ν' ∈ E, ν' aStar = ν aStar → ν' = ν) : gravesLai E ν = 0 := by
  classical
  refine le_antisymm ?_ zero_le
  have hfeas : ∀ ν' ∈ alt E ν,
      1 ≤ ∑ a, Function.update (0 : α → ℝ≥0∞) aStar ⊤ a * klDiv (ν a) (ν' a) := by
    intro ν' hν'
    have := hE ν' hν'.1
    refine one_le_sum_mul_klDiv_of_ne (Function.update_self _ _ _) fun heq ↦ ?_
    have : Nonempty α := ⟨aStar⟩
    exact not_mem_alt_self (hid ν' hν'.1 heq ▸ hν')
  calc gravesLai E ν ≤ ∑ a, Function.update (0 : α → ℝ≥0∞) aStar ⊤ a * ENNReal.ofReal (gap ν a) :=
        iInf₂_le _ hfeas
    _ = 0 := by rw [sum_update_top_mul_ofReal_gap _ (gap_eq_zero_of_unique haStar)]; simp

/-! ### Unstructured classes -/

section Product

variable [MeasurableSingletonClass α] {D : α → Set (Measure ℝ)}

/-- **Lower bound on the weights** (Step 1 of the proof of [INC-P007, Theorem `thm:main`]): on an
unstructured class, every feasible weight has `w_a ≥ 1 / 𝒦_inf(ν_a, m⋆; D_a)` at every suboptimal
arm `a`, by the alternatives that replace the law of `a` by a law of `D_a` with a mean above `m⋆`.
-/
lemma inv_dInf_le_of_feasible (hD : ∀ a, ∀ Q ∈ D a, IsFiniteMeasure Q) (hν : ν ∈ productClass D)
    (haStar : ∀ a ≠ aStar, 0 < gap ν a) {w : α → ℝ≥0∞}
    (hw : ∀ ν' ∈ alt (productClass D) ν, 1 ≤ ∑ b, w b * klDiv (ν b) (ν' b)) {a : α}
    (ha : 0 < gap ν a) : (dInf (D a) (ν a) (⨆ b, (ν b)[id]))⁻¹ ≤ w a := by
  classical
  rw [ENNReal.inv_le_iff_inv_le, le_dInf_iff]
  intro Q hQ hQmean
  have haS : a ≠ aStar := fun h ↦ ha.ne' (h ▸ gap_eq_zero_of_unique haStar)
  -- The instance `ν'` in which the law of the arm `a` is replaced by `Q`.
  set ν' := Kernel.ofFunOfCountable (Function.update (fun b ↦ ν b) a Q)
  have hν'a : ν' a = Q := by simp [ν']
  have hν'b : ∀ b ≠ a, ν' b = ν b := fun b hb ↦ by simp [ν', Function.update_of_ne hb]
  have hν'D : ν' ∈ productClass D := fun b ↦ by
    rcases eq_or_ne b a with rfl | hb
    · rwa [hν'a]
    · rw [hν'b b hb]
      exact hν b
  have hν'alt : ν' ∈ alt (productClass D) ν := by
    refine (mem_alt_iff_of_unique haStar).mpr ⟨hν'D, ?_⟩
    rw [gap, sub_pos, hν'b aStar haS.symm, ← iSup_integral_eq_of_unique haStar]
    have hle := le_ciSup (f := fun i ↦ (ν' i)[id]) (Finite.bddAbove_range _) a
    rw [hν'a] at hle
    exact hQmean.trans_le hle
  have hsum : ∑ b, w b * klDiv (ν b) (ν' b) = w a * klDiv (ν a) Q := by
    rw [sum_eq_single a]
    · rw [hν'a]
    · intro b _ hb
      have := hD b _ (hν b)
      rw [hν'b b hb, klDiv_self, mul_zero]
    · simp
  have h1 := hw ν' hν'alt
  rw [hsum] at h1
  refine (ENNReal.inv_le_iff_le_mul (fun h ↦ ?_) (fun h ↦ ?_)).mpr h1
  · intro h0
    rw [h0, zero_mul] at h1
    exact absurd h1 (by simp)
  · intro h0
    rw [h0, mul_zero] at h1
    exact absurd h1 (by simp)

/-- **Lower bound** of [INC-P007, Theorem `thm:main`] (Steps 1 and 2 of its proof):
`∑_{a ≠ a⋆} Δ_a / 𝒦_inf(ν_a, m⋆; D_a) ≤ C(ν; ∏_a D_a)`. -/
lemma le_gravesLai_productClass (hD : ∀ a, ∀ Q ∈ D a, IsFiniteMeasure Q)
    (hν : ν ∈ productClass D) (haStar : ∀ a ≠ aStar, 0 < gap ν a) :
    ∑ a ∈ univ.filter (fun a ↦ 0 < gap ν a),
        ENNReal.ofReal (gap ν a) / dInf (D a) (ν a) (⨆ b, (ν b)[id]) ≤
      gravesLai (productClass D) ν := by
  refine le_iInf₂ fun w hw ↦ ?_
  calc ∑ a ∈ univ.filter (fun a ↦ 0 < gap ν a),
        ENNReal.ofReal (gap ν a) / dInf (D a) (ν a) (⨆ b, (ν b)[id])
      ≤ ∑ a ∈ univ.filter (fun a ↦ 0 < gap ν a), w a * ENNReal.ofReal (gap ν a) := by
        refine sum_le_sum fun a ha ↦ ?_
        rw [ENNReal.div_eq_inv_mul]
        gcongr
        exact inv_dInf_le_of_feasible hD hν haStar hw (mem_filter.mp ha).2
    _ ≤ ∑ a, w a * ENNReal.ofReal (gap ν a) :=
        sum_le_sum_of_subset (filter_subset _ _)

omit [MeasurableSingletonClass α] in
/-- **Feasible weights** (Step 3 of the proof of [INC-P007, Theorem `thm:main`], with a margin):
if `𝒦_inf(ν_a, m⋆; D_a) > 0` at every suboptimal arm, then for every `δ ≠ 0` the weights
`1 / 𝒦_inf(ν_a, m⋆; D_a) + δ`, with `∞` at `a⋆`, are feasible. -/
lemma feasible_update_inv_dInf_add [DecidableEq α] (hD : ∀ a, ∀ Q ∈ D a, IsFiniteMeasure Q)
    (hν : ν ∈ productClass D) (haStar : ∀ a ≠ aStar, 0 < gap ν a)
    (hK : ∀ a, 0 < gap ν a → dInf (D a) (ν a) (⨆ b, (ν b)[id]) ≠ 0) {δ : ℝ≥0∞} (hδ : δ ≠ 0) :
    ∀ ν' ∈ alt (productClass D) ν, 1 ≤ ∑ a, Function.update
      (fun a ↦ (dInf (D a) (ν a) (⨆ b, (ν b)[id]))⁻¹ + δ) aStar ⊤ a * klDiv (ν a) (ν' a) := by
  intro ν' hν'
  obtain ⟨hν'D, hgap⟩ := (mem_alt_iff_of_unique haStar).mp hν'
  have := hD aStar _ (hν aStar)
  have := hD aStar _ (hν'D aStar)
  by_cases hne : ν' aStar ≠ ν aStar
  · exact one_le_sum_mul_klDiv_of_ne (by simp) hne
  rw [not_not] at hne
  have : Nonempty α := ⟨aStar⟩
  -- Some arm `b` has, in `ν'`, a mean above that of `aStar`, which is `m⋆`.
  rw [gap, sub_pos] at hgap
  obtain ⟨b, hb⟩ := exists_lt_of_lt_ciSup hgap
  have hbS : b ≠ aStar := fun h ↦ (h ▸ hb).false
  rw [hne, ← iSup_integral_eq_of_unique haStar] at hb
  set K := dInf (D b) (ν b) (⨆ c, (ν c)[id])
  have hKle : K ≤ klDiv (ν b) (ν' b) := dInf_le (hν'D b) hb
  have h1 : 1 ≤ (K⁻¹ + δ) * klDiv (ν b) (ν' b) := by
    by_cases hKtop : K = ⊤
    · rw [hKtop, top_le_iff] at hKle
      rw [hKle, ENNReal.mul_top (by simp [hδ])]
      exact le_top
    · calc (1 : ℝ≥0∞) = K⁻¹ * K := (ENNReal.inv_mul_cancel (hK b (haStar b hbS)) hKtop).symm
        _ ≤ (K⁻¹ + δ) * klDiv (ν b) (ν' b) := by gcongr; exact le_self_add
  calc 1 ≤ (K⁻¹ + δ) * klDiv (ν b) (ν' b) := h1
    _ = Function.update (fun a ↦ (dInf (D a) (ν a) (⨆ c, (ν c)[id]))⁻¹ + δ) aStar ⊤ b *
          klDiv (ν b) (ν' b) := by rw [Function.update_of_ne hbS]
    _ ≤ _ := single_le_sum (f := fun a ↦ Function.update
          (fun a ↦ (dInf (D a) (ν a) (⨆ c, (ν c)[id]))⁻¹ + δ) aStar ⊤ a * klDiv (ν a) (ν' a))
          (fun _ _ ↦ zero_le) (mem_univ b)

omit [MeasurableSingletonClass α] in
/-- **Upper bound** of [INC-P007, Theorem `thm:main`]:
`C(ν; ∏_a D_a) ≤ ∑_{a ≠ a⋆} Δ_a / 𝒦_inf(ν_a, m⋆; D_a)`. The weights of
`feasible_update_inv_dInf_add` cost `S + δ ∑_a Δ_a`, which tends to `S` as `δ → 0`. -/
lemma gravesLai_productClass_le (hD : ∀ a, ∀ Q ∈ D a, IsFiniteMeasure Q)
    (hν : ν ∈ productClass D) (haStar : ∀ a ≠ aStar, 0 < gap ν a) :
    gravesLai (productClass D) ν ≤ ∑ a ∈ univ.filter (fun a ↦ 0 < gap ν a),
      ENNReal.ofReal (gap ν a) / dInf (D a) (ν a) (⨆ b, (ν b)[id]) := by
  classical
  set K := fun a ↦ dInf (D a) (ν a) (⨆ b, (ν b)[id])
  set S := ∑ a ∈ univ.filter (fun a ↦ 0 < gap ν a), ENNReal.ofReal (gap ν a) / K a
  rcases eq_or_ne S ⊤ with hS | hS
  · rw [hS]; exact le_top
  -- A vanishing `𝒦_inf` at a suboptimal arm would make `S` infinite.
  have hK : ∀ a, 0 < gap ν a → K a ≠ 0 := fun a ha h0 ↦ hS (by
    refine top_le_iff.mp ?_
    calc ⊤ = ENNReal.ofReal (gap ν a) / K a := by
          rw [h0, ENNReal.div_zero (ENNReal.ofReal_pos.mpr ha).ne']
      _ ≤ S := single_le_sum (f := fun a ↦ ENNReal.ofReal (gap ν a) / K a)
          (fun _ _ ↦ zero_le) (mem_filter.mpr ⟨mem_univ a, ha⟩))
  set c := ∑ a, ENNReal.ofReal (gap ν a)
  -- For every `δ ≠ 0`, `C ≤ S + δ c`.
  have hδ : ∀ δ : ℝ≥0∞, δ ≠ 0 → gravesLai (productClass D) ν ≤ S + δ * c := by
    intro δ hδ
    have hcost : ∑ a, ((K a)⁻¹ + δ) * ENNReal.ofReal (gap ν a) ≤ S + δ * c := by
      simp_rw [add_mul, sum_add_distrib, c, mul_sum]
      gcongr
      simp only [S, sum_filter]
      refine sum_le_sum fun a _ ↦ ?_
      split_ifs with ha
      · rw [ENNReal.div_eq_inv_mul]
      · simp [ENNReal.ofReal_eq_zero.mpr (not_lt.mp ha)]
    calc gravesLai (productClass D) ν
        ≤ ∑ a, Function.update (fun a ↦ (K a)⁻¹ + δ) aStar ⊤ a * ENNReal.ofReal (gap ν a) :=
          iInf₂_le _ (feasible_update_inv_dInf_add hD hν haStar hK hδ)
      _ = ∑ a, ((K a)⁻¹ + δ) * ENNReal.ofReal (gap ν a) :=
          sum_update_top_mul_ofReal_gap _ (gap_eq_zero_of_unique haStar)
      _ ≤ S + δ * c := hcost
  -- Let `δ = 1 / n → 0`.
  have hc : c ≠ ⊤ := ENNReal.sum_ne_top.mpr fun _ _ ↦ ENNReal.ofReal_ne_top
  have hlim : Tendsto (fun n : ℕ ↦ S + (n : ℝ≥0∞)⁻¹ * c) atTop (𝓝 (S + 0 * c)) :=
    tendsto_const_nhds.add (ENNReal.Tendsto.mul_const ENNReal.tendsto_inv_nat_nhds_zero (.inr hc))
  rw [zero_mul, add_zero] at hlim
  exact ge_of_tendsto' hlim fun n ↦ hδ _ (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top n))

/-- **The Graves–Lai constant of an unstructured class** [INC-P007, Theorem `thm:main`]: for an
instance `ν ∈ ∏_a D_a` with a unique optimal arm `a⋆`,
`C(ν; ∏_a D_a) = ∑_{a ≠ a⋆} Δ_a / 𝒦_inf(ν_a, m⋆; D_a)` in `[0, ∞]`. Only the finiteness of the laws
of the models is used. -/
lemma gravesLai_productClass (hD : ∀ a, ∀ Q ∈ D a, IsFiniteMeasure Q)
    (hν : ν ∈ productClass D) (haStar : ∀ a ≠ aStar, 0 < gap ν a) :
    gravesLai (productClass D) ν = ∑ a ∈ univ.filter (fun a ↦ 0 < gap ν a),
      ENNReal.ofReal (gap ν a) / dInf (D a) (ν a) (⨆ b, (ν b)[id]) :=
  le_antisymm (gravesLai_productClass_le hD hν haStar) (le_gravesLai_productClass hD hν haStar)

end Product

end Incognita.StochasticBandits
