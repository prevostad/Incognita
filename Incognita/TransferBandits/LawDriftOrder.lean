/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.LawDriftReach
public import LMLExplore.InformationTheory.KullbackLeibler.Finite

/-! # Ordering the constants `D^d_a` by the pseudo-distance

The tools of [INC-P002, prop:order (b), (c)]: a larger pseudo-distance gives a smaller constant,
and the four examples of [INC-P002, def:ipm] are ordered, `|m(q) - m(q')| ≤ W₁ ≤ KS ≤ TV`
[INC-P002, lem:ipm-order].

## Main statements

* `ofReal_sq_sum_abs_sub_div_two_le_vecKL`: Pinsker's inequality for `vecKL`, from LMLExplore's
  `LMLExplore.sq_sum_abs_sub_le_two_mul_sum_mul_log_div`.
* `ofReal_sq_sub_vecMean_div_two_le_vecKs`, `vecKs_pos`: `K_S(ρ, ℓ) ≥ (ℓ - m(ρ))² / 2 > 0` when
  `m(ρ) < ℓ` (part of [INC-P002, lem:projection]).
* `driftConstant_le_of_ipm_le`: if `d₁ ≤ d₂` on `𝒫_S²` and `K_S(ν_a, μ) > 0`, then
  `D^{d₂} ≤ D^{d₁}` [INC-P002, prop:order, proof].
* `ipm_mono`, `ipm_w1Class_le_ipm_ksClass`: `KS ≤ TV` and `W₁ ≤ KS` on `S ⊆ [0,1]`
  [INC-P002, lem:ipm-order]; the second by Abel summation (`abs_sum_mul_sub_le`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace Incognita.TransferBandits

variable {S : Finset ℝ}

/-! ### Pinsker's inequality and the positivity of `K_S` -/

/-- Pinsker's inequality for the divergence of [INC-P002, def:laws]:
`(∑_y |r(y) - q(y)|)² / 2 ≤ KL(r, q)` for probability vectors. -/
lemma ofReal_sq_sum_abs_sub_div_two_le_vecKL {r q : S → ℝ} (hr : r ∈ probVecs S)
    (hq : q ∈ probVecs S) :
    ENNReal.ofReal ((∑ y, |r y - q y|) ^ 2 / 2) ≤ vecKL r q := by
  unfold vecKL
  split_ifs with h
  · apply ENNReal.ofReal_le_ofReal
    have hsum : (∑ y, if 0 < r y then r y * Real.log (r y / q y) else 0) =
        ∑ y, r y * Real.log (r y / q y) :=
      Finset.sum_congr rfl fun y _ ↦ by
        split_ifs with hy
        · rfl
        · rw [le_antisymm (not_lt.mp hy) (hr.1 y), zero_mul]
    rw [hsum]
    have := LMLExplore.sq_sum_abs_sub_le_two_mul_sum_mul_log_div (x := r) (z := q)
      (LMLExplore.mem_simplex_iff.2 hr) (LMLExplore.mem_simplex_iff.2 hq)
      fun y hy ↦ by
        by_contra hne
        exact (h y (lt_of_le_of_ne (hr.1 y) (Ne.symm hne))).ne' hy
    linarith
  · exact le_top

/-- `K_S(ρ, ℓ) ≥ (ℓ - m(ρ))² / 2` when `m(ρ) ≤ ℓ`, on `S ⊆ [0,1]`: by Pinsker's inequality every
`q` of mean at least `ℓ` has `KL(ρ, q) ≥ (ℓ - m(ρ))² / 2` (part of [INC-P002, lem:projection]). -/
lemma ofReal_sq_sub_vecMean_div_two_le_vecKs (hS : ∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) {r : S → ℝ}
    (hr : r ∈ probVecs S) {ℓ : ℝ} (h : vecMean r ≤ ℓ) :
    ENNReal.ofReal ((ℓ - vecMean r) ^ 2 / 2) ≤ vecKs S r ℓ := by
  refine le_iInf₂ fun q hq ↦ le_trans (ENNReal.ofReal_le_ofReal ?_)
    (ofReal_sq_sum_abs_sub_div_two_le_vecKL hr hq.1)
  have habs : |∑ y : S, (y : ℝ) * (q y - r y)| ≤ ∑ y, |q y - r y| :=
    abs_sum_le_of_mem_Icc fun y ↦ hS y y.2
  have h1 : ℓ - vecMean r ≤ ∑ y, |r y - q y| := by
    calc ℓ - vecMean r ≤ vecMean q - vecMean r := by linarith [hq.2]
      _ ≤ |vecMean q - vecMean r| := le_abs_self _
      _ ≤ ∑ y, |q y - r y| := by rwa [vecMean_sub]
      _ = ∑ y, |r y - q y| := Finset.sum_congr rfl fun y _ ↦ abs_sub_comm _ _
  have h0 : 0 ≤ ℓ - vecMean r := by linarith
  gcongr

/-- `K_S(ρ, ℓ) > 0` when `m(ρ) < ℓ`, on `S ⊆ [0,1]`, by
`ofReal_sq_sub_vecMean_div_two_le_vecKs` (part of [INC-P002, lem:projection]). -/
lemma vecKs_pos (hS : ∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) {r : S → ℝ} (hr : r ∈ probVecs S) {ℓ : ℝ}
    (h : vecMean r < ℓ) : 0 < vecKs S r ℓ :=
  (ENNReal.ofReal_pos.mpr (div_pos (pow_pos (sub_pos.mpr h) 2) two_pos)).trans_le
    (ofReal_sq_sub_vecMean_div_two_le_vecKs hS hr h.le)

/-- `K_0 = K_S(ν_a, μ) > 0` for an arm of an instance on `S ⊆ [0,1]` whose mean is below `μ`. -/
lemma vecKs_lawVec_pos {α : Type*} [MeasurableSpace α] (hS : ∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1)
    {ν : Kernel α ℝ} (hν : ν ∈ supportBandits S α) {a : α} {μ : ℝ} (ha : (ν a)[id] < μ) :
    0 < vecKs S (lawVec S (ν a)) μ := by
  have := hν.1
  exact vecKs_pos hS (lawVec_mem_probVecs (hν.2 a)) ((integral_id_eq_vecMean (hν.2 a)) ▸ ha)

/-! ### Monotonicity of the constant in the pseudo-distance -/

/-- `J_a(x, c; μ) ≥ x K_S(ν_a, μ)`: the first law of every alternative pair has mean at least
`μ`. -/
lemma mul_vecKs_le_programme (𝓕 : Set (S → ℝ)) (l : ℝ) (r r' : S → ℝ) (μ x c : ℝ) :
    ENNReal.ofReal x * vecKs S r μ ≤ programme 𝓕 l r r' μ x c :=
  le_iInf₂ fun p hp ↦ by
    calc ENNReal.ofReal x * vecKs S r μ ≤ ENNReal.ofReal x * vecKL r p.1 := by
          gcongr
          exact iInf₂_le p.1 ⟨hp.1, hp.2.2.1⟩
      _ ≤ _ := le_self_add

/-- When `K_S(ν_a, μ) > 0`, the set defining `D_a(c)` is nonempty: `J_a(x, c; μ) ≥ 1` for
`x = 1/K_S(ν_a, μ)` (for every `x > 0` when `K_S = ∞`). -/
lemma exists_one_le_programme {𝓕 : Set (S → ℝ)} {l : ℝ} {r r' : S → ℝ} {μ c : ℝ}
    (hK : 0 < vecKs S r μ) : ∃ x, 0 < x ∧ 1 ≤ programme 𝓕 l r r' μ x c := by
  rcases eq_or_ne (vecKs S r μ) ∞ with h | h
  · refine ⟨1, one_pos, le_trans ?_ (mul_vecKs_le_programme 𝓕 l r r' μ 1 c)⟩
    rw [h, ENNReal.ofReal_one, one_mul]
    exact le_top
  · have hpos := ENNReal.toReal_pos hK.ne' h
    refine ⟨1 / (vecKs S r μ).toReal, one_div_pos.mpr hpos,
      le_trans (le_of_eq ?_) (mul_vecKs_le_programme 𝓕 l r r' μ _ c)⟩
    rw [ENNReal.ofReal_div_of_pos hpos, ENNReal.ofReal_one, ENNReal.ofReal_toReal h,
      ENNReal.div_mul_cancel hK.ne' h]

/-- A larger pseudo-distance gives a smaller constant [INC-P002, prop:order, proof]: if
`d₁ ≤ d₂` on `𝒫_S²`, every pair feasible for `d₂` is feasible for `d₁`, so `J^{d₂} ≥ J^{d₁}` and
`D^{d₂}(c) ≤ D^{d₁}(c)`; `K_S(ν_a, μ) > 0` makes the set defining `D^{d₁}(c)` nonempty. -/
lemma driftConstant_le_of_ipm_le {𝓕₁ 𝓕₂ : Set (S → ℝ)} {l : ℝ} {r r' : S → ℝ} {μ c : ℝ}
    (h : ∀ q ∈ probVecs S, ∀ q' ∈ probVecs S, ipm 𝓕₁ q q' ≤ ipm 𝓕₂ q q')
    (hK : 0 < vecKs S r μ) :
    driftConstant 𝓕₂ l r r' μ c ≤ driftConstant 𝓕₁ l r r' μ c := by
  have hJ : ∀ x, programme 𝓕₁ l r r' μ x c ≤ programme 𝓕₂ l r r' μ x c := fun x ↦
    le_iInf₂ fun p hp ↦ iInf₂_le p ⟨hp.1, hp.2.1, hp.2.2.1, (h _ hp.1 _ hp.2.1).trans hp.2.2.2⟩
  exact csInf_le_csInf ⟨0, fun x hx ↦ hx.1.le⟩ (exists_one_le_programme hK)
    fun x hx ↦ ⟨hx.1, hx.2.trans (hJ x)⟩

/-! ### The order of the four examples -/

/-- A smaller class of test functions gives a smaller pseudo-distance. -/
lemma ipm_mono {𝓕₁ 𝓕₂ : Set (S → ℝ)} (h : 𝓕₁ ⊆ 𝓕₂) (h₁ : 𝓕₁.Nonempty)
    (h₂ : ∀ f ∈ 𝓕₂, ∀ y, f y ∈ Set.Icc 0 1) (q q' : S → ℝ) : ipm 𝓕₁ q q' ≤ ipm 𝓕₂ q q' := by
  have := h₁.to_subtype
  exact ciSup_le fun f ↦ le_ciSup_of_le (bddAbove_ipm h₂ q q') ⟨f, h f.2⟩ le_rfl

/-- Abel summation on a finite set `T ⊂ ℝ` [INC-P002, lem:ipm-order, proof]: if `f` is
`1`-Lipschitz on `T`, `T ⊆ [m, b]` with `b ∈ T`, and every partial sum
`G(s) = ∑_{y ∈ T, y ≤ s} D(y)` has `|G(s)| ≤ K`, then
`|∑_{y ∈ T} f(y) D(y) - f(b) ∑_{y ∈ T} D(y)| ≤ (b - m) K`. By induction on the maximum. -/
lemma abs_sum_mul_sub_le (T : Finset ℝ) (f D : ℝ → ℝ) {K m : ℝ}
    (hK : ∀ s, |∑ y ∈ T with y ≤ s, D y| ≤ K)
    (hf : ∀ y ∈ T, ∀ z ∈ T, |f y - f z| ≤ |y - z|) (hm : ∀ y ∈ T, m ≤ y) :
    ∀ b ∈ T, (∀ y ∈ T, y ≤ b) →
      |∑ y ∈ T, f y * D y - f b * ∑ y ∈ T, D y| ≤ (b - m) * K := by
  induction T using Finset.induction_on_max with
  | empty => simp
  | insert a T hlt ih =>
    intro b hb hbmax
    have hab : b = a := le_antisymm
      ((Finset.mem_insert.mp hb).elim (fun h ↦ h.le) fun h ↦ (hlt b h).le)
      (hbmax a (Finset.mem_insert_self a T))
    subst hab
    have haT : b ∉ T := fun h ↦ (hlt b h).false
    have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
    have hmb : m ≤ b := hm b (Finset.mem_insert_self b T)
    rw [Finset.sum_insert haT, Finset.sum_insert haT]
    rcases T.eq_empty_or_nonempty with hT | hT
    · subst hT
      simp only [Finset.sum_empty, add_zero, sub_self, abs_zero]
      exact mul_nonneg (sub_nonneg.mpr hmb) hK0
    -- the partial sums of `T` are partial sums of `insert b T`, at `min s b'`
    set b' := T.max' hT
    have hb'T : b' ∈ T := T.max'_mem hT
    have hb'b : b' < b := hlt b' hb'T
    have hfilt : ∀ s, ∑ y ∈ T with y ≤ s, D y = ∑ y ∈ insert b T with y ≤ min s b', D y := by
      intro s
      have hn : ¬ b ≤ min s b' := fun h ↦ (hb'b.trans_le (h.trans (min_le_right _ _))).false
      simp only [Finset.filter_insert, hn, ↓reduceIte]
      refine Finset.sum_congr ?_ fun _ _ ↦ rfl
      ext y
      simp only [Finset.mem_filter, le_min_iff]
      exact ⟨fun h ↦ ⟨h.1, h.2, T.le_max' y h.1⟩, fun h ↦ ⟨h.1, h.2.1⟩⟩
    have hKT : ∀ s, |∑ y ∈ T with y ≤ s, D y| ≤ K := fun s ↦ by rw [hfilt]; exact hK _
    have hsumT : |∑ y ∈ T, D y| ≤ K := by
      have := hKT b'
      rwa [Finset.filter_true_of_mem fun y hy ↦ T.le_max' y hy] at this
    have ih' := ih hKT (fun y hy z hz ↦ hf y (Finset.mem_insert_of_mem hy) z
      (Finset.mem_insert_of_mem hz)) (fun y hy ↦ hm y (Finset.mem_insert_of_mem hy)) b' hb'T
      fun y hy ↦ T.le_max' y hy
    have hfb : |f b' - f b| ≤ b - b' := by
      have := hf b' (Finset.mem_insert_of_mem hb'T) b (Finset.mem_insert_self b T)
      rwa [abs_of_neg (sub_neg.mpr hb'b), neg_sub] at this
    have hsplit : f b * D b + ∑ y ∈ T, f y * D y - f b * (D b + ∑ y ∈ T, D y) =
        (∑ y ∈ T, f y * D y - f b' * ∑ y ∈ T, D y) + (f b' - f b) * ∑ y ∈ T, D y := by ring
    rw [hsplit]
    calc _ ≤ |∑ y ∈ T, f y * D y - f b' * ∑ y ∈ T, D y| + |f b' - f b| * |∑ y ∈ T, D y| :=
          (abs_add_le _ _).trans_eq (by rw [abs_mul])
      _ ≤ (b' - m) * K + (b - b') * K := by
          gcongr
      _ = (b - m) * K := by ring

/-- `W₁ ≤ KS` on probability vectors of `S ⊆ [0,1]` [INC-P002, lem:ipm-order]: for a `1`-Lipschitz
`f`, Abel summation bounds `|∑_y f(y) (q(y) - q'(y))|` by `(x_max - x_min) KS(q, q')`, which is
at most `KS(q, q')`. -/
lemma ipm_w1Class_le_ipm_ksClass (hS : ∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) {q q' : S → ℝ}
    (hq : q ∈ probVecs S) (hq' : q' ∈ probVecs S) :
    ipm (w1Class S) q q' ≤ ipm (ksClass S) q q' := by
  have : Nonempty (w1Class S) := w1Class_isTestClass.1.to_subtype
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · subst hSe
    exact (zero_not_mem_probVecs (Subsingleton.elim q 0 ▸ hq)).elim
  refine ciSup_le fun f ↦ ?_
  set K := ipm (ksClass S) q q'
  -- the functions on `ℝ` that extend `f` and `q - q'` by `0`
  let F : ℝ → ℝ := fun x ↦ if h : x ∈ S then (f : S → ℝ) ⟨x, h⟩ else 0
  let D : ℝ → ℝ := fun x ↦ if h : x ∈ S then q ⟨x, h⟩ - q' ⟨x, h⟩ else 0
  have hF : ∀ y : S, F y = (f : S → ℝ) y := fun y ↦ by simp [F]
  have hD : ∀ y : S, D y = q y - q' y := fun y ↦ by simp [D]
  have hsum : ∀ g : ℝ → ℝ, ∑ y : S, g y = ∑ x ∈ S, g x := fun g ↦ Finset.sum_coe_sort S g
  have hK : ∀ s, |∑ x ∈ S with x ≤ s, D x| ≤ K := fun s ↦ by
    have hle := le_ciSup (bddAbove_ipm ksClass_isTestClass.2 q q')
      ⟨fun y : S ↦ if (y : ℝ) ≤ s then 1 else 0, s, rfl⟩
    refine le_of_eq_of_le ?_ hle
    rw [Finset.sum_filter, ← hsum fun x ↦ if x ≤ s then D x else 0]
    refine congrArg _ (Finset.sum_congr rfl fun y _ ↦ ?_)
    rw [hD]
    change _ = (if (y : ℝ) ≤ s then (1 : ℝ) else 0) * (q y - q' y)
    split_ifs <;> simp
  have hmain := abs_sum_mul_sub_le S F D (m := S.min' hSne) hK
    (fun y hy z hz ↦ by simpa [F, hy, hz] using (f : w1Class S).2.2 ⟨y, hy⟩ ⟨z, hz⟩)
    (fun y hy ↦ S.min'_le y hy) (S.max' hSne) (S.max'_mem hSne) fun y hy ↦ S.le_max' y hy
  have hD0 : ∑ x ∈ S, D x = 0 := by
    rw [← hsum D, Finset.sum_congr rfl fun y _ ↦ hD y, Finset.sum_sub_distrib, hq.2, hq'.2,
      sub_self]
  rw [hD0, mul_zero, sub_zero, ← hsum fun x ↦ F x * D x] at hmain
  simp only [hF, hD] at hmain
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  have hwidth : S.max' hSne - S.min' hSne ≤ 1 := by
    linarith [(hS _ (S.max'_mem hSne)).2, (hS _ (S.min'_mem hSne)).1]
  exact hmain.trans (mul_le_of_le_one_left hK0 hwidth)

/-- `KS ≤ TV`: the indicators of `(-∞, s]` are test functions of the total variation. -/
lemma ipm_ksClass_le_ipm_tvClass (q q' : S → ℝ) : ipm (ksClass S) q q' ≤ ipm (tvClass S) q q' :=
  ipm_mono (fun f hf ↦ ksClass_isTestClass.2 f hf) ksClass_isTestClass.1 (fun _ hf ↦ hf) q q'

end Incognita.TransferBandits
