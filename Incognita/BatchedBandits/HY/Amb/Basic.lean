/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.HY.HighBatches
public import Incognita.BatchedBandits.HY.Grid

/-! # A sub-optimal arm passes the consistency test when `x = 1`

[INC-P000, Lemma `lem:amb`], Steps 3–4 (the arm `a` is rejected at `t_ℓ`), for one history of HY:
the statistics at the cutoff `r = t_ℓ` and at the previous cutoff `r' = t_(ℓ-1)` are those of the
history `h` of the rounds `< t_ℓ` (`HY.threshold` reads both). The facts of Steps 1–2 (from
Lemmas `lem:optW`, `lem:fewC`, `lem:logcountC`) and the events `Acc_ℓ`, `KC_ℓ` of
Definition `def:amb` enter as hypotheses. `d_a = 𝒦_inf(ν_a, m⋆)` is the divergence of the paper
(`\da`), not the gap `Δ_a`.

* `HY.ofReal_threshold_le_of_mem`, `HY.threshold_le`, `HY.threshold_nonneg`: the consistency
  threshold `Λ̂_ℓ` is at most `L_ℓ`, and at most the bracket
  `N_c K̂_(ℓ-1)(c) / y_(ℓ-1) + log N_c` of every arm `c ∈ Q_ℓ` (not well sampled at `t_ℓ`, other
  than the previous leader).
* `HY.ofReal_mul_threshold_le_count_mul_testKinf`: Steps 3–4: with `K̂_ℓ(a) ≥ ε² / 8`,
  `a ≠ ĉ_(ℓ-1)`, the conditions (b) and (c) of Definition `def:amb`, and the old and new test
  divergences `K̂_(ℓ-1)(a) ≤ d_a (1 + 3γ/32)`, `K̂_ℓ(a) ≥ d_a (1 - γ/16)`, the arm `a` is
  rejected: `N_a(t_ℓ) K̂_ℓ(a) ≥ h_ℓ = (1 - γ_ℓ) y_(ℓ-1) Λ̂_ℓ`.
* `HY.testKinf_le_old`, `HY.le_testKinf_new`: the two bounds on the test divergences, from the
  accurate test levels (`Acc_ℓ`) and the accurate divergences of `a` (`KC_ℓ`), through
  Lemmas `lem:kinf`(iii), (v) and `lem:pseudo`(i)–(ii).
* `hyAlg_ae_ofReal_mul_threshold_le_count_mul_testKinf`: Steps 1–4 along almost every run: with
  the conclusions of Steps 1–2 and the traces of `Acc_ℓ`, `KC_ℓ` as hypotheses, `a ≠ ĉ_ℓ`,
  `K̂_ℓ(a) ≥ ε²/8` and `a` is rejected at `t_ℓ`.
* `Grid.exists_sum_activated_le`: Step 7, a function bounded and eventually `O(y^(-2))` has
  bounded sums over the activated batches (Lemma `lem:sparse`); the decay of the terms is
  `eventually_rpow_mul_exp_neg_le` of `Sums`.

The probabilities of Steps 5–6 are in `Incognita.BatchedBandits.HY.Amb.Prob` and
`Incognita.BatchedBandits.HY.Amb.Series`; the constants of Lemma `lem:constC` in
`Incognita.BatchedBandits.HY.Constants`; the abstract form of Lemma `lem:decompC` in
`Incognita.BatchedBandits.Counting`.
-/

@[expose] public section

open Learning Finset

open scoped ENNReal

namespace Incognita.BatchedBandits

namespace HY

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}

/-- The consistency threshold is nonnegative. -/
lemma threshold_nonneg {w₀ L y' : ℝ} (h : Hist Unit α ℝ n) (r r' U U' : ℕ) :
    0 ≤ threshold w₀ L y' h r r' U U' :=
  ENNReal.toReal_nonneg

/-- The consistency threshold is at most `L_ℓ` (for `L_ℓ ≥ 0`). -/
lemma threshold_le {w₀ L y' : ℝ} (hL : 0 ≤ L) (h : Hist Unit α ℝ n) (r r' U U' : ℕ) :
    threshold w₀ L y' h r r' U U' ≤ L := by
  unfold threshold
  calc _ ≤ (ENNReal.ofReal L).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (min_le_left _ _)
    _ = L := ENNReal.toReal_ofReal hL

/-- [INC-P000, Definition `def:hy`, (4)] The consistency threshold `Λ̂_ℓ` is at most the bracket
`N_c K̂_(ℓ-1)(c) / y_(ℓ-1) + log N_c` of every arm `c ∈ Q_ℓ` (not well sampled at `t_ℓ` and other
than the previous leader), in `ℝ≥0∞` (the paper's (eq:old) of the proof of Lemma `lem:amb`). -/
lemma ofReal_threshold_le_of_mem {w₀ L y' : ℝ} (h : Hist Unit α ℝ n) (r r' U U' : ℕ) {c : α}
    (hws : ¬ IsWellSampled h r U c) (hne : c ≠ leader w₀ h r') :
    ENNReal.ofReal (threshold w₀ L y' h r r' U U') ≤
      (count h r c : ℝ≥0∞) * testKinf w₀ h r' U' c / ENNReal.ofReal y' +
        ENNReal.ofReal (Real.log (count h r c)) := by
  classical
  unfold threshold
  rw [ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_left _ _))]
  refine (min_le_right _ _).trans ((iInf_le _ c).trans ?_)
  rw [ite_eq_left ⟨hws, hne⟩]

/-- [INC-P000, proof of Lemma `lem:amb`, Steps 3–4, for one history] Let `N = N_a(t_ℓ) ≥ 1` be the
count of an arm `a` at the cutoff `r = t_ℓ` of a history, `K̂_ℓ(a)` its test divergence at `r`
and `K̂_(ℓ-1)(a)` the one at the previous cutoff `r'`, `y' = y_(ℓ-1) ∈ (0, ȳ]`, `γ ∈ (0, 1/2]`,
`L = L_ℓ ≥ 0`, `ε > 0` and `Δ ≥ 0`, with
* `K̂_ℓ(a) ≥ ε² / 8` and `a ≠ ĉ_(ℓ-1)` (Steps 1–2 of the paper);
* `ȳ L ≤ (U / 2)(ε² / 8)` (condition (b) of Definition `def:amb`, `U = U_ℓ`);
* `2 ȳ log N ≤ γ (ε² / 8) N` (condition (c) at the count `N ≥ n_ℓ`);
* `K̂_(ℓ-1)(a) ≤ Δ (1 + 3γ/32)` and `K̂_ℓ(a) ≥ Δ (1 - γ/16)` (Step 4, case (i), from `Acc_ℓ` and
  `KC_ℓ`: `HY.testKinf_le_old`, `HY.le_testKinf_new`).
Then `a` is rejected: `K̂_ℓ(a) > 0` and `N K̂_ℓ(a) ≥ (1 - γ) y' Λ̂_ℓ`. -/
lemma ofReal_mul_threshold_le_count_mul_testKinf {w₀ L y' yb γ ε Δ : ℝ} {h : Hist Unit α ℝ n}
    {r r' U U' : ℕ} {a : α}
    (hL : 0 ≤ L) (hy' : 0 < y') (hyb : y' ≤ yb) (hγ0 : 0 < γ) (hγ : γ ≤ 1 / 2) (hΔ : 0 ≤ Δ)
    (hε : 0 < ε) (hne : a ≠ leader w₀ h r')
    (hKnew : ENNReal.ofReal (ε ^ 2 / 8) ≤ testKinf w₀ h r U a)
    (hW : yb * L ≤ U / 2 * (ε ^ 2 / 8))
    (hlog : 2 * yb * Real.log (count h r a) ≤ γ * (ε ^ 2 / 8) * count h r a)
    (hold : testKinf w₀ h r' U' a ≤ ENNReal.ofReal (Δ * (1 + 3 * γ / 32)))
    (hnew : ENNReal.ofReal (Δ * (1 - γ / 16)) ≤ testKinf w₀ h r U a) :
    0 < testKinf w₀ h r U a ∧
      ENNReal.ofReal ((1 - γ) * y' * threshold w₀ L y' h r r' U U') ≤
        (count h r a : ℝ≥0∞) * testKinf w₀ h r U a := by
  -- If `a` is well sampled, `N K̂_ℓ(a) ≥ (U/2)(ε²/8) ≥ ȳ L ≥ y' Λ̂_ℓ` (Step 3); otherwise
  -- `a ∈ Q_ℓ`, so `Λ̂_ℓ ≤ N K̂_(ℓ-1)(a) / y' + log N`, and either `log N > (γ/2) Λ̂_ℓ` (case (ii):
  -- condition (c)) or `K̂_ℓ(a) ≥ (1 - γ/2) K̂_(ℓ-1)(a)` gives `N K̂_ℓ(a) ≥ (1 - γ/2)² y' Λ̂_ℓ`
  -- (case (i)).
  set N := count h r a with hN
  set Kn := testKinf w₀ h r U a with hKn
  set Ko := testKinf w₀ h r' U' a with hKo
  set Λ := threshold w₀ L y' h r r' U U' with hΛ
  have hΛ0 : 0 ≤ Λ := threshold_nonneg h r r' U U'
  have hΛL : Λ ≤ L := threshold_le hL h r r' U U'
  have hε8 : 0 < ε ^ 2 / 8 := by positivity
  have hpos : 0 < Kn := lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hε8) hKnew
  refine ⟨hpos, ?_⟩
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hlogN0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  -- the bound through `ε² / 8`
  have hvia : ∀ x : ℝ, x ≤ N * (ε ^ 2 / 8) → ENNReal.ofReal x ≤ (N : ℝ≥0∞) * Kn := by
    intro x hx
    refine (ENNReal.ofReal_le_ofReal hx).trans ?_
    rw [ENNReal.ofReal_mul hN0, ENNReal.ofReal_natCast]
    gcongr
  have hyΛ : y' * Λ ≤ yb * L := mul_le_mul hyb hΛL hΛ0 (hy'.le.trans hyb)
  have h1γ : (1 - γ) * y' * Λ ≤ y' * Λ := by
    have : 0 ≤ y' * Λ := mul_nonneg hy'.le hΛ0
    nlinarith
  by_cases hWs : IsWellSampled h r U a
  · -- Step 3: `a` is well sampled
    have hNU : (U : ℝ) ≤ 2 * N := by exact_mod_cast hWs
    refine hvia _ ?_
    nlinarith
  -- Step 4: `a ∈ Q_ℓ`
  have hQ := ofReal_threshold_le_of_mem (L := L) (y' := y') h r r' U U' hWs hne
  rw [← hN, ← hKo, ← hΛ] at hQ
  by_cases hcase : γ / 2 * Λ < Real.log N
  · -- case (ii): the count is large
    refine hvia _ ?_
    have h2 : γ * (y' * Λ) ≤ 2 * yb * Real.log N := by
      have : γ * Λ ≤ 2 * Real.log N := by linarith
      nlinarith
    have h3 : γ * (y' * Λ) ≤ γ * (ε ^ 2 / 8 * N) := by nlinarith
    have h4 : y' * Λ ≤ ε ^ 2 / 8 * N := le_of_mul_le_mul_left h3 hγ0
    nlinarith
  · -- case (i): the new divergence is at least `(1 - γ/2)` times the old one
    have hcase : Real.log N ≤ γ / 2 * Λ := not_lt.mp hcase
    set ko := Δ * (1 + 3 * γ / 32) with hko
    have hko0 : 0 ≤ ko := by positivity
    have hQ' : ENNReal.ofReal Λ ≤ ENNReal.ofReal (N * ko / y' + Real.log N) := by
      refine hQ.trans ?_
      rw [ENNReal.ofReal_add (by positivity) hlogN0]
      gcongr
      rw [ENNReal.ofReal_div_of_pos hy', ENNReal.ofReal_mul hN0, ENNReal.ofReal_natCast]
      gcongr
    have hΛle : Λ ≤ N * ko / y' + Real.log N :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hQ'
    have hΛle' : y' * (Λ - Real.log N) ≤ N * ko := by
      have := mul_le_mul_of_nonneg_left hΛle hy'.le
      rw [mul_add, mul_div_cancel₀ _ hy'.ne'] at this
      linarith
    have hnew' : ENNReal.ofReal ((1 - γ / 2) * ko) ≤ Kn := by
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) hnew
      have hq : (1 - γ / 2) * (1 + 3 * γ / 32) ≤ 1 - γ / 16 := by nlinarith
      have := mul_le_mul_of_nonneg_left hq hΔ
      rw [hko]
      linarith
    refine le_trans (ENNReal.ofReal_le_ofReal (?_ : (1 - γ) * y' * Λ ≤ N * ((1 - γ / 2) * ko)))
      ?_
    · have hA : (1 - γ) * y' * Λ ≤ (1 - γ / 2) * (y' * (Λ - Real.log N)) := by
        have h1 : (1 - γ / 2) * Λ ≤ Λ - Real.log N := by linarith
        have h2 : 0 ≤ y' * Λ := mul_nonneg hy'.le hΛ0
        have h3 : (1 - γ / 2) * (y' * ((1 - γ / 2) * Λ)) ≤
            (1 - γ / 2) * (y' * (Λ - Real.log N)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hy'.le) (by linarith)
        have h4 : (1 - γ / 2) * (y' * ((1 - γ / 2) * Λ)) - (1 - γ) * y' * Λ =
            γ ^ 2 / 4 * (y' * Λ) := by ring
        have h5 : 0 ≤ γ ^ 2 / 4 * (y' * Λ) := by positivity
        linarith
      have hB : (1 - γ / 2) * (y' * (Λ - Real.log N)) ≤ (1 - γ / 2) * (N * ko) :=
        mul_le_mul_of_nonneg_left hΛle' (by linarith)
      linarith
    · rw [ENNReal.ofReal_mul hN0, ENNReal.ofReal_natCast]
      gcongr

/-- [INC-P000, proof of Lemma `lem:amb`, Step 4, the new divergence] For rewards in `[0, 1]`,
`w₀ ≥ 0`, an arm `a` with `N_a ≥ 1` at the cutoff `r`, `0 < ζ`, `2ζ ≤ m < 1`, a test level
`μ̂ ∈ [m - 2ζ, 1)` (the paper's `μ̂_ℓ ≥ m⋆ - 2ζ_ℓ` on `Acc_ℓ`) and the accurate divergence
`𝒦_inf(ν̂_a, m) ≥ Δ - ζ'` (the event `KC_ℓ` at the count `N_a(t_ℓ)`) with `2ζ / (1 - m) ≤ ζ'`:
`K̂_ℓ(a) ≥ Δ - 2ζ'` (Lemmas `lem:kinf`(iii), (v) and `lem:pseudo`(i)). -/
lemma le_testKinf_new {w₀ m ζ ζ' Δ : ℝ} {h : Hist Unit α ℝ n} {r U : ℕ} {a : α} (hw₀ : 0 ≤ w₀)
    (hfb : ∀ i, (h i).feedback ∈ Set.Icc (0 : ℝ) 1) (hN : 1 ≤ count h r a) (hζ : 0 < ζ)
    (h2ζ : 2 * ζ ≤ m) (hm : m < 1)
    (hlev : m - 2 * ζ ≤ pseudoMean w₀ h r (reference w₀ h r U))
    (hlev1 : pseudoMean w₀ h r (reference w₀ h r U) < 1)
    (hKC : ENNReal.ofReal (Δ - ζ') ≤ pseudoKinf 0 h r a m) (hζ' : 2 * ζ / (1 - m) ≤ ζ') :
    ENNReal.ofReal (Δ - 2 * ζ') ≤ testKinf w₀ h r U a := by
  have hN' : (1 : ℝ) ≤ count h r a := by exact_mod_cast hN
  have hshift := pseudoKinf_le_pseudoKinf_sub_add (w₀ := 0) (h := h) (r := r) (c := a) le_rfl
    (by linarith : 0 < 2 * ζ) h2ζ hm hfb (by rw [add_zero]; linarith)
  have hc0 : 0 ≤ 2 * ζ / (1 - m) := div_nonneg (by linarith) (by linarith)
  have h1 : ENNReal.ofReal (Δ - 2 * ζ') ≤ pseudoKinf 0 h r a (m - 2 * ζ) := by
    have h2 : ENNReal.ofReal (Δ - ζ' - 2 * ζ / (1 - m)) ≤ pseudoKinf 0 h r a (m - 2 * ζ) := by
      rw [ENNReal.ofReal_sub _ hc0, tsub_le_iff_right]
      exact hKC.trans hshift
    exact le_trans (ENNReal.ofReal_le_ofReal (by linarith)) h2
  refine h1.trans ((pseudoKinf_zero_le hw₀ (by linarith) (by linarith) hfb hN).trans ?_)
  exact pseudoKinf_mono hw₀ (by linarith) hlev hlev1 hfb

/-- [INC-P000, proof of Lemma `lem:amb`, Step 4, the old divergence] For rewards in `[0, 1]`,
`w₀ ≥ 0`, an arm `a` with `N'_a ≥ 1` at the cutoff `r'`, `0 < ζ`, `0 ≤ m`, `m + ζ < 1`, a test
level `μ̂' ≤ m + ζ` (the paper's `μ̂_(ℓ-1) ≤ m⋆ + ζ_ℓ` on `Acc_ℓ`), `w₀ κ(m + ζ) ≤ ζ' N'_a`
(condition (d) of Definition `def:amb` at the count `N_a(t_(ℓ-1)) ≥ n_ℓ`), the accurate divergence
`𝒦_inf(ν̂_a, m) ≤ Δ + ζ'` (the event `KC_ℓ` at that count) and `ζ / (1 - (m + ζ)) ≤ ζ'`, with
`Δ, ζ' ≥ 0`: `K̂_(ℓ-1)(a) ≤ Δ + 3ζ'` (Lemmas `lem:kinf`(iii), (v) and `lem:pseudo`(ii)). -/
lemma testKinf_le_old {w₀ m ζ ζ' Δ : ℝ} {h : Hist Unit α ℝ n} {r' U' : ℕ} {a : α}
    (hw₀ : 0 ≤ w₀) (hfb : ∀ i, (h i).feedback ∈ Set.Icc (0 : ℝ) 1) (hN : 1 ≤ count h r' a)
    (hζ : 0 < ζ) (hm0 : 0 ≤ m) (hm : m + ζ < 1) (hΔ : 0 ≤ Δ) (hζ'0 : 0 ≤ ζ')
    (hlev : pseudoMean w₀ h r' (reference w₀ h r' U') ≤ m + ζ)
    (hw : w₀ * Real.log (1 / (1 - (m + ζ))) ≤ ζ' * count h r' a)
    (hKC : pseudoKinf 0 h r' a m ≤ ENNReal.ofReal (Δ + ζ')) (hζ' : ζ / (1 - (m + ζ)) ≤ ζ') :
    testKinf w₀ h r' U' a ≤ ENNReal.ofReal (Δ + 3 * ζ') := by
  set N := count h r' a with hNdef
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hmono : testKinf w₀ h r' U' a ≤ pseudoKinf w₀ h r' a (m + ζ) :=
    pseudoKinf_mono hw₀ (pseudoMean_nonneg hw₀ hfb _) hlev hm hfb
  have hmul := mul_pseudoKinf_le (h := h) (r := r') (c := a) hw₀ hm (by linarith) hfb hN
  have hshift := pseudoKinf_le_pseudoKinf_sub_add (w₀ := 0) (h := h) (r := r') (c := a) le_rfl
    hζ (by linarith : ζ ≤ m + ζ) hm hfb (by rw [add_zero]; linarith)
  rw [add_sub_cancel_right] at hshift
  have h0 : pseudoKinf 0 h r' a (m + ζ) ≤ ENNReal.ofReal (Δ + 2 * ζ') := by
    refine hshift.trans ?_
    rw [show Δ + 2 * ζ' = (Δ + ζ') + ζ' by ring, ENNReal.ofReal_add (by linarith) hζ'0]
    gcongr
  have hprod : (N : ℝ≥0∞) * testKinf w₀ h r' U' a ≤ (N : ℝ≥0∞) * ENNReal.ofReal (Δ + 3 * ζ') := by
    calc (N : ℝ≥0∞) * testKinf w₀ h r' U' a ≤ (N : ℝ≥0∞) * pseudoKinf w₀ h r' a (m + ζ) := by
          gcongr
      _ ≤ (N : ℝ≥0∞) * pseudoKinf 0 h r' a (m + ζ) +
          ENNReal.ofReal (w₀ * Real.log (1 / (1 - (m + ζ)))) := hmul
      _ ≤ (N : ℝ≥0∞) * ENNReal.ofReal (Δ + 2 * ζ') + ENNReal.ofReal (ζ' * N) := by
          gcongr
      _ = (N : ℝ≥0∞) * ENNReal.ofReal (Δ + 3 * ζ') := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
              (by positivity)]
          congr 1
          ring
  have hN0 : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  exact (ENNReal.mul_le_mul_iff_right hN0 (ENNReal.natCast_ne_top N)).mp hprod

end HY

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α]

/-- [INC-P000, Lemma `lem:amb`, Steps 1–4, along a run] Along almost every run of HY (`w₀ ≥ 0`) on
an instance `ν` of `𝒫`, let `ℓ ≥ 2` (the test at `t_ℓ` for the batch `ℓ + 1`), a sub-optimal arm
`a`, `ε, ζ > 0`, `γ = γ_ℓ ∈ (0, 1/2]`, `Δ ≥ 0` (the paper's `d_a = 𝒦_inf(ν_a, m⋆)`), `ζ' = 2ζ/(1 -
m⋆) = γΔ/32`
(the paper's `ζ_ℓ`, `ζ'_ℓ`), `ȳ ≥ y_(ℓ-1)` and a count `n_ℓ ≥ e`, with the conditions of
Definition `def:amb`: (b) `ȳ L_ℓ ≤ (U_ℓ/2)(ε²/8)`, (c) `16 ȳ log n_ℓ ≤ γ ε² n_ℓ`,
(d) `w₀ κ(m⋆ + ζ) ≤ ζ' n_ℓ`, `2 w₀ ≤ ζ U_ℓ` and `2ζ ≤ min(ε, m⋆, 1 - m⋆)`, and
`t_(ℓ-1) ≥ K U_(ℓ-1)`, `U_(ℓ-1) ≤ U_ℓ`. Assume the facts of Steps 1–2 (from Lemmas `lem:optW`,
`lem:fewC`, `lem:logcountC` at `j = ℓ + 1` and `j = ℓ`):
* some optimal arm is well sampled at `t_ℓ`, and `μ̂_ℓ ≥ m⋆ - 2ε`;
* `m̂_a(t_ℓ) < m⋆ - 3ε`, `N_a(t_ℓ) ≥ n_ℓ`, `N_a(t_(ℓ-1)) ≥ n_ℓ` and `a ≠ ĉ_(ℓ-1)`;
and the traces of `Acc_ℓ` (every arm with `N_c(t_k) ≥ U_(ℓ-1)/2`, `k ∈ {ℓ - 1, ℓ}`, has
`|m̂_c(t_k) - m_c| ≤ ζ`) and `KC_ℓ` (`|𝒦_inf(ν̂_a(t_k), m⋆) - Δ| ≤ ζ'` for `k ∈ {ℓ - 1, ℓ}`). Then
`a ≠ ĉ_ℓ`, `K̂_ℓ(a) ≥ ε²/8`, and `a` is rejected at `t_ℓ`:
`K̂_ℓ(a) > 0` and `N_a(t_ℓ) K̂_ℓ(a) ≥ (1 - γ_ℓ) y_(ℓ-1) Λ̂_ℓ` (the threshold `h_ℓ` of HY). -/
lemma hyAlg_ae_ofReal_mul_threshold_le_count_mul_testKinf (w₀ β : ℝ) (hw₀ : 0 ≤ w₀) (ωs θ γ : ℕ → ℝ)
    (g : Grid (Fintype.card α)) {ν : ProbabilityTheory.Kernel α ℝ}
    [ProbabilityTheory.IsMarkovKernel ν] (hν : ν ∈ unitBandits α) :
    ∀ᵐ ω ∂(trajMeasure (hyAlg w₀ β ωs θ γ g : Algorithm Unit α ℝ) (Environment.bandit ν)),
      ∀ ℓ, 2 ≤ ℓ → ∀ (a : α) (ε ζ ζ' Δ yb nl : ℝ),
      (∫ y, id y ∂(ν a)) < (⨆ b, ∫ y, id y ∂(ν b)) →
      0 < ε → 0 < ζ → 0 < γ ℓ → γ ℓ ≤ 1 / 2 → 0 ≤ Δ →
      ζ' = 2 * ζ / (1 - (⨆ b, ∫ y, id y ∂(ν b))) → ζ' = γ ℓ * Δ / 32 →
      2 * ζ ≤ ε → 2 * ζ ≤ (⨆ b, ∫ y, id y ∂(ν b)) → 2 * ζ ≤ 1 - (⨆ b, ∫ y, id y ∂(ν b)) →
      2 * w₀ ≤ ζ * g.netSize β ℓ →
      w₀ * Real.log (1 / (1 - ((⨆ b, ∫ y, id y ∂(ν b)) + ζ))) ≤ ζ' * nl →
      g.ratio (ℓ - 1) ^ 2 ≤ yb → yb * g.logEnd ℓ ≤ g.netSize β ℓ / 2 * (ε ^ 2 / 8) →
      Real.exp 1 ≤ nl → 16 * yb * Real.log nl ≤ γ ℓ * ε ^ 2 * nl →
      Fintype.card α * g.netSize β (ℓ - 1) ≤ g.t (ℓ - 1) →
      g.netSize β (ℓ - 1) ≤ g.netSize β ℓ →
      (∃ a', (∫ y, id y ∂(ν a')) = (⨆ b, ∫ y, id y ∂(ν b)) ∧
        g.netSize β ℓ ≤ 2 * pullCount IT.action a' (g.t ℓ) ω) →
      (⨆ b, ∫ y, id y ∂(ν b)) - 2 * ε ≤
        HY.pseudoMean w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ)
          (HY.reference w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ)
            (g.netSize β ℓ)) →
      HY.pseudoMean 0 (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) a <
        (⨆ b, ∫ y, id y ∂(ν b)) - 3 * ε →
      nl ≤ pullCount IT.action a (g.t ℓ) ω → nl ≤ pullCount IT.action a (g.t (ℓ - 1)) ω →
      a ≠ HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t (ℓ - 1)) ω) (g.t (ℓ - 1)) →
      (∀ c k, ℓ - 1 ≤ k → k ≤ ℓ → g.netSize β (ℓ - 1) ≤ 2 * pullCount IT.action c (g.t k) ω →
        |HY.pseudoMean 0 (history IT.obs IT.action IT.feedback (g.t k) ω) (g.t k) c -
          ∫ y, id y ∂(ν c)| ≤ ζ) →
      (∀ k, ℓ - 1 ≤ k → k ≤ ℓ →
        HY.pseudoKinf 0 (history IT.obs IT.action IT.feedback (g.t k) ω) (g.t k) a
            (⨆ b, ∫ y, id y ∂(ν b)) ≤ ENNReal.ofReal (Δ + ζ') ∧
          ENNReal.ofReal (Δ - ζ') ≤ HY.pseudoKinf 0
            (history IT.obs IT.action IT.feedback (g.t k) ω) (g.t k) a (⨆ b, ∫ y, id y ∂(ν b))) →
      a ≠ HY.leader w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) ∧
      ENNReal.ofReal (ε ^ 2 / 8) ≤ HY.testKinf w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω)
        (g.t ℓ) (g.netSize β ℓ) a ∧
      0 < HY.testKinf w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ)
        (g.netSize β ℓ) a ∧
      ENNReal.ofReal ((1 - γ ℓ) * g.ratio (ℓ - 1) ^ 2 *
          HY.threshold w₀ (g.logEnd ℓ) (g.ratio (ℓ - 1) ^ 2)
            (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ) (g.t (ℓ - 1))
            (g.netSize β ℓ) (g.netSize β (ℓ - 1))) ≤
        (pullCount IT.action a (g.t ℓ) ω : ℝ≥0∞) *
          HY.testKinf w₀ (history IT.obs IT.action IT.feedback (g.t ℓ) ω) (g.t ℓ)
            (g.netSize β ℓ) a := by
  filter_upwards [ae_feedback_mem_Icc (alg := hyAlg w₀ β ωs θ γ g) hν,
    hyAlg_ae_one_le_pullCount w₀ β ωs θ γ g (Environment.bandit ν)] with ω hfb hN1
  intro ℓ hℓ a ε ζ ζ' Δ yb nl ha hε hζ hγ0 hγ hΔ hζ'1 hζ'2 h2ε h2m h2m1 hwU hwn hyb hb he hc
    hKU hUU ⟨a', ha'opt, ha'ws⟩ hμε hmean hnl hnl' hne hAcc hKC
  set ms := ⨆ b, ∫ y, id y ∂(ν b) with hms
  have hle_ms : ∀ c, (∫ y, id y ∂(ν c)) ≤ ms := fun c ↦
    le_ciSup (Finite.bddAbove_range fun b ↦ ∫ y, id y ∂(ν b)) c
  set h := history IT.obs IT.action IT.feedback (g.t ℓ) ω with hh
  set h' := history IT.obs IT.action IT.feedback (g.t (ℓ - 1)) ω with hh'
  have hfbh : ∀ i, (h i).feedback ∈ Set.Icc (0 : ℝ) 1 := fun i ↦ hfb i
  have hfbh' : ∀ i, (h' i).feedback ∈ Set.Icc (0 : ℝ) 1 := fun i ↦ hfb i
  have hrr : g.t (ℓ - 1) ≤ g.t ℓ := g.strictMono.monotone (Nat.sub_le ℓ 1)
  have hcnt : ∀ c, HY.count h (g.t ℓ) c = pullCount IT.action c (g.t ℓ) ω := fun c ↦
    HY.count_history (O := IT.obs) (A := IT.action) (Y := IT.feedback) (ω := ω) le_rfl c
  have hcnt' : ∀ c, HY.count h' (g.t (ℓ - 1)) c = pullCount IT.action c (g.t (ℓ - 1)) ω :=
    fun c ↦ HY.count_history (O := IT.obs) (A := IT.action) (Y := IT.feedback) (ω := ω) le_rfl c
  have hms1 : ms < 1 := by linarith
  have hmsζ : ms + ζ < 1 := by linarith
  have hnl1 : (1 : ℝ) < nl := lt_of_lt_of_le (by linarith [Real.add_one_le_exp (1 : ℝ)]) he
  have hNa : 1 ≤ HY.count h (g.t ℓ) a := by
    rw [hcnt]; exact_mod_cast (show (1 : ℝ) ≤ pullCount IT.action a (g.t ℓ) ω by linarith)
  have hNa' : 1 ≤ HY.count h' (g.t (ℓ - 1)) a := by
    rw [hcnt']
    exact_mod_cast (show (1 : ℝ) ≤ pullCount IT.action a (g.t (ℓ - 1)) ω by linarith)
  have hU1 : 1 ≤ g.netSize β ℓ := g.one_le_netSize β ℓ
  -- the test level at `t_ℓ`: `m⋆ - 2ζ ≤ μ̂_ℓ ≤ m⋆ + ζ`
  have hws' : HY.IsWellSampled h (g.t ℓ) (g.netSize β ℓ) a' := by
    unfold HY.IsWellSampled; rw [hcnt]; exact ha'ws
  obtain ⟨hrefws, hrefge⟩ := HY.reference_spec (w₀ := w₀) hws'
  set ref := HY.reference w₀ h (g.t ℓ) (g.netSize β ℓ) with href
  have hrefws' : g.netSize β (ℓ - 1) ≤ 2 * pullCount IT.action ref (g.t ℓ) ω := by
    have := hrefws
    unfold HY.IsWellSampled at this
    rw [hcnt] at this
    omega
  have hμup : HY.pseudoMean w₀ h (g.t ℓ) ref ≤ ms + ζ := by
    have hm := HY.pseudoMean_le_add_of_abs_sub_le hw₀ (hAcc ref ℓ (by omega) le_rfl hrefws')
      (fun k ↦ (hfbh k).1)
    linarith [hle_ms ref]
  have hμlo : ms - 2 * ζ ≤ HY.pseudoMean w₀ h (g.t ℓ) ref := by
    have hdev := abs_le.mp (hAcc a' ℓ (by omega) le_rfl (by omega))
    have h1 := HY.pseudoMean_zero_sub_le_of_le hw₀ hfbh hU1 hws'
    have h2 : 2 * w₀ / (g.netSize β ℓ : ℝ) ≤ ζ := by
      rw [div_le_iff₀ (by exact_mod_cast hU1)]
      linarith
    linarith
  have hμ1 : HY.pseudoMean w₀ h (g.t ℓ) ref < 1 := by linarith
  -- Step 1: `K̂_ℓ(a) ≥ 𝒦_inf(ν̂_a(t_ℓ), m⋆ - 2ε) ≥ ε²/8` and `a ≠ ĉ_ℓ`
  have hmean0 : 0 ≤ HY.pseudoMean 0 h (g.t ℓ) a := HY.pseudoMean_nonneg le_rfl hfbh a
  have hD : ENNReal.ofReal (ε ^ 2 / 8) ≤ HY.pseudoKinf 0 h (g.t ℓ) a (ms - 2 * ε) := by
    have := HY.ofReal_sq_div_eight_le_pseudoKinf (h := h) (r := g.t ℓ) (c := a) (w₀ := 0)
      (μ := ms - 2 * ε) (q := HY.pseudoMean 0 h (g.t ℓ) a) le_rfl (by linarith) (by linarith) hfbh
      (by rw [add_zero]; exact_mod_cast hNa) le_rfl (by linarith)
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) this
    have h0 : ε ≤ ms - 2 * ε - HY.pseudoMean 0 h (g.t ℓ) a := by linarith
    have : ε ^ 2 ≤ (ms - 2 * ε - HY.pseudoMean 0 h (g.t ℓ) a) ^ 2 := by
      have := mul_le_mul h0 h0 hε.le (by linarith)
      nlinarith
    linarith
  have hDpos : 0 < HY.pseudoKinf 0 h (g.t ℓ) a (ms - 2 * ε) :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity)) hD
  obtain ⟨-, hnotL, hDK, -⟩ := HY.pseudoMean_lt_and_ne_leader_and_pseudoKinf_le_testKinf
      (U := g.netSize β ℓ) hw₀ hfbh hNa (by linarith)
    (hμε.trans_eq rfl) hμ1 hDpos
  have hKnew8 : ENNReal.ofReal (ε ^ 2 / 8) ≤ HY.testKinf w₀ h (g.t ℓ) (g.netSize β ℓ) a :=
    hD.trans hDK
  refine ⟨hnotL, hKnew8, ?_⟩
  -- the previous test level: `μ̂_(ℓ-1) ≤ m⋆ + ζ`, some arm is well sampled at `t_(ℓ-1)`
  obtain ⟨c₀, hc₀'⟩ := exists_le_pullCount_of_card_mul_le (A := IT.action) (ω := ω) hKU
  have hc₀ : HY.IsWellSampled h' (g.t (ℓ - 1)) (g.netSize β (ℓ - 1)) c₀ := by
    unfold HY.IsWellSampled
    rw [hcnt']
    omega
  obtain ⟨hrefws₀, -⟩ := HY.reference_spec (w₀ := w₀) hc₀
  set ref' := HY.reference w₀ h' (g.t (ℓ - 1)) (g.netSize β (ℓ - 1)) with href'
  have hμ'up : HY.pseudoMean w₀ h' (g.t (ℓ - 1)) ref' ≤ ms + ζ := by
    have hws0 : g.netSize β (ℓ - 1) ≤ 2 * pullCount IT.action ref' (g.t (ℓ - 1)) ω := by
      have := hrefws₀
      unfold HY.IsWellSampled at this
      rwa [hcnt'] at this
    have hm := HY.pseudoMean_le_add_of_abs_sub_le hw₀
      (hAcc ref' (ℓ - 1) le_rfl (Nat.sub_le ℓ 1) hws0) (fun k ↦ (hfbh' k).1)
    linarith [hle_ms ref']
  -- Step 4: the old and new test divergences
  have hζ'0 : 0 ≤ ζ' := by rw [hζ'2]; positivity
  have hold : HY.testKinf w₀ h' (g.t (ℓ - 1)) (g.netSize β (ℓ - 1)) a ≤
      ENNReal.ofReal (Δ * (1 + 3 * γ ℓ / 32)) := by
    have hK := HY.testKinf_le_old (U' := g.netSize β (ℓ - 1)) hw₀ hfbh' hNa' hζ (by linarith)
      hmsζ hΔ hζ'0 hμ'up (by
        rw [hcnt']
        refine hwn.trans (mul_le_mul_of_nonneg_left hnl' hζ'0))
      ((hKC (ℓ - 1) le_rfl (Nat.sub_le ℓ 1)).1) (by
        rw [hζ'1, div_le_div_iff₀ (by linarith) (by linarith)]
        nlinarith)
    refine hK.trans_eq ?_
    congr 1
    rw [hζ'2]
    ring
  have hnew : ENNReal.ofReal (Δ * (1 - γ ℓ / 16)) ≤
      HY.testKinf w₀ h (g.t ℓ) (g.netSize β ℓ) a := by
    have hK := HY.le_testKinf_new (U := g.netSize β ℓ) hw₀ hfbh hNa hζ h2m hms1 hμlo hμ1
      ((hKC ℓ (by omega) le_rfl).2) (by rw [hζ'1])
    refine le_of_eq_of_le ?_ hK
    congr 1
    rw [hζ'2]
    ring
  -- condition (c) at the count `N_a(t_ℓ) ≥ n_ℓ`
  have hy1 : 1 ≤ g.ratio (ℓ - 1) ^ 2 := one_le_pow₀ (g.one_le_ratio _)
  have hyb0 : 0 < yb := by linarith
  have hlogN : 2 * yb * Real.log (HY.count h (g.t ℓ) a) ≤
      γ ℓ * (ε ^ 2 / 8) * HY.count h (g.t ℓ) a := by
    rw [hcnt]
    have := mul_log_le_mul_of_le (C := 16 * yb) (D := γ ℓ * ε ^ 2) (by positivity) he hnl hc
    linarith
  -- `a ≠ ĉ_(ℓ-1)` on the history `h`
  have hne' : a ≠ HY.leader w₀ h (g.t (ℓ - 1)) := by
    rw [hh, HY.leader_history hrr]
    exact hne
  have hold' : HY.testKinf w₀ h (g.t (ℓ - 1)) (g.netSize β (ℓ - 1)) a ≤
      ENNReal.ofReal (Δ * (1 + 3 * γ ℓ / 32)) := by
    rw [hh, HY.testKinf_history hrr]
    exact hold
  have hres := HY.ofReal_mul_threshold_le_count_mul_testKinf (L := g.logEnd ℓ)
      (y' := g.ratio (ℓ - 1) ^ 2) (yb := yb)
    (g.logEnd_pos (by omega)).le (by linarith) hyb hγ0 hγ hΔ hε hne' hKnew8 hb hlogN hold' hnew
  rw [hcnt] at hres
  exact hres

/-! ### Lemma `lem:amb`, Step 7: the series over the activated batches -/

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- [INC-P000, proof of Lemma `lem:amb`, Step 7, the series] On every grid, with the default `ϑ`,
let `f ≥ 0` on `[1, ∞)` be bounded on `[1, ∞)` and eventually at most `C y^(-2)`. Then the sums
`∑_(ℓ ∈ S) f(L_ℓ)` over the finite sets `S` of activated batches with `t_ℓ ≥ e^e` are bounded
uniformly in `S`. This is the finiteness of the paper's `C₄(ε)`. -/
lemma Grid.exists_sum_activated_le {K' : ℕ} (g : Grid K') {f : ℝ → ℝ}
    (hf0 : ∀ y, 1 ≤ y → 0 ≤ f y) {F : ℝ} (hF : ∀ y, 1 ≤ y → f y ≤ F) {C y₀ : ℝ}
    (hC : ∀ y, y₀ ≤ y → f y ≤ C * y ^ (-2 : ℝ)) :
    ∃ B, ∀ S : Finset ℕ, (∀ ℓ ∈ S, g.imedEnd g.hyTheta ℓ < g.t (ℓ + 1) ∧
      Real.exp (Real.exp 1) ≤ (g.t ℓ : ℝ)) → ∑ ℓ ∈ S, f (g.logEnd ℓ) ≤ B := by
  -- By Lemma `lem:sparse` (`Grid.sum_activated_le`) the sum is at most `∑_k (k + 1) M_k`, with
  -- `M_k = F` on the first blocks and `M_k = C 4^(-k)` on the others, and
  -- `(k + 1) 4^(-k) ≤ 2^(-k)`.
  obtain ⟨k₀, hk₀⟩ := pow_unbounded_of_one_lt y₀ (show (1 : ℝ) < 2 by norm_num)
  set F' := max F 0 with hF'
  set C' := max C 0 with hC'
  refine ⟨(k₀ + 1 : ℝ) ^ 2 * F' + 4 * C', fun S hS ↦ ?_⟩
  -- a block bound `κ` for `S`
  obtain ⟨κ, hκ⟩ : ∃ κ : ℕ, ∀ ℓ ∈ S, g.logEnd ℓ < 2 ^ κ := by
    obtain ⟨κ, hκ⟩ := pow_unbounded_of_one_lt (∑ ℓ ∈ S, |g.logEnd ℓ|) (show (1 : ℝ) < 2 by norm_num)
    refine ⟨κ, fun ℓ hℓ ↦ lt_of_le_of_lt ?_ hκ⟩
    exact (le_abs_self _).trans (Finset.single_le_sum (fun i _ ↦ abs_nonneg (g.logEnd i)) hℓ)
  set M : ℕ → ℝ := fun k ↦ if k₀ ≤ k then C' * (1 / 4 : ℝ) ^ k else F' with hM
  have hMb : ∀ k, ∀ y, (2 : ℝ) ^ k ≤ y → y < 2 ^ (k + 1) → f y ≤ M k := by
    intro k y hy1 _
    have hy1' : (1 : ℝ) ≤ y := (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)).trans hy1
    simp only [hM]
    split_ifs with hk
    · have hy0 : y₀ ≤ y := hk₀.le.trans ((pow_le_pow_right₀ (by norm_num) hk).trans hy1)
      refine (hC y hy0).trans ?_
      have hypos : 0 < y := by linarith
      have h1 : y ^ (-2 : ℝ) ≤ (1 / 4 : ℝ) ^ k := by
        have h2 : y ^ (-2 : ℝ) = (y ^ 2)⁻¹ := by
          rw [Real.rpow_neg hypos.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        rw [h2, one_div, inv_pow, inv_le_inv₀ (by positivity) (by positivity)]
        calc (4 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
          _ ≤ y ^ 2 := by gcongr
      have hy2 : 0 ≤ y ^ (-2 : ℝ) := Real.rpow_nonneg hypos.le _
      calc C * y ^ (-2 : ℝ) ≤ C' * y ^ (-2 : ℝ) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hy2
        _ ≤ C' * (1 / 4 : ℝ) ^ k := mul_le_mul_of_nonneg_left h1 (le_max_right _ _)
    · exact (hF y hy1').trans (le_max_left _ _)
  have hsum := g.sum_activated_le (κ := κ) S (fun ℓ hℓ ↦ ⟨(hS ℓ hℓ).1, (hS ℓ hℓ).2, hκ ℓ hℓ⟩)
    hf0 hMb
  refine hsum.trans ?_
  -- the two parts of the series
  have hsplit : ∀ k : ℕ, ((k : ℝ) + 1) * M k ≤
      (if k < k₀ then ((k₀ : ℝ) + 1) * F' else 0) + 2 * C' * (1 / 2 : ℝ) ^ k := by
    intro k
    have hF0 : 0 ≤ F' := le_max_right _ _
    have hC0 : 0 ≤ C' := le_max_right _ _
    simp only [hM]
    split_ifs with h1 h2 h2
    · omega
    · -- `(k + 1) 4^(-k) ≤ 2^(-k) ≤ 2 · 2^(-k)`
      have hk2 : ((k : ℝ) + 1) ≤ 2 ^ k := by
        have : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
        exact_mod_cast this
      have : ((k : ℝ) + 1) * (1 / 4 : ℝ) ^ k ≤ (1 / 2 : ℝ) ^ k := by
        calc ((k : ℝ) + 1) * (1 / 4 : ℝ) ^ k ≤ 2 ^ k * (1 / 4 : ℝ) ^ k := by gcongr
          _ = (1 / 2 : ℝ) ^ k := by rw [← mul_pow]; norm_num
      have h4 : 0 ≤ (1 / 2 : ℝ) ^ k := by positivity
      nlinarith
    · have hk : (k : ℝ) + 1 ≤ k₀ + 1 := by exact_mod_cast Nat.succ_le_succ (by omega : k ≤ k₀)
      have : 0 ≤ 2 * C' * (1 / 2 : ℝ) ^ k := by positivity
      nlinarith
    · omega
  refine (Finset.sum_le_sum fun k _ ↦ hsplit k).trans ?_
  rw [Finset.sum_add_distrib]
  have h1 : ∑ k ∈ Finset.Ico 1 κ, (if k < k₀ then ((k₀ : ℝ) + 1) * F' else 0) ≤
      ((k₀ : ℝ) + 1) ^ 2 * F' := by
    rw [← Finset.sum_filter]
    have hF0 : 0 ≤ F' := le_max_right _ _
    calc ∑ k ∈ (Finset.Ico 1 κ).filter (· < k₀), ((k₀ : ℝ) + 1) * F'
        = (((Finset.Ico 1 κ).filter (· < k₀)).card : ℝ) * (((k₀ : ℝ) + 1) * F') := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((k₀ : ℝ) + 1) * (((k₀ : ℝ) + 1) * F') := by
          gcongr
          have : ((Finset.Ico 1 κ).filter (· < k₀)).card ≤ k₀ + 1 := by
            refine (Finset.card_le_card fun k hk ↦ ?_).trans (Finset.card_range (k₀ + 1)).le
            exact Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hk).2; omega)
          exact_mod_cast this
      _ = ((k₀ : ℝ) + 1) ^ 2 * F' := by ring
  have h2 : ∑ k ∈ Finset.Ico 1 κ, 2 * C' * (1 / 2 : ℝ) ^ k ≤ 4 * C' := by
    rw [← Finset.mul_sum]
    have hC0 : 0 ≤ 2 * C' := by have := le_max_right C 0; positivity
    have hs := sum_le_hasSum (Finset.Ico 1 κ) (fun k _ ↦ by positivity) hasSum_geometric_two
    nlinarith
  linarith

end Incognita.BatchedBandits
