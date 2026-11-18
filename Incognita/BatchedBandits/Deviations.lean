/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.DualGrid
public import Mathlib.Probability.Moments.Basic

/-! # Deviations of `n 𝒦_inf` with a gain

[INC-P000, Lemmas `lem:single` and `lem:pair`]. Let `Y_0, Y_1, …` be independent with values in
`[0, 1]` and a common mean `m` (the paper's i.i.d. stack of an arm, law `ν`), `r ∈ [0, 1)` a level
and
`F(λ) = ∑_{i < n} log (1 - λ (Y_i - r))`, so that `n 𝒦_inf(ν̂_n, r) = sup_{λ ∈ [0, 1/(1-r))} F(λ)`.

* `measureReal_le_sum_log_le`: the Chernoff bound at one `λ ∈ [0, 1/(1-r))` with the power
  `s = 1 + 2η`: `P(F(λ) ≥ w) ≤ e^(-s w)` when `2 η r ≤ m - r`.
* `measure_exists_le_sum_log_le`: Lemma `lem:single`,
  `P(n 𝒦_inf(ν̂_n, r) ≥ z) ≤ k_n e^(2s) e^(-s z)`, for the event "some `λ ∈ [0, 1/(1-r))` has
  `F(λ) ≥ z - 1`", which contains `{n 𝒦_inf(ν̂_n, r) ≥ z}` for every `z`; and
  `measure_exists_le_sum_log_le'`, the bound `(4 + 2 κ(r)) e^(2s) n² e^(-s z)`.
* `integral_exp_mul_log_add_le_one`, `measure_exists_le_sum_log_le_and_le_sum`: Lemma `lem:pair`,
  `P(n 𝒦_inf(ν̂_n, r) ≥ z, S_(n') ≥ n' q) ≤ k_n e^(2s) e^(-s z)` under the moment conditions on
  `Φ_ν(θ, q)` and `Ψ_ν(θ, q)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open Real (exp)

namespace Incognita.BatchedBandits

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {Y : ℕ → Ω → ℝ} {m : ℝ}

/-- **One factor** [INC-P000, proof of Lemma `lem:single`, Step 2]: for `Y ∈ [0, 1]` of mean `m`,
`λ ∈ [0, 1/(1-r))`, `η ≥ 0` and `2 η r ≤ m - r`, `E[(1 - λ (Y - r))^(1+2η)] ≤ 1`, written with
`exp ((1 + 2η) log (1 - λ (Y - r)))`. -/
lemma integral_exp_mul_log_le_one {X : Ω → ℝ} (hXm : Measurable X)
    (hb : ∀ᵐ ω ∂P, X ω ∈ Set.Icc (0 : ℝ) 1) (hmean : P[X] = m) {r lam η : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam * (1 - r) < 1) (hη : 0 ≤ η) (hηr : 2 * η * r ≤ m - r) :
    ∫ ω, exp ((1 + 2 * η) * Real.log (1 - lam * (X ω - r))) ∂P ≤ 1 := by
  have hXi : Integrable X P := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hXm.aestronglyMeasurable ?_
    filter_upwards [hb] with ω hω
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hω.1, hω.2]
  -- pointwise: `y^(1+2η) ≤ e^(2ηλr) y`
  have hpt : ∀ᵐ ω ∂P, exp ((1 + 2 * η) * Real.log (1 - lam * (X ω - r))) ≤
      exp (2 * η * (lam * r)) * (1 - lam * (X ω - r)) := by
    filter_upwards [hb] with ω hω
    have hy := HY.one_sub_mul_pos hlam0 hlam1 hω.2
    rw [add_mul, one_mul, Real.exp_add, Real.exp_log hy, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ hy.le
    refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ (by linarith))
    have := Real.log_le_sub_one_of_pos hy
    nlinarith [hω.1]
  have hint2 : Integrable (fun ω ↦ exp (2 * η * (lam * r)) * (1 - lam * (X ω - r))) P :=
    ((integrable_const 1).sub ((hXi.sub (integrable_const r)).const_mul lam)).const_mul _
  have hint1 : Integrable (fun ω ↦ exp ((1 + 2 * η) * Real.log (1 - lam * (X ω - r)))) P := by
    refine Integrable.mono' hint2 (by fun_prop :
      Measurable fun ω ↦ exp ((1 + 2 * η) * Real.log (1 - lam * (X ω - r)))).aestronglyMeasurable
      ?_
    filter_upwards [hpt] with ω hω
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hω
  calc _ ≤ ∫ ω, exp (2 * η * (lam * r)) * (1 - lam * (X ω - r)) ∂P :=
        integral_mono_ae hint1 hint2 hpt
    _ = exp (2 * η * (lam * r)) * (1 - lam * (m - r)) := by
        have hfun : (fun ω ↦ 1 - lam * (X ω - r)) = fun ω ↦ (1 + lam * r) - lam * X ω := by
          funext ω
          ring
        rw [integral_const_mul, hfun, integral_sub (integrable_const _) (hXi.const_mul lam),
          integral_const, integral_const_mul, hmean]
        simp only [probReal_univ, smul_eq_mul, one_mul]
        ring
    _ ≤ exp (2 * η * (lam * r)) * exp (-(lam * (m - r))) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        have := Real.add_one_le_exp (-(lam * (m - r)))
        linarith
    _ = exp (lam * (2 * η * r - (m - r))) := by rw [← Real.exp_add]; ring_nf
    _ ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hlam0 (by linarith))

/-- **Chernoff at one point** [INC-P000, proof of Lemma `lem:single`, Steps 2–3]: for independent
`Y_i ∈ [0, 1]` of common mean `m`, `λ ∈ [0, 1/(1-r))`, `η ≥ 0` with `2 η r ≤ m - r`,
every `n` and every `w`, `P(∑_{i < n} log (1 - λ (Y_i - r)) ≥ w) ≤ e^(-(1+2η) w)`. -/
lemma measureReal_le_sum_log_le (hind : iIndepFun Y P) (hmeas : ∀ i, Measurable (Y i))
    (hb : ∀ i, ∀ᵐ ω ∂P, Y i ω ∈ Set.Icc (0 : ℝ) 1) (hmean : ∀ i, P[Y i] = m) {r lam η : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam * (1 - r) < 1) (hη : 0 ≤ η)
    (hηr : 2 * η * r ≤ m - r) (n : ℕ) (w : ℝ) :
    P.real {ω | w ≤ ∑ i ∈ range n, Real.log (1 - lam * (Y i ω - r))} ≤
      exp (-(1 + 2 * η) * w) := by
  set X : ℕ → Ω → ℝ := fun i ω ↦ Real.log (1 - lam * (Y i ω - r)) with hX
  have hXm : ∀ i, Measurable (X i) := fun i ↦ by
    have := hmeas i
    simp only [hX]
    fun_prop
  have hXind : iIndepFun X P :=
    hind.comp (g := fun _ y ↦ Real.log (1 - lam * (y - r))) fun _ ↦ by fun_prop
  have hfun : (fun ω ↦ ∑ i ∈ range n, X i ω) = ∑ i ∈ range n, X i := by
    ext ω
    simp
  -- integrability of `exp (s ∑ X_i)`: it is bounded almost surely
  have hint : Integrable (fun ω ↦ exp ((1 + 2 * η) * ∑ i ∈ range n, X i ω)) P := by
    refine Integrable.mono' (integrable_const (exp ((1 + 2 * η) * (n * (lam * r))))) (by fun_prop)
      ?_
    filter_upwards [ae_all_iff.2 hb] with ω hω
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_exp]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    calc ∑ i ∈ range n, X i ω ≤ ∑ _i ∈ range n, lam * r := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          have hy := HY.one_sub_mul_pos hlam0 hlam1 (hω i).2
          have := Real.log_le_sub_one_of_pos hy
          simp only [hX]
          nlinarith [(hω i).1]
      _ = n * (lam * r) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hch := measure_ge_le_exp_mul_mgf (X := fun ω ↦ ∑ i ∈ range n, X i ω) (μ := P) w
    (t := 1 + 2 * η) (by linarith) hint
  rw [hfun, hXind.mgf_sum hXm] at hch
  refine hch.trans ?_
  calc exp (-(1 + 2 * η) * w) * ∏ i ∈ range n, mgf (X i) P (1 + 2 * η)
      ≤ exp (-(1 + 2 * η) * w) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        refine Finset.prod_le_one₀ (fun i _ ↦ mgf_nonneg) fun i _ ↦ ?_
        exact integral_exp_mul_log_le_one (hmeas i) (hb i) (hmean i) hlam0 hlam1 hη hηr
    _ = _ := mul_one _

/-- [INC-P000, Lemma `lem:single`] For independent `Y_i ∈ [0, 1]` of common mean `m`,
`0 ≤ r < m`, `η ≥ 0` with `2 η r ≤ m - r`, `n ≥ 1` and every `z`, with `s = 1 + 2η`,
`P(n 𝒦_inf(ν̂_n, r) ≥ z) ≤ k_n e^(2s) e^(-s z)`. The event is written "some
`λ ∈ [0, 1/(1-r))` has `F(λ) ≥ z - 1`", which contains `{n 𝒦_inf(ν̂_n, r) ≥ z}`; the paper's
`r < m` is implied by `2 η r ≤ m - r` when `η > 0`, and only `r < 1` is used. -/
lemma measure_exists_le_sum_log_le (hind : iIndepFun Y P) (hmeas : ∀ i, Measurable (Y i))
    (hb : ∀ i, ∀ᵐ ω ∂P, Y i ω ∈ Set.Icc (0 : ℝ) 1) (hmean : ∀ i, P[Y i] = m) {r η : ℝ}
    (hr0 : 0 ≤ r) (hr : r < 1) (hη : 0 ≤ η) (hηr : 2 * η * r ≤ m - r) {n : ℕ} (hn : 1 ≤ n)
    (z : ℝ) :
    P {ω | ∃ lam, 0 ≤ lam ∧ lam * (1 - r) < 1 ∧
        z - 1 ≤ ∑ i ∈ range n, Real.log (1 - lam * (Y i ω - r))} ≤
      ENNReal.ofReal ((⌈2 * n * Real.log (n / (1 - r))⌉₊ + 1 : ℕ) *
        exp (2 * (1 + 2 * η)) * exp (-(1 + 2 * η) * z)) := by
  set kn := ⌈2 * n * Real.log (n / (1 - r))⌉₊ + 1 with hkn
  set s := 1 + 2 * η with hs
  have hs0 : 0 < s := by rw [hs]; linarith
  rcases lt_or_ge z 2 with hz | hz
  · -- the bound is at least `1`
    refine prob_le_one.trans ?_
    rw [ENNReal.one_le_ofReal]
    have hk1 : (1 : ℝ) ≤ kn := by exact_mod_cast (show 1 ≤ kn by omega)
    have he : 1 ≤ exp (2 * s) * exp (-s * z) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp_iff.mpr (by nlinarith)
    have : 0 ≤ exp (2 * s) * exp (-s * z) := by positivity
    nlinarith
  -- the grid points
  set grid : ℕ → ℝ := fun k ↦ (1 - 1 / (2 * n : ℝ)) ^ k / (1 - r) with hgrid
  have hsub : {ω | ∃ lam, 0 ≤ lam ∧ lam * (1 - r) < 1 ∧
      z - 1 ≤ ∑ i ∈ range n, Real.log (1 - lam * (Y i ω - r))} ≤ᵐ[P]
      ⋃ k ∈ Finset.Icc 1 kn,
        {ω | z - 2 ≤ ∑ i ∈ range n, Real.log (1 - grid k * (Y i ω - r))} := by
    filter_upwards [ae_all_iff.2 hb] with ω hω
    rintro ⟨lam, hlam0, hlam1, hF⟩
    obtain ⟨k, hk1, hkle, hk⟩ := exists_grid_le_sum_log hn (y := fun i ↦ Y i ω)
      (fun i _ ↦ hω i) hr0 hr (z' := z - 1) (by linarith) hlam0 hlam1 hF
    simp only [Set.mem_iUnion, Finset.mem_Icc, Set.mem_ofPred_eq]
    exact ⟨k, ⟨hk1, hkle⟩, by linarith⟩
  refine (measure_mono_ae hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  have hterm : ∀ k ∈ Finset.Icc 1 kn,
      P {ω | z - 2 ≤ ∑ i ∈ range n, Real.log (1 - grid k * (Y i ω - r))} ≤
        ENNReal.ofReal (exp (2 * s) * exp (-s * z)) := by
    intro k hk
    obtain ⟨hg0, hg1⟩ := grid_mem hn hr (Finset.mem_Icc.mp hk).1
    rw [← ofReal_measureReal]
    refine ENNReal.ofReal_le_ofReal ((measureReal_le_sum_log_le hind hmeas hb hmean hg0 hg1
      hη hηr n (z - 2)).trans_eq ?_)
    rw [← Real.exp_add, hs]
    ring_nf
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, show kn + 1 - 1 = kn by omega,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  exact le_of_eq (by ring_nf)

/-- [INC-P000, Lemma `lem:single`, second bound] Under the hypotheses of
`measure_exists_le_sum_log_le`, the probability is at most
`(4 + 2 κ(r)) e^(2s) n² e^(-s z)`, `κ(r) = log (1/(1-r))`. -/
lemma measure_exists_le_sum_log_le' (hind : iIndepFun Y P) (hmeas : ∀ i, Measurable (Y i))
    (hb : ∀ i, ∀ᵐ ω ∂P, Y i ω ∈ Set.Icc (0 : ℝ) 1) (hmean : ∀ i, P[Y i] = m) {r η : ℝ}
    (hr0 : 0 ≤ r) (hr : r < 1) (hη : 0 ≤ η) (hηr : 2 * η * r ≤ m - r) {n : ℕ} (hn : 1 ≤ n)
    (z : ℝ) :
    P {ω | ∃ lam, 0 ≤ lam ∧ lam * (1 - r) < 1 ∧
        z - 1 ≤ ∑ i ∈ range n, Real.log (1 - lam * (Y i ω - r))} ≤
      ENNReal.ofReal ((4 + 2 * Real.log (1 / (1 - r))) * exp (2 * (1 + 2 * η)) * n ^ 2 *
        exp (-(1 + 2 * η) * z)) := by
  refine (measure_exists_le_sum_log_le hind hmeas hb hmean hr0 hr hη hηr hn z).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have h := gridSize_le hn hr0 hr
  have he : 0 ≤ exp (2 * (1 + 2 * η)) * exp (-(1 + 2 * η) * z) := by positivity
  calc ((⌈2 * n * Real.log (n / (1 - r))⌉₊ + 1 : ℕ) : ℝ) * exp (2 * (1 + 2 * η)) *
        exp (-(1 + 2 * η) * z)
      = ((⌈2 * n * Real.log (n / (1 - r))⌉₊ + 1 : ℕ) : ℝ) *
        (exp (2 * (1 + 2 * η)) * exp (-(1 + 2 * η) * z)) := by ring
    _ ≤ (4 + 2 * Real.log (1 / (1 - r))) * n ^ 2 *
        (exp (2 * (1 + 2 * η)) * exp (-(1 + 2 * η) * z)) := mul_le_mul_of_nonneg_right h he
    _ = _ := by ring

/-! ### Lemma `lem:pair` -/

/-- **The factor `A`** [INC-P000, proof of Lemma `lem:pair`, Step 3]: for `Y ∈ [0, 1]`,
`λ ∈ [0, 1/(1-r))`, `y = 1 - λ (Y - r)`, `s = 1 + 2η` and the moments
`Φ = E[e^(θ(Y-q))]`, `Ψ = E[(1 - Y) e^(θ(Y-q))]` with `e^(2ηκ(r)) Φ ≤ 1` and
`e^(2ηκ(r)) Ψ ≤ 1 - r`, `E[y^s e^(θ(Y-q))] ≤ 1`. -/
lemma integral_exp_mul_log_add_le_one {X : Ω → ℝ} (hXm : Measurable X)
    (hb : ∀ᵐ ω ∂P, X ω ∈ Set.Icc (0 : ℝ) 1) {r q θ η lam : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hη : 0 ≤ η)
    (hlam0 : 0 ≤ lam) (hlam1 : lam * (1 - r) < 1)
    (hΦ : exp (2 * η * Real.log (1 / (1 - r))) * ∫ ω, exp (θ * (X ω - q)) ∂P ≤ 1)
    (hΨ : exp (2 * η * Real.log (1 / (1 - r))) * ∫ ω, (1 - X ω) * exp (θ * (X ω - q)) ∂P ≤
      1 - r) :
    ∫ ω, exp ((1 + 2 * η) * Real.log (1 - lam * (X ω - r)) + θ * (X ω - q)) ∂P ≤ 1 := by
  set κ := Real.log (1 / (1 - r)) with hκ
  have h1r : 0 < 1 - r := by linarith
  have hbd : ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 → |θ * (x - q)| ≤ |θ| * (1 + |q|) := by
    intro x hx
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg θ)
    have : |x - q| ≤ |x| + |q| := abs_sub _ _
    have : |x| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
    linarith
  have hE : Integrable (fun ω ↦ exp (θ * (X ω - q))) P := by
    refine Integrable.mono' (integrable_const (exp (|θ| * (1 + |q|))))
      (by fun_prop : Measurable fun ω ↦ exp (θ * (X ω - q))).aestronglyMeasurable ?_
    filter_upwards [hb] with ω hω
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_exp]
    exact (le_abs_self _).trans (hbd _ hω)
  have hE' : Integrable (fun ω ↦ (1 - X ω) * exp (θ * (X ω - q))) P := by
    refine Integrable.mono' hE (by fun_prop : Measurable fun ω ↦
      (1 - X ω) * exp (θ * (X ω - q))).aestronglyMeasurable ?_
    filter_upwards [hb] with ω hω
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
    have : |1 - X ω| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hω.1, hω.2]
    nlinarith [Real.exp_pos (θ * (X ω - q))]
  -- pointwise: `y^s e^(θ(Y-q)) ≤ e^(2ηκ) ((1 - λ(1-r)) e^(θ(Y-q)) + λ (1 - Y) e^(θ(Y-q)))`
  have hpt : ∀ᵐ ω ∂P, exp ((1 + 2 * η) * Real.log (1 - lam * (X ω - r)) + θ * (X ω - q)) ≤
      exp (2 * η * κ) * ((1 - lam * (1 - r)) * exp (θ * (X ω - q)) +
        lam * ((1 - X ω) * exp (θ * (X ω - q)))) := by
    filter_upwards [hb] with ω hω
    have hy := HY.one_sub_mul_pos hlam0 hlam1 hω.2
    have hyκ : Real.log (1 - lam * (X ω - r)) ≤ κ := by
      rw [hκ]
      refine Real.log_le_log hy ?_
      rw [le_div_iff₀ h1r]
      nlinarith [hω.1, mul_le_mul_of_nonneg_left hlam1.le hr0, mul_nonneg hlam0 hω.1]
    rw [add_mul, one_mul, Real.exp_add, Real.exp_add, Real.exp_log hy]
    have hsplit : (1 - lam * (1 - r)) * exp (θ * (X ω - q)) +
        lam * ((1 - X ω) * exp (θ * (X ω - q))) =
        (1 - lam * (X ω - r)) * exp (θ * (X ω - q)) := by ring
    rw [hsplit]
    have h2 : exp (2 * η * Real.log (1 - lam * (X ω - r))) ≤ exp (2 * η * κ) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hyκ (by linarith))
    have := Real.exp_pos (θ * (X ω - q))
    calc (1 - lam * (X ω - r)) * exp (2 * η * Real.log (1 - lam * (X ω - r))) *
          exp (θ * (X ω - q))
        = exp (2 * η * Real.log (1 - lam * (X ω - r))) *
          ((1 - lam * (X ω - r)) * exp (θ * (X ω - q))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 (by positivity)
  have hint2 : Integrable (fun ω ↦ exp (2 * η * κ) * ((1 - lam * (1 - r)) *
      exp (θ * (X ω - q)) + lam * ((1 - X ω) * exp (θ * (X ω - q))))) P :=
    ((hE.const_mul _).add (hE'.const_mul _)).const_mul _
  have hint1 : Integrable
      (fun ω ↦ exp ((1 + 2 * η) * Real.log (1 - lam * (X ω - r)) + θ * (X ω - q))) P := by
    refine Integrable.mono' hint2 (by fun_prop : Measurable fun ω ↦
      exp ((1 + 2 * η) * Real.log (1 - lam * (X ω - r)) + θ * (X ω - q))).aestronglyMeasurable ?_
    filter_upwards [hpt] with ω hω
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hω
  have hc : 0 ≤ 1 - lam * (1 - r) := by linarith
  calc _ ≤ _ := integral_mono_ae hint1 hint2 hpt
    _ = (1 - lam * (1 - r)) * (exp (2 * η * κ) * ∫ ω, exp (θ * (X ω - q)) ∂P) +
        lam * (exp (2 * η * κ) * ∫ ω, (1 - X ω) * exp (θ * (X ω - q)) ∂P) := by
        rw [integral_const_mul, integral_add (hE.const_mul _) (hE'.const_mul _),
          integral_const_mul, integral_const_mul]
        ring
    _ ≤ (1 - lam * (1 - r)) * 1 + lam * (1 - r) := by
        gcongr
    _ = 1 := by ring

/-- [INC-P000, Lemma `lem:pair`] For independent `Y_i ∈ [0, 1]`, `0 ≤ r < 1`, `q ∈ ℝ`,
`θ ≥ 0`, `η ≥ 0` with `e^(2ηκ(r)) Φ_i(θ, q) ≤ 1` and `e^(2ηκ(r)) Ψ_i(θ, q) ≤ 1 - r` for every `i`
(`Φ_i(θ, q) = E[e^(θ(Y_i - q))]`, `Ψ_i(θ, q) = E[(1 - Y_i) e^(θ(Y_i - q))]`, the paper's `Φ_ν`,
`Ψ_ν` for an i.i.d. stack), `1 ≤ n ≤ n'` and every `z`, with `s = 1 + 2η`,
`P(n 𝒦_inf(ν̂_n, r) ≥ z, S_(n') ≥ n' q) ≤ k_n e^(2s) e^(-s z)`, the first event written as in
`measure_exists_le_sum_log_le`. -/
lemma measure_exists_le_sum_log_le_and_le_sum (hind : iIndepFun Y P)
    (hmeas : ∀ i, Measurable (Y i)) (hb : ∀ i, ∀ᵐ ω ∂P, Y i ω ∈ Set.Icc (0 : ℝ) 1)
    {r q θ η : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (hθ : 0 ≤ θ) (hη : 0 ≤ η)
    (hΦ : ∀ i, exp (2 * η * Real.log (1 / (1 - r))) * ∫ ω, exp (θ * (Y i ω - q)) ∂P ≤ 1)
    (hΨ : ∀ i, exp (2 * η * Real.log (1 / (1 - r))) *
      ∫ ω, (1 - Y i ω) * exp (θ * (Y i ω - q)) ∂P ≤ 1 - r)
    {n n' : ℕ} (hn : 1 ≤ n) (hnn' : n ≤ n') (z : ℝ) :
    P {ω | (∃ lam, 0 ≤ lam ∧ lam * (1 - r) < 1 ∧
        z - 1 ≤ ∑ i ∈ range n, Real.log (1 - lam * (Y i ω - r))) ∧
        n' * q ≤ ∑ i ∈ range n', Y i ω} ≤
      ENNReal.ofReal ((⌈2 * n * Real.log (n / (1 - r))⌉₊ + 1 : ℕ) *
        exp (2 * (1 + 2 * η)) * exp (-(1 + 2 * η) * z)) := by
  set kn := ⌈2 * n * Real.log (n / (1 - r))⌉₊ + 1 with hkn
  set s := 1 + 2 * η with hs
  have hs0 : 0 < s := by rw [hs]; linarith
  have h1r : 0 < 1 - r := by linarith
  have hκ0 : 0 ≤ Real.log (1 / (1 - r)) := Real.log_nonneg (by rw [le_div_iff₀ h1r]; linarith)
  rcases lt_or_ge z 2 with hz | hz
  · refine prob_le_one.trans ?_
    rw [ENNReal.one_le_ofReal]
    have hk1 : (1 : ℝ) ≤ kn := by exact_mod_cast (show 1 ≤ kn by omega)
    have he : 1 ≤ exp (2 * s) * exp (-s * z) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp_iff.mpr (by nlinarith)
    have : 0 ≤ exp (2 * s) * exp (-s * z) := by positivity
    nlinarith
  set grid : ℕ → ℝ := fun k ↦ (1 - 1 / (2 * n : ℝ)) ^ k / (1 - r) with hgrid
  -- one grid point: Chernoff for `∑_{i < n'} V_i`, `V_i = s log y_i 1(i < n) + θ (Y_i - q)`
  have hpoint : ∀ lam, 0 ≤ lam → lam * (1 - r) < 1 →
      P {ω | z - 2 ≤ ∑ i ∈ range n, Real.log (1 - lam * (Y i ω - r)) ∧
        n' * q ≤ ∑ i ∈ range n', Y i ω} ≤ ENNReal.ofReal (exp (2 * s) * exp (-s * z)) := by
    intro lam hlam0 hlam1
    set V : ℕ → Ω → ℝ := fun i ω ↦ (if i < n then s * Real.log (1 - lam * (Y i ω - r)) else 0) +
      θ * (Y i ω - q) with hV
    have hVm : ∀ i, Measurable (V i) := fun i ↦ by
      have := hmeas i
      simp only [hV]
      split_ifs <;> fun_prop
    have hVind : iIndepFun V P :=
      hind.comp (g := fun i y ↦ (if i < n then s * Real.log (1 - lam * (y - r)) else 0) +
        θ * (y - q)) fun i ↦ by split_ifs <;> fun_prop
    have hfun : (fun ω ↦ ∑ i ∈ range n', V i ω) = ∑ i ∈ range n', V i := by
      ext ω
      simp
    have hint : Integrable (fun ω ↦ exp (1 * ∑ i ∈ range n', V i ω)) P := by
      refine Integrable.mono' (integrable_const
        (exp (n' * (s * (lam * r) + θ * (1 + |q|))))) (by fun_prop) ?_
      filter_upwards [ae_all_iff.2 hb] with ω hω
      rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_exp, one_mul]
      calc ∑ i ∈ range n', V i ω ≤ ∑ _i ∈ range n', (s * (lam * r) + θ * (1 + |q|)) := by
            refine Finset.sum_le_sum fun i _ ↦ ?_
            simp only [hV]
            have hθq : θ * (Y i ω - q) ≤ θ * (1 + |q|) := by
              refine mul_le_mul_of_nonneg_left ?_ hθ
              have := neg_abs_le q
              linarith [(hω i).2]
            have h1 : (if i < n then s * Real.log (1 - lam * (Y i ω - r)) else 0) ≤
                s * (lam * r) := by
              split_ifs
              · have hy := HY.one_sub_mul_pos hlam0 hlam1 (hω i).2
                have := Real.log_le_sub_one_of_pos hy
                refine mul_le_mul_of_nonneg_left ?_ hs0.le
                nlinarith [(hω i).1]
              · exact mul_nonneg hs0.le (mul_nonneg hlam0 hr0)
            linarith
        _ = n' * (s * (lam * r) + θ * (1 + |q|)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hch := measure_ge_le_exp_mul_mgf (X := fun ω ↦ ∑ i ∈ range n', V i ω) (μ := P)
      (s * (z - 2)) (t := 1) zero_le_one hint
    rw [hfun, hVind.mgf_sum hVm] at hch
    have hprod : ∏ i ∈ range n', mgf (V i) P 1 ≤ 1 := by
      refine Finset.prod_le_one₀ (fun i _ ↦ mgf_nonneg) fun i _ ↦ ?_
      simp only [mgf, one_mul, hV]
      split_ifs with hin
      · exact integral_exp_mul_log_add_le_one (hmeas i) (hb i) hr0 hr hη hlam0 hlam1 (hΦ i)
          (hΨ i)
      · simp only [zero_add]
        have : exp (2 * η * Real.log (1 / (1 - r))) ≥ 1 :=
          Real.one_le_exp_iff.mpr (mul_nonneg (by linarith) hκ0)
        have hI : 0 ≤ ∫ ω, exp (θ * (Y i ω - q)) ∂P :=
          integral_nonneg fun ω ↦ (Real.exp_pos _).le
        nlinarith [hΦ i]
    -- the event is contained in `{s (z - 2) ≤ ∑ V_i}`
    have hsub : {ω | z - 2 ≤ ∑ i ∈ range n, Real.log (1 - lam * (Y i ω - r)) ∧
        n' * q ≤ ∑ i ∈ range n', Y i ω} ⊆ {ω | s * (z - 2) ≤ ∑ i ∈ range n', V i ω} := by
      rintro ω ⟨h1, h2⟩
      simp only [Set.mem_ofPred_eq, hV]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
      have hsplit : ∑ i ∈ range n', (if i < n then s * Real.log (1 - lam * (Y i ω - r)) else 0) =
          s * ∑ i ∈ range n, Real.log (1 - lam * (Y i ω - r)) := by
        rw [← Finset.sum_range_add_sum_Ico _ hnn', Finset.mul_sum]
        have h0 : ∑ i ∈ Finset.Ico n n',
            (if i < n then s * Real.log (1 - lam * (Y i ω - r)) else 0) = 0 :=
          Finset.sum_eq_zero fun i hi ↦ by
            rw [ite_eq_right (not_lt.mpr (Finset.mem_Ico.mp hi).1)]
        rw [h0, add_zero]
        exact Finset.sum_congr rfl fun i hi ↦ by rw [ite_eq_left (Finset.mem_range.mp hi)]
      rw [hsplit]
      have : 0 ≤ θ * (∑ i ∈ range n', Y i ω - n' * q) :=
        mul_nonneg hθ (by linarith)
      nlinarith
    refine (measure_mono hsub).trans ?_
    rw [← ofReal_measureReal]
    refine ENNReal.ofReal_le_ofReal (hch.trans ?_)
    calc exp (-1 * (s * (z - 2))) * ∏ i ∈ range n', mgf (V i) P 1
        ≤ exp (-1 * (s * (z - 2))) * 1 :=
          mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
      _ = exp (2 * s) * exp (-s * z) := by rw [mul_one, ← Real.exp_add]; ring_nf
  -- the union bound over the grid
  have hsub : {ω | (∃ lam, 0 ≤ lam ∧ lam * (1 - r) < 1 ∧
      z - 1 ≤ ∑ i ∈ range n, Real.log (1 - lam * (Y i ω - r))) ∧
      n' * q ≤ ∑ i ∈ range n', Y i ω} ≤ᵐ[P]
      ⋃ k ∈ Finset.Icc 1 kn, {ω | z - 2 ≤ ∑ i ∈ range n, Real.log (1 - grid k * (Y i ω - r)) ∧
        n' * q ≤ ∑ i ∈ range n', Y i ω} := by
    filter_upwards [ae_all_iff.2 hb] with ω hω
    rintro ⟨⟨lam, hlam0, hlam1, hF⟩, hS⟩
    obtain ⟨k, hk1, hkle, hk⟩ := exists_grid_le_sum_log hn (y := fun i ↦ Y i ω)
      (fun i _ ↦ hω i) hr0 hr (z' := z - 1) (by linarith) hlam0 hlam1 hF
    simp only [Set.mem_iUnion, Finset.mem_Icc, Set.mem_ofPred_eq]
    exact ⟨k, ⟨hk1, hkle⟩, by linarith, hS⟩
  refine (measure_mono_ae hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  have hterm : ∀ k ∈ Finset.Icc 1 kn,
      P {ω | z - 2 ≤ ∑ i ∈ range n, Real.log (1 - grid k * (Y i ω - r)) ∧
        n' * q ≤ ∑ i ∈ range n', Y i ω} ≤ ENNReal.ofReal (exp (2 * s) * exp (-s * z)) := by
    intro k hk
    obtain ⟨hg0, hg1⟩ := grid_mem hn hr (Finset.mem_Icc.mp hk).1
    exact hpoint _ hg0 hg1
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, show kn + 1 - 1 = kn by omega,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  exact le_of_eq (by ring_nf)

end Incognita.BatchedBandits
