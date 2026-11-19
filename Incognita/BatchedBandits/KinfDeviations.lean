/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.DualGrid
public import Incognita.ForMathlib.Probability.Moments.Hoeffding

/-! # Deviations of the empirical `𝒦_inf`

[INC-P000, Lemmas `lem:lowerdev` and `lem:upperdev`]. Let `Y_0, Y_1, …` be independent with law
`ν` on `[0, 1]` (the stack of an arm), `μ ∈ [0, 1)` a level, `κ(μ) = log (1/(1-μ))`, and
`F(λ) = ∑_{k < N} log (1 - λ (Y_k - μ))`, so that `N 𝒦_inf(ν̂_N, μ) = sup_{λ ∈ [0, 1/(1-μ))} F(λ)`
and `𝒦_inf(ν, μ) = sup_λ E_ν[log (1 - λ (Y - μ))]`. For `ε' > 0` let `ϖ = e^(-ε'/4)`,
`R' = κ(μ) - log (1 - ϖ)` and `ρ' = ε'² / (2 R'²)`. These bounds are variants of those of
[CGMMS13, Section 5, Theorem 2], [HT15] and [GHMS22, Section 2.3].

* `measure_forall_sum_log_le_le`: Lemma `lem:lowerdev`, for every `λ ∈ [0, 1/(1-μ))`,
  `P(∀ λ'', F(λ'') ≤ N (E_ν[log (1 - λ (Y - μ))] - 3ε'/4)) ≤ e^(-ρ' N)`; with `λ` such that
  `E_ν[log (1 - λ(Y - μ))] ≥ 𝒦_inf(ν, μ) - ε'/4`, the event contains
  `{𝒦_inf(ν̂_N, μ) ≤ 𝒦_inf(ν, μ) - ε'}`, which is the paper's statement.
* `measure_exists_add_le_sum_log_le`: Lemma `lem:upperdev`, for an upper bound `K` of the dual
  formula of `𝒦_inf(ν, μ)`, `P(∃ λ, F(λ) ≥ n (K + 7ε'/8)) ≤ n_g e^(-ρ' n)`; the event contains
  `{𝒦_inf(ν̂_n, μ) ≥ 𝒦_inf(ν, μ) + ε'}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open Real (exp)

namespace Incognita.BatchedBandits

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {Y : ℕ → Ω → ℝ}

/-- `log (1 - λ (y - μ))` lies in `[log (1 - λ (1 - μ)), κ(μ)]` for `y ∈ [0, 1]`,
`λ ∈ [0, 1/(1-μ))`, `μ ∈ [0, 1)`. -/
lemma log_one_sub_mul_mem {lam μ y : ℝ} (hμ0 : 0 ≤ μ) (hμ : μ < 1) (hlam0 : 0 ≤ lam)
    (hlam1 : lam * (1 - μ) < 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    Real.log (1 - lam * (1 - μ)) ≤ Real.log (1 - lam * (y - μ)) ∧
      Real.log (1 - lam * (y - μ)) ≤ Real.log (1 / (1 - μ)) := by
  have h1μ : 0 < 1 - μ := by linarith
  constructor
  · refine Real.log_le_log (by linarith) ?_
    nlinarith [hy.2]
  · refine Real.log_le_log (HY.one_sub_mul_pos hlam0 hlam1 hy.2) ?_
    rw [le_div_iff₀ h1μ]
    nlinarith [hy.1, mul_nonneg (mul_nonneg hlam0 hy.1) h1μ.le,
      mul_le_mul_of_nonneg_left hlam1.le hμ0]

/-- [INC-P000, Lemma `lem:lowerdev`] For independent `Y_k` of law `ν` on `[0, 1]`, `μ ∈ [0, 1)`,
`ε' > 0`, `λ ∈ [0, 1/(1-μ))` and `N ≥ 1`, with `A = E_ν[log (1 - λ (Y - μ))]` and
`F(λ'') = ∑_{k < N} log (1 - λ'' (Y_k - μ))`,
`P(∀ λ'' ∈ [0, 1/(1-μ)), F(λ'') ≤ N (A - 3ε'/4)) ≤ exp (-ε'² N / (2 R'²))`, where
`R' = log (1/(1-μ)) - log (1 - e^(-ε'/4))`. -/
lemma measure_forall_sum_log_le_le (hind : iIndepFun Y P) (hmeas : ∀ k, Measurable (Y k))
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hlaw : ∀ k, P.map (Y k) = ν)
    (hν : ∀ᵐ y ∂ν, y ∈ Set.Icc (0 : ℝ) 1) {μ ε' lam : ℝ} (hμ0 : 0 ≤ μ) (hμ : μ < 1)
    (hε' : 0 < ε') (hlam0 : 0 ≤ lam) (hlam1 : lam * (1 - μ) < 1) {N : ℕ} (hN : 1 ≤ N) :
    P {ω | ∀ l, 0 ≤ l → l * (1 - μ) < 1 →
        ∑ k ∈ range N, Real.log (1 - l * (Y k ω - μ)) ≤
          N * (∫ y, Real.log (1 - lam * (y - μ)) ∂ν - 3 * ε' / 4)} ≤
      ENNReal.ofReal (exp (-(ε' ^ 2 / (2 * (Real.log (1 / (1 - μ)) -
        Real.log (1 - exp (-(ε' / 4)))) ^ 2) * N))) := by
  -- With `ϖ = e^(-ε'/4)`: at `λ'' = ϖ λ` the test function `g(y) = log (1 - ϖ λ (y - μ))` has
  -- values in an interval of length `R'` and mean `≥ A - ε'/4` (Lemma `lem:kinf`(vi));
  -- Hoeffding's inequality (Lemma `lem:hoeffding`(a)) for `(g(Y_k) - log (1 - ϖ)) / R' ∈ [0, 1]`
  -- concludes.
  set ϖ := exp (-(ε' / 4)) with hϖ
  have hϖ0 : 0 < ϖ := Real.exp_pos _
  have hϖ1 : ϖ < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  set κ := Real.log (1 / (1 - μ)) with hκ
  have h1μ : 0 < 1 - μ := by linarith
  have hκ0 : 0 ≤ κ := Real.log_nonneg (by rw [le_div_iff₀ h1μ]; linarith)
  set a := Real.log (1 - ϖ) with ha
  have ha0 : a < 0 := Real.log_neg (by linarith) (by linarith)
  set R := κ - a with hR
  have hR0 : 0 < R := by linarith
  set g : ℝ → ℝ := fun y ↦ Real.log (1 - ϖ * lam * (y - μ)) with hg
  have hl'0 : 0 ≤ ϖ * lam := mul_nonneg hϖ0.le hlam0
  have hl'1 : ϖ * lam * (1 - μ) < 1 := by nlinarith
  have hl'2 : ϖ * lam * (1 - μ) ≤ ϖ := by nlinarith
  -- `g` takes its values in `[a, κ]` on `[0, 1]`
  have hgmem : ∀ y ∈ Set.Icc (0 : ℝ) 1, a ≤ g y ∧ g y ≤ κ := by
    intro y hy
    obtain ⟨h1, h2⟩ := log_one_sub_mul_mem hμ0 hμ hl'0 hl'1 hy
    refine ⟨le_trans (Real.log_le_log (by linarith) (by linarith)) h1, h2⟩
  have hgm : Measurable g := by simp only [hg]; fun_prop
  -- integrability under `ν`
  have hgi : Integrable g ν := Integrable.of_mem_Icc a κ hgm.aemeasurable
    (by filter_upwards [hν] with y hy using hgmem y hy)
  have hfm : Measurable fun y : ℝ ↦ Real.log (1 - lam * (y - μ)) := by fun_prop
  have hfi : Integrable (fun y : ℝ ↦ Real.log (1 - lam * (y - μ))) ν := by
    refine Integrable.of_mem_Icc (Real.log (1 - lam * (1 - μ))) κ hfm.aemeasurable ?_
    filter_upwards [hν] with y hy
    exact log_one_sub_mul_mem hμ0 hμ hlam0 hlam1 hy
  set A := ∫ y, Real.log (1 - lam * (y - μ)) ∂ν with hA
  -- `E_ν g ≥ A - ε'/4`
  have hEg : A - ε' / 4 ≤ ∫ y, g y ∂ν := by
    have hpt : ∀ᵐ y ∂ν, Real.log ϖ + Real.log (1 - lam * (y - μ)) ≤ g y := by
      filter_upwards [hν] with y hy
      have := log_le_log_one_sub_mul hlam0 hlam1 hϖ0 hϖ1.le hy.2
      simpa [hg] using this
    have : ∫ y, (Real.log ϖ + Real.log (1 - lam * (y - μ))) ∂ν ≤ ∫ y, g y ∂ν :=
      integral_mono_ae ((integrable_const _).add hfi) hgi hpt
    rw [integral_add (integrable_const _) hfi, integral_const, probReal_univ, one_smul, hϖ,
      Real.log_exp] at this
    linarith
  -- the normalised variables
  set W : ℕ → Ω → ℝ := fun k ω ↦ (g (Y k ω) - a) / R with hW
  have hWm : ∀ k, Measurable (W k) := fun k ↦ by
    have := hmeas k
    simp only [hW]
    fun_prop
  have hWind : iIndepFun W P := hind.comp (g := fun _ y ↦ (g y - a) / R) fun _ ↦ by fun_prop
  have hYb : ∀ k, ∀ᵐ ω ∂P, Y k ω ∈ Set.Icc (0 : ℝ) 1 := fun k ↦
    ae_of_ae_map (hmeas k).aemeasurable (by rw [hlaw k]; exact hν)
  have hWb : ∀ k, ∀ᵐ ω ∂P, W k ω ∈ Set.Icc (0 : ℝ) 1 := by
    intro k
    filter_upwards [hYb k] with ω hω
    obtain ⟨h1, h2⟩ := hgmem _ hω
    simp only [hW, Set.mem_Icc]
    constructor
    · exact div_nonneg (by linarith) hR0.le
    · rw [div_le_one hR0]
      linarith
  set mW := (∫ y, g y ∂ν - a) / R with hmW
  have hWmean : ∀ k, P[W k] = mW := by
    intro k
    have : ∫ ω, W k ω ∂P = ∫ y, (g y - a) / R ∂(P.map (Y k)) := by
      rw [integral_map (hmeas k).aemeasurable (by fun_prop : Measurable fun y ↦
        (g y - a) / R).aestronglyMeasurable]
    rw [this, hlaw k, integral_div, integral_sub hgi (integrable_const a), integral_const,
      probReal_univ, one_smul]
  -- the event is contained in a lower deviation of `∑ W_k`
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set dev := N * ε' / (2 * R) with hdev
  have hsub : {ω | ∀ l, 0 ≤ l → l * (1 - μ) < 1 →
      ∑ k ∈ range N, Real.log (1 - l * (Y k ω - μ)) ≤ N * (A - 3 * ε' / 4)} ⊆
      {ω | ∑ k ∈ range N, W k ω ≤ N * mW - dev} := by
    intro ω hω
    have h := hω (ϖ * lam) hl'0 hl'1
    simp only [Set.mem_ofPred_eq]
    have hsumW : ∑ k ∈ range N, W k ω = (∑ k ∈ range N, g (Y k ω) - N * a) / R := by
      simp only [hW]
      rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
    rw [hsumW, div_le_iff₀ hR0]
    have hgsum : ∑ k ∈ range N, g (Y k ω) ≤ N * (A - 3 * ε' / 4) := by simpa [hg] using h
    have : (N * mW - dev) * R = N * (∫ y, g y ∂ν - a) - N * ε' / 2 := by
      rw [hmW, hdev]
      field_simp
    rw [this]
    nlinarith
  have hdev0 : 0 ≤ dev := by positivity
  have hhoef := measureReal_sum_range_le_sub_le hWind (fun k ↦ (hWm k).aemeasurable) hWb
    hWmean hN hdev0
  refine (measure_mono hsub).trans ?_
  rw [← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal (hhoef.trans_eq ?_)
  congr 1
  rw [hdev]
  field_simp

/-- One side of the Lipschitz bound of `log`: `log a - log b ≤ |a - b| / c` for `a > 0` and
`b ≥ c > 0`. -/
lemma log_sub_log_le_abs_div {a b c : ℝ} (ha : 0 < a) (hc : 0 < c) (hcb : c ≤ b) :
    Real.log a - Real.log b ≤ |a - b| / c := by
  have hb : 0 < b := hc.trans_le hcb
  rw [← Real.log_div ha.ne' hb.ne']
  have h1 := Real.log_le_sub_one_of_pos (div_pos ha hb)
  have h2 : a / b - 1 = (a - b) / b := by field_simp
  have h3 : (a - b) / b ≤ |a - b| / b := div_le_div_of_nonneg_right (le_abs_self _) hb.le
  have h4 : |a - b| / b ≤ |a - b| / c := div_le_div_of_nonneg_left (abs_nonneg _) hc hcb
  linarith

/-- [INC-P000, Lemma `lem:upperdev`] For independent `Y_k` of law `ν` on `[0, 1]`, `μ ∈ [0, 1)`,
`ε' > 0`, `n ≥ 1` and an upper bound `K` of the dual formula of `𝒦_inf(ν, μ)`
(`E_ν[log (1 - λ (Y - μ))] ≤ K` for every `λ ∈ [0, 1/(1-μ))`; `K = 𝒦_inf(ν, μ)` in the paper),
with `F(λ) = ∑_{k < n} log (1 - λ (Y_k - μ))`,
`P(∃ λ ∈ [0, 1/(1-μ)), F(λ) ≥ n (K + 7ε'/8)) ≤ n_g exp (-ε'² n / (2 R'²))`, where
`R' = log (1/(1-μ)) - log (1 - ϖ)`, `n_g = ⌈8 / (ε' (1 - ϖ)(1 - μ))⌉ + 1` and `ϖ = e^(-ε'/4)`;
the event contains `{𝒦_inf(ν̂_n, μ) ≥ 𝒦_inf(ν, μ) + ε'}`. -/
lemma measure_exists_add_le_sum_log_le (hind : iIndepFun Y P) (hmeas : ∀ k, Measurable (Y k))
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hlaw : ∀ k, P.map (Y k) = ν)
    (hν : ∀ᵐ y ∂ν, y ∈ Set.Icc (0 : ℝ) 1) {μ ε' K : ℝ} (hμ0 : 0 ≤ μ) (hμ : μ < 1)
    (hε' : 0 < ε')
    (hK : ∀ l, 0 ≤ l → l * (1 - μ) < 1 → ∫ y, Real.log (1 - l * (y - μ)) ∂ν ≤ K)
    {n : ℕ} (hn : 1 ≤ n) :
    P {ω | ∃ l, 0 ≤ l ∧ l * (1 - μ) < 1 ∧
        n * (K + 7 * ε' / 8) ≤ ∑ k ∈ range n, Real.log (1 - l * (Y k ω - μ))} ≤
      ENNReal.ofReal ((⌈8 / (ε' * (1 - exp (-(ε' / 4))) * (1 - μ))⌉₊ + 1 : ℕ) *
        exp (-(ε' ^ 2 / (2 * (Real.log (1 / (1 - μ)) -
          Real.log (1 - exp (-(ε' / 4)))) ^ 2) * n))) := by
  -- The net `λ_j = min(j η', ϖ/(1-μ))`, `η' = ε'(1 - ϖ)/8`; `F` is `n/(1 - ϖ)`-Lipschitz on
  -- `[0, ϖ/(1-μ)]`; at `λ' = ϖ λ` (Lemma `lem:kinf`(vi)) and the nearest net point,
  -- `F(λ_j) ≥ n (K + ε'/2)`; Hoeffding's inequality at each point of the net.
  set ϖ := exp (-(ε' / 4)) with hϖ
  have hϖ0 : 0 < ϖ := Real.exp_pos _
  have hϖ1 : ϖ < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  set κ := Real.log (1 / (1 - μ)) with hκ
  have h1μ : 0 < 1 - μ := by linarith
  have hκ0 : 0 ≤ κ := Real.log_nonneg (by rw [le_div_iff₀ h1μ]; linarith)
  set a := Real.log (1 - ϖ) with ha
  have ha0 : a < 0 := Real.log_neg (by linarith) (by linarith)
  set R := κ - a with hR
  have hR0 : 0 < R := by linarith
  set ng := ⌈8 / (ε' * (1 - ϖ) * (1 - μ))⌉₊ + 1 with hng
  have h1ϖ : 0 < 1 - ϖ := by linarith
  have hden : 0 < ε' * (1 - ϖ) * (1 - μ) := by positivity
  set η' := ε' * (1 - ϖ) / 8 with hη'
  have hη'0 : 0 < η' := by rw [hη']; positivity
  set b := ϖ / (1 - μ) with hb
  set net : ℕ → ℝ := fun j ↦ min (j * η') b with hnet
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hYb : ∀ k, ∀ᵐ ω ∂P, Y k ω ∈ Set.Icc (0 : ℝ) 1 := fun k ↦
    ae_of_ae_map (hmeas k).aemeasurable (by rw [hlaw k]; exact hν)
  -- the net points are admissible
  have hnet0 : ∀ j, 0 ≤ net j := fun j ↦ le_min (by positivity) (by positivity)
  have hnetb : ∀ j, net j * (1 - μ) ≤ ϖ := fun j ↦ by
    have := min_le_right (j * η') b
    calc net j * (1 - μ) ≤ b * (1 - μ) := mul_le_mul_of_nonneg_right this h1μ.le
      _ = ϖ := by rw [hb]; field_simp
  have hnet1 : ∀ j, net j * (1 - μ) < 1 := fun j ↦ (hnetb j).trans_lt hϖ1
  -- Hoeffding at one net point
  have hpoint : ∀ j, P {ω | n * (K + ε' / 2) ≤ ∑ k ∈ range n,
      Real.log (1 - net j * (Y k ω - μ))} ≤
      ENNReal.ofReal (exp (-(ε' ^ 2 / (2 * R ^ 2) * n))) := by
    intro j
    set l := net j with hl
    have hl0 := hnet0 j
    have hl1 := hnet1 j
    set f : ℝ → ℝ := fun y ↦ Real.log (1 - l * (y - μ)) with hf
    have hfm : Measurable f := by simp only [hf]; fun_prop
    have hfmem : ∀ y ∈ Set.Icc (0 : ℝ) 1, a ≤ f y ∧ f y ≤ κ := by
      intro y hy
      obtain ⟨h1, h2⟩ := log_one_sub_mul_mem hμ0 hμ hl0 hl1 hy
      refine ⟨le_trans (Real.log_le_log (by linarith) (by linarith [hnetb j])) h1, h2⟩
    have hfi : Integrable f ν := Integrable.of_mem_Icc a κ hfm.aemeasurable
      (by filter_upwards [hν] with y hy using hfmem y hy)
    set W : ℕ → Ω → ℝ := fun k ω ↦ (f (Y k ω) - a) / R with hW
    have hWm : ∀ k, Measurable (W k) := fun k ↦ by
      have := hmeas k
      simp only [hW]
      fun_prop
    have hWind : iIndepFun W P := hind.comp (g := fun _ y ↦ (f y - a) / R) fun _ ↦ by fun_prop
    have hWb : ∀ k, ∀ᵐ ω ∂P, W k ω ∈ Set.Icc (0 : ℝ) 1 := by
      intro k
      filter_upwards [hYb k] with ω hω
      obtain ⟨h1, h2⟩ := hfmem _ hω
      simp only [hW, Set.mem_Icc]
      exact ⟨div_nonneg (by linarith) hR0.le, by rw [div_le_one hR0]; linarith⟩
    set mW := (∫ y, f y ∂ν - a) / R with hmW
    have hWmean : ∀ k, P[W k] = mW := by
      intro k
      have : ∫ ω, W k ω ∂P = ∫ y, (f y - a) / R ∂(P.map (Y k)) := by
        rw [integral_map (hmeas k).aemeasurable (by fun_prop : Measurable fun y ↦
          (f y - a) / R).aestronglyMeasurable]
      rw [this, hlaw k, integral_div, integral_sub hfi (integrable_const a), integral_const,
        probReal_univ, one_smul]
    set dev := n * ε' / (2 * R) with hdev
    have hsub : {ω | n * (K + ε' / 2) ≤ ∑ k ∈ range n, Real.log (1 - l * (Y k ω - μ))} ⊆
        {ω | n * mW + dev ≤ ∑ k ∈ range n, W k ω} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      have hsumW : ∑ k ∈ range n, W k ω = (∑ k ∈ range n, f (Y k ω) - n * a) / R := by
        simp only [hW]
        rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul]
      rw [hsumW, le_div_iff₀ hR0]
      have hEf : ∫ y, f y ∂ν ≤ K := hK l hl0 hl1
      have : (n * mW + dev) * R = n * (∫ y, f y ∂ν - a) + n * ε' / 2 := by
        rw [hmW, hdev]
        field_simp
      rw [this]
      have hfs : n * (K + ε' / 2) ≤ ∑ k ∈ range n, f (Y k ω) := by simpa [hf] using hω
      nlinarith
    have hhoef := measureReal_add_le_sum_range_le hWind (fun k ↦ (hWm k).aemeasurable) hWb
      hWmean hn (by positivity : 0 ≤ dev)
    refine (measure_mono hsub).trans ?_
    rw [← ofReal_measureReal]
    refine ENNReal.ofReal_le_ofReal (hhoef.trans_eq ?_)
    congr 1
    rw [hdev]
    field_simp
  -- the event forces a large value on the net
  have hsub : {ω | ∃ l, 0 ≤ l ∧ l * (1 - μ) < 1 ∧
      n * (K + 7 * ε' / 8) ≤ ∑ k ∈ range n, Real.log (1 - l * (Y k ω - μ))} ≤ᵐ[P]
      ⋃ j ∈ Finset.range ng,
        {ω | n * (K + ε' / 2) ≤ ∑ k ∈ range n, Real.log (1 - net j * (Y k ω - μ))} := by
    filter_upwards [ae_all_iff.2 hYb] with ω hω
    rintro ⟨l, hl0, hl1, hF⟩
    set l' := ϖ * l with hl'
    have hl'0 : 0 ≤ l' := mul_nonneg hϖ0.le hl0
    have hl'b : l' ≤ b := by
      rw [hl', hb, le_div_iff₀ h1μ]
      nlinarith
    -- the nearest net point below `l'`
    set j := ⌊l' / η'⌋₊ with hj
    have hjη : (j : ℝ) * η' ≤ l' := by
      have := Nat.floor_le (div_nonneg hl'0 hη'0.le)
      rwa [le_div_iff₀ hη'0] at this
    have hjη' : l' < (j + 1) * η' := by
      have := Nat.lt_floor_add_one (l' / η')
      rwa [div_lt_iff₀ hη'0] at this
    have hnetj : net j = j * η' := min_eq_left (hjη.trans hl'b)
    have hjng : j < ng := by
      have h1 : (j : ℝ) ≤ l' / η' := Nat.floor_le (div_nonneg hl'0 hη'0.le)
      have h2 : l' / η' ≤ 8 / (ε' * (1 - ϖ) * (1 - μ)) := by
        rw [div_le_div_iff₀ hη'0 hden, hη']
        have : l' * (1 - μ) ≤ ϖ := by
          calc l' * (1 - μ) ≤ b * (1 - μ) := mul_le_mul_of_nonneg_right hl'b h1μ.le
            _ = ϖ := by rw [hb]; field_simp
        nlinarith [mul_pos hε' h1ϖ]
      have h3 := Nat.le_ceil (8 / (ε' * (1 - ϖ) * (1 - μ)))
      have : (j : ℝ) < ng := by
        rw [hng]
        push_cast
        linarith
      exact_mod_cast this
    simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_ofPred_eq]
    refine ⟨j, hjng, ?_⟩
    -- `F(ϖ λ) ≥ F(λ) + n log ϖ` and `F(λ_j) ≥ F(ϖ λ) - n η' / (1 - ϖ)`
    have hscale : ∀ k ∈ range n, Real.log ϖ + Real.log (1 - l * (Y k ω - μ)) ≤
        Real.log (1 - l' * (Y k ω - μ)) := fun k _ ↦ by
      have := log_le_log_one_sub_mul hl0 hl1 hϖ0 hϖ1.le (hω k).2
      rwa [show ϖ * l = l' from rfl] at this
    have hlip : ∀ k ∈ range n, Real.log (1 - l' * (Y k ω - μ)) - η' / (1 - ϖ) ≤
        Real.log (1 - net j * (Y k ω - μ)) := fun k _ ↦ by
      have hyk := hω k
      have hpos' : 0 < 1 - l' * (Y k ω - μ) :=
        HY.one_sub_mul_pos hl'0 (by nlinarith) hyk.2
      have hbig : 1 - ϖ ≤ 1 - net j * (Y k ω - μ) := by
        have := hnetb j
        nlinarith [hnet0 j, hyk.2]
      have hL := log_sub_log_le_abs_div hpos' h1ϖ hbig
      have habs : |1 - l' * (Y k ω - μ) - (1 - net j * (Y k ω - μ))| ≤ η' := by
        have e : 1 - l' * (Y k ω - μ) - (1 - net j * (Y k ω - μ)) =
            (net j - l') * (Y k ω - μ) := by ring
        rw [e, abs_mul]
        have h1 : |net j - l'| ≤ η' := by
          rw [hnetj, abs_le]
          constructor <;> nlinarith
        have h2 : |Y k ω - μ| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith [hyk.1, hyk.2]
        calc |net j - l'| * |Y k ω - μ| ≤ η' * 1 :=
              mul_le_mul h1 h2 (abs_nonneg _) hη'0.le
          _ = η' := mul_one _
      have : |1 - l' * (Y k ω - μ) - (1 - net j * (Y k ω - μ))| / (1 - ϖ) ≤ η' / (1 - ϖ) :=
        div_le_div_of_nonneg_right habs h1ϖ.le
      linarith
    have hs1 := Finset.sum_le_sum hscale
    have hs2 := Finset.sum_le_sum hlip
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs1
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs2
    have hlogϖ : Real.log ϖ = -(ε' / 4) := by rw [hϖ, Real.log_exp]
    have hη'ϖ : η' / (1 - ϖ) = ε' / 8 := by
      rw [hη']
      have : (1 - ϖ) ≠ 0 := by linarith
      field_simp
    rw [hlogϖ] at hs1
    rw [hη'ϖ] at hs2
    linarith
  refine (measure_mono_ae hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  refine (Finset.sum_le_sum fun j _ ↦ hpoint j).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]

end Incognita.BatchedBandits
