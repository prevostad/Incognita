/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.HY.Ranks

/-! # The rank of the consistency test when `x = 1`

[INC-P000, Definition `def:amb`], conditions (b)–(e): each holds for every large `ℓ` (the rank
`ℓ₄(ε)` itself is a proof-internal definition, not formalised). With the default margins
`γ_ℓ = min(1/2, max(L_ℓ, 1)^(-1/4))`, `ζ'_ℓ = γ_ℓ Δ / 32` and a count threshold `n_ℓ = c L_ℓ`
(the paper's `n_ℓ ≥ (1 - δ) L_ℓ / (κ(m⋆ + ε) + 1)`):

* `Grid.eventually_hyGamma_eq`: `γ_ℓ = L_ℓ^(-1/4)` for every large `ℓ` (condition (e), first part);
* `Grid.eventually_mul_logEnd_le_netSize`: `C L_ℓ ≤ U_ℓ` for `β > 1` (condition (b), with
  `C = 16 ȳ / ε²`);
* `Grid.eventually_log_le_hyGamma_mul`: `C log (c L_ℓ) ≤ γ_ℓ c' (c L_ℓ)` (condition (c) in the
  form of `hyAlg_ae_ofReal_mul_threshold_le_count_mul_testKinf`, `16 ȳ log n_ℓ ≤ γ_ℓ ε² n_ℓ`), and
  `e ≤ c L_ℓ`;
* `Grid.eventually_le_hyGamma_mul_logEnd`, `Grid.eventually_le_hyGamma_mul_netSize`: condition (d),
  `C ≤ γ_ℓ c L_ℓ` (the paper's `w₀ κ ≤ ζ'_ℓ n_ℓ`) and `C ≤ γ_ℓ U_ℓ` (the paper's `2w₀ ≤ ζ_ℓ U_ℓ`);
* `Grid.eventually_logEnd_le_four_mul`: `L_ℓ ≤ 4 L_(ℓ-2)` when `x_ℓ → 1` (condition (e)).
* `Grid.eventually_div_four_rpow_le_netSize`: `U_(ℓ-1) ≥ (L_ℓ/4)^β` (from condition (e); the
  bound on the event `Acc_ℓ^c` in Step 5 of the proof of Lemma `lem:amb`).
* `Grid.eventually_netSize_bounds`: condition (a), the hypotheses of Lemma `lem:optW` at `j`:
  `U_(j-1) ≤ 2 t_j^(1-δ)`, `C L_j ≤ U_(j-1)` (`u_j ≤ U_(j-1)/2`), `C' ≤ U_(j-1)`
  (`2w₀ ≤ ε U_(j-1)`) and `K U_(j-1) ≤ t_(j-1)`.
* `Grid.eventually_mul_t_le_imedEnd_sub`: with the default `ϑ`, every large batch has a long IMED
  phase, `s_ℓ - t_ℓ ≥ K t_ℓ` (the third condition defining `ℓ_W`, Definition `def:water`; the
  hypothesis of `hyAlg_ae_le_card_filter_le_imedIndex`).
-/

@[expose] public section

open Real Filter

open scoped Topology

namespace Incognita.BatchedBandits

namespace Grid

variable {K : ℕ} (g : Grid K)

/-- With the default margins, `γ_ℓ = L_ℓ^(-1/4)` for every large `ℓ` (as soon as `L_ℓ ≥ 16`). -/
lemma eventually_hyGamma_eq : ∀ᶠ ℓ in atTop, g.hyGamma ℓ = g.logEnd ℓ ^ (-(1 / 4 : ℝ)) := by
  filter_upwards [g.tendsto_logEnd_atTop.eventually_ge_atTop 16] with ℓ hℓ
  have h1 : max (g.logEnd ℓ) 1 = g.logEnd ℓ := max_eq_left (by linarith)
  unfold hyGamma
  rw [h1, min_eq_right]
  have hpos : 0 < g.logEnd ℓ := by linarith
  have h16 : (16 : ℝ) ^ (-(1 / 4 : ℝ)) = 1 / 2 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  calc g.logEnd ℓ ^ (-(1 / 4 : ℝ)) ≤ (16 : ℝ) ^ (-(1 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hℓ (by norm_num)
    _ = 1 / 2 := h16

/-- For `β > 1` and every `C`, `C L_ℓ ≤ U_ℓ` for every large `ℓ`, on a grid with converging ratios
(condition (b) of Definition `def:amb`, `ȳ L_ℓ ≤ (U_ℓ/2)(ε²/8)`, with `C = 16 ȳ / ε²`). -/
lemma eventually_mul_logEnd_le_netSize {x : ℝ} (hg : Tendsto g.ratio atTop (𝓝 x)) {β : ℝ}
    (hβ : 1 < β) {C : ℝ} (hC : 0 ≤ C) : ∀ᶠ ℓ in atTop, C * g.logEnd ℓ ≤ g.netSize β ℓ := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (g.eventually_add_mul_logEnd_le_netSize hg hβ hC 0)
  refine eventually_atTop.mpr ⟨N + 1, fun ℓ hℓ ↦ ?_⟩
  have h := hN (ℓ - 1) (by omega)
  rw [show ℓ - 1 + 1 = ℓ by omega] at h
  push_cast at h
  linarith

/-- For `c, c' > 0` and every `C`, eventually `C log (c L_ℓ) ≤ γ_ℓ c' (c L_ℓ)` and `e ≤ c L_ℓ`
(condition (c) of Definition `def:amb` in the form of
`hyAlg_ae_ofReal_mul_threshold_le_count_mul_testKinf`: with `n_ℓ = c L_ℓ`,
`C = 16 ȳ` and `c' = ε²`, `16 ȳ log n_ℓ ≤ γ_ℓ ε² n_ℓ`; `γ_ℓ c L_ℓ = c L_ℓ^(3/4)`). -/
lemma eventually_log_le_hyGamma_mul {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c') (C : ℝ) :
    ∀ᶠ ℓ in atTop, C * Real.log (c * g.logEnd ℓ) ≤ g.hyGamma ℓ * c' * (c * g.logEnd ℓ) ∧
      Real.exp 1 ≤ c * g.logEnd ℓ := by
  -- `log (c L) = o(L^(3/4))`
  have hlo : (fun L : ℝ ↦ Real.log (c * L)) =o[atTop] fun L ↦ L ^ (3 / 4 : ℝ) := by
    have h1 : (fun L : ℝ ↦ Real.log (c * L)) =ᶠ[atTop] fun L ↦ Real.log c + Real.log L := by
      filter_upwards [eventually_gt_atTop 0] with L hL
      rw [Real.log_mul hc.ne' hL.ne']
    refine Asymptotics.IsLittleO.congr' ?_ h1.symm EventuallyEq.rfl
    refine Asymptotics.IsLittleO.add ?_ (isLittleO_log_rpow_atTop (by norm_num))
    refine Asymptotics.isLittleO_const_left.mpr (Or.inr ?_)
    refine (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 4)).congr' ?_
    filter_upwards [eventually_ge_atTop 0] with L hL
    simp [Real.norm_of_nonneg (Real.rpow_nonneg hL _)]
  have hb := (hlo.bound (show 0 < c * c' / (|C| + 1) by positivity)).filter_mono le_rfl
  have hb' := g.tendsto_logEnd_atTop.eventually hb
  filter_upwards [hb', g.eventually_hyGamma_eq, g.tendsto_logEnd_atTop.eventually_ge_atTop 1,
    g.tendsto_logEnd_atTop.eventually_ge_atTop (Real.exp 1 / c)] with ℓ hℓ hγ hL1 hLe
  set L := g.logEnd ℓ with hL
  have hL0 : 0 < L := by linarith
  refine ⟨?_, by rwa [div_le_iff₀ hc, mul_comm] at hLe⟩
  rw [hγ]
  have hcL : 1 ≤ c * L := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)])
    (show Real.exp 1 ≤ c * L by rwa [div_le_iff₀ hc, mul_comm] at hLe)
  have hlog0 : 0 ≤ Real.log (c * L) := Real.log_nonneg hcL
  rw [Real.norm_of_nonneg hlog0, Real.norm_of_nonneg (by positivity)] at hℓ
  -- `L^(-1/4) · L = L^(3/4)`
  have hpow : L ^ (-(1 / 4 : ℝ)) * L = L ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_add_one hL0.ne']
    norm_num
  have hrhs : L ^ (-(1 / 4 : ℝ)) * c' * (c * L) = c * c' * L ^ (3 / 4 : ℝ) := by
    rw [← hpow]
    ring
  rw [hrhs]
  have h2 : (|C| + 1) * Real.log (c * L) ≤ c * c' * L ^ (3 / 4 : ℝ) := by
    have := mul_le_mul_of_nonneg_left hℓ (by positivity : (0 : ℝ) ≤ |C| + 1)
    rwa [← mul_assoc, mul_div_cancel₀ _ (by positivity)] at this
  have h3 : C * Real.log (c * L) ≤ (|C| + 1) * Real.log (c * L) :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) hlog0
  linarith

/-- For `c > 0` and every `C`, `C ≤ γ_ℓ c L_ℓ` for every large `ℓ` (condition (d) of
Definition `def:amb`, `w₀ κ(m⋆ + ε) ≤ ζ'_ℓ n_ℓ`, with `ζ'_ℓ n_ℓ = γ_ℓ (Δ/32) c L_ℓ`). -/
lemma eventually_le_hyGamma_mul_logEnd {c : ℝ} (hc : 0 < c) (C : ℝ) :
    ∀ᶠ ℓ in atTop, C ≤ g.hyGamma ℓ * (c * g.logEnd ℓ) := by
  filter_upwards [g.eventually_hyGamma_eq, g.tendsto_logEnd_atTop.eventually_gt_atTop 0,
    g.eventually_le_mul_logEnd_rpow (β := 7 / 4) (by norm_num) hc C] with ℓ hγ hL0 hL
  rw [hγ]
  have hpow : g.logEnd ℓ ^ (-(1 / 4 : ℝ)) * g.logEnd ℓ = g.logEnd ℓ ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_add_one hL0.ne']
    norm_num
  calc C ≤ g.logEnd ℓ ^ (3 / 4 : ℝ) * c := by rw [mul_comm]; norm_num at hL ⊢; exact hL
    _ = g.logEnd ℓ ^ (-(1 / 4 : ℝ)) * (c * g.logEnd ℓ) := by rw [← hpow]; ring

/-- For `β > 1`, `c > 0` and every `C`, `C ≤ γ_ℓ c U_ℓ` for every large `ℓ`, on a grid with
converging ratios (condition (d) of Definition `def:amb`, `2 w₀ ≤ ζ_ℓ U_ℓ`, with
`ζ_ℓ = γ_ℓ Δ (1 - m⋆)/64`): `U_ℓ ≥ L_ℓ` and `C ≤ γ_ℓ c L_ℓ`. -/
lemma eventually_le_hyGamma_mul_netSize {x : ℝ} (hg : Tendsto g.ratio atTop (𝓝 x)) {β : ℝ}
    (hβ : 1 < β) {c : ℝ} (hc : 0 < c) (C : ℝ) :
    ∀ᶠ ℓ in atTop, C ≤ g.hyGamma ℓ * (c * g.netSize β ℓ) := by
  filter_upwards [g.eventually_le_hyGamma_mul_logEnd hc C,
    g.eventually_mul_logEnd_le_netSize hg hβ (C := 1) zero_le_one,
    g.eventually_hyGamma_eq, g.tendsto_logEnd_atTop.eventually_gt_atTop 0] with ℓ h1 h2 hγ hL0
  rw [one_mul] at h2
  have hγ0 : 0 ≤ g.hyGamma ℓ := by rw [hγ]; positivity
  calc C ≤ g.hyGamma ℓ * (c * g.logEnd ℓ) := h1
    _ ≤ g.hyGamma ℓ * (c * g.netSize β ℓ) := by gcongr

/-- On a grid with `x_ℓ → 1`, `L_ℓ ≤ 4 L_(ℓ-2)` for every large `ℓ` (condition (e) of
Definition `def:amb`): `L_ℓ = x_ℓ x_(ℓ-1) L_(ℓ-2)` with `x ≤ 2`. -/
lemma eventually_logEnd_le_four_mul (hg : Tendsto g.ratio atTop (𝓝 1)) :
    ∀ᶠ ℓ in atTop, g.logEnd ℓ ≤ 4 * g.logEnd (ℓ - 2) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (g.eventually_ratio_le hg (by norm_num : (1 : ℝ) < 2))
  refine eventually_atTop.mpr ⟨N + 4, fun ℓ hℓ ↦ ?_⟩
  have h1 := g.logEnd_succ_eq (j := ℓ - 1) (by omega)
  have h2 := g.logEnd_succ_eq (j := ℓ - 2) (by omega)
  rw [show ℓ - 1 + 1 = ℓ by omega] at h1
  rw [show ℓ - 2 + 1 = ℓ - 1 by omega] at h2
  have hx1 := hN ℓ (by omega)
  have hx2 := hN (ℓ - 1) (by omega)
  have hL0 : 0 < g.logEnd (ℓ - 2) := g.logEnd_pos (by omega)
  have hL1 : 0 < g.logEnd (ℓ - 1) := g.logEnd_pos (by omega)
  rw [h1, h2]
  have hr1 : 0 ≤ g.ratio (ℓ - 1 + 1) := le_trans zero_le_one (by
    rcases Nat.lt_or_ge (ℓ - 1 + 1) 2 with h | h
    · omega
    · exact (g.one_lt_ratio h).le)
  have hr2 : 0 ≤ g.ratio (ℓ - 2 + 1) := le_trans zero_le_one (by
    rcases Nat.lt_or_ge (ℓ - 2 + 1) 2 with h | h
    · omega
    · exact (g.one_lt_ratio h).le)
  rw [show ℓ - 1 + 1 = ℓ by omega] at hr1
  rw [show ℓ - 2 + 1 = ℓ - 1 by omega] at hr2
  have h3 : g.ratio (ℓ - 1) * g.logEnd (ℓ - 2) ≤ 2 * g.logEnd (ℓ - 2) :=
    mul_le_mul_of_nonneg_right hx2 hL0.le
  have h4 : g.ratio ℓ * (g.ratio (ℓ - 1) * g.logEnd (ℓ - 2)) ≤
      2 * (g.ratio (ℓ - 1) * g.logEnd (ℓ - 2)) :=
    mul_le_mul_of_nonneg_right hx1 (mul_nonneg hr2 hL0.le)
  linarith

/-- On a grid with `x_ℓ → 1`, for `β ≥ 0`, `U_(ℓ-1) ≥ L_(ℓ-2)^β ≥ (L_ℓ/4)^β` for every large `ℓ`
(the proof of Lemma `lem:amb`, Step 5, the event `Acc_ℓ^c`, through condition (e) of
Definition `def:amb`). -/
lemma eventually_div_four_rpow_le_netSize (hg : Tendsto g.ratio atTop (𝓝 1)) {β : ℝ}
    (hβ : 0 ≤ β) : ∀ᶠ ℓ in atTop, (g.logEnd ℓ / 4) ^ β ≤ g.netSize β (ℓ - 1) := by
  filter_upwards [g.eventually_logEnd_le_four_mul hg, eventually_ge_atTop 3] with ℓ hℓ h3
  rw [show ℓ - 1 = ℓ - 2 + 1 by omega, g.netSize_succ β (by omega)]
  have hL0 : 0 ≤ g.logEnd ℓ / 4 := div_nonneg (g.logEnd_pos (by omega)).le (by norm_num)
  calc (g.logEnd ℓ / 4) ^ β ≤ g.logEnd (ℓ - 2) ^ β := Real.rpow_le_rpow hL0 (by linarith) hβ
    _ ≤ _ := Nat.le_ceil _

/-- `U_(ℓ+1) ≤ L_ℓ^β + 1` for `ℓ ≥ 1`. -/
lemma netSize_succ_le (β : ℝ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    (g.netSize β (ℓ + 1) : ℝ) ≤ g.logEnd ℓ ^ β + 1 := by
  rw [g.netSize_succ β hℓ]
  exact (Nat.ceil_lt_add_one (Real.rpow_nonneg (g.logEnd_pos hℓ).le β)).le

/-- [INC-P000, Definition `def:amb`, condition (a)] On a grid with `x_ℓ → 1`, for `β > 1`, `δ < 1`
and every `C`, `C'`, `K'`, every large `j` has `U_(j-1) ≤ 2 t_j^(1-δ)` (written `2 e^((1-δ) L_j)`),
`C L_j ≤ U_(j-1)` (the paper's `u_j ≤ ½ U_(j-1)` with `C = (1 + η₀)/ε²`), `C' ≤ U_(j-1)` (the
paper's `2w₀ ≤ ε U_(j-1)`) and `K' U_(j-1) ≤ t_(j-1)`: the net sizes are powers of `L`, the batch
ends exponentials of `L`. -/
lemma eventually_netSize_bounds (hg : Tendsto g.ratio atTop (𝓝 1)) {β : ℝ} (hβ : 1 < β)
    {δ : ℝ} (hδ : δ < 1) (C C' K' : ℝ) :
    ∀ᶠ j in atTop, (g.netSize β (j - 1) : ℝ) ≤ 2 * Real.exp ((1 - δ) * g.logEnd j) ∧
      C * g.logEnd j ≤ g.netSize β (j - 1) ∧ C' ≤ g.netSize β (j - 1) ∧
      K' * g.netSize β (j - 1) ≤ g.t (j - 1) := by
  have hβ0 : 0 ≤ β := by linarith
  have hL := g.tendsto_logEnd_atTop
  -- `L^β + 1 ≤ e^((1-δ) L)` and `|K'| (L^β + 1) ≤ e^L` for large `L`
  have he1 := hL.eventually (eventually_mul_rpow_add_one_le_exp 1 β (by linarith : 0 < 1 - δ))
  have he2 := hL.eventually (eventually_mul_rpow_add_one_le_exp (|K'|) β one_pos)
  -- `4 |C| L ≤ L^β`
  have hpow := g.eventually_le_mul_logEnd_rpow hβ one_pos (4 * |C|)
  have h4 := g.eventually_logEnd_le_four_mul hg
  have hU := g.eventually_le_netSize (by linarith : 0 < β) C'
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp he1
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp he2
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.mp hpow
  obtain ⟨N₄, hN₄⟩ := eventually_atTop.mp h4
  obtain ⟨N₅, hN₅⟩ := eventually_atTop.mp hU
  refine eventually_atTop.mpr ⟨N₁ + N₂ + N₃ + N₄ + N₅ + 4, fun j hj ↦ ?_⟩
  have hUle : (g.netSize β (j - 1) : ℝ) ≤ g.logEnd (j - 2) ^ β + 1 := by
    have := g.netSize_succ_le β (ℓ := j - 2) (by omega)
    rwa [show j - 2 + 1 = j - 1 by omega] at this
  have hLm1 : g.logEnd (j - 2) ≤ g.logEnd j := g.logEnd_monotone (by omega)
  have hLm2 : g.logEnd (j - 2) ≤ g.logEnd (j - 1) := g.logEnd_monotone (by omega)
  have hL20 : 0 < g.logEnd (j - 2) := g.logEnd_pos (by omega)
  have hpowm : g.logEnd (j - 2) ^ β ≤ g.logEnd j ^ β :=
    Real.rpow_le_rpow hL20.le hLm1 hβ0
  have hpowm' : g.logEnd (j - 2) ^ β ≤ g.logEnd (j - 1) ^ β :=
    Real.rpow_le_rpow hL20.le hLm2 hβ0
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := hN₁ j (by omega)
    rw [one_mul] at this
    have he : 0 < Real.exp ((1 - δ) * g.logEnd j) := Real.exp_pos _
    linarith
  · -- `C L_j ≤ 4 |C| L_(j-2) ≤ L_(j-2)^β ≤ U_(j-1)`
    have h1 := hN₄ j (by omega)
    have h2 := hN₃ (j - 2) (by omega)
    rw [one_mul] at h2
    have hLb : g.logEnd (j - 2) ^ β = g.logEnd (j - 2) * g.logEnd (j - 2) ^ (β - 1) := by
      rw [Real.rpow_sub_one hL20.ne', mul_div_cancel₀ _ hL20.ne']
    have hU' : g.logEnd (j - 2) ^ β ≤ g.netSize β (j - 1) := by
      rw [show j - 1 = j - 2 + 1 by omega, g.netSize_succ β (by omega)]
      exact Nat.le_ceil _
    have hj0 : 0 ≤ g.logEnd j := (g.logEnd_pos (by omega)).le
    calc C * g.logEnd j ≤ |C| * g.logEnd j := mul_le_mul_of_nonneg_right (le_abs_self C) hj0
      _ ≤ |C| * (4 * g.logEnd (j - 2)) := mul_le_mul_of_nonneg_left h1 (abs_nonneg C)
      _ = g.logEnd (j - 2) * (4 * |C|) := by ring
      _ ≤ g.logEnd (j - 2) * g.logEnd (j - 2) ^ (β - 1) :=
          mul_le_mul_of_nonneg_left h2 hL20.le
      _ = g.logEnd (j - 2) ^ β := hLb.symm
      _ ≤ g.netSize β (j - 1) := hU'
  · exact hN₅ (j - 1) (by omega)
  · have h1 := hN₂ (j - 1) (by omega)
    have hj1 : 1 ≤ j - 1 := by omega
    rw [one_mul, g.exp_logEnd hj1] at h1
    have hU0 : (0 : ℝ) ≤ g.netSize β (j - 1) := Nat.cast_nonneg _
    calc K' * g.netSize β (j - 1) ≤ |K'| * g.netSize β (j - 1) :=
          mul_le_mul_of_nonneg_right (le_abs_self K') hU0
      _ ≤ |K'| * (g.logEnd (j - 1) ^ β + 1) :=
          mul_le_mul_of_nonneg_left (hUle.trans (by linarith)) (abs_nonneg K')
      _ ≤ g.t (j - 1) := h1

/-- [INC-P000, Definition `def:water`, the third condition defining `ℓ_W`] With the default
exponents `ϑ_ℓ = 1 / log log t_ℓ`, for every `K'`, every large `ℓ` has `K' t_ℓ ≤ s_ℓ - t_ℓ`:
`t_ℓ^(ϑ_ℓ) = e^(L_ℓ / log L_ℓ) ≥ K' + 2` eventually, and `⌊t (K' + 2)⌋ - t ≥ K' t`. -/
lemma eventually_mul_t_le_imedEnd_sub (K' : ℕ) :
    ∀ᶠ ℓ in atTop, K' * g.t ℓ ≤ g.imedEnd g.hyTheta ℓ - g.t ℓ := by
  -- `L / log L → ∞`
  have hlo : Tendsto (fun L : ℝ ↦ L / Real.log L) atTop atTop := by
    have := (isLittleO_log_rpow_atTop (r := 1) one_pos).tendsto_div_nhds_zero
    simp only [Real.rpow_one] at this
    have hT : Tendsto (fun L : ℝ ↦ Real.log L / L) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨this, ?_⟩
      filter_upwards [eventually_gt_atTop 1] with L hL
      exact div_pos (Real.log_pos hL) (by linarith)
    have hEq : (fun L : ℝ ↦ Real.log L / L)⁻¹ =ᶠ[atTop] fun L : ℝ ↦ L / Real.log L := by
      filter_upwards [eventually_gt_atTop 1] with L hL
      simp [inv_div]
    exact Tendsto.congr' hEq hT.inv_tendsto_nhdsGT_zero
  have hev := (hlo.comp g.tendsto_logEnd_atTop).eventually_ge_atTop (Real.log (K' + 2))
  have het : ∀ᶠ ℓ in atTop, Real.exp (Real.exp 1) ≤ (g.t ℓ : ℝ) := by
    have ht : Tendsto (fun ℓ ↦ (g.t ℓ : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp g.strictMono.tendsto_atTop
    exact ht.eventually_ge_atTop _
  filter_upwards [hev, het, eventually_ge_atTop 1] with ℓ hL ht hℓ
  simp only [Function.comp_apply] at hL
  have htpos : (0 : ℝ) < g.t ℓ := g.t_pos hℓ
  have hθ := g.hyTheta_eq ht
  have hlogL := g.one_le_log_logEnd ht
  -- `t^(ϑ) ≥ K' + 2`
  have hpow : (K' + 2 : ℝ) ≤ (g.t ℓ : ℝ) ^ g.hyTheta ℓ := by
    rw [hθ, Real.rpow_def_of_pos htpos]
    have : Real.log (g.t ℓ) * (1 / Real.log (g.logEnd ℓ)) = g.logEnd ℓ / Real.log (g.logEnd ℓ) := by
      unfold logEnd; ring
    rw [this, ← Real.exp_log (show (0 : ℝ) < K' + 2 by positivity)]
    exact Real.exp_le_exp.mpr hL
  have hprod : (g.t ℓ : ℝ) ^ (1 + g.hyTheta ℓ) = g.t ℓ * (g.t ℓ : ℝ) ^ g.hyTheta ℓ := by
    rw [Real.rpow_add htpos, Real.rpow_one]
  have hge : ((K' + 1) * g.t ℓ + 1 : ℝ) ≤ (g.t ℓ : ℝ) ^ (1 + g.hyTheta ℓ) := by
    rw [hprod]
    have h1 : (1 : ℝ) ≤ g.t ℓ := by have := g.two_le_t hℓ; exact_mod_cast (show 1 ≤ g.t ℓ by omega)
    nlinarith
  have hfl : (K' + 1) * g.t ℓ ≤ g.imedEnd g.hyTheta ℓ := by
    unfold imedEnd
    refine Nat.le_floor ?_
    push_cast
    linarith
  have : K' * g.t ℓ + g.t ℓ ≤ g.imedEnd g.hyTheta ℓ := by
    have : (K' + 1) * g.t ℓ = K' * g.t ℓ + g.t ℓ := by ring
    omega
  omega

end Grid

end Incognita.BatchedBandits
