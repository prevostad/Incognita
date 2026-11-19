/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.Counting
public import Incognita.BatchedBandits.Queue

/-! # Many high batches

[INC-P000, Lemma `lem:levelC`], in an abstract form. For a run of HY, `Λ_j` is the water level of
batch `j` [INC-P000, Definition `def:water`], and batch `j` is `(g, L)`-high if
`Λ_j ≥ (1 - g) L_L` (Definition `def:high`). Lemma `lem:lowmass` says that, for every `ℓ > ℓ_W`
and `v ≥ 0`, the batches `i ∈ [ℓ_W, ℓ)` with `Λ_i < v`, outside a set of at most `K` batches,
carry at most `K e^v` pulls; `exists_card_le_sum_low_le` proves this from (W2), for every
sequence of actions. `exists_rank_card_high_le` proves Lemma `lem:levelC` for **every**
sequence `Λ` with that property, with a rank that does not depend on `Λ`: on a grid with
`x_ℓ → 1`, for every `g ∈ (0, 1)` and `m'`, there is `L₀` such that every `L ≥ L₀` has at least
`m'` batches `j ∈ [2, L)` that are `(g, L)`-high. The proof is the paper's: otherwise the grid
would grow through at most `K + m'` batches (Lemma `lem:growth`), and `log t_(L-1) ≤
(1 - g/2) log t_L + O(1)` contradicts `x_L → 1`.
-/

@[expose] public section

open Real Finset Filter Learning

open scoped Topology

namespace Incognita.BatchedBandits

/-- `(1 + β₀)^h ≤ e^(β₀ h)`. -/
lemma one_add_pow_le_exp {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) (h : ℕ) : (1 + β₀) ^ h ≤ Real.exp (β₀ * h) := by
  rw [mul_comm, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp β₀]) h

/-- [INC-P000, Lemma `lem:levelC`, abstract form] On a grid with `x_ℓ → 1`, let `g ∈ (0, 1)`,
`m'`, `K` and `ℓ_W ≥ 1`. There is a rank `L₀` such that, for every sequence `Λ` with the property
of Lemma `lem:lowmass` (for every `L > ℓ_W` and `v ≥ 0`, some set `E` of at most `K` batches has
`∑_{i ∈ [ℓ_W, L), Λ_i < v, i ∉ E} B_i ≤ K e^v`) and every `L ≥ L₀`, at least `m'` batches
`j ∈ [2, L)` have `Λ_j ≥ (1 - g) L_L`. -/
lemma exists_rank_card_high_le {K' : ℕ} (gr : Grid K') (hgr : Tendsto gr.ratio atTop (𝓝 1))
    {g : ℝ} (hg0 : 0 < g) (hg1 : g < 1) (m' K lW : ℕ) (hlW : 1 ≤ lW) :
    ∃ L₀, ∀ Λ : ℕ → ℝ, (∀ L, lW < L → ∀ v : ℝ, 0 ≤ v → ∃ E : Finset ℕ, E.card ≤ K ∧
        ∑ i ∈ (Finset.Ico lW L).filter (fun i ↦ Λ i < v ∧ i ∉ E),
          ((gr.t i : ℝ) - gr.t (i - 1)) ≤ K * Real.exp v) →
      ∀ L, L₀ ≤ L → m' ≤ ((Finset.Ico 2 L).filter fun j ↦ (1 - g) * gr.logEnd L ≤ Λ j).card := by
  set hb : ℕ := K + m' with hhb
  set β₀ : ℝ := Real.log ((1 - g / 2) / (1 - g)) / (hb + 1) with hβ₀
  have h1g : 0 < 1 - g := by linarith
  have hlogq : 0 < Real.log ((1 - g / 2) / (1 - g)) :=
    Real.log_pos (by rw [lt_div_iff₀ h1g]; linarith)
  have hβ₀0 : 0 < β₀ := by positivity
  -- `(1 + β₀)^hb (1 - g) ≤ 1 - g/2`
  have hpowβ : (1 + β₀) ^ hb * (1 - g) ≤ 1 - g / 2 := by
    have h1 := one_add_pow_le_exp hβ₀0.le hb
    have h2 : β₀ * hb ≤ Real.log ((1 - g / 2) / (1 - g)) := by
      have hfrac : (hb : ℝ) / (hb + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith
      calc β₀ * hb = Real.log ((1 - g / 2) / (1 - g)) * (hb / (hb + 1)) := by
            rw [hβ₀]
            ring
        _ ≤ Real.log ((1 - g / 2) / (1 - g)) * 1 := mul_le_mul_of_nonneg_left hfrac hlogq.le
        _ = _ := mul_one _
    have h3 : Real.exp (β₀ * hb) ≤ (1 - g / 2) / (1 - g) := by
      calc Real.exp (β₀ * hb) ≤ Real.exp (Real.log ((1 - g / 2) / (1 - g))) :=
            Real.exp_le_exp.mpr h2
        _ = _ := Real.exp_log (div_pos (by linarith) h1g)
    have := h1.trans h3
    rw [le_div_iff₀ h1g] at this
    exact this
  -- the rank `k₀`
  obtain ⟨k₁, hk₁⟩ := eventually_atTop.1 ((tendsto_order.1 hgr).2 (1 + β₀) (by linarith))
  set k₀ := max k₁ lW with hk₀
  have hk₀lW : lW ≤ k₀ := le_max_right _ _
  have hk₀x : ∀ j, k₀ < j → gr.ratio j ≤ 1 + β₀ := fun j hj ↦
    (hk₁ j (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hj))).le
  set ω' : ℝ := (1 + β₀) ^ hb * (Real.log (gr.t k₀ + K) + hb * Real.log 2) with hω'
  -- the rank `L₀`
  have hL : Tendsto gr.logEnd atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp gr.strictMono.tendsto_atTop)
  have hev1 : ∀ᶠ L in atTop, gr.ratio L < 1 / (1 - g / 4) :=
    (tendsto_order.1 hgr).2 _ (by rw [gt_iff_lt, lt_div_iff₀ (by linarith)]; linarith)
  have hev2 : ∀ᶠ L in atTop, 4 * ω' / g < gr.logEnd L := hL.eventually_gt_atTop _
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.1 (hev1.and hev2)
  refine ⟨max L₁ (k₀ + 2), fun Λ hlow L hL₀ ↦ ?_⟩
  have hLL₁ : L₁ ≤ L := (le_max_left _ _).trans hL₀
  have hLk₀ : k₀ + 2 ≤ L := (le_max_right _ _).trans hL₀
  obtain ⟨hxL, hLL⟩ := hL₁ L hLL₁
  by_contra hcon
  have hcon := not_le.mp hcon
  set Hi := (Finset.Ico 2 L).filter fun j ↦ (1 - g) * gr.logEnd L ≤ Λ j with hHi
  set v := (1 - g) * gr.logEnd L with hv
  have hLpos : 0 < gr.logEnd L := gr.logEnd_pos (by omega)
  have hv0 : 0 ≤ v := by positivity
  obtain ⟨E, hEcard, hEsum⟩ := hlow L (by omega) v hv0
  set S := Hi ∪ E with hS
  have hScard : S.card ≤ hb := (Finset.card_union_le _ _).trans (by omega)
  -- little mass outside `S`
  have hmass : ∑ j ∈ (Finset.Ioc k₀ (L - 1)).filter (· ∉ S), ((gr.t j : ℝ) - gr.t (j - 1)) ≤
      K * Real.exp v := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun j _ _ ↦
      sub_nonneg.mpr (gr.t_le_t (by omega))) hEsum
    intro j hj
    obtain ⟨hjI, hjS⟩ := Finset.mem_filter.mp hj
    have hjI' := Finset.mem_Ioc.mp hjI
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_, ?_⟩
    · by_contra hge
      have hge := not_lt.mp hge
      exact hjS (Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hge⟩))
    · exact fun hjE ↦ hjS (Finset.mem_union_right _ hjE)
  -- the grid cannot grow enough
  have hgrow := gr.log_t_le_of_growth (k₀ := k₀) (n := L - 1) (by omega) (by omega) hβ₀0.le
    hk₀x S hmass
  set h' := ((Finset.Ioc k₀ (L - 1)).filter (· ∈ S)).card with hh'
  have hh'le : h' ≤ hb := by
    refine le_trans (Finset.card_le_card ?_) hScard
    intro j hj
    exact (Finset.mem_filter.mp hj).2
  have htk : (2 : ℝ) ≤ gr.t k₀ := by exact_mod_cast gr.two_le_t (by omega)
  have hA0 : 0 ≤ Real.log (gr.t k₀ + K * Real.exp v) :=
    Real.log_nonneg (by have : 0 ≤ (K : ℝ) * Real.exp v := by positivity
                        linarith)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h1β : 1 ≤ 1 + β₀ := by linarith
  have hmonoh : (1 + β₀) ^ h' * (Real.log (gr.t k₀ + K * Real.exp v) + h' * Real.log 2) ≤
      (1 + β₀) ^ hb * (Real.log (gr.t k₀ + K * Real.exp v) + hb * Real.log 2) := by
    have hp : (1 + β₀) ^ h' ≤ (1 + β₀) ^ hb := pow_le_pow_right₀ h1β hh'le
    have hq : (h' : ℝ) * Real.log 2 ≤ hb * Real.log 2 :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hh'le) hlog2
    have : 0 ≤ Real.log (gr.t k₀ + K * Real.exp v) + h' * Real.log 2 := by positivity
    calc _ ≤ (1 + β₀) ^ hb * (Real.log (gr.t k₀ + K * Real.exp v) + h' * Real.log 2) :=
          mul_le_mul_of_nonneg_right hp this
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hlogsum : Real.log (gr.t k₀ + K * Real.exp v) ≤ Real.log (gr.t k₀ + K) + v := by
    have he : 1 ≤ Real.exp v := Real.one_le_exp_iff.mpr hv0
    have : (gr.t k₀ : ℝ) + K * Real.exp v ≤ (gr.t k₀ + K) * Real.exp v := by
      nlinarith [Nat.cast_nonneg (α := ℝ) K]
    calc Real.log (gr.t k₀ + K * Real.exp v) ≤ Real.log ((gr.t k₀ + K) * Real.exp v) :=
          Real.log_le_log (by positivity) this
      _ = Real.log (gr.t k₀ + K) + v := by
          rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
  have hupper : Real.log (gr.t (L - 1)) ≤ (1 - g / 2) * gr.logEnd L + ω' := by
    calc Real.log (gr.t (L - 1)) ≤ _ := hgrow
      _ ≤ _ := hmonoh
      _ ≤ (1 + β₀) ^ hb * (Real.log (gr.t k₀ + K) + v + hb * Real.log 2) := by
          gcongr
      _ = (1 + β₀) ^ hb * (1 - g) * gr.logEnd L + ω' := by rw [hω', hv]; ring
      _ ≤ (1 - g / 2) * gr.logEnd L + ω' := by
          gcongr
  -- but `log t_(L-1) = L_L / x_L ≥ (1 - g/4) L_L`
  have hratio : gr.ratio L * gr.logEnd (L - 1) = gr.logEnd L := by
    have := gr.logEnd_succ_eq (j := L - 1) (by omega)
    rw [show L - 1 + 1 = L by omega] at this
    rw [this]
  have hxpos : 0 < gr.ratio L := by
    have := gr.one_lt_ratio (ℓ := L) (by omega)
    linarith
  have hlower : (1 - g / 4) * gr.logEnd L ≤ gr.logEnd (L - 1) := by
    have h1 : gr.ratio L * (1 - g / 4) ≤ 1 := by
      rw [lt_div_iff₀ (by linarith)] at hxL
      linarith
    have hL1 : 0 ≤ gr.logEnd (L - 1) := (gr.logEnd_pos (by omega)).le
    nlinarith
  have hfinal : g / 4 * gr.logEnd L ≤ ω' := by
    have hlower' : (1 - g / 4) * gr.logEnd L ≤ Real.log (gr.t (L - 1)) := hlower
    linarith
  have : 4 * ω' / g < gr.logEnd L := hLL
  rw [div_lt_iff₀ hg0] at this
  linarith

/-! ### Lemma `lem:lowmass` -/

section LowMass

variable {β Ω : Type*} [DecidableEq β] [Fintype β] {A : ℕ → Ω → β} {ω : Ω}

/-- The batch sizes are the sums of the increments of the counts:
`B_i = ∑_c (N_c(t_i) - N_c(t_(i-1)))`. -/
lemma t_sub_eq_sum_pullCount_sub {K' : ℕ} (gr : Grid K') {i : ℕ} (hi : 1 ≤ i) :
    gr.t i - gr.t (i - 1) =
      ∑ c, (pullCount A c (gr.t i) ω - pullCount A c (gr.t (i - 1)) ω) := by
  have hle : gr.t (i - 1) ≤ gr.t i := gr.strictMono.monotone (by omega)
  have h := card_filter_mem_eq_sum (A := A) (ω := ω) Finset.univ hle
  rw [Finset.filter_true_of_mem (fun _ _ ↦ Finset.mem_univ _), Nat.card_Ico] at h
  exact h

omit [Fintype β] in
/-- The increments of a count over the batches `[a, b)` sum to at most `N(t_(b-1))`. -/
lemma sum_Ico_pullCount_sub_le {K' : ℕ} (gr : Grid K') (c : β) {a b : ℕ} (hab : a ≤ b) :
    ∑ i ∈ Finset.Ico a b, (pullCount A c (gr.t i) ω - pullCount A c (gr.t (i - 1)) ω) ≤
      pullCount A c (gr.t (b - 1)) ω := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    rw [Finset.sum_Ico_succ_top hb, show b + 1 - 1 = b by omega]
    have : pullCount A c (gr.t (b - 1)) ω ≤ pullCount A c (gr.t b) ω :=
      pullCount_mono _ (gr.strictMono.monotone (by omega)) _
    omega

/-- [INC-P000, Lemma `lem:lowmass`, abstract form] Let `ℓ_W ≥ 1`, `ℓ`, and water levels `Λ_i`
such that (W2) holds in the batches `i ∈ [ℓ_W, ℓ)`: every arm `c` pulled in batch `i` has
`log N_c(t_(i-1)) ≤ Λ_i`. Then for every real `v` there is a set `E` of at most `K` batches with
`∑_{i ∈ [ℓ_W, ℓ), Λ_i < v, i ∉ E} B_i ≤ K e^v`: `E` holds the last such batch `e(c)` in which
each arm is pulled, and an arm is pulled in the others at most `N_c(t_(e(c)-1)) < e^v` times. -/
lemma exists_card_le_sum_low_le {K' : ℕ} (gr : Grid K') {Λ : ℕ → ℝ} {lW ℓ : ℕ}
    (hlW : 1 ≤ lW)
    (hW2 : ∀ i, lW ≤ i → i < ℓ → ∀ c, pullCount A c (gr.t (i - 1)) ω <
      pullCount A c (gr.t i) ω → Real.log (pullCount A c (gr.t (i - 1)) ω) ≤ Λ i)
    {v : ℝ} :
    ∃ E : Finset ℕ, E.card ≤ Fintype.card β ∧
      ∑ i ∈ (Finset.Ico lW ℓ).filter (fun i ↦ Λ i < v ∧ i ∉ E),
        ((gr.t i : ℝ) - gr.t (i - 1)) ≤ Fintype.card β * Real.exp v := by
  set Lo := (Finset.Ico lW ℓ).filter fun i ↦ Λ i < v with hLo
  set d : β → ℕ → ℕ := fun c i ↦
    pullCount A c (gr.t i) ω - pullCount A c (gr.t (i - 1)) ω with hd
  set Pc : β → Finset ℕ := fun c ↦ Lo.filter fun i ↦ 0 < d c i with hPc
  set e : β → ℕ := fun c ↦ (Pc c).sup id with he
  set E := (Finset.univ.filter fun c ↦ (Pc c).Nonempty).image e with hE
  refine ⟨E, (Finset.card_image_le).trans ((Finset.card_filter_le _ _).trans
    (by rw [Finset.card_univ])), ?_⟩
  -- the mass is the sum of the increments
  have hmass : ∑ i ∈ (Finset.Ico lW ℓ).filter (fun i ↦ Λ i < v ∧ i ∉ E),
      ((gr.t i : ℝ) - gr.t (i - 1)) =
      ∑ c, ∑ i ∈ (Finset.Ico lW ℓ).filter (fun i ↦ Λ i < v ∧ i ∉ E), (d c i : ℝ) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi1 : 1 ≤ i := by have := (Finset.mem_Ico.mp (Finset.mem_filter.mp hi).1).1; omega
    have hle : gr.t (i - 1) ≤ gr.t i := gr.strictMono.monotone (by omega)
    have h := t_sub_eq_sum_pullCount_sub (A := A) (ω := ω) gr hi1
    rw [← Nat.cast_sub hle, h]
    push_cast
    rfl
  rw [hmass]
  rw [show (Fintype.card β : ℝ) * Real.exp v = ∑ _c : β, Real.exp v by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]]
  refine Finset.sum_le_sum fun c _ ↦ ?_
  rcases (Pc c).eq_empty_or_nonempty with hempty | hne
  · -- `c` is not pulled in the low batches
    have : ∀ i ∈ (Finset.Ico lW ℓ).filter (fun i ↦ Λ i < v ∧ i ∉ E), d c i = 0 := by
      intro i hi
      obtain ⟨hiI, hiv, -⟩ := Finset.mem_filter.mp hi
      by_contra hne
      have : i ∈ Pc c := Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hiI, hiv⟩,
        Nat.pos_of_ne_zero hne⟩
      rw [hempty] at this
      exact absurd this (Finset.notMem_empty i)
    rw [Finset.sum_eq_zero fun i hi ↦ by rw [this i hi, Nat.cast_zero]]
    exact (Real.exp_pos v).le
  · -- the last low batch `e(c)` in which `c` is pulled
    have hecmem : e c ∈ Pc c := by
      obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (Pc c) id hne
      have : e c = m := le_antisymm (Finset.sup_le fun i hi ↦ hmax i hi)
        (Finset.le_sup (f := id) hm)
      rw [this]
      exact hm
    have hecE : e c ∈ E := Finset.mem_image.mpr
      ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ c, hne⟩, rfl⟩
    obtain ⟨hecLo, hecd⟩ := Finset.mem_filter.mp hecmem
    obtain ⟨hecI, hecv⟩ := Finset.mem_filter.mp hecLo
    have hecI' := Finset.mem_Ico.mp hecI
    -- (W2) at `e(c)`: `N_c(t_(e(c)-1)) < e^v`
    have hW := hW2 (e c) hecI'.1 hecI'.2 c (by simp only [hd] at hecd; omega)
    have hN : (pullCount A c (gr.t (e c - 1)) ω : ℝ) < Real.exp v := by
      rcases Nat.eq_zero_or_pos (pullCount A c (gr.t (e c - 1)) ω) with h0 | h0
      · rw [h0, Nat.cast_zero]
        exact Real.exp_pos v
      · have h0' : (0 : ℝ) < pullCount A c (gr.t (e c - 1)) ω := by exact_mod_cast h0
        calc (pullCount A c (gr.t (e c - 1)) ω : ℝ)
            = Real.exp (Real.log (pullCount A c (gr.t (e c - 1)) ω)) := (Real.exp_log h0').symm
          _ < Real.exp v := Real.exp_lt_exp.mpr (hW.trans_lt hecv)
    -- the other low batches in which `c` is pulled lie in `[ℓ_W, e(c))`
    have hsub : ∑ i ∈ (Finset.Ico lW ℓ).filter (fun i ↦ Λ i < v ∧ i ∉ E), d c i ≤
        ∑ i ∈ Finset.Ico lW (e c), d c i := by
      rw [← Finset.sum_filter_add_sum_filter_not ((Finset.Ico lW ℓ).filter
        (fun i ↦ Λ i < v ∧ i ∉ E)) (fun i ↦ 0 < d c i)]
      have h0 : ∑ i ∈ ((Finset.Ico lW ℓ).filter (fun i ↦ Λ i < v ∧ i ∉ E)).filter
          (fun i ↦ ¬ 0 < d c i), d c i = 0 :=
        Finset.sum_eq_zero fun i hi ↦ by
          have := (Finset.mem_filter.mp hi).2
          omega
      rw [h0, add_zero]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ ↦ Nat.zero_le _
      intro i hi
      obtain ⟨hi1, hdi⟩ := Finset.mem_filter.mp hi
      obtain ⟨hiI, hiv, hiE⟩ := Finset.mem_filter.mp hi1
      have hiP : i ∈ Pc c := Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hiI, hiv⟩, hdi⟩
      have hile : i ≤ e c := Finset.le_sup (f := id) hiP
      have hine : i ≠ e c := fun h ↦ hiE (h ▸ hecE)
      exact Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hiI).1, lt_of_le_of_ne hile hine⟩
    have htel := sum_Ico_pullCount_sub_le (A := A) (ω := ω) gr c hecI'.1
    have : (∑ i ∈ (Finset.Ico lW ℓ).filter (fun i ↦ Λ i < v ∧ i ∉ E), d c i : ℕ) ≤
        pullCount A c (gr.t (e c - 1)) ω := hsub.trans htel
    calc ∑ i ∈ (Finset.Ico lW ℓ).filter (fun i ↦ Λ i < v ∧ i ∉ E), (d c i : ℝ)
        = ((∑ i ∈ (Finset.Ico lW ℓ).filter (fun i ↦ Λ i < v ∧ i ∉ E), d c i : ℕ) : ℝ) := by
          push_cast
          rfl
      _ ≤ pullCount A c (gr.t (e c - 1)) ω := by exact_mod_cast this
      _ ≤ Real.exp v := hN.le

end LowMass

end Incognita.BatchedBandits
