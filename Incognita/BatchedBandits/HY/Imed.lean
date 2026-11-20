/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.HY.KInf

/-! # IMED rounds of HY

[INC-P000, Lemma `lem:imedround`], for every history with rewards in `[0, 1]` (no probability).
At a round `n` of an IMED phase, HY pulls `HY.imedArm w₀ y h r` with `y = y_ℓ` and the statistics
at the cutoff `r = t_ℓ`; the paper's round is `t = n + 1`, and its `N_c(t - 1)` is
`pullCount' n h c`.

* `HY.imedKinf_leader`: `K̃_ℓ(ĉ_ℓ) = 0` (Step 1).
* `HY.imedIndex_imedArm_lt`: if the pulled arm `c` is not the leader, its index is
  `J_ℓ(c, t) < y_ℓ log t` (Steps 1–2); `HY.imedKinf_imedArm_ne_top`: then `K̃_ℓ(c) < ∞` (for
  `N_c(t - 1) ≥ 1`); `HY.mul_toReal_imedKinf_add_lt`: the real form
  `N_c(t - 1) K̃_ℓ(c) + y_ℓ log N_c(t - 1) < y_ℓ log t`.
* `HY.pseudoKinf_pos_and_le_mul_pseudoKinf`: Lemma `lem:highC`, evidence in a high batch, with (W1)
  as a hypothesis.
* `HY.imedIndex_imedArm_le`: the IMED arm minimises the index (the hypothesis (min) of the
  water-level lemma `lem:W`, `Incognita.BatchedBandits.log_div_card_le_index`).
* `HY.pullCount'_pacedArm_lt_target`, `HY.target_le_pullCount'_of_pacedArm_eq`: the paced rule
  satisfies the hypotheses (rule) and (idle) of the queue lemma `lem:service`
  (`Incognita.BatchedBandits.backlog_le`).
* `pullCount_le_max_of_forall`: the consequence (Step 3), for any sequence of actions: if every
  pull of `c` at a round `k ∈ [a, b)` has `N_c(k) D < g(k)` (`g` nondecreasing, `D > 0`), then
  `N_c(b) ≤ max(N_c(a), 1 + g(b - 1) / D)`; with `g(k) = y_ℓ log (k + 1)`, `a = t_ℓ` and `b = t'`
  this is the paper's `N_c(t') ≤ max(N_c(t_ℓ), 1 + y_ℓ log t' / D)`. It is the case
  `g'(k) = 1 + g(k) / D` of `pullCount_le_max_of_forall_add_one` (`N_c(k) + 1 ≤ g'(k)` at every
  pull; and `N_c(b) ≤ g'(b - 1)` when `c` is pulled in `[a, b)`, used by Lemma `lem:pullsC`).
-/

@[expose] public section

open Learning Finset

open scoped ENNReal

namespace Incognita.BatchedBandits

namespace HY

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} {h : Hist Unit α ℝ n} {r : ℕ}

omit [Fintype α] in
/-- The current count is at most the number of rounds. -/
lemma pullCount'_le (c : α) : pullCount' n h c ≤ n :=
  (Finset.card_filter_le _ _).trans_eq (by simp)

omit [Fintype α] in
/-- For rewards in `[0, 1]` and `w₀ ≥ 0`, the pseudo-mean is at most `1`. -/
lemma pseudoMean_le_one {w₀ : ℝ} (hw₀ : 0 ≤ w₀) (hfb : ∀ i, (h i).feedback ∈ Set.Icc (0 : ℝ) 1)
    (c : α) : pseudoMean w₀ h r c ≤ 1 := by
  unfold pseudoMean
  have hden : 0 ≤ (count h r c : ℝ) + w₀ := by positivity
  rcases hden.eq_or_lt with h0 | h0
  · rw [← h0, div_zero]
    exact zero_le_one
  rw [div_le_one h0]
  have : ∑ i, ind h r c i * (h i).feedback ≤ ∑ i, ind h r c i :=
    Finset.sum_le_sum fun i _ ↦ by
      have := ind_nonneg (h := h) (r := r) (c := c) i
      nlinarith [(hfb i).2]
  rw [← count_eq_sum_ind] at this
  linarith

variable [Nonempty α]

/-- [INC-P000, proof of Lemma `lem:imedround`, Step 1] The IMED divergence of the leader is `0`:
by Lemma `lem:kinf`(ii) if its pseudo-mean is `< 1`, by the convention if it is `1`. -/
lemma imedKinf_leader {w₀ : ℝ} (hw₀ : 0 ≤ w₀) (hfb : ∀ i, (h i).feedback ∈ Set.Icc (0 : ℝ) 1)
    (hpos : 0 < (count h r (leader w₀ h r) : ℝ) + w₀) :
    imedKinf w₀ h r (leader w₀ h r) = 0 := by
  unfold imedKinf
  by_cases hμ : pseudoMean w₀ h r (leader w₀ h r) < 1
  · exact pseudoKinf_eq_zero_of_le_pseudoMean hw₀ hμ (fun i ↦ (hfb i).2) hpos le_rfl
  · have h1 : pseudoMean w₀ h r (leader w₀ h r) = 1 :=
      le_antisymm (pseudoMean_le_one hw₀ hfb _) (not_lt.mp hμ)
    simp [pseudoKinf, h1]

/-- The IMED index of the leader is `y log N_ĉ(t - 1)`. -/
lemma imedIndex_leader {w₀ y : ℝ} (hw₀ : 0 ≤ w₀)
    (hfb : ∀ i, (h i).feedback ∈ Set.Icc (0 : ℝ) 1)
    (hpos : 0 < (count h r (leader w₀ h r) : ℝ) + w₀) :
    imedIndex w₀ y h r (leader w₀ h r) =
      ((y * Real.log (pullCount' n h (leader w₀ h r)) : ℝ) : EReal) := by
  simp [imedIndex, imedKinf_leader hw₀ hfb hpos]

/-- [INC-P000, Lemma `lem:imedround`, Steps 1–2] If the arm pulled at an IMED round is not the
leader, its index is below `y log t`, `t = n + 1`: the leader has index
`y log N_ĉ(t - 1) ≤ y log (t - 1) < y log t`, and it is not a minimiser. -/
lemma imedIndex_imedArm_lt {w₀ y : ℝ} (hw₀ : 0 ≤ w₀) (hy : 0 < y)
    (hfb : ∀ i, (h i).feedback ∈ Set.Icc (0 : ℝ) 1)
    (hpos : 0 < (count h r (leader w₀ h r) : ℝ) + w₀) (hn : 1 ≤ n)
    (hne : imedArm w₀ y h r ≠ leader w₀ h r) :
    imedIndex w₀ y h r (imedArm w₀ y h r) < ((y * Real.log (n + 1) : ℝ) : EReal) := by
  -- the index of the leader
  have hlead : imedIndex w₀ y h r (leader w₀ h r) < ((y * Real.log (n + 1) : ℝ) : EReal) := by
    rw [imedIndex_leader hw₀ hfb hpos, EReal.coe_lt_coe_iff]
    refine mul_lt_mul_of_pos_left ?_ hy
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hN : Real.log (pullCount' n h (leader w₀ h r)) ≤ Real.log n := by
      rcases Nat.eq_zero_or_pos (pullCount' n h (leader w₀ h r)) with h0 | h0
      · rw [h0, Nat.cast_zero, Real.log_zero]
        exact Real.log_nonneg (by exact_mod_cast hn)
      · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast pullCount'_le _)
    exact hN.trans_lt (Real.log_lt_log hn0 (by linarith))
  unfold imedArm at hne ⊢
  split_ifs at hne ⊢ with hall
  · exact absurd rfl hne
  · simp only [not_forall, not_le] at hall
    obtain ⟨c', hc'⟩ := hall
    have hmin := isMinOn_argmin (fun c ↦ imedIndex w₀ y h r c) (Set.mem_univ c')
    exact (hmin.trans_lt hc').trans hlead

/-- [INC-P000, Lemma `lem:imedround`] If the arm `c` pulled at an IMED round is not the leader
and `N_c(t - 1) ≥ 1`, then `K̃_ℓ(c) < ∞`. -/
lemma imedKinf_imedArm_ne_top {w₀ y : ℝ} (hw₀ : 0 ≤ w₀) (hy : 0 < y)
    (hfb : ∀ i, (h i).feedback ∈ Set.Icc (0 : ℝ) 1)
    (hpos : 0 < (count h r (leader w₀ h r) : ℝ) + w₀) (hn : 1 ≤ n)
    (hne : imedArm w₀ y h r ≠ leader w₀ h r) (hN : 1 ≤ pullCount' n h (imedArm w₀ y h r)) :
    imedKinf w₀ h r (imedArm w₀ y h r) ≠ ⊤ := by
  intro htop
  have hlt := imedIndex_imedArm_lt hw₀ hy hfb hpos hn hne
  have hN0 : (pullCount' n h (imedArm w₀ y h r) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (show pullCount' n h (imedArm w₀ y h r) ≠ 0 by omega)
  rw [imedIndex, htop, ENNReal.mul_top hN0, EReal.coe_ennreal_top, EReal.top_add_coe] at hlt
  exact not_top_lt hlt

/-- [INC-P000, Lemma `lem:imedround`, the real form] If the arm `c` pulled at an IMED round is not
the leader and `N_c(t - 1) ≥ 1`, then `N_c(t - 1) K̃_ℓ(c) + y log N_c(t - 1) < y log t`. -/
lemma mul_toReal_imedKinf_add_lt {w₀ y : ℝ} (hw₀ : 0 ≤ w₀) (hy : 0 < y)
    (hfb : ∀ i, (h i).feedback ∈ Set.Icc (0 : ℝ) 1)
    (hpos : 0 < (count h r (leader w₀ h r) : ℝ) + w₀) (hn : 1 ≤ n)
    (hne : imedArm w₀ y h r ≠ leader w₀ h r) (hN : 1 ≤ pullCount' n h (imedArm w₀ y h r)) :
    (pullCount' n h (imedArm w₀ y h r) : ℝ) * (imedKinf w₀ h r (imedArm w₀ y h r)).toReal +
        y * Real.log (pullCount' n h (imedArm w₀ y h r)) < y * Real.log (n + 1) := by
  have hlt := imedIndex_imedArm_lt hw₀ hy hfb hpos hn hne
  have hfin := imedKinf_imedArm_ne_top hw₀ hy hfb hpos hn hne hN
  rw [imedIndex] at hlt
  have hprod : ((pullCount' n h (imedArm w₀ y h r) : ℝ≥0∞) *
      imedKinf w₀ h r (imedArm w₀ y h r) : ℝ≥0∞) =
      ENNReal.ofReal ((pullCount' n h (imedArm w₀ y h r) : ℝ) *
        (imedKinf w₀ h r (imedArm w₀ y h r)).toReal) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
      ENNReal.ofReal_toReal hfin]
  have hnn : 0 ≤ (pullCount' n h (imedArm w₀ y h r) : ℝ) *
      (imedKinf w₀ h r (imedArm w₀ y h r)).toReal := by positivity
  rw [hprod, EReal.coe_ennreal_ofReal, max_eq_left hnn, ← EReal.coe_add,
    EReal.coe_lt_coe_iff] at hlt
  exact hlt

omit [Fintype α] [Nonempty α] in
/-- For rewards `≥ 0` and `w₀ ≥ 0`, the pseudo-mean is nonnegative. -/
lemma pseudoMean_nonneg {w₀ : ℝ} (hw₀ : 0 ≤ w₀) (hfb : ∀ i, (h i).feedback ∈ Set.Icc (0 : ℝ) 1)
    (c : α) : 0 ≤ pseudoMean w₀ h r c := by
  unfold pseudoMean
  exact div_nonneg (Finset.sum_nonneg fun i _ ↦ mul_nonneg (ind_nonneg i) (hfb i).1)
    (by positivity)

@[deprecated (since := "2026-11-19")] alias pseudoMean_nonneg' := pseudoMean_nonneg

/-- [INC-P000, Lemma `lem:highC`] Evidence in a high batch, for the statistics of HY at the cutoff
`r = t_(i-1)`: let `r' ∈ [m̃⋆_(i-1), 1)`, `D = 𝒦_inf(ν̃_c(t_(i-1)), r')`, `y = y_(i-1) ≥ 1`, and an
arm `c` whose count `N = N_c(t_i)` satisfies `1 ≤ N ≤ N̄` and (W1) at the level `v`,
`N K̃_(i-1)(c) / y ≥ v - log N` (the paper's `v ≤ Λ_i ≤ N K̃/y + log N`). If `Y = v - log N̄ > 0`,
then `0 < D ≤ κ(r')` and `N D ≥ Y`. -/
lemma pseudoKinf_pos_and_le_mul_pseudoKinf {w₀ : ℝ} (hw₀ : 0 ≤ w₀)
    (hfb : ∀ i, (h i).feedback ∈ Set.Icc (0 : ℝ) 1) {c : α} (hpos : 0 < (count h r c : ℝ) + w₀)
    {r' : ℝ} (hr' : r' < 1)
    (hlead : pseudoMean w₀ h r (leader w₀ h r) ≤ r') {N : ℕ} (hN1 : 1 ≤ N) {Nbar y v : ℝ}
    (hy : 1 ≤ y) (hNb : (N : ℝ) ≤ Nbar) (hY : 0 < v - Real.log Nbar)
    (hW1 : ENNReal.ofReal (v - Real.log N) ≤ (N : ℝ≥0∞) * imedKinf w₀ h r c / ENNReal.ofReal y) :
    0 < pseudoKinf w₀ h r c r' ∧
      pseudoKinf w₀ h r c r' ≤ ENNReal.ofReal (Real.log (1 / (1 - r'))) ∧
      ENNReal.ofReal (v - Real.log Nbar) ≤ (N : ℝ≥0∞) * pseudoKinf w₀ h r c r' := by
  have hμ0 := pseudoMean_nonneg (r := r) hw₀ hfb (leader w₀ h r)
  have hr'0 : 0 ≤ r' := hμ0.trans hlead
  -- `K̃_(i-1)(c) ≤ D`, Lemma `lem:kinf`(iii)
  have hKD : imedKinf w₀ h r c ≤ pseudoKinf w₀ h r c r' :=
    pseudoKinf_mono hw₀ hμ0 hlead hr' hfb
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hlog : Real.log N ≤ Real.log Nbar := Real.log_le_log (by linarith) hNb
  have hdiv : (N : ℝ≥0∞) * imedKinf w₀ h r c / ENNReal.ofReal y ≤
      (N : ℝ≥0∞) * imedKinf w₀ h r c := by
    refine ENNReal.div_le_of_le_mul ?_
    calc (N : ℝ≥0∞) * imedKinf w₀ h r c = (N : ℝ≥0∞) * imedKinf w₀ h r c * 1 := (mul_one _).symm
      _ ≤ (N : ℝ≥0∞) * imedKinf w₀ h r c * ENNReal.ofReal y := by
          gcongr
          exact ENNReal.one_le_ofReal.mpr hy
  have hmain : ENNReal.ofReal (v - Real.log Nbar) ≤ (N : ℝ≥0∞) * pseudoKinf w₀ h r c r' :=
    calc ENNReal.ofReal (v - Real.log Nbar) ≤ ENNReal.ofReal (v - Real.log N) :=
          ENNReal.ofReal_le_ofReal (by linarith)
      _ ≤ _ := hW1
      _ ≤ (N : ℝ≥0∞) * imedKinf w₀ h r c := hdiv
      _ ≤ _ := by gcongr
  refine ⟨?_, pseudoKinf_le_ofReal_log hw₀ hr' hr'0 hfb hpos, hmain⟩
  refine pos_iff_ne_zero.mpr fun hD ↦ ?_
  rw [hD, mul_zero, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hmain
  linarith

@[deprecated (since := "2026-11-19")] alias highC := pseudoKinf_pos_and_le_mul_pseudoKinf

/-- **The IMED rule** [INC-P000, Definition `def:hy`, IMED phase; the hypothesis (min) of
Lemma `lem:W`]: the arm of the IMED phase minimises the IMED index `J_ℓ(·, t)`. -/
lemma imedIndex_imedArm_le {w₀ y : ℝ} (c : α) :
    imedIndex w₀ y h r (imedArm w₀ y h r) ≤ imedIndex w₀ y h r c := by
  unfold imedArm
  split_ifs with hall
  · exact hall c
  · exact isMinOn_argmin (fun c ↦ imedIndex w₀ y h r c) (Set.mem_univ c)

/-- **The paced rule, demanding arm** [INC-P000, Definition `def:hy`, (7); the hypothesis (rule)
of Lemma `lem:service`]: if the arm of the paced phase is not the leader, its current count is
below its target. -/
lemma pullCount'_pacedArm_lt_target {w₀ thr ω y logt : ℝ} {U Unext : ℕ}
    (hne : pacedArm w₀ thr ω y logt h r U Unext ≠ leader w₀ h r) :
    pullCount' n h (pacedArm w₀ thr ω y logt h r U Unext) <
      target w₀ thr ω y logt h r U Unext (pacedArm w₀ thr ω y logt h r U Unext) := by
  unfold pacedArm at hne ⊢
  split_ifs at hne ⊢ with hex
  · obtain ⟨c, hc⟩ := hex
    set f : α → EReal := fun c ↦ if c ≠ leader w₀ h r ∧
      pullCount' n h c < target w₀ thr ω y logt h r U Unext c
      then ((-((Fintype.equivFin α c : ℕ) : ℝ) : ℝ) : EReal) else ⊥ with hf
    have hmax := isMaxOn_argmax f (Set.mem_univ c)
    have hfc : f c ≠ ⊥ := by
      simp only [hf, ite_eq_left hc]
      exact EReal.coe_ne_bot _
    have hfa : f (argmax f) ≠ ⊥ := fun h ↦ hfc (le_bot_iff.mp (h ▸ hmax))
    by_contra hcon
    apply hfa
    simp only [hf]
    exact ite_eq_right fun h ↦ hcon h.2
  · exact absurd rfl hne

/-- **The paced rule, leader** [INC-P000, Definition `def:hy`, (7); the hypothesis (idle) of
Lemma `lem:service`]: if the arm of the paced phase is the leader, no other arm is below its
target. -/
lemma target_le_pullCount'_of_pacedArm_eq {w₀ thr ω y logt : ℝ} {U Unext : ℕ}
    (heq : pacedArm w₀ thr ω y logt h r U Unext = leader w₀ h r) {c : α}
    (hc : c ≠ leader w₀ h r) :
    target w₀ thr ω y logt h r U Unext c ≤ pullCount' n h c := by
  by_contra hlt
  have hlt := not_le.mp hlt
  have hne : pacedArm w₀ thr ω y logt h r U Unext ≠ leader w₀ h r := by
    unfold pacedArm
    rw [ite_eq_left ⟨c, hc, hlt⟩]
    intro hargmax
    set f : α → EReal := fun c ↦ if c ≠ leader w₀ h r ∧
      pullCount' n h c < target w₀ thr ω y logt h r U Unext c
      then ((-((Fintype.equivFin α c : ℕ) : ℝ) : ℝ) : EReal) else ⊥ with hf
    have hmax := isMaxOn_argmax f (Set.mem_univ c)
    have hfc : f c ≠ ⊥ := by
      simp only [hf, ite_eq_left (And.intro hc hlt)]
      exact EReal.coe_ne_bot _
    have hfa : f (argmax f) ≠ ⊥ := fun h ↦ hfc (le_bot_iff.mp (h ▸ hmax))
    apply hfa
    simp only [hf]
    exact ite_eq_right fun h ↦ h.1 hargmax
  exact hne heq

end HY

/-- [INC-P000, proof of Lemma `lem:pullsC`, the last pull, general form] For a sequence of
actions `A` and an arm `c`, if every pull of `c` at a round `k ∈ [a, b)` has `N_c(k) + 1 ≤ g(k)`
with `g` nondecreasing, then `N_c(b) ≤ max(N_c(a), g(b - 1))`; if moreover `c` is pulled at some
round of `[a, b)`, then `N_c(b) ≤ g(b - 1)` (at the last pull `k`, `N_c(b) = N_c(k) + 1`). -/
lemma pullCount_le_max_of_forall_add_one {β Ω : Type*} [DecidableEq β] {A : ℕ → Ω → β} {c : β}
    {ω : Ω} {g : ℕ → ℝ} (hg : Monotone g) {a b : ℕ} (hab : a ≤ b)
    (hpull : ∀ k, a ≤ k → k < b → A k ω = c → (pullCount A c k ω : ℝ) + 1 ≤ g k) :
    (pullCount A c b ω : ℝ) ≤ max (pullCount A c a ω : ℝ) (g (b - 1)) ∧
      ((∃ k, a ≤ k ∧ k < b ∧ A k ω = c) → (pullCount A c b ω : ℝ) ≤ g (b - 1)) := by
  induction b, hab using Nat.le_induction with
  | base =>
    exact ⟨le_max_left _ _, fun ⟨k, hk1, hk2, _⟩ ↦ absurd (hk1.trans_lt hk2) (lt_irrefl _)⟩
  | succ b hb ih =>
    obtain ⟨ih1, ih2⟩ := ih fun k hk1 hk2 hAk ↦ hpull k hk1 (by omega) hAk
    have hgb : g (b - 1) ≤ g (b + 1 - 1) := hg (by omega)
    rw [pullCount_add_one, show b + 1 - 1 = b by omega] at *
    by_cases hA : A b ω = c
    · rw [ite_eq_left hA]
      have h1 := hpull b hb (by omega) hA
      push_cast
      exact ⟨le_max_of_le_right h1, fun _ ↦ h1⟩
    · rw [ite_eq_right hA, add_zero]
      refine ⟨ih1.trans (max_le_max le_rfl hgb), fun ⟨k, hk1, hk2, hAk⟩ ↦ ?_⟩
      have hkb : k < b := lt_of_le_of_ne (by omega) fun h ↦ hA (h ▸ hAk)
      exact (ih2 ⟨k, hk1, hkb, hAk⟩).trans hgb

/-- [INC-P000, proof of Lemma `lem:imedround`, Step 3, general form] For a sequence of actions
`A` and an arm `c`, if every pull of `c` at a round `k ∈ [a, b)` has `N_c(k) D < g(k)`, with
`D > 0` and `g` nondecreasing, then `N_c(b) ≤ max(N_c(a), 1 + g(b - 1) / D)`: the case
`g'(k) = 1 + g(k) / D` of `pullCount_le_max_of_forall_add_one`. -/
lemma pullCount_le_max_of_forall {β Ω : Type*} [DecidableEq β] {A : ℕ → Ω → β} {c : β}
    {ω : Ω} {D : ℝ} (hD : 0 < D) {g : ℕ → ℝ} (hg : Monotone g) {a b : ℕ} (hab : a ≤ b)
    (hpull : ∀ k, a ≤ k → k < b → A k ω = c → (pullCount A c k ω : ℝ) * D < g k) :
    (pullCount A c b ω : ℝ) ≤ max (pullCount A c a ω : ℝ) (1 + g (b - 1) / D) :=
  (pullCount_le_max_of_forall_add_one (g := fun k ↦ 1 + g k / D)
    (fun _ _ h ↦ add_le_add_right (div_le_div_of_nonneg_right (hg h) hD.le) 1) hab
    fun k hk hkb hA ↦ by
      have := (lt_div_iff₀ hD).mpr (hpull k hk hkb hA)
      linarith).1

end Incognita.BatchedBandits
