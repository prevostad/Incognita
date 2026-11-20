/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import LMLExplore.Analysis.SpecialFunctions.Log.Basic
public import LeanMachineLearning.SequentialLearning.FiniteActions
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.EReal.Basic

/-! # The IMED phase lifts the water level

[INC-P000, Lemma `lem:W`, Steps 1–2], in an abstract form. A sequence of actions `A` (at a fixed
`ω`; the paper's round `t ≥ 1` pulls `A (t - 1) ω`, and `N_c(t) = pullCount A c t ω`) runs a batch
on the rounds `(r, T]`, whose rounds `(r, s]`, `s ≤ T`, are IMED rounds. The indices
`I_t(c) ∈ EReal` (the paper's `N_c(t - 1) K̃_(j-1)(c) / y_(j-1) + log N_c(t - 1)`) satisfy

* (mono) `t ↦ I_t(c)` is nondecreasing on `(r, T + 1]`;
* (min) at an IMED round `t`, the pulled arm minimises `I_t`;
* (log) `I_t(c) ≥ y log N_c(t - 1)` for a factor `y ≥ 0`.

The indices of HY are `J_t(c) = y I_t(c)` with `y = y_(j-1)`; the lemmas are stated for indices
bounded below by `y log N` so that they apply to `J` directly. The water level of the batch is
`Λ = min_c I_(T+1)(c)` (the paper's, for `J / y`); the statements bound every `I_(T+1)(c')` from
below, which is a bound on `Λ`.

* `log_pullCount_le_index`: (W2) at the IMED rounds, `y log N_c(r) ≤ I_(T+1)(c')` for every arm
  `c` pulled at an IMED round and every arm `c'`.
* `log_div_card_le_index`: Step 2 of the proof of Lemma `lem:W`(ii), if every count at `r` is at
  least `1`, then `y log ((s - r) / K) ≤ I_(T+1)(c')` for every arm `c'`.
-/

@[expose] public section

open Learning Finset

namespace Incognita.BatchedBandits

variable {β Ω : Type*} [DecidableEq β] {A : ℕ → Ω → β} {ω : Ω}

@[deprecated (since := "2026-11-19")]
alias log_natCast_le_log_natCast := Real.log_natCast_le_log_natCast

/-- [INC-P000, proof of Lemma `lem:W`, Step 1] (W2) at the IMED rounds: an arm `c` pulled at an
IMED round `t ∈ (r, s]` has `y log N_c(r) ≤ I_(T+1)(c')` for every arm `c'`:
`y log N_c(r) ≤ y log N_c(t - 1) ≤ I_t(c) ≤ I_t(c') ≤ I_(T+1)(c')`. -/
lemma log_pullCount_le_index {I : β → ℕ → EReal} {r s T : ℕ} (hsT : s ≤ T) {y : ℝ}
    (hy : 0 ≤ y)
    (hmono : ∀ c t t', r < t → t ≤ t' → t' ≤ T + 1 → I c t ≤ I c t')
    (hmin : ∀ t, r < t → t ≤ s → ∀ c', I (A (t - 1) ω) t ≤ I c' t)
    (hlog : ∀ c t, r < t → t ≤ T + 1 →
      ((y * Real.log (pullCount A c (t - 1) ω) : ℝ) : EReal) ≤ I c t)
    {t : ℕ} (hrt : r < t) (hts : t ≤ s) (c' : β) :
    ((y * Real.log (pullCount A (A (t - 1) ω) r ω) : ℝ) : EReal) ≤ I c' (T + 1) := by
  have hcount : pullCount A (A (t - 1) ω) r ω ≤ pullCount A (A (t - 1) ω) (t - 1) ω :=
    pullCount_mono _ (by omega) _
  calc ((y * Real.log (pullCount A (A (t - 1) ω) r ω) : ℝ) : EReal)
      ≤ ((y * Real.log (pullCount A (A (t - 1) ω) (t - 1) ω) : ℝ) : EReal) :=
        EReal.coe_le_coe_iff.mpr (mul_le_mul_of_nonneg_left
          (Real.log_natCast_le_log_natCast hcount) hy)
    _ ≤ I (A (t - 1) ω) t := hlog _ t hrt (by omega)
    _ ≤ I c' t := hmin t hrt hts c'
    _ ≤ I c' (T + 1) := hmono c' t (T + 1) hrt (by omega) le_rfl

/-- The pulls of `c` in the rounds `(r, s]` (indices `[r, s)`): `N_c(s) - N_c(r)`. -/
lemma pullCount_sub_eq_card {c : β} {r s : ℕ} (hrs : r ≤ s) :
    pullCount A c s ω - pullCount A c r ω =
      ((Finset.Ico r s).filter fun u ↦ A u ω = c).card := by
  rw [pullCount_eq_sum, pullCount_eq_sum, ← Finset.sum_range_add_sum_Ico _ hrs,
    Nat.add_sub_cancel_left, Finset.card_filter]

/-- [INC-P000, proof of Lemma `lem:W`, Step 2] If the rounds `(r, s]` are IMED rounds, `r < s`,
and every count at `r` is at least `1`, then `y log ((s - r) / K) ≤ I_(T+1)(c')` for every arm
`c'` (`K` arms): some arm `c⋆` is pulled at least `(s - r)/K` times in `(r, s]`; at its last
pull `t⋆`, `N_(c⋆)(t⋆ - 1) ≥ (s - r)/K` and `c⋆` minimises `I_(t⋆)`. -/
lemma log_div_card_le_index [Fintype β] [Nonempty β] {I : β → ℕ → EReal} {r s T : ℕ}
    (hrs : r < s) (hsT : s ≤ T) {y : ℝ} (hy : 0 ≤ y)
    (hmono : ∀ c t t', r < t → t ≤ t' → t' ≤ T + 1 → I c t ≤ I c t')
    (hmin : ∀ t, r < t → t ≤ s → ∀ c', I (A (t - 1) ω) t ≤ I c' t)
    (hlog : ∀ c t, r < t → t ≤ T + 1 →
      ((y * Real.log (pullCount A c (t - 1) ω) : ℝ) : EReal) ≤ I c t)
    (hN1 : ∀ c, 1 ≤ pullCount A c r ω) (c' : β) :
    ((y * Real.log (((s - r : ℕ) : ℝ) / Fintype.card β) : ℝ) : EReal) ≤ I c' (T + 1) := by
  have hK : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  -- the counts in the IMED rounds sum to `s - r`
  have hsum : ∑ c, (((Finset.Ico r s).filter fun u ↦ A u ω = c).card : ℝ) = (s - r : ℕ) := by
    have := Finset.card_eq_sum_card_fiberwise (f := fun u ↦ A u ω) (s := Finset.Ico r s)
      (t := Finset.univ) (fun _ _ ↦ Finset.mem_univ _)
    rw [Nat.card_Ico] at this
    exact_mod_cast this.symm
  -- pigeonhole
  obtain ⟨cs, -, hcs⟩ : ∃ cs ∈ (Finset.univ : Finset β),
      ((s - r : ℕ) : ℝ) / Fintype.card β ≤
        (((Finset.Ico r s).filter fun u ↦ A u ω = cs).card : ℝ) := by
    refine Finset.exists_le_of_sum_le Finset.univ_nonempty ?_
    rw [hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    exact le_rfl
  set F := (Finset.Ico r s).filter fun u ↦ A u ω = cs with hF
  have hFpos : 0 < F.card := by
    have : (0 : ℝ) < ((s - r : ℕ) : ℝ) / Fintype.card β :=
      div_pos (by exact_mod_cast (show 0 < s - r by omega)) hK
    exact_mod_cast this.trans_le hcs
  have hFne : F.Nonempty := Finset.card_pos.mp hFpos
  set k := F.max' hFne with hk
  have hkF : k ∈ F := F.max'_mem hFne
  have hk' := Finset.mem_filter.mp hkF
  have hkIco := Finset.mem_Ico.mp hk'.1
  -- no pull of `cs` after `k` in the IMED rounds, so `N(k) = N(s) - 1`
  have hafter : pullCount A cs s ω = pullCount A cs (k + 1) ω := by
    have h := pullCount_sub_eq_card (A := A) (ω := ω) (c := cs) (show k + 1 ≤ s by omega)
    have hzero : ((Finset.Ico (k + 1) s).filter fun u ↦ A u ω = cs).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro u hu hAu
      have huF : u ∈ F := Finset.mem_filter.mpr
        ⟨Finset.mem_Ico.mpr ⟨by have := (Finset.mem_Ico.mp hu).1; omega,
          (Finset.mem_Ico.mp hu).2⟩, hAu⟩
      have := F.le_max' u huF
      have := (Finset.mem_Ico.mp hu).1
      omega
    have hmono' : pullCount A cs (k + 1) ω ≤ pullCount A cs s ω := pullCount_mono _ (by omega) _
    omega
  have hstep : pullCount A cs (k + 1) ω = pullCount A cs k ω + 1 := by
    rw [pullCount_add_one, ite_eq_left hk'.2]
  have hcount := pullCount_sub_eq_card (A := A) (ω := ω) (c := cs) hrs.le
  have hNr := hN1 cs
  -- `N_(cs)(k) ≥ (s - r) / K`
  have hNk : ((s - r : ℕ) : ℝ) / Fintype.card β ≤ pullCount A cs k ω := by
    have : F.card ≤ pullCount A cs k ω := by
      rw [← hF] at hcount
      omega
    exact hcs.trans (by exact_mod_cast this)
  have hlogk : Real.log (((s - r : ℕ) : ℝ) / Fintype.card β) ≤ Real.log (pullCount A cs k ω) :=
    Real.log_le_log (div_pos (by exact_mod_cast (show 0 < s - r by omega)) hK) hNk
  have hAk : A (k + 1 - 1) ω = cs := by simpa using hk'.2
  calc ((y * Real.log (((s - r : ℕ) : ℝ) / Fintype.card β) : ℝ) : EReal)
      ≤ ((y * Real.log (pullCount A cs (k + 1 - 1) ω) : ℝ) : EReal) := by
        rw [Nat.add_sub_cancel]
        exact EReal.coe_le_coe_iff.mpr (mul_le_mul_of_nonneg_left hlogk hy)
    _ ≤ I cs (k + 1) := hlog cs (k + 1) (by omega) (by omega)
    _ ≤ I c' (k + 1) := hAk ▸ hmin (k + 1) (by omega) (by omega) c'
    _ ≤ I c' (T + 1) := hmono c' (k + 1) (T + 1) (by omega) (by omega) le_rfl

/-- If the count of `c` increases between the rounds `a` and `b`, then `c` is pulled at some round
of `[a, b)`. -/
lemma exists_action_eq_of_pullCount_lt {c : β} {a b : ℕ}
    (h : pullCount A c a ω < pullCount A c b ω) : ∃ k, a ≤ k ∧ k < b ∧ A k ω = c := by
  have hab : a ≤ b := le_of_not_gt fun hba ↦ (pullCount_mono (A := A) c hba.le ω).not_gt h
  have hpos : 0 < ((Finset.Ico a b).filter fun u ↦ A u ω = c).card := by
    rw [← pullCount_sub_eq_card hab]
    omega
  obtain ⟨k, hk⟩ := Finset.card_pos.mp hpos
  simp only [Finset.mem_filter, Finset.mem_Ico] at hk
  exact ⟨k, hk.1.1, hk.1.2, hk.2⟩

/-- Pigeonhole on the counts: with `K` arms and `K U ≤ t`, some arm has at least `U` pulls among
the first `t` rounds. -/
lemma exists_le_pullCount_of_card_mul_le [Fintype β] [Nonempty β] {U t : ℕ}
    (h : Fintype.card β * U ≤ t) : ∃ c, U ≤ pullCount A c t ω := by
  by_contra hno
  push Not at hno
  have hsum : ∑ c, pullCount A c t ω < ∑ _c : β, U :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun c _ ↦ hno c
  rw [sum_pullCount, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  omega

end Incognita.BatchedBandits
