/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.LawDriftOrder
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! # The constant of the mean gap in closed form

The tools of [INC-P002, prop:order (a)]: under `m(ν'_a) ≤ μ⋆ + L_a`, the programme of the mean gap
splits, `J^mean_a(x, c) = x K_0 + c K'_0`, and `D^mean_a(c) = (1 - c K'_0)_+ / K_0`.

The paper takes the pair of Kullback–Leibler projections `(Q⋆, Q'⋆)` as the minimiser of the
programme (lem:projection). The proof here needs neither their existence nor their uniqueness:
it moves any law `q` of mean at least `ℓ` to a mixture `(1 - s) q + s r` of mean exactly `ℓ`,
which is no farther from `r` (`exists_vecMean_eq_vecKL_le`), so that near-minimisers of `K_0` and
`K'_0` form an alternative pair of the mean gap.

## Main statements

* `vecKL_mix_le`: `KL(r, (1 - t) q + t r) ≤ KL(r, q)` for `t ∈ [0, 1]` (convexity).
* `exists_vecMean_eq_vecKL_le`: if `m(r) ≤ ℓ ≤ m(q)`, some law of mean exactly `ℓ` is no farther
  from `r` than `q`.
* `vecKs_ne_top`: `K_S(r, ℓ) < ∞` for `ℓ < x_max`.
* `programme_meanClass`: `J^mean(x, c; μ) = x K_S(r, μ) + c K_S(r', μ - l)` when
  `m(r) ≤ μ` and `m(r') ≤ μ + l`.
* `ofReal_driftConstant_meanClass`: `D^mean(c) = (1 - c K'_0)_+ / K_0`, in `ℝ≥0∞`.
-/

@[expose] public section

open scoped ENNReal

namespace Incognita.TransferBandits

variable {S : Finset ℝ}

/-! ### Mixtures of probability vectors -/

/-- A convex combination `(1 - t) q + t q'` of two probability vectors, `t ∈ [0, 1]`, is a
probability vector: `LMLExplore.convex_simplex`, read through `LMLExplore.mem_simplex_iff`
(`probVecs S` and `LMLExplore.simplex S` have the same defining formula, but `simplex` is not
exposed, so the two memberships are not interchangeable as terms in a module). -/
lemma smul_add_smul_mem_probVecs {q q' : S → ℝ} (hq : q ∈ probVecs S) (hq' : q' ∈ probVecs S)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : (1 - t) • q + t • q' ∈ probVecs S :=
  LMLExplore.mem_simplex_iff.1 <| LMLExplore.convex_simplex S (LMLExplore.mem_simplex_iff.2 hq)
    (LMLExplore.mem_simplex_iff.2 hq') (sub_nonneg.2 ht1) ht0 (sub_add_cancel 1 t)

lemma vecMean_smul_add_smul (t : ℝ) (q q' : S → ℝ) :
    vecMean ((1 - t) • q + t • q') = (1 - t) * vecMean q + t * vecMean q' := by
  rw [vecMean_add, vecMean_smul, vecMean_smul]

/-- `KL(r, q) < ∞` when `q` charges every point that `r` charges. -/
lemma vecKL_ne_top {r q : S → ℝ} (h : ∀ y, 0 < r y → 0 < q y) : vecKL r q ≠ ∞ := by
  unfold vecKL
  split_ifs
  exact ENNReal.ofReal_ne_top

/-- **Convexity**: mixing `r` into the second argument shrinks `KL(r, ·)` by the weight left,
`KL(r, (1 - t) q + t r) ≤ (1 - t) KL(r, q)` for `t ∈ [0, 1]` (termwise, by the concavity of `log`;
for `t = 1` both sides are `0`). -/
lemma vecKL_mix_le_mul (r q : S → ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    vecKL r ((1 - t) • q + t • r) ≤ ENNReal.ofReal (1 - t) * vecKL r q := by
  rcases ht1.lt_or_eq with ht1' | rfl
  swap
  · simp [vecKL_self]
  by_cases hc : ∀ y, 0 < r y → 0 < q y
  swap
  · have : vecKL r q = ∞ := by
      unfold vecKL
      simp only [hc, ↓reduceIte]
    rw [this, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by linarith)).ne']
    exact le_top
  set m : S → ℝ := (1 - t) • q + t • r with hm
  have hmpos : ∀ y, 0 < r y → 0 < m y := fun y hy ↦ by
    have hq := hc y hy
    simp only [hm, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases ht0.eq_or_lt with rfl | ht
    · simpa using hq
    · nlinarith
  -- termwise: `r log (r / m) ≤ (1 - t) r log (r / q)`
  have hterm : ∀ y, (if 0 < r y then r y * Real.log (r y / m y) else 0) ≤
      (1 - t) * (if 0 < r y then r y * Real.log (r y / q y) else 0) := fun y ↦ by
    split_ifs with hy
    · have hq := hc y hy
      have hconc := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.2 hq)
        (Set.mem_Ioi.2 hy) (sub_nonneg.2 ht1) ht0 (by ring)
      simp only [smul_eq_mul] at hconc
      have hmy : m y = (1 - t) * q y + t * r y := by simp [hm]
      rw [Real.log_div hy.ne' (hmpos y hy).ne', Real.log_div hy.ne' hq.ne', hmy]
      nlinarith [mul_le_mul_of_nonneg_left hconc hy.le]
    · simp
  unfold vecKL
  rw [ite_eq_left_of_eq_true _ _ (eq_true hmpos), ite_eq_left_of_eq_true _ _ (eq_true hc),
    ← ENNReal.ofReal_mul (sub_nonneg.2 ht1), Finset.mul_sum]
  exact ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun y _ ↦ hterm y)

/-- **Convexity**: mixing `r` into the second argument does not increase `KL(r, ·)`,
`KL(r, (1 - t) q + t r) ≤ KL(r, q)` for `t ∈ [0, 1]`. -/
lemma vecKL_mix_le (r q : S → ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    vecKL r ((1 - t) • q + t • r) ≤ vecKL r q :=
  (vecKL_mix_le_mul r q ht0 ht1).trans <|
    mul_le_of_le_one_left zero_le (ENNReal.ofReal_le_one.2 (by linarith))

/-- The mixture `(1 - s) q + s r` with `s = (m(q) - ℓ)/(m(q) - m(r))` has mean `ℓ`. -/
lemma vecMean_mix_eq {r q : S → ℝ} (h : vecMean r < vecMean q) (ℓ : ℝ) :
    vecMean ((1 - (vecMean q - ℓ) / (vecMean q - vecMean r)) • q +
      ((vecMean q - ℓ) / (vecMean q - vecMean r)) • r) = ℓ := by
  have hd : 0 < vecMean q - vecMean r := sub_pos.2 h
  have hs : (vecMean q - ℓ) / (vecMean q - vecMean r) * (vecMean q - vecMean r) =
      vecMean q - ℓ := div_mul_cancel₀ _ hd.ne'
  rw [vecMean_smul_add_smul]
  linear_combination (-1 : ℝ) * hs

/-- If `m(r) ≤ ℓ ≤ m(q)`, the mixture `(1 - s) q + s r` with `s = (m(q) - ℓ)/(m(q) - m(r))` has
mean exactly `ℓ` and is no farther from `r` than `q` (`vecKL_mix_le`). -/
lemma exists_vecMean_eq_vecKL_le {r q : S → ℝ} (hr : r ∈ probVecs S) (hq : q ∈ probVecs S)
    {ℓ : ℝ} (hrℓ : vecMean r ≤ ℓ) (hℓq : ℓ ≤ vecMean q) :
    ∃ q₁ ∈ probVecs S, vecMean q₁ = ℓ ∧ vecKL r q₁ ≤ vecKL r q := by
  rcases (hrℓ.trans hℓq).eq_or_lt with h | h
  · exact ⟨q, hq, by linarith, le_rfl⟩
  have hd : 0 < vecMean q - vecMean r := sub_pos.2 h
  have hs0 : 0 ≤ (vecMean q - ℓ) / (vecMean q - vecMean r) := div_nonneg (by linarith) hd.le
  have hs1 : (vecMean q - ℓ) / (vecMean q - vecMean r) ≤ 1 := (div_le_one hd).2 (by linarith)
  exact ⟨_, smul_add_smul_mem_probVecs hq hr hs0 hs1, vecMean_mix_eq h ℓ,
    vecKL_mix_le r q hs0 hs1⟩

/-- `K_S(r, μ)` grows at least linearly in the level: if `m(r) < μ ≤ m(q)`, then
`(m(q) - m(r)) K_S(r, μ) ≤ (μ - m(r)) KL(r, q)`. The mixture `(1 - s) q + s r` of mean `μ` has
`1 - s = (μ - m(r))/(m(q) - m(r))` and divergence at most `(1 - s) KL(r, q)`
(`vecKL_mix_le_mul`). -/
lemma ofReal_mul_vecKs_le {r q : S → ℝ} (hr : r ∈ probVecs S) (hq : q ∈ probVecs S) {μ : ℝ}
    (hrμ : vecMean r < μ) (hμq : μ ≤ vecMean q) :
    ENNReal.ofReal (vecMean q - vecMean r) * vecKs S r μ ≤
      ENNReal.ofReal (μ - vecMean r) * vecKL r q := by
  have h : vecMean r < vecMean q := hrμ.trans_le hμq
  have hd : 0 < vecMean q - vecMean r := sub_pos.2 h
  set s := (vecMean q - μ) / (vecMean q - vecMean r) with hs_def
  have hs0 : 0 ≤ s := div_nonneg (by linarith) hd.le
  have hs1 : s ≤ 1 := (div_le_one hd).2 (by linarith)
  have h1s : (vecMean q - vecMean r) * (1 - s) = μ - vecMean r := by
    rw [hs_def]
    field_simp
    ring
  calc ENNReal.ofReal (vecMean q - vecMean r) * vecKs S r μ
      ≤ ENNReal.ofReal (vecMean q - vecMean r) * vecKL r ((1 - s) • q + s • r) := by
        gcongr
        exact iInf₂_le _ ⟨smul_add_smul_mem_probVecs hq hr hs0 hs1, (vecMean_mix_eq h μ).ge⟩
    _ ≤ ENNReal.ofReal (vecMean q - vecMean r) * (ENNReal.ofReal (1 - s) * vecKL r q) := by
        gcongr
        exact vecKL_mix_le_mul r q hs0 hs1
    _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul hd.le, h1s]

/-- `K_S(r, ℓ) < ∞` for `ℓ < x_max`: the mixture `(1 - t) r + t δ_{x_max}` with mean `ℓ` charges
every point that `r` charges. -/
lemma vecKs_ne_top {b : ℝ} {y₁ : S} (hy₁ : (y₁ : ℝ) = b) {r : S → ℝ}
    (hr : r ∈ probVecs S) {ℓ : ℝ} (hℓ : ℓ < b) : vecKs S r ℓ ≠ ∞ := by
  rcases le_or_gt ℓ (vecMean r) with h | h
  · rw [vecKs_eq_zero hr h]
    exact ENNReal.zero_ne_top
  have hd : 0 < b - vecMean r := by linarith
  set t := (ℓ - vecMean r) / (b - vecMean r)
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hd.le
  have ht1 : t < 1 := (div_lt_one hd).2 (by linarith)
  have hq := mix_single_mem_probVecs hr y₁ ht0 ht1.le
  have hmean : ℓ ≤ vecMean ((1 - t) • r + t • Pi.single y₁ 1) := by
    have ht : t * (b - vecMean r) = ℓ - vecMean r := div_mul_cancel₀ _ hd.ne'
    rw [vecMean_smul_add_smul, vecMean_single, hy₁]
    refine le_of_eq ?_
    linear_combination (-1 : ℝ) * ht
  refine ne_top_of_le_ne_top (vecKL_ne_top fun y hy ↦ ?_) (iInf₂_le _ ⟨hq, hmean⟩)
  have : 0 ≤ (Pi.single y₁ (1 : ℝ) : S → ℝ) y := (single_mem_probVecs y₁).1 y
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  nlinarith

/-! ### The programme and the constant of the mean gap -/

lemma nonempty_of_vecKs_ne_top {r : S → ℝ} {ℓ : ℝ} (h : vecKs S r ℓ ≠ ∞) :
    {q ∈ probVecs S | ℓ ≤ vecMean q}.Nonempty :=
  Set.nonempty_iff_ne_empty.2 fun he ↦ h (by rw [vecKs, he]; simp)

lemma mul_biInf_of_nonempty {ι : Type*} {s : Set ι} (hs : s.Nonempty) {a : ℝ≥0∞} (ha : a ≠ ∞)
    (f : ι → ℝ≥0∞) : a * ⨅ i ∈ s, f i = ⨅ i ∈ s, a * f i := by
  rcases eq_or_ne a 0 with rfl | ha0
  · simp [biInf_const hs]
  · rw [ENNReal.mul_iInf_of_ne ha0 ha]
    exact iInf_congr fun i ↦ ENNReal.mul_iInf_of_ne ha0 ha

/-- The programme of the mean gap splits [INC-P002, prop:order (a), proof]: when `m(r) ≤ μ` and
`m(r') ≤ μ + l`, `J^mean(x, c; μ) = x K_S(r, μ) + c K_S(r', μ - l)`. A pair of the mean gap has
`m(q) ≥ μ` and `m(q') ≥ μ - l`, which gives `≥`; conversely, laws `q`, `q'` of means at least `μ`
and `μ - l` are moved to means `μ` and `min(m(q'), μ + l)` without increasing their divergences
(`exists_vecMean_eq_vecKL_le`), and then form a pair of the mean gap. The finiteness of the two
`K_S` only makes their sets nonempty. -/
lemma programme_meanClass {r r' : S → ℝ} (hr : r ∈ probVecs S) (hr' : r' ∈ probVecs S)
    {l μ : ℝ} (hl : 0 ≤ l) (hrμ : vecMean r ≤ μ) (hr'μ : vecMean r' ≤ μ + l)
    (hK : vecKs S r μ ≠ ∞) (hK' : vecKs S r' (μ - l) ≠ ∞) (x c : ℝ) :
    programme (meanClass S) l r r' μ x c =
      ENNReal.ofReal x * vecKs S r μ + ENNReal.ofReal c * vecKs S r' (μ - l) := by
  refine le_antisymm ?_ (le_iInf₂ fun p hp ↦ ?_)
  · rw [vecKs, vecKs, mul_biInf_of_nonempty (nonempty_of_vecKs_ne_top hK) ENNReal.ofReal_ne_top,
      mul_biInf_of_nonempty (nonempty_of_vecKs_ne_top hK') ENNReal.ofReal_ne_top]
    simp only [ENNReal.iInf_add, ENNReal.add_iInf]
    refine le_iInf₂ fun q' hq' ↦ le_iInf₂ fun q hq ↦ ?_
    obtain ⟨q₁, hq₁, hm₁, hKL₁⟩ := exists_vecMean_eq_vecKL_le hr hq.1 hrμ hq.2
    -- the source law: kept if its mean is at most `μ + l`, else moved to mean `μ + l`
    obtain ⟨q₁', hq₁', hlo, hhi, hKL₁'⟩ : ∃ q₁' ∈ probVecs S,
        μ - l ≤ vecMean q₁' ∧ vecMean q₁' ≤ μ + l ∧ vecKL r' q₁' ≤ vecKL r' q' := by
      rcases le_or_gt (vecMean q') (μ + l) with h | h
      · exact ⟨q', hq'.1, hq'.2, h, le_rfl⟩
      · obtain ⟨q₁', hq₁', hm, hKL⟩ := exists_vecMean_eq_vecKL_le hr' hq'.1 hr'μ h.le
        exact ⟨q₁', hq₁', by linarith [hq'.2], hm.le, hKL⟩
    have hpair : (q₁, q₁') ∈ altPairs (meanClass S) l μ := by
      refine ⟨hq₁, hq₁', hm₁.ge, ?_⟩
      rw [ipm_meanClass, hm₁, abs_le]
      constructor <;> linarith
    refine (programme_le x c hpair).trans ?_
    gcongr
  · have h1 : μ ≤ vecMean p.1 := hp.2.2.1
    have h2 : μ - l ≤ vecMean p.2 := by
      have := hp.2.2.2
      rw [ipm_meanClass, abs_le] at this
      linarith
    gcongr
    · exact iInf₂_le p.1 ⟨hp.1, h1⟩
    · exact iInf₂_le p.2 ⟨hp.2.1, h2⟩

/-- The constant of the mean gap, read in the reals [INC-P002, prop:order (a)]: when `m(r) < μ`,
`m(r') ≤ μ + l` and both `K_0 = K_S(r, μ)` and `K'_0 = K_S(r', μ - l)` are finite, on `S ⊆ [0,1]`,
`D^mean(c)` and `(1 - c K'_0) / K_0` have the same positive part, for `c ≥ 0` (`K_0 > 0` by
`vecKs_pos`). From `programme_meanClass`, `J^mean(x, c) ≥ 1` if and only if
`x ≥ (1 - c K'_0) / K_0`. -/
lemma ofReal_driftConstant_meanClass_eq_ofReal (hS : ∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1)
    {r r' : S → ℝ} (hr : r ∈ probVecs S) (hr' : r' ∈ probVecs S) {l μ : ℝ} (hl : 0 ≤ l)
    (hrμ : vecMean r < μ) (hr'μ : vecMean r' ≤ μ + l) (hK : vecKs S r μ ≠ ∞)
    (hK' : vecKs S r' (μ - l) ≠ ∞) {c : ℝ} (hc : 0 ≤ c) :
    ENNReal.ofReal (driftConstant (meanClass S) l r r' μ c) =
      ENNReal.ofReal ((1 - c * (vecKs S r' (μ - l)).toReal) / (vecKs S r μ).toReal) := by
  set k := (vecKs S r μ).toReal with hk_def
  set k' := (vecKs S r' (μ - l)).toReal with hk'_def
  have hk : 0 < k := ENNReal.toReal_pos (vecKs_pos hS hr hrμ).ne' hK
  have hk' : 0 ≤ k' := ENNReal.toReal_nonneg
  have eK : vecKs S r μ = ENNReal.ofReal k := (ENNReal.ofReal_toReal hK).symm
  have eK' : vecKs S r' (μ - l) = ENNReal.ofReal k' := (ENNReal.ofReal_toReal hK').symm
  set t := (1 - c * k') / k with ht
  have hset : {x : ℝ | 0 < x ∧ 1 ≤ programme (meanClass S) l r r' μ x c} =
      {x : ℝ | 0 < x ∧ t ≤ x} := by
    ext x
    simp only [Set.mem_ofPred_eq, programme_meanClass hr hr' hl hrμ.le hr'μ hK hK', eK, eK']
    refine and_congr_right fun hx ↦ ?_
    rw [← ENNReal.ofReal_mul hx.le, ← ENNReal.ofReal_mul hc,
      ← ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.one_le_ofReal, ht,
      div_le_iff₀ hk]
    constructor <;> intro h <;> linarith
  rw [driftConstant, hset]
  rcases le_or_gt t 0 with h | h
  · have : {x : ℝ | 0 < x ∧ t ≤ x} = Set.Ioi 0 := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_Ioi]
      exact ⟨fun hx ↦ hx.1, fun hx ↦ ⟨hx, h.trans hx.le⟩⟩
    rw [this, csInf_Ioi, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
  · have : {x : ℝ | 0 < x ∧ t ≤ x} = Set.Ici t := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_Ici]
      exact ⟨fun hx ↦ hx.2, fun hx ↦ ⟨h.trans_le hx, hx⟩⟩
    rw [this, csInf_Ici]

/-- The constant of the mean gap [INC-P002, prop:order (a)]: under the hypotheses of
`ofReal_driftConstant_meanClass_eq_ofReal`, `D^mean(c) = (1 - c K'_0)_+ / K_0` in `ℝ≥0∞`. -/
lemma ofReal_driftConstant_meanClass (hS : ∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) {r r' : S → ℝ}
    (hr : r ∈ probVecs S) (hr' : r' ∈ probVecs S) {l μ : ℝ} (hl : 0 ≤ l) (hrμ : vecMean r < μ)
    (hr'μ : vecMean r' ≤ μ + l) (hK : vecKs S r μ ≠ ∞) (hK' : vecKs S r' (μ - l) ≠ ∞)
    {c : ℝ} (hc : 0 ≤ c) :
    ENNReal.ofReal (driftConstant (meanClass S) l r r' μ c) =
      (1 - ENNReal.ofReal c * vecKs S r' (μ - l)) / vecKs S r μ := by
  have hk : 0 < (vecKs S r μ).toReal := ENNReal.toReal_pos (vecKs_pos hS hr hrμ).ne' hK
  rw [ofReal_driftConstant_meanClass_eq_ofReal hS hr hr' hl hrμ hr'μ hK hK' hc,
    ENNReal.ofReal_div_of_pos hk, ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_mul hc,
    ENNReal.ofReal_one, ENNReal.ofReal_toReal hK, ENNReal.ofReal_toReal hK']

/-! ### When the source helps the mean gap -/

/-- Pinsker's inequality read on the means: on `S ⊆ [0,1]`, if `m(q) ≤ m(r) - δ` with `δ ≥ 0`, then
`KL(r, q) ≥ δ² / 2`. -/
lemma ofReal_sq_div_two_le_vecKL (hS : ∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) {r q : S → ℝ}
    (hr : r ∈ probVecs S) (hq : q ∈ probVecs S) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : vecMean q ≤ vecMean r - δ) : ENNReal.ofReal (δ ^ 2 / 2) ≤ vecKL r q := by
  refine (ENNReal.ofReal_le_ofReal ?_).trans (ofReal_sq_sum_abs_sub_div_two_le_vecKL hr hq)
  have habs : |∑ y : S, (y : ℝ) * (r y - q y)| ≤ ∑ y, |r y - q y| :=
    abs_sum_le_of_mem_Icc fun y ↦ hS y y.2
  have h1 : δ ≤ ∑ y, |r y - q y| := by
    rw [← vecMean_sub] at habs
    linarith [le_abs_self (vecMean r - vecMean q)]
  gcongr

/-- The source helps the mean gap when its mean is too high [INC-P002, prop:criteria (b), proof]:
if `m(r') > μ + l`, `m(r) < μ` and `K_0 = K_S(r, μ) < ∞`, on `S ⊆ [0,1]`, then
`D^mean(c) < 1/K_0` for every `c > 0`. With `δ = (m(r') - μ - l)/2`, a pair of the mean gap either
has `m(q) ≥ μ + δ`, and then `KL(r, q) ≥ K_0 (1 + δ/(μ - m(r)))` (`ofReal_mul_vecKs_le`), or
`m(q') ≤ m(r') - δ`, and then `KL(r', q') ≥ δ²/2` (Pinsker); so `J^mean(x, c) ≥ 1` for some
`x < 1/K_0`. -/
lemma ofReal_driftConstant_meanClass_lt (hS : ∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) {r r' : S → ℝ}
    (hr : r ∈ probVecs S) (hr' : r' ∈ probVecs S) {l μ : ℝ} (hrμ : vecMean r < μ)
    (hK : vecKs S r μ ≠ ∞) (h : μ + l < vecMean r') {c : ℝ} (hc : 0 < c) :
    ENNReal.ofReal (driftConstant (meanClass S) l r r' μ c) < (vecKs S r μ)⁻¹ := by
  set k := (vecKs S r μ).toReal with hk_def
  have hk : 0 < k := ENNReal.toReal_pos (vecKs_pos hS hr hrμ).ne' hK
  have eK : vecKs S r μ = ENNReal.ofReal k := (ENNReal.ofReal_toReal hK).symm
  set g := μ - vecMean r with hg_def
  have hg : 0 < g := sub_pos.2 hrμ
  set δ := (vecMean r' - μ - l) / 2 with hδ_def
  have hδ : 0 < δ := by rw [hδ_def]; linarith
  set η := δ ^ 2 / 2 with hη_def
  have hη : 0 < η := by positivity
  set x := max (1 / (k * (1 + δ / g))) ((1 - c * η) / k) with hx_def
  have hx0 : 0 < x := lt_max_of_lt_left (by positivity)
  have hxk : x < 1 / k := max_lt
    (one_div_lt_one_div_of_lt hk (lt_mul_of_one_lt_right hk (by linarith [div_pos hδ hg])))
    (div_lt_div_of_pos_right (by linarith [mul_pos hc hη]) hk)
  have hJ : 1 ≤ programme (meanClass S) l r r' μ x c := by
    refine le_iInf₂ fun p hp ↦ ?_
    have hμp : μ ≤ vecMean p.1 := hp.2.2.1
    have hp2 : vecMean p.2 ≤ vecMean p.1 + l := by
      have := hp.2.2.2
      rw [ipm_meanClass, abs_le] at this
      linarith
    have hkq : ENNReal.ofReal k ≤ vecKL r p.1 := eK ▸ iInf₂_le p.1 ⟨hp.1, hμp⟩
    by_cases hv : μ + δ ≤ vecMean p.1
    · refine le_trans ?_ le_self_add
      rcases eq_or_ne (vecKL r p.1) ∞ with htop | htop
      · rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 hx0).ne']
        exact le_top
      set κ := (vecKL r p.1).toReal
      have hlin := ofReal_mul_vecKs_le hr hp.1 hrμ hμp
      rw [eK, ← ENNReal.ofReal_toReal htop, ← ENNReal.ofReal_mul (by linarith),
        ← ENNReal.ofReal_mul hg.le, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hlin
      have hκ : k * (1 + δ / g) ≤ κ := by
        have e : k * (1 + δ / g) = k * (g + δ) / g := by field_simp
        rw [e, div_le_iff₀ hg]
        nlinarith
      have hx1 : 1 ≤ x * κ := by
        have hpos : 0 < k * (1 + δ / g) := by positivity
        calc (1 : ℝ) = 1 / (k * (1 + δ / g)) * (k * (1 + δ / g)) := by field_simp
          _ ≤ x * κ := mul_le_mul (le_max_left _ _) hκ hpos.le hx0.le
      rw [← ENNReal.ofReal_toReal htop, ← ENNReal.ofReal_mul hx0.le]
      exact ENNReal.one_le_ofReal.2 hx1
    · have hq' : ENNReal.ofReal η ≤ vecKL r' p.2 :=
        ofReal_sq_div_two_le_vecKL hS hr' hp.2.1 hδ.le (by rw [hδ_def] at hv ⊢; linarith)
      have hxk1 : 1 ≤ x * k + c * η := by
        have := (div_le_iff₀ hk).1 (le_max_right (1 / (k * (1 + δ / g))) ((1 - c * η) / k))
        linarith
      calc (1 : ℝ≥0∞) ≤ ENNReal.ofReal (x * k + c * η) := ENNReal.one_le_ofReal.2 hxk1
        _ = ENNReal.ofReal x * ENNReal.ofReal k + ENNReal.ofReal c * ENNReal.ofReal η := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hx0.le,
            ENNReal.ofReal_mul hc.le]
        _ ≤ _ := by gcongr
  have hD : driftConstant (meanClass S) l r r' μ c ≤ x :=
    csInf_le ⟨0, fun _ hy ↦ hy.1.le⟩ ⟨hx0, hJ⟩
  calc ENNReal.ofReal (driftConstant (meanClass S) l r r' μ c) ≤ ENNReal.ofReal x :=
        ENNReal.ofReal_le_ofReal hD
    _ < ENNReal.ofReal (1 / k) := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hxk
    _ = (vecKs S r μ)⁻¹ := by rw [one_div, ENNReal.ofReal_inv_of_pos hk, ← eK]

/-- The source helps the mean gap at all [INC-P002, prop:criteria (b), for the mean gap]: when
`m(r) < μ`, `l ≥ 0` and both `K_0 = K_S(r, μ)` and `K'_0 = K_S(r', μ - l)` are finite, on
`S ⊆ [0,1]`, `D^mean(c) < 1/K_0` if and only if `l < |m(r') - μ|`, for every `c > 0`. Below
`μ + l`, by `ofReal_driftConstant_meanClass_eq_ofReal` it holds exactly when `K'_0 > 0`, that is
`m(r') < μ - l`; above, by `ofReal_driftConstant_meanClass_lt`. -/
lemma ofReal_driftConstant_meanClass_lt_iff (hS : ∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1)
    {r r' : S → ℝ} (hr : r ∈ probVecs S) (hr' : r' ∈ probVecs S) {l μ : ℝ} (hl : 0 ≤ l)
    (hrμ : vecMean r < μ) (hK : vecKs S r μ ≠ ∞) (hK' : vecKs S r' (μ - l) ≠ ∞) {c : ℝ}
    (hc : 0 < c) :
    ENNReal.ofReal (driftConstant (meanClass S) l r r' μ c) < (vecKs S r μ)⁻¹ ↔
      l < |vecMean r' - μ| := by
  rcases le_or_gt (vecMean r') (μ + l) with h | h
  swap
  · exact ⟨fun _ ↦ by rw [lt_abs]; left; linarith,
      fun _ ↦ ofReal_driftConstant_meanClass_lt hS hr hr' hrμ hK h hc⟩
  set k := (vecKs S r μ).toReal with hk_def
  set k' := (vecKs S r' (μ - l)).toReal with hk'_def
  have hk : 0 < k := ENNReal.toReal_pos (vecKs_pos hS hr hrμ).ne' hK
  have eK : vecKs S r μ = ENNReal.ofReal k := (ENNReal.ofReal_toReal hK).symm
  rw [ofReal_driftConstant_meanClass_eq_ofReal hS hr hr' hl hrμ h hK hK' hc.le, ← hk_def,
    ← hk'_def, eK,
    ← ENNReal.ofReal_inv_of_pos hk, ENNReal.ofReal_lt_ofReal_iff (inv_pos.2 hk), ← one_div,
    div_lt_div_iff_of_pos_right hk]
  -- both sides say `K'_0 > 0`, that is `m(r') < μ - l`
  have hiff : 0 < k' ↔ vecMean r' < μ - l := by
    refine ⟨fun hpos ↦ ?_, fun hlt ↦ ENNReal.toReal_pos (vecKs_pos hS hr' hlt).ne' hK'⟩
    by_contra hge
    rw [hk'_def, vecKs_eq_zero hr' (not_lt.1 hge), ENNReal.toReal_zero] at hpos
    exact hpos.false
  have habs : l < |vecMean r' - μ| ↔ vecMean r' < μ - l := by
    rw [lt_abs]
    constructor
    · rintro (h' | h') <;> linarith
    · intro h'; right; linarith
  rw [habs, ← hiff]
  constructor
  · intro h'
    by_contra hk'0
    have : k' = 0 := le_antisymm (not_lt.1 hk'0) ENNReal.toReal_nonneg
    rw [this, mul_zero, sub_zero] at h'
    exact h'.false
  · intro h'
    linarith [mul_pos hc h']

end Incognita.TransferBandits
