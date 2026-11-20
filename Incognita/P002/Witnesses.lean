/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.LawDriftChecks
public import Incognita.P003.SourceIgnoring

/-! # Joint satisfiability of the hypotheses of the frozen statements of P002

For each frozen statement `Incognita.Statements.P002.<name>`, the lemma
`Incognita.P002.<name>_satisfiable` gives an explicit instance satisfying all its hypotheses at
once (AGENTS.md §6.4). The instance: two arms `Bool`, the support `S = {0, 1}`, the mean gap
(`meanClass S`), the bounds `L ≡ 1`, the target `ν = ν'` with `ν true = δ_1` and
`ν false = δ_0` (so `μ⋆ = 1`, arm `true` optimal, arm `false` suboptimal), source sizes `N' ≡ 0`
and the rate `c = 0`. The hypothesis `π ∈ Cons(N')` is satisfied by the source-ignoring KL-UCB of
LMLExplore (`isLawConsistent_klucb`, from [INC-P003]'s `ofAlgorithm_isConsistent`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Incognita.TransferBandits

open scoped ENNReal Topology

namespace Incognita.P002

/-- The support `{0, 1}`. -/
noncomputable abbrev S01 : Finset ℝ := {0, 1}

lemma S01_subset : ∀ y ∈ S01, y ∈ Set.Icc (0 : ℝ) 1 := by
  intro y hy
  simp only [S01, Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl <;> norm_num

lemma S01_card : 2 ≤ S01.card := by
  rw [S01, Finset.card_pair (by norm_num)]

lemma meanClass_isTestClass {S : Finset ℝ} (hS : ∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) :
    IsTestClass (meanClass S) := by
  refine ⟨Set.singleton_nonempty _, fun f hf y ↦ ?_⟩
  rw [Set.mem_singleton_iff.mp hf]
  exact hS y y.2

/-- The point `1` of `S01`. -/
noncomputable abbrev one01 : S01 := ⟨1, by simp⟩
/-- The point `0` of `S01`. -/
noncomputable abbrev zero01 : S01 := ⟨0, by simp⟩

/-- The instance `δ_1` on arm `true`, `δ_0` on arm `false`. -/
noncomputable abbrev nu01 : Kernel Bool ℝ :=
  Kernel.deterministic (fun b ↦ ((if b then one01 else zero01 : S01) : ℝ))
    (measurable_of_countable _)

lemma nu01_mem : nu01 ∈ supportBandits S01 Bool :=
  deterministic_mem_supportBandits _

lemma mean_nu01 (b : Bool) : (nu01 b)[id] = if b then 1 else 0 := by
  rw [Kernel.deterministic_apply, integral_dirac]
  cases b <;> simp

lemma bestMean_nu01 : bestMean nu01 = 1 := by
  unfold bestMean
  refine le_antisymm (ciSup_le fun b ↦ ?_) ?_
  · rw [mean_nu01]; split_ifs <;> norm_num
  · refine le_ciSup_of_le (Set.finite_range _).bddAbove true ?_
    rw [mean_nu01]; simp

lemma false_suboptimal : (nu01 false)[id] < bestMean nu01 := by
  rw [mean_nu01, bestMean_nu01]; norm_num

lemma true_optimal :
    ∃ i, (nu01 i)[id] = bestMean nu01 ∧
      ipm (meanClass S01) (lawVec S01 (nu01 i)) (lawVec S01 (nu01 i)) < (fun _ ↦ (1 : ℝ)) i :=
  ⟨true, by rw [mean_nu01, bestMean_nu01]; simp,
    by rw [ipm_self]; norm_num⟩

lemma nu01_mem_lawDriftClass :
    (nu01, nu01) ∈ lawDriftClass (meanClass S01) (fun _ : Bool ↦ (1 : ℝ)) :=
  self_mem_lawDriftClass (fun _ ↦ one_pos) nu01_mem

lemma tendsto_zero_div_log :
    Tendsto (fun T : ℕ ↦ (((fun _ _ ↦ 0 : ℕ → Bool → ℕ) T false : ℕ) : ℝ) / Real.log T) atTop
      (𝓝 0) := by
  simp

lemma limsup_zero_div_log :
    limsup (fun T : ℕ ↦ ((((fun _ _ ↦ 0 : ℕ → Bool → ℕ) T false : ℕ) : ℝ≥0∞) /
      ENNReal.ofReal (Real.log T))) atTop < ∞ := by
  simp

/-- Witness of `Cons(N')`: the source-ignoring learner of LMLExplore's KL-UCB belongs to
`Cons(N')` for every `S ⊆ [0,1]`, every `𝓕`, `L` and `N'`. -/
lemma isLawConsistent_klucb {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]
    [MeasurableSpace α] [MeasurableSingletonClass α] {S : Finset ℝ}
    (hS : ∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) (𝓕 : Set (S → ℝ)) (L : α → ℝ) (N' : ℕ → α → ℕ) :
    IsLawConsistent 𝓕 L N' (TransferAlgorithm.ofAlgorithm LMLExplore.Bandits.klucb) := by
  rcases lt_or_ge (Fintype.card α) 2 with hK | hK
  · -- one arm: no arm is suboptimal
    have : Subsingleton α := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    intro ν _ _ k hk
    have hbest : bestMean ν = (ν k)[id] := by
      exact le_antisymm (ciSup_le fun j ↦ by rw [Subsingleton.elim j k])
        (le_ciSup (f := fun j ↦ (ν j)[id]) (Set.finite_range _).bddAbove k)
    exact absurd hk (by rw [hbest]; exact lt_irrefl _)
  · exact isLawConsistent_of_isConsistent_one hS N'
      (Incognita.P003.ofAlgorithm_isConsistent hK Relations.isConsistentOnUnit_klucb).1

lemma card_bool : 2 ≤ Fintype.card Bool := by simp

/-- Hypotheses of `upper_bound_klucb` (thm:main (i)). -/
lemma upper_bound_klucb_satisfiable :
    ∃ (S : Finset ℝ) (𝓕 : Set (S → ℝ)) (L : Bool → ℝ) (ν ν' : Kernel Bool ℝ) (a : Bool),
      2 ≤ Fintype.card Bool ∧ (∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) ∧ 2 ≤ S.card ∧
      IsTestClass 𝓕 ∧ (∀ k, 0 < L k) ∧ ν ∈ supportBandits S Bool ∧
      ν' ∈ supportBandits S Bool ∧
      (∃ i, (ν i)[id] = bestMean ν ∧ ipm 𝓕 (lawVec S (ν i)) (lawVec S (ν' i)) < L i) ∧
      (ν a)[id] < bestMean ν :=
  ⟨S01, meanClass S01, fun _ ↦ 1, nu01, nu01, false, card_bool, S01_subset, S01_card,
    meanClass_isTestClass S01_subset, fun _ ↦ one_pos, nu01_mem, nu01_mem, true_optimal,
    false_suboptimal⟩

/-- Hypotheses of `upper_bound_transfer` (thm:main (ii)). -/
lemma upper_bound_transfer_satisfiable :
    ∃ (S : Finset ℝ) (𝓕 : Set (S → ℝ)) (L : Bool → ℝ) (ν ν' : Kernel Bool ℝ)
      (N' : ℕ → Bool → ℕ) (a : Bool) (c : ℝ),
      2 ≤ Fintype.card Bool ∧ (∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) ∧ 2 ≤ S.card ∧
      IsTestClass 𝓕 ∧ (∀ k, 0 < L k) ∧ ν ∈ supportBandits S Bool ∧
      ν' ∈ supportBandits S Bool ∧
      (∃ i, (ν i)[id] = bestMean ν ∧ ipm 𝓕 (lawVec S (ν i)) (lawVec S (ν' i)) < L i) ∧
      (ν a)[id] < bestMean ν ∧
      Tendsto (fun T : ℕ ↦ (N' T a : ℝ) / Real.log T) atTop (𝓝 c) :=
  ⟨S01, meanClass S01, fun _ ↦ 1, nu01, nu01, fun _ _ ↦ 0, false, 0, card_bool, S01_subset,
    S01_card, meanClass_isTestClass S01_subset, fun _ ↦ one_pos, nu01_mem, nu01_mem,
    true_optimal, false_suboptimal, tendsto_zero_div_log⟩

/-- Hypotheses of `lower_bound` (prop:lower). -/
lemma lower_bound_satisfiable :
    ∃ (S : Finset ℝ) (𝓕 : Set (S → ℝ)) (L : Bool → ℝ) (N' : ℕ → Bool → ℕ)
      (π : TransferAlgorithm Bool) (ν ν' : Kernel Bool ℝ) (a : Bool),
      2 ≤ Fintype.card Bool ∧ (∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) ∧ 2 ≤ S.card ∧
      IsTestClass 𝓕 ∧ (∀ k, 0 < L k) ∧ IsLawConsistent 𝓕 L N' π ∧
      (ν, ν') ∈ lawDriftClass 𝓕 L ∧ (ν a)[id] < bestMean ν ∧
      limsup (fun T : ℕ ↦ (N' T a : ℝ≥0∞) / ENNReal.ofReal (Real.log T)) atTop < ∞ :=
  ⟨S01, meanClass S01, fun _ ↦ 1, fun _ _ ↦ 0,
    TransferAlgorithm.ofAlgorithm LMLExplore.Bandits.klucb, nu01, nu01, false, card_bool,
    S01_subset, S01_card, meanClass_isTestClass S01_subset, fun _ ↦ one_pos,
    isLawConsistent_klucb S01_subset _ _ _, nu01_mem_lawDriftClass, false_suboptimal,
    limsup_zero_div_log⟩

/-- Hypotheses shared by the four statements of cor:optimal. -/
lemma optimal_satisfiable :
    ∃ (S : Finset ℝ) (𝓕 : Set (S → ℝ)) (L : Bool → ℝ) (ν ν' : Kernel Bool ℝ)
      (N' : ℕ → Bool → ℕ) (c : Bool → ℝ),
      2 ≤ Fintype.card Bool ∧ (∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) ∧ 2 ≤ S.card ∧
      IsTestClass 𝓕 ∧ (∀ k, 0 < L k) ∧ (ν, ν') ∈ lawDriftClass 𝓕 L ∧
      (∀ k, (ν k)[id] < bestMean ν →
        Tendsto (fun T : ℕ ↦ (N' T k : ℝ) / Real.log T) atTop (𝓝 (c k))) ∧
      (ν false)[id] < bestMean ν ∧
      IsLawConsistent 𝓕 L N' (TransferAlgorithm.ofAlgorithm LMLExplore.Bandits.klucb) :=
  ⟨S01, meanClass S01, fun _ ↦ 1, nu01, nu01, fun _ _ ↦ 0, fun _ ↦ 0, card_bool, S01_subset,
    S01_card, meanClass_isTestClass S01_subset, fun _ ↦ one_pos, nu01_mem_lawDriftClass,
    fun _ _ ↦ by simp, false_suboptimal, isLawConsistent_klucb S01_subset _ _ _⟩

/-- Hypotheses of `optimal_isLawConsistent` (cor:optimal, first claim). -/
lemma optimal_isLawConsistent_satisfiable :
    ∃ (S : Finset ℝ) (𝓕 : Set (S → ℝ)) (L : Bool → ℝ) (ν ν' : Kernel Bool ℝ)
      (N' : ℕ → Bool → ℕ) (c : Bool → ℝ),
      2 ≤ Fintype.card Bool ∧ (∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) ∧ 2 ≤ S.card ∧
      IsTestClass 𝓕 ∧ (∀ k, 0 < L k) ∧ (ν, ν') ∈ lawDriftClass 𝓕 L ∧
      ∀ k, (ν k)[id] < bestMean ν →
        Tendsto (fun T : ℕ ↦ (N' T k : ℝ) / Real.log T) atTop (𝓝 (c k)) := by
  obtain ⟨S, 𝓕, L, ν, ν', N', c, h1, h2, h3, h4, h5, h6, h7, -⟩ := optimal_satisfiable
  exact ⟨S, 𝓕, L, ν, ν', N', c, h1, h2, h3, h4, h5, h6, h7⟩

/-- Hypotheses of `optimal_tendsto_pulls` (cor:optimal, second claim). -/
lemma optimal_tendsto_pulls_satisfiable :
    ∃ (S : Finset ℝ) (𝓕 : Set (S → ℝ)) (L : Bool → ℝ) (ν ν' : Kernel Bool ℝ)
      (N' : ℕ → Bool → ℕ) (c : Bool → ℝ) (a : Bool),
      2 ≤ Fintype.card Bool ∧ (∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) ∧ 2 ≤ S.card ∧
      IsTestClass 𝓕 ∧ (∀ k, 0 < L k) ∧ (ν, ν') ∈ lawDriftClass 𝓕 L ∧
      (∀ k, (ν k)[id] < bestMean ν →
        Tendsto (fun T : ℕ ↦ (N' T k : ℝ) / Real.log T) atTop (𝓝 (c k))) ∧
      (ν a)[id] < bestMean ν := by
  obtain ⟨S, 𝓕, L, ν, ν', N', c, h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := optimal_satisfiable
  exact ⟨S, 𝓕, L, ν, ν', N', c, false, h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- Hypotheses of `optimal_tendsto_regret` (cor:optimal, third claim). -/
lemma optimal_tendsto_regret_satisfiable :
    ∃ (S : Finset ℝ) (𝓕 : Set (S → ℝ)) (L : Bool → ℝ) (ν ν' : Kernel Bool ℝ)
      (N' : ℕ → Bool → ℕ) (c : Bool → ℝ),
      2 ≤ Fintype.card Bool ∧ (∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) ∧ 2 ≤ S.card ∧
      IsTestClass 𝓕 ∧ (∀ k, 0 < L k) ∧ (ν, ν') ∈ lawDriftClass 𝓕 L ∧
      ∀ k, (ν k)[id] < bestMean ν →
        Tendsto (fun T : ℕ ↦ (N' T k : ℝ) / Real.log T) atTop (𝓝 (c k)) :=
  optimal_isLawConsistent_satisfiable

/-- Hypotheses of `optimal_regret_lower` (cor:optimal, fourth claim). -/
lemma optimal_regret_lower_satisfiable :
    ∃ (S : Finset ℝ) (𝓕 : Set (S → ℝ)) (L : Bool → ℝ) (ν ν' : Kernel Bool ℝ)
      (N' : ℕ → Bool → ℕ) (c : Bool → ℝ) (π : TransferAlgorithm Bool),
      2 ≤ Fintype.card Bool ∧ (∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) ∧ 2 ≤ S.card ∧
      IsTestClass 𝓕 ∧ (∀ k, 0 < L k) ∧ (ν, ν') ∈ lawDriftClass 𝓕 L ∧
      (∀ k, (ν k)[id] < bestMean ν →
        Tendsto (fun T : ℕ ↦ (N' T k : ℝ) / Real.log T) atTop (𝓝 (c k))) ∧
      IsLawConsistent 𝓕 L N' π := by
  obtain ⟨S, 𝓕, L, ν, ν', N', c, h1, h2, h3, h4, h5, h6, h7, -, h9⟩ := optimal_satisfiable
  exact ⟨S, 𝓕, L, ν, ν', N', c, _, h1, h2, h3, h4, h5, h6, h7, h9⟩

/-! ### The instance of the structure results

The support `S = {0, 1/2, 1}`, the instance `ν = ν'` with `ν true = δ_{1/2}` and
`ν false = δ_0` (so `μ⋆ = 1/2 < 1 = x_max`, arm `false` suboptimal), the bounds `L ≡ 1` (then
`K'_0 = 0`) or `L ≡ 1/4` (for prop:criteria and prop:tv (a)), the mean gap as `d`, and `c = 1`.
With `L ≡ 1/4` both projections of `δ_0` are in the binding case (`isKLProj_single_zero`):
`Q⋆ = ½ δ_0 + ½ δ_1` at the level `μ⋆ = 1/2` and `Q'⋆ = ¾ δ_0 + ¼ δ_1` at the level
`μ⋆ - L = 1/4`, so `K'_0 = log (4/3) ∈ (0, 1)` and `c = 1` has `c K'_0 < 1`. -/

/-- The support `{0, 1/2, 1}`. -/
noncomputable abbrev S3 : Finset ℝ := {0, 1 / 2, 1}

lemma S3_subset : ∀ y ∈ S3, y ∈ Set.Icc (0 : ℝ) 1 := by
  intro y hy
  simp only [S3, Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl | rfl <;> norm_num

lemma S3_card : 2 ≤ S3.card := by
  rw [S3, Finset.card_insert_of_notMem (by norm_num), Finset.card_pair (by norm_num)]
  norm_num

lemma S3_nonempty : S3.Nonempty := ⟨0, by simp⟩

/-- The point `1/2` of `S3`. -/
noncomputable abbrev half3 : S3 := ⟨1 / 2, by simp⟩
/-- The point `0` of `S3`. -/
noncomputable abbrev zero3 : S3 := ⟨0, by simp⟩

/-- The instance `δ_{1/2}` on arm `true`, `δ_0` on arm `false`. -/
noncomputable abbrev nu3 : Kernel Bool ℝ :=
  Kernel.deterministic (fun b ↦ ((if b then half3 else zero3 : S3) : ℝ))
    (measurable_of_countable _)

lemma nu3_mem : nu3 ∈ supportBandits S3 Bool :=
  deterministic_mem_supportBandits _

lemma mean_nu3 (b : Bool) : (nu3 b)[id] = if b then 1 / 2 else 0 := by
  rw [Kernel.deterministic_apply, integral_dirac]
  cases b <;> simp

lemma bestMean_nu3 : bestMean nu3 = 1 / 2 := by
  unfold bestMean
  refine le_antisymm (ciSup_le fun b ↦ ?_) ?_
  · rw [mean_nu3]; split_ifs <;> norm_num
  · refine le_ciSup_of_le (Set.finite_range _).bddAbove true ?_
    rw [mean_nu3]; simp

lemma false_suboptimal3 : (nu3 false)[id] < bestMean nu3 := by
  rw [mean_nu3, bestMean_nu3]; norm_num

lemma bestMean_lt_max3 : bestMean nu3 < S3.max' S3_nonempty := by
  rw [bestMean_nu3]
  exact lt_of_lt_of_le (by norm_num) (S3.le_max' 1 (by simp))

lemma mean_cond3 : (nu3 false)[id] ≤ bestMean nu3 + (fun _ : Bool ↦ (1 : ℝ)) false := by
  rw [mean_nu3, bestMean_nu3]; norm_num

lemma lawVec_nu3_false : lawVec S3 (nu3 false) = Pi.single zero3 1 := by
  simp only [Kernel.deterministic_apply, Bool.false_eq_true, ↓reduceIte]
  exact lawVec_dirac zero3

/-- The point `1` of `S3`. -/
noncomputable abbrev one3 : S3 := ⟨1, by simp⟩

lemma S3_le : ∀ y ∈ S3, y ≤ 1 := fun y hy ↦ (S3_subset y hy).2

/-- `c K_S(δ_0, ℓ) < 1` for `c = 1` and `ℓ ∈ [0, b/2)`, on a support `S ⊆ (-∞, b]` containing `0`
and `b > 0`: then `K_S(δ_0, ℓ) = log (1 / (1 - ℓ/b)) < log 2 < 1`. -/
lemma one_mul_vecKs_single_zero_lt_one {S : Finset ℝ} {b : ℝ}
    (hS : ∀ y ∈ S, y ≤ b) {y₀ y₁ : S} (hy₀ : (y₀ : ℝ) = 0) (hy₁ : (y₁ : ℝ) = b) {ℓ : ℝ}
    (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ < b / 2) : ENNReal.ofReal 1 * vecKs S (Pi.single y₀ 1) ℓ < 1 := by
  have hb : 0 < b := by linarith
  rw [ENNReal.ofReal_one, one_mul, vecKs_single_zero hS hy₀ hy₁ hℓ0 (by linarith),
    ENNReal.ofReal_lt_one]
  have ht : ℓ / b < 1 / 2 := by rw [div_lt_iff₀ hb]; linarith
  have hpos : 0 < 1 - ℓ / b := by linarith
  have hx : 1 / (1 - ℓ / b) < 2 := by rw [div_lt_iff₀ hpos]; linarith
  linarith [Real.log_le_sub_one_of_pos (by positivity : 0 < 1 / (1 - ℓ / b))]

/-- The drift bound `1/4` of the instance on `S3`: `μ⋆ - L = 1/4`. -/
lemma level3 : bestMean nu3 - (fun _ : Bool ↦ (1 / 4 : ℝ)) false = 1 / 4 := by
  rw [bestMean_nu3]; norm_num

/-- `Q⋆ = ½ δ_0 + ½ δ_1`, the projection of `ν_false = δ_0` at the level `μ⋆ = 1/2` on `S3`. -/
lemma isKLProj_Q3 : IsKLProj (lawVec S3 (nu3 false)) (bestMean nu3)
    (Pi.single zero3 (1 - 1 / 2 / 1) + Pi.single one3 (1 / 2 / 1)) := by
  rw [lawVec_nu3_false, bestMean_nu3]
  exact isKLProj_single_zero S3_le rfl rfl (by norm_num) (by norm_num)

/-- `Q'⋆ = ¾ δ_0 + ¼ δ_1`, the projection of `ν'_false = δ_0` at the level `μ⋆ - L = 1/4` on
`S3`. -/
lemma isKLProj_Q3' :
    IsKLProj (lawVec S3 (nu3 false)) (bestMean nu3 - (fun _ : Bool ↦ (1 / 4 : ℝ)) false)
      (Pi.single zero3 (1 - 1 / 4 / 1) + Pi.single one3 (1 / 4 / 1)) := by
  rw [lawVec_nu3_false, level3]
  exact isKLProj_single_zero S3_le rfl rfl (by norm_num) (by norm_num)

/-- `K'_0 = log (4/3) < 1` on `S3` with `L ≡ 1/4`, so `c = 1` has `c K'_0 < 1`. -/
lemma K0P3_lt : ENNReal.ofReal 1 *
    vecKs S3 (lawVec S3 (nu3 false)) (bestMean nu3 - (fun _ : Bool ↦ (1 / 4 : ℝ)) false) < 1 := by
  rw [lawVec_nu3_false, level3]
  exact one_mul_vecKs_single_zero_lt_one S3_le rfl (y₁ := one3) rfl (by norm_num)
    (by norm_num)

/-- `K'_0 = log (4/3) > 0` on `S3` with `L ≡ 1/4`. -/
lemma K0P3_pos :
    0 < vecKs S3 (lawVec S3 (nu3 false)) (bestMean nu3 - (fun _ : Bool ↦ (1 / 4 : ℝ)) false) := by
  rw [lawVec_nu3_false, level3]
  exact vecKs_single_zero_pos S3_le rfl (by norm_num) (by norm_num)

lemma mean_cond3' : (nu3 false)[id] ≤ bestMean nu3 + (fun _ : Bool ↦ (1 / 4 : ℝ)) false := by
  rw [mean_nu3, bestMean_nu3]; norm_num

lemma pair_subset3 : ({0, 1} : Finset ℝ) ⊆ S3 := by
  intro y hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl <;> simp

lemma carried01 : nu3 false ({0, 1} : Set ℝ)ᶜ = 0 := by
  rw [Kernel.deterministic_apply,
    Measure.dirac_apply' _ ((Set.finite_singleton (1 : ℝ)).insert 0).measurableSet.compl]
  simp

/-- Hypotheses of `order_mean` (prop:order (a)). -/
lemma order_mean_satisfiable :
    ∃ (S : Finset ℝ) (hSne : S.Nonempty) (L : Bool → ℝ) (ν ν' : Kernel Bool ℝ) (a : Bool),
      2 ≤ Fintype.card Bool ∧ (∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) ∧ 2 ≤ S.card ∧ (∀ k, 0 < L k) ∧
      ν ∈ supportBandits S Bool ∧ ν' ∈ supportBandits S Bool ∧ (ν a)[id] < bestMean ν ∧
      bestMean ν < S.max' hSne ∧
      (ν' a)[id] ≤ bestMean ν + L a :=
  ⟨S3, S3_nonempty, fun _ ↦ 1, nu3, nu3, false, card_bool, S3_subset, S3_card, fun _ ↦ one_pos,
    nu3_mem, nu3_mem, false_suboptimal3, bestMean_lt_max3, mean_cond3⟩

/-- Hypotheses of `order_le_mean` (prop:order (b)). -/
lemma order_le_mean_satisfiable :
    ∃ (S : Finset ℝ) (hSne : S.Nonempty) (L : Bool → ℝ) (ν ν' : Kernel Bool ℝ) (a : Bool)
      (𝓕 : Set (S → ℝ)),
      2 ≤ Fintype.card Bool ∧ (∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) ∧ 2 ≤ S.card ∧ (∀ k, 0 < L k) ∧
      ν ∈ supportBandits S Bool ∧ ν' ∈ supportBandits S Bool ∧ (ν a)[id] < bestMean ν ∧
      bestMean ν < S.max' hSne ∧
      IsTestClass 𝓕 ∧ HasMeanProperty 𝓕 :=
  ⟨S3, S3_nonempty, fun _ ↦ 1, nu3, nu3, false, meanClass S3, card_bool, S3_subset, S3_card, fun _ ↦
    one_pos, nu3_mem, nu3_mem, false_suboptimal3, bestMean_lt_max3, meanClass_isTestClass S3_subset,
    hasMeanProperty_meanClass⟩

/-- Hypotheses of `order_chain` (prop:order (c)). -/
lemma order_chain_satisfiable :
    ∃ (S : Finset ℝ) (hSne : S.Nonempty) (L : Bool → ℝ) (ν ν' : Kernel Bool ℝ) (a : Bool),
      2 ≤ Fintype.card Bool ∧ (∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) ∧ 2 ≤ S.card ∧ (∀ k, 0 < L k) ∧
      ν ∈ supportBandits S Bool ∧ ν' ∈ supportBandits S Bool ∧ (ν a)[id] < bestMean ν ∧
      bestMean ν < S.max' hSne :=
  ⟨S3, S3_nonempty, fun _ ↦ 1, nu3, nu3, false, card_bool, S3_subset, S3_card, fun _ ↦ one_pos,
    nu3_mem, nu3_mem, false_suboptimal3, bestMean_lt_max3⟩

/-- Hypotheses of `criteria_gain_over_mean` (prop:criteria (a)), with the premises of its
conclusion: the projections `Q⋆ = ½ δ_0 + ½ δ_1` and `Q'⋆ = ¾ δ_0 + ¼ δ_1` (both in the binding
case, `L ≡ 1/4`, `K'_0 = log (4/3)`) and `c = 1`, with `c K'_0 < 1`. -/
lemma criteria_gain_over_mean_satisfiable :
    ∃ (S : Finset ℝ) (hSne : S.Nonempty) (L : Bool → ℝ) (ν ν' : Kernel Bool ℝ) (a : Bool)
      (𝓕 : Set (S → ℝ)) (c : ℝ) (Q Q' : S → ℝ),
      2 ≤ Fintype.card Bool ∧ (∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) ∧ 2 ≤ S.card ∧ (∀ k, 0 < L k) ∧
      ν ∈ supportBandits S Bool ∧ ν' ∈ supportBandits S Bool ∧ (ν a)[id] < bestMean ν ∧
      bestMean ν < S.max' hSne ∧
      IsTestClass 𝓕 ∧ HasMeanProperty 𝓕 ∧ (ν' a)[id] ≤ bestMean ν + L a ∧ 0 < c ∧
      ENNReal.ofReal c * vecKs S (lawVec S (ν' a)) (bestMean ν - L a) < 1 ∧
      IsKLProj (lawVec S (ν a)) (bestMean ν) Q ∧ IsKLProj (lawVec S (ν' a)) (bestMean ν - L a) Q' :=
  ⟨S3, S3_nonempty, fun _ ↦ 1 / 4, nu3, nu3, false, meanClass S3, 1, _, _, card_bool, S3_subset,
    S3_card, fun _ ↦ by norm_num, nu3_mem, nu3_mem, false_suboptimal3, bestMean_lt_max3,
    meanClass_isTestClass S3_subset, hasMeanProperty_meanClass, mean_cond3', one_pos, K0P3_lt,
    isKLProj_Q3, isKLProj_Q3'⟩

/-- Hypotheses of `criteria_source_helps` (prop:criteria (b)), with the projection
`Q⋆ = ½ δ_0 + ½ δ_1` of its conclusion. -/
lemma criteria_source_helps_satisfiable :
    ∃ (S : Finset ℝ) (hSne : S.Nonempty) (L : Bool → ℝ) (ν ν' : Kernel Bool ℝ) (a : Bool)
      (𝓕 : Set (S → ℝ)) (c : ℝ) (Q : S → ℝ),
      2 ≤ Fintype.card Bool ∧ (∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) ∧ 2 ≤ S.card ∧ (∀ k, 0 < L k) ∧
      ν ∈ supportBandits S Bool ∧ ν' ∈ supportBandits S Bool ∧ (ν a)[id] < bestMean ν ∧
      bestMean ν < S.max' hSne ∧
      IsTestClass 𝓕 ∧ 0 < c ∧ IsKLProj (lawVec S (ν a)) (bestMean ν) Q :=
  ⟨S3, S3_nonempty, fun _ ↦ 1 / 4, nu3, nu3, false, meanClass S3, 1, _, card_bool, S3_subset,
    S3_card, fun _ ↦ by norm_num, nu3_mem, nu3_mem, false_suboptimal3, bestMean_lt_max3,
    meanClass_isTestClass S3_subset, one_pos, isKLProj_Q3⟩

/-- Hypotheses of `criteria_source_helps_mean` (prop:criteria (b), mean gap). -/
lemma criteria_source_helps_mean_satisfiable :
    ∃ (S : Finset ℝ) (hSne : S.Nonempty) (L : Bool → ℝ) (ν ν' : Kernel Bool ℝ) (a : Bool)
      (c : ℝ),
      2 ≤ Fintype.card Bool ∧ (∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) ∧ 2 ≤ S.card ∧ (∀ k, 0 < L k) ∧
      ν ∈ supportBandits S Bool ∧ ν' ∈ supportBandits S Bool ∧ (ν a)[id] < bestMean ν ∧
      bestMean ν < S.max' hSne ∧ 0 < c :=
  ⟨S3, S3_nonempty, fun _ ↦ 1, nu3, nu3, false, 1, card_bool, S3_subset, S3_card, fun _ ↦ one_pos,
    nu3_mem, nu3_mem, false_suboptimal3, bestMean_lt_max3, one_pos⟩

/-- Hypotheses of `threshold_iff` (prop:threshold (a)). -/
lemma threshold_iff_satisfiable :
    ∃ (S : Finset ℝ) (hSne : S.Nonempty) (L : Bool → ℝ) (ν ν' : Kernel Bool ℝ) (a : Bool)
      (𝓕 : Set (S → ℝ)),
      2 ≤ Fintype.card Bool ∧ (∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) ∧ 2 ≤ S.card ∧ (∀ k, 0 < L k) ∧
      ν ∈ supportBandits S Bool ∧ ν' ∈ supportBandits S Bool ∧ (ν a)[id] < bestMean ν ∧
      bestMean ν < S.max' hSne ∧ IsTestClass 𝓕 :=
  ⟨S3, S3_nonempty, fun _ ↦ 1, nu3, nu3, false, meanClass S3, card_bool, S3_subset, S3_card, fun _ ↦
    one_pos, nu3_mem, nu3_mem, false_suboptimal3, bestMean_lt_max3, meanClass_isTestClass S3_subset⟩

/-- Hypotheses of `threshold_mean_w1` (prop:threshold (b)). -/
lemma threshold_mean_w1_satisfiable :
    ∃ (S : Finset ℝ) (hSne : S.Nonempty) (L : Bool → ℝ) (ν ν' : Kernel Bool ℝ) (a : Bool),
      2 ≤ Fintype.card Bool ∧ (∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) ∧ 2 ≤ S.card ∧ (∀ k, 0 < L k) ∧
      ν ∈ supportBandits S Bool ∧ ν' ∈ supportBandits S Bool ∧ (ν a)[id] < bestMean ν ∧
      bestMean ν < S.max' hSne :=
  ⟨S3, S3_nonempty, fun _ ↦ 1, nu3, nu3, false, card_bool, S3_subset, S3_card, fun _ ↦ one_pos,
    nu3_mem, nu3_mem, false_suboptimal3, bestMean_lt_max3⟩

/-- Hypotheses of `threshold_tv` (prop:threshold (c)). -/
lemma threshold_tv_satisfiable :
    ∃ (S : Finset ℝ) (hSne : S.Nonempty) (L : Bool → ℝ) (ν ν' : Kernel Bool ℝ) (a : Bool),
      2 ≤ Fintype.card Bool ∧ (∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) ∧ 2 ≤ S.card ∧ (∀ k, 0 < L k) ∧
      ν ∈ supportBandits S Bool ∧ ν' ∈ supportBandits S Bool ∧ (ν a)[id] < bestMean ν ∧
      bestMean ν < S.max' hSne :=
  ⟨S3, S3_nonempty, fun _ ↦ 1, nu3, nu3, false, card_bool, S3_subset, S3_card, fun _ ↦ one_pos,
    nu3_mem, nu3_mem, false_suboptimal3, bestMean_lt_max3⟩

/-- Hypotheses of `bernoulli_no_gain` (prop:bernoulli). -/
lemma bernoulli_no_gain_satisfiable :
    ∃ (S : Finset ℝ) (hSne : S.Nonempty) (L : Bool → ℝ) (ν ν' : Kernel Bool ℝ) (a : Bool)
      (𝓕 : Set (S → ℝ)),
      2 ≤ Fintype.card Bool ∧ (∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) ∧ 2 ≤ S.card ∧ (∀ k, 0 < L k) ∧
      ν ∈ supportBandits S Bool ∧ ν' ∈ supportBandits S Bool ∧ (ν a)[id] < bestMean ν ∧
      bestMean ν < S.max' hSne ∧
      (ν' a)[id] ≤ bestMean ν + L a ∧ {0, 1} ⊆ S ∧ ν a ({0, 1} : Set ℝ)ᶜ = 0 ∧
      ν' a ({0, 1} : Set ℝ)ᶜ = 0 ∧ IsTestClass 𝓕 ∧ HasMeanProperty 𝓕 :=
  ⟨S3, S3_nonempty, fun _ ↦ 1, nu3, nu3, false, meanClass S3, card_bool, S3_subset, S3_card, fun _ ↦
    one_pos, nu3_mem, nu3_mem, false_suboptimal3, bestMean_lt_max3, mean_cond3, pair_subset3,
    carried01, carried01, meanClass_isTestClass S3_subset, hasMeanProperty_meanClass⟩

/-- Hypotheses of `w1_no_gain` (prop:w1). -/
lemma w1_no_gain_satisfiable :
    ∃ (S : Finset ℝ) (hSne : S.Nonempty) (L : Bool → ℝ) (ν ν' : Kernel Bool ℝ) (a : Bool),
      2 ≤ Fintype.card Bool ∧ (∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) ∧ 2 ≤ S.card ∧ (∀ k, 0 < L k) ∧
      ν ∈ supportBandits S Bool ∧ ν' ∈ supportBandits S Bool ∧ (ν a)[id] < bestMean ν ∧
      bestMean ν < S.max' hSne ∧ ν' a = ν a :=
  ⟨S3, S3_nonempty, fun _ ↦ 1, nu3, nu3, false, card_bool, S3_subset, S3_card, fun _ ↦ one_pos,
    nu3_mem, nu3_mem, false_suboptimal3, bestMean_lt_max3, rfl⟩

/-- Hypotheses of `tv_projections` (prop:tv (a)), with the projections `Q⋆ = ½ δ_0 + ½ δ_1` and
`Q'⋆ = ¾ δ_0 + ¼ δ_1` of its conclusion. -/
lemma tv_projections_satisfiable :
    ∃ (S : Finset ℝ) (hSne : S.Nonempty) (L : Bool → ℝ) (ν ν' : Kernel Bool ℝ) (a : Bool)
      (Q Q' : S → ℝ),
      2 ≤ Fintype.card Bool ∧ (∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) ∧ 2 ≤ S.card ∧ (∀ k, 0 < L k) ∧
      ν ∈ supportBandits S Bool ∧ ν' ∈ supportBandits S Bool ∧ (ν a)[id] < bestMean ν ∧
      bestMean ν < S.max' hSne ∧
      0 < vecKs S (lawVec S (ν' a)) (bestMean ν - L a) ∧
      IsKLProj (lawVec S (ν a)) (bestMean ν) Q ∧ IsKLProj (lawVec S (ν' a)) (bestMean ν - L a) Q' :=
  ⟨S3, S3_nonempty, fun _ ↦ 1 / 4, nu3, nu3, false, _, _, card_bool, S3_subset, S3_card, fun _ ↦ by
    norm_num, nu3_mem, nu3_mem, false_suboptimal3, bestMean_lt_max3, K0P3_pos, isKLProj_Q3,
    isKLProj_Q3'⟩

/-! ### The instance of prop:tv (b)

The support `S = {0, 1/4, 1/2}` (so `x_max - x_min = 1/2 < 1`), the instance `ν = ν'` with
`ν true = δ_{1/4}` and `ν false = δ_0` (so `μ⋆ = 1/4 < 1/2 = x_max`), the bounds `L ≡ 1/8`. The
projections of `δ_0` are `Q⋆ = ½ δ_0 + ½ δ_{1/2}` (level `1/4`) and `Q'⋆ = ¾ δ_0 + ¼ δ_{1/2}`
(level `1/8`), so `K'_0 = log (4/3) ∈ (0, 1)` and `c = 1` has `c K'_0 < 1`. -/

/-- The support `{0, 1/4, 1/2}`. -/
noncomputable abbrev S4 : Finset ℝ := {0, 1 / 4, 1 / 2}

lemma S4_subset : ∀ y ∈ S4, y ∈ Set.Icc (0 : ℝ) 1 := by
  intro y hy
  simp only [S4, Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl | rfl <;> norm_num

lemma S4_le : ∀ y ∈ S4, y ≤ 1 / 2 := by
  intro y hy
  simp only [S4, Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl | rfl <;> norm_num

lemma S4_card : 2 ≤ S4.card := by
  rw [S4, Finset.card_insert_of_notMem (by norm_num), Finset.card_pair (by norm_num)]
  norm_num

lemma S4_nonempty : S4.Nonempty := ⟨0, by simp⟩

lemma S4_max : S4.max' S4_nonempty = 1 / 2 :=
  le_antisymm (S4.max'_le _ _ S4_le) (S4.le_max' _ (by simp))

lemma S4_min : S4.min' S4_nonempty = 0 := by
  refine le_antisymm (S4.min'_le _ (by simp)) (S4.le_min' _ _ fun y hy ↦ (S4_subset y hy).1)

/-- The point `1/4` of `S4`. -/
noncomputable abbrev quarter4 : S4 := ⟨1 / 4, by simp⟩
/-- The point `1/2` of `S4`. -/
noncomputable abbrev half4 : S4 := ⟨1 / 2, by simp⟩
/-- The point `0` of `S4`. -/
noncomputable abbrev zero4 : S4 := ⟨0, by simp⟩

/-- The instance `δ_{1/4}` on arm `true`, `δ_0` on arm `false`. -/
noncomputable abbrev nu4 : Kernel Bool ℝ :=
  Kernel.deterministic (fun b ↦ ((if b then quarter4 else zero4 : S4) : ℝ))
    (measurable_of_countable _)

lemma nu4_mem : nu4 ∈ supportBandits S4 Bool :=
  deterministic_mem_supportBandits _

lemma mean_nu4 (b : Bool) : (nu4 b)[id] = if b then 1 / 4 else 0 := by
  rw [Kernel.deterministic_apply, integral_dirac]
  cases b <;> simp

lemma bestMean_nu4 : bestMean nu4 = 1 / 4 := by
  unfold bestMean
  refine le_antisymm (ciSup_le fun b ↦ ?_) ?_
  · rw [mean_nu4]; split_ifs <;> norm_num
  · refine le_ciSup_of_le (Set.finite_range _).bddAbove true ?_
    rw [mean_nu4]; simp

lemma lawVec_nu4_false : lawVec S4 (nu4 false) = Pi.single zero4 1 := by
  simp only [Kernel.deterministic_apply, Bool.false_eq_true, ↓reduceIte]
  exact lawVec_dirac zero4

lemma level4 : bestMean nu4 - (fun _ : Bool ↦ (1 / 8 : ℝ)) false = 1 / 8 := by
  rw [bestMean_nu4]; norm_num

/-- Hypotheses of `tv_strict_gain` (prop:tv (b)), with the premises of its conclusion: the
projections `Q⋆ = ½ δ_0 + ½ δ_{1/2}` and `Q'⋆ = ¾ δ_0 + ¼ δ_{1/2}`, the first disjunct
`x_max - x_min = 1/2 < 1`, and `c = 1` with `c K'_0 = log (4/3) < 1`. -/
lemma tv_strict_gain_satisfiable :
    ∃ (S : Finset ℝ) (hSne : S.Nonempty) (L : Bool → ℝ) (ν ν' : Kernel Bool ℝ) (a : Bool)
      (Q Q' : S → ℝ) (c : ℝ),
      2 ≤ Fintype.card Bool ∧ (∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) ∧ 2 ≤ S.card ∧ (∀ k, 0 < L k) ∧
      ν ∈ supportBandits S Bool ∧ ν' ∈ supportBandits S Bool ∧ (ν a)[id] < bestMean ν ∧
      bestMean ν < S.max' hSne ∧
      0 < vecKs S (lawVec S (ν' a)) (bestMean ν - L a) ∧
      IsKLProj (lawVec S (ν a)) (bestMean ν) Q ∧ IsKLProj (lawVec S (ν' a)) (bestMean ν - L a) Q' ∧
      (S.max' hSne - S.min' hSne < 1 ∨
        ∃ y : S, S.min' hSne < y ∧ (y : ℝ) < S.max' hSne ∧ Q y ≠ Q' y) ∧
      0 < c ∧ ENNReal.ofReal c * vecKs S (lawVec S (ν' a)) (bestMean ν - L a) < 1 := by
  refine ⟨S4, S4_nonempty, fun _ ↦ 1 / 8, nu4, nu4, false,
    Pi.single zero4 (1 - 1 / 4 / (1 / 2)) + Pi.single half4 (1 / 4 / (1 / 2)),
    Pi.single zero4 (1 - 1 / 8 / (1 / 2)) + Pi.single half4 (1 / 8 / (1 / 2)), 1, card_bool,
    S4_subset, S4_card, fun _ ↦ by norm_num, nu4_mem, nu4_mem, ?_, ?_, ?_, ?_, ?_, ?_, one_pos, ?_⟩
  · rw [mean_nu4, bestMean_nu4]; norm_num
  · rw [bestMean_nu4, S4_max]; norm_num
  · rw [lawVec_nu4_false, level4]
    exact vecKs_single_zero_pos S4_le rfl (by norm_num) (by norm_num)
  · rw [lawVec_nu4_false, bestMean_nu4]
    exact isKLProj_single_zero S4_le rfl rfl (by norm_num) (by norm_num)
  · rw [lawVec_nu4_false, level4]
    exact isKLProj_single_zero S4_le rfl rfl (by norm_num) (by norm_num)
  · left
    rw [S4_max, S4_min]
    norm_num
  · rw [lawVec_nu4_false, level4]
    exact one_mul_vecKs_single_zero_lt_one S4_le rfl (y₁ := half4) rfl (by norm_num)
      (by norm_num)

/-! ### The instance of prop:tv (c)

The support `S = {0, 1/8, 1/4, 1/2, 1}`, the instance `ν = ν'` with `ν true = δ_{1/2}` and
`ν false = (δ_{1/8} + δ_{1/4}) / 2` (two interior atoms, mean `3/16`), the bounds `L ≡ 1/8`: then
`μ⋆ - L = 3/8 > 1/4`, so `K'_0 > 0` (`vecKs_pos_of_support_le`). -/

/-- The support `{0, 1/8, 1/4, 1/2, 1}`. -/
noncomputable abbrev S5 : Finset ℝ := {0, 1 / 8, 1 / 4, 1 / 2, 1}

lemma S5_subset : ∀ y ∈ S5, y ∈ Set.Icc (0 : ℝ) 1 := by
  intro y hy
  simp only [S5, Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl <;> norm_num

lemma S5_card : 2 ≤ S5.card := by
  calc 2 = ({0, 1} : Finset ℝ).card := (Finset.card_pair (by norm_num)).symm
    _ ≤ S5.card := Finset.card_le_card (by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl <;> simp)

lemma S5_nonempty : S5.Nonempty := ⟨0, by simp⟩

/-- The law `(δ_{1/8} + δ_{1/4}) / 2`. -/
noncomputable abbrev mix5 : Measure ℝ :=
  (2⁻¹ : ℝ≥0∞) • Measure.dirac (1 / 8 : ℝ) + (2⁻¹ : ℝ≥0∞) • Measure.dirac (1 / 4 : ℝ)

lemma isProbabilityMeasure_mix5 : IsProbabilityMeasure mix5 :=
  ⟨by simp [mix5, ENNReal.inv_two_add_inv_two]⟩

/-- The instance `δ_{1/2}` on arm `true`, `(δ_{1/8} + δ_{1/4}) / 2` on arm `false`. -/
noncomputable abbrev nu5 : Kernel Bool ℝ :=
  Kernel.ofFunOfCountable fun b ↦ if b then Measure.dirac (1 / 2 : ℝ) else mix5

lemma nu5_apply (b : Bool) : nu5 b = if b then Measure.dirac (1 / 2 : ℝ) else mix5 := rfl

lemma isMarkovKernel_nu5 : IsMarkovKernel nu5 := by
  refine ⟨fun b ↦ ?_⟩
  rw [nu5_apply]
  cases b
  · exact isProbabilityMeasure_mix5
  · simp only [↓reduceIte]
    infer_instance

lemma nu5_mem : nu5 ∈ supportBandits S5 Bool := by
  refine ⟨isMarkovKernel_nu5, fun b ↦ ?_⟩
  rw [nu5_apply]
  cases b
  · simp [mix5]
  · simp

lemma mean_nu5 (b : Bool) : (nu5 b)[id] = if b then 1 / 2 else 3 / 16 := by
  rw [nu5_apply]
  cases b
  · have hi : ∀ x : ℝ, Integrable id ((2⁻¹ : ℝ≥0∞) • Measure.dirac x) :=
      fun x ↦ (integrable_dirac (by simp)).smul_measure (by simp)
    simp only [Bool.false_eq_true, ↓reduceIte, mix5]
    rw [integral_add_measure (hi _) (hi _), integral_smul_measure, integral_smul_measure,
      integral_dirac, integral_dirac]
    norm_num
  · simp

lemma bestMean_nu5 : bestMean nu5 = 1 / 2 := by
  unfold bestMean
  refine le_antisymm (ciSup_le fun b ↦ ?_) ?_
  · rw [mean_nu5]; split_ifs <;> norm_num
  · refine le_ciSup_of_le (Set.finite_range _).bddAbove true ?_
    rw [mean_nu5]; simp

lemma lawVec_nu5_mem : lawVec S5 (nu5 false) ∈ probVecs S5 := by
  have := isProbabilityMeasure_mix5
  exact lawVec_mem_probVecs (nu5_mem.2 false)

lemma lawVec_nu5_supp : ∀ y : S5, 0 < lawVec S5 (nu5 false) y → (y : ℝ) ≤ 1 / 4 := by
  intro y hy
  by_contra h
  have h8 : (1 / 8 : ℝ) ≠ y := by intro e; rw [← e] at h; norm_num at h
  have h4 : (1 / 4 : ℝ) ≠ y := by intro e; rw [← e] at h; norm_num at h
  have h0 : nu5 false {(y : ℝ)} = 0 := by
    rw [nu5_apply]
    simp only [Bool.false_eq_true, ↓reduceIte, mix5, add_apply, smul_apply,
      Measure.dirac_apply' _ (measurableSet_singleton _),
      Set.indicator_of_notMem (show (1 / 8 : ℝ) ∉ ({(y : ℝ)} : Set ℝ) from
        fun e ↦ h8 (Set.mem_singleton_iff.mp e)),
      Set.indicator_of_notMem (show (1 / 4 : ℝ) ∉ ({(y : ℝ)} : Set ℝ) from
        fun e ↦ h4 (Set.mem_singleton_iff.mp e)), smul_zero, add_zero]
  unfold lawVec at hy
  rw [h0] at hy
  simp at hy

lemma K0P5_pos :
    0 < vecKs S5 (lawVec S5 (nu5 false)) (bestMean nu5 - (fun _ : Bool ↦ (1 / 8 : ℝ)) false) := by
  rw [bestMean_nu5]
  exact vecKs_pos_of_support_le S5_subset lawVec_nu5_mem (b := 1 / 4) (by norm_num)
    lawVec_nu5_supp

/-- Hypotheses of `tv_strict_gain_self` (prop:tv (c)). -/
lemma tv_strict_gain_self_satisfiable :
    ∃ (S : Finset ℝ) (hSne : S.Nonempty) (L : Bool → ℝ) (ν ν' : Kernel Bool ℝ) (a : Bool),
      2 ≤ Fintype.card Bool ∧ (∀ y ∈ S, y ∈ Set.Icc (0 : ℝ) 1) ∧ 2 ≤ S.card ∧ (∀ k, 0 < L k) ∧
      ν ∈ supportBandits S Bool ∧ ν' ∈ supportBandits S Bool ∧ (ν a)[id] < bestMean ν ∧
      bestMean ν < S.max' hSne ∧ 0 < vecKs S (lawVec S (ν' a)) (bestMean ν - L a) ∧
      ν' a = ν a ∧
      ∃ y z : ℝ, y ≠ z ∧ S.min' hSne < y ∧ y < S.max' hSne ∧
        S.min' hSne < z ∧ z < S.max' hSne ∧ 0 < ν a {y} ∧ 0 < ν a {z} := by
  have hmin : S5.min' S5_nonempty < 1 / 8 := (S5.min'_le 0 (by simp)).trans_lt (by norm_num)
  have hmax : (1 / 2 : ℝ) < S5.max' S5_nonempty :=
    lt_of_lt_of_le (by norm_num) (S5.le_max' 1 (by simp))
  refine ⟨S5, S5_nonempty, fun _ ↦ 1 / 8, nu5, nu5, false, card_bool, S5_subset, S5_card,
    fun _ ↦ by norm_num, nu5_mem, nu5_mem, ?_, ?_, K0P5_pos, rfl, 1 / 8, 1 / 4, by norm_num,
    hmin, by linarith, by linarith, by linarith, ?_, ?_⟩
  · rw [mean_nu5, bestMean_nu5]; norm_num
  · rw [bestMean_nu5]; exact hmax
  · rw [nu5_apply]; simp [mix5, Measure.dirac_apply' _ (measurableSet_singleton _)]
  · rw [nu5_apply]; simp [mix5, Measure.dirac_apply' _ (measurableSet_singleton _)]


end Incognita.P002
