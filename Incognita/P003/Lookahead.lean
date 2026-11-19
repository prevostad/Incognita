/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.ForMathlib.Probability.Distributions.Bernoulli
public import Incognita.ForMathlib.Probability.ProductMeasure
public import Incognita.P003.Exclusions
public import Incognita.TransferBandits.SourceKL
public import LMLExplore.InformationTheory.KullbackLeibler.Bernoulli
public import TauCeti.InformationTheory.KullbackLeibler.ChainRule

/-! # P003, thm:main (b): the decomposition fails for the look-ahead map

Proof of [INC-P003, thm:main (b)], following the paper's proof.

## Main statements

* `map_sourceMeasure_pair`: under `P'_{ν'}`, the first two values `(X'_{a₁,1}, X'_{a₁,2})` of the
  stack of `a₁` have law `ν'_{a₁} ⊗ ν'_{a₁}`.
* `exists_sourceData_lookahead`: the source data of the look-ahead map are `Φ(X'_{a₁,1}, X'_{a₁,2})`
  for a measurable `Φ`, which has a measurable left inverse on `ℝ × {0, 1}`.
* `klDiv_sourceLaw_lookahead`: for source laws of `a₁` concentrated on `{0, 1}`, the divergence of
  the laws of the source data is that of the laws of the first two values.
* `lintegral_lookahead`: `E_{ν'}[N^la_{a₁}] = 2 - p` when `ν'_{a₁} = Ber(p)`.
* `lookahead_divergence`: the frozen statement.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Incognita.TransferBandits

open scoped ENNReal unitInterval

namespace Incognita.P003

section Helpers

variable {α : Type*} [DecidableEq α] [MeasurableSpace α]

omit [DecidableEq α] in
/-- Under `P'_{ν'}`, the first two values `(X'_{a₁,1}, X'_{a₁,2})` of the stack of `a₁` have law
`ν'_{a₁} ⊗ ν'_{a₁}`. -/
lemma map_sourceMeasure_pair (ν' : Kernel α ℝ) [IsMarkovKernel ν'] (a₁ : α) :
    (sourceMeasure ν').map (fun ω : SourceSpace α ↦ (ω.2 a₁ 0, ω.2 a₁ 1)) =
      (ν' a₁).prod (ν' a₁) := by
  have h : (fun ω : SourceSpace α ↦ (ω.2 a₁ 0, ω.2 a₁ 1)) =
      (fun w : ℕ → ℝ ↦ (w 0, w 1)) ∘ (fun z : α → ℕ → ℝ ↦ z a₁) ∘ Prod.snd := rfl
  rw [h, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_map (by fun_prop) measurable_snd, sourceMeasure, Measure.map_snd_prod,
    measure_univ, one_smul, Measure.infinitePi_map_eval, infinitePi_map_zero_one]

omit [MeasurableSpace α] in
/-- The source data of the look-ahead map are a measurable function `Φ` of the first two values
of the stack of `a₁`, and `Φ` has a measurable left inverse on `ℝ × {0, 1}` (the size tells
whether the second value is `1`). -/
lemma exists_sourceData_lookahead (a₁ : α) :
    ∃ Φ : ℝ × ℝ → Source α, Measurable Φ ∧
      sourceData (lookahead a₁) = Φ ∘ (fun ω : SourceSpace α ↦ (ω.2 a₁ 0, ω.2 a₁ 1)) ∧
      ∃ g : Source α → ℝ × ℝ, Measurable g ∧ ∀ x : ℝ × ℝ, (x.2 = 0 ∨ x.2 = 1) → g (Φ x) = x := by
  let n : ℝ → α → ℕ := fun y a ↦ if a = a₁ then (if (1 / 2 : ℝ) < y then 1 else 2) else 0
  have hn : Measurable n := by
    refine measurable_pi_iff.mpr fun a ↦ ?_
    by_cases ha : a = a₁
    · simp only [n, ha, ↓reduceIte]
      exact Measurable.ite measurableSet_Ioi measurable_const measurable_const
    · simp only [n, ha, ↓reduceIte]
      exact measurable_const
  refine ⟨fun x ↦ (n x.2, fun a j ↦ if j < n x.2 a then (if j = 0 then x.1 else x.2) else 0),
    ?_, ?_, ⟨fun s ↦ (s.2 a₁ 0, if s.1 a₁ = 1 then 1 else s.2 a₁ 1), ?_, ?_⟩⟩
  · refine (hn.comp measurable_snd).prodMk (measurable_pi_iff.mpr fun a ↦
      measurable_pi_iff.mpr fun j ↦ ?_)
    refine Measurable.ite ?_ (Measurable.ite (MeasurableSet.const _) measurable_fst
      measurable_snd) measurable_const
    exact measurableSet_lt measurable_const
      ((measurable_pi_apply a).comp (hn.comp measurable_snd))
  · funext ω
    refine Prod.ext rfl ?_
    funext a j
    simp only [sourceData, lookahead, Function.comp_apply, n]
    by_cases ha : a = a₁
    · subst ha
      by_cases hj : j = 0
      · subst hj
        simp
      · by_cases hj1 : j = 1
        · subst hj1
          simp
        · have : ¬ j < 2 := by omega
          have : ¬ j < 1 := by omega
          split_ifs <;> simp_all
    · simp [ha]
  · refine measurable_snd.eval.eval.prodMk (Measurable.ite ?_ measurable_const
      measurable_snd.eval.eval)
    exact measurableSet_eq_fun measurable_fst.eval measurable_const
  · rintro ⟨x₀, x₁⟩ hx
    simp only at hx
    rcases hx with rfl | rfl
    · norm_num [n]
    · norm_num [n]

/-- The divergence between the laws of the source data of the look-ahead map, for two source laws
of `a₁` concentrated on `{0, 1}`, is the divergence between the laws of the first two values. -/
lemma klDiv_sourceLaw_lookahead (a₁ : α) (ν' ν₂' : Kernel α ℝ) [IsMarkovKernel ν']
    [IsMarkovKernel ν₂'] (h₁ : ∀ᵐ x ∂(ν' a₁), x = 0 ∨ x = 1)
    (h₂ : ∀ᵐ x ∂(ν₂' a₁), x = 0 ∨ x = 1) :
    klDiv (sourceLaw ν' (lookahead a₁)) (sourceLaw ν₂' (lookahead a₁)) =
      klDiv ((ν' a₁).prod (ν' a₁)) ((ν₂' a₁).prod (ν₂' a₁)) := by
  obtain ⟨Φ, hΦ, hD, g, hg, hgΦ⟩ := exists_sourceData_lookahead a₁
  have hpair : Measurable fun ω : SourceSpace α ↦ (ω.2 a₁ 0, ω.2 a₁ 1) := by fun_prop
  have hlaw : ∀ (μ : Kernel α ℝ) [IsMarkovKernel μ],
      sourceLaw μ (lookahead a₁) = ((μ a₁).prod (μ a₁)).map Φ := fun μ _ ↦ by
    rw [sourceLaw, hD, ← Measure.map_map hΦ hpair, map_sourceMeasure_pair]
  have hinv : ∀ m : Measure ℝ, [IsProbabilityMeasure m] → (∀ᵐ x ∂m, x = 0 ∨ x = 1) →
      ((m.prod m).map Φ).map g = m.prod m := fun m _ hm ↦ by
    have hae : ∀ᵐ x ∂(m.prod m), x.2 = 0 ∨ x.2 = 1 := by
      refine ae_of_ae_map (p := fun y : ℝ ↦ y = 0 ∨ y = 1) measurable_snd.aemeasurable ?_
      rwa [Measure.map_snd_prod, measure_univ, one_smul]
    rw [Measure.map_map hg hΦ, Measure.map_congr (g := id) (by
      filter_upwards [hae] with x hx using hgΦ x hx), Measure.map_id]
  rw [hlaw ν', hlaw ν₂']
  refine le_antisymm (klDiv_map_le _ _ hΦ) ?_
  calc klDiv ((ν' a₁).prod (ν' a₁)) ((ν₂' a₁).prod (ν₂' a₁))
  _ = klDiv ((((ν' a₁).prod (ν' a₁)).map Φ).map g) ((((ν₂' a₁).prod (ν₂' a₁)).map Φ).map g) := by
    rw [hinv _ h₁, hinv _ h₂]
  _ ≤ _ := klDiv_map_le _ _ hg

/-- The expected size of the look-ahead map on `a₁` is `2 - p` when `ν'_{a₁} = Ber(p)`: the size
is `1` with probability `p` (second value `1`) and `2` otherwise. -/
lemma lintegral_lookahead (a₁ : α) (ν' : Kernel α ℝ) [IsMarkovKernel ν'] {p : I}
    (h₁ : ν' a₁ = Ber((1 : ℝ), 0, p)) :
    ∫⁻ ω, (lookahead a₁ ω a₁ : ℝ≥0∞) ∂(sourceMeasure ν') = ENNReal.ofReal (2 - p) := by
  have hf : Measurable fun y : ℝ ↦ ((if (1 / 2 : ℝ) < y then 1 else 2 : ℕ) : ℝ≥0∞) :=
    measurable_from_top.comp (Measurable.ite measurableSet_Ioi measurable_const measurable_const)
  have hsnd : Measurable fun ω : SourceSpace α ↦ ω.2 a₁ 1 := by fun_prop
  have hmap : (sourceMeasure ν').map (fun ω : SourceSpace α ↦ ω.2 a₁ 1) = ν' a₁ :=
    map_eval_sourceMeasure ν' a₁ 1
  have heq : ∀ ω : SourceSpace α, (lookahead a₁ ω a₁ : ℝ≥0∞) =
      ((if (1 / 2 : ℝ) < ω.2 a₁ 1 then 1 else 2 : ℕ) : ℝ≥0∞) := fun ω ↦ by
    simp [lookahead]
  rw [lintegral_congr heq,
    ← lintegral_map (f := fun y : ℝ ↦ ((if (1 / 2 : ℝ) < y then 1 else 2 : ℕ) : ℝ≥0∞)) hf hsnd,
    hmap, h₁, bernoulliMeasure_def, lintegral_add_measure, lintegral_smul_measure,
    lintegral_smul_measure, lintegral_dirac, lintegral_dirac]
  have hp0 : (0 : ℝ) ≤ p := p.2.1
  have hp1 : (p : ℝ) ≤ 1 := p.2.2
  norm_num
  rw [ENNReal.smul_def, smul_eq_mul, ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_coe_nnreal (p := unitInterval.toNNReal (σ p)),
    ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  simp only [unitInterval.toNNReal, unitInterval.coe_symm_eq]
  -- the coercions to `ℝ` of `p` and of `σ p = 1 - p`, by definition
  change (p : ℝ) + (1 - (p : ℝ)) * 2 = 2 - p
  ring


end Helpers

/-- [INC-P003, thm:main (b)] For the look-ahead map, `KL(P, P₂) = 2 kl(p, q)` while the right-hand
side of the decomposition is `(2 - p) kl(p, q) < 2 kl(p, q)`; the look-ahead map is a bounded
size map and not a size rule. -/
theorem lookahead_divergence {α : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (hK : 2 ≤ Fintype.card α) (a₁ : α)
    {p q : I} (hp : (p : ℝ) ∈ Set.Ioo 0 1) (hq : (q : ℝ) ∈ Set.Ioo 0 1) (hpq : p ≠ q)
    (π : TransferAlgorithm α) (T : ℕ) {ν ν' ν₂' : Kernel α ℝ}
    (hν : ν ∈ unitBandits α) (hν' : ν' ∈ unitBandits α)
    (h₁ : ν' a₁ = Ber((1 : ℝ), 0, p)) (h₂ : ν₂' a₁ = Ber((1 : ℝ), 0, q))
    (h₃ : ∀ a, a ≠ a₁ → ν₂' a = ν' a) :
    Measurable (lookahead a₁) ∧ (∃ M : ℕ, ∀ ω a, lookahead a₁ ω a ≤ M) ∧
      ¬ IsSizeRule (lookahead a₁) ∧
      klDiv (gameMeasure ν' (lookahead a₁) ν π T) (gameMeasure ν₂' (lookahead a₁) ν π T) =
        2 * klDiv (Ber((1 : ℝ), 0, p)) (Ber((1 : ℝ), 0, q)) ∧
      ∑ a, (∫⁻ x, (sourceCount a x.1 : ℝ≥0∞) ∂(gameMeasure ν' (lookahead a₁) ν π T)) *
          klDiv (ν' a) (ν₂' a) +
        ∑ a, (∫⁻ x, (onlineCount a x.2 : ℝ≥0∞) ∂(gameMeasure ν' (lookahead a₁) ν π T)) *
          klDiv (ν a) (ν a) =
        ENNReal.ofReal (2 - p) * klDiv (Ber((1 : ℝ), 0, p)) (Ber((1 : ℝ), 0, q)) ∧
      ENNReal.ofReal (2 - p) * klDiv (Ber((1 : ℝ), 0, p)) (Ber((1 : ℝ), 0, q)) <
        2 * klDiv (Ber((1 : ℝ), 0, p)) (Ber((1 : ℝ), 0, q)) := by
  have : IsMarkovKernel ν := hν.1
  have : IsMarkovKernel ν' := hν'.1
  have : IsMarkovKernel ν₂' := ⟨fun a ↦ by
    by_cases ha : a = a₁
    · rw [ha, h₂]
      infer_instance
    · rw [h₃ a ha]
      infer_instance⟩
  obtain ⟨hmeas, hbdd, hnot⟩ := lookahead_not_isSizeRule hK a₁
  have hpI : (p : ℝ) ∈ Set.Icc 0 1 := ⟨hp.1.le, hp.2.le⟩
  have hqI : (q : ℝ) ∈ Set.Icc 0 1 := ⟨hq.1.le, hq.2.le⟩
  have hK0 : klDiv (Ber((1 : ℝ), 0, p)) (Ber((1 : ℝ), 0, q)) ≠ 0 := by
    rw [LMLExplore.klDiv_bernoulliMeasure, Ne, LMLExplore.klBer_eq_zero_iff hpI hqI]
    exact fun h ↦ hpq (Subtype.ext h)
  have hKtop : klDiv (Ber((1 : ℝ), 0, p)) (Ber((1 : ℝ), 0, q)) ≠ ∞ := by
    rw [LMLExplore.klDiv_bernoulliMeasure, LMLExplore.klBer_ne_top_iff hpI hqI]
    exact ⟨fun h ↦ absurd h hq.1.ne', fun h ↦ absurd h hq.2.ne⟩
  have hgame := lintegral_sourceCount_gameMeasure hmeas ν' ν π T a₁
  refine ⟨hmeas, hbdd, hnot, ?_, ?_, ?_⟩
  · -- `KL(P, P₂)`: the online kernels agree, and the divergence of the source data is that of
    -- the first two values of `a₁`
    rw [gameMeasure, gameMeasure, klDiv_compProd_left,
      klDiv_sourceLaw_lookahead a₁ ν' ν₂' (by rw [h₁]; exact ae_bernoulli_zero_or_one p)
        (by rw [h₂]; exact ae_bernoulli_zero_or_one q), h₁, h₂, TauCeti.klDiv_prod_prod, two_mul]
  · -- the right side: only `a₁` has a positive divergence, and `E[N'_(a₁)] = 2 - p`
    rw [Finset.sum_eq_single a₁ (fun b _ hb ↦ by rw [h₃ b hb, klDiv_self, mul_zero])
      (by simp)]
    simp only [klDiv_self, mul_zero, Finset.sum_const_zero, add_zero]
    rw [hgame, lintegral_lookahead a₁ ν' h₁, h₁, h₂]
  · -- `(2 - p) kl(p, q) < 2 kl(p, q)`, since `0 < kl(p, q) < ∞` and `p > 0`
    rw [mul_comm _ (klDiv _ _), mul_comm 2 (klDiv _ _)]
    refine ENNReal.mul_lt_mul_right hK0 hKtop ?_
    rw [← ENNReal.ofReal_ofNat 2]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by linarith [hp.1])

end Incognita.P003
