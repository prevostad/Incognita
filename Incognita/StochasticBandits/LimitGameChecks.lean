/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.ForTauCeti.Probability.BrownianMotion.Martingale
public import Incognita.StochasticBandits.LimitGame
public import TauCeti.Probability.BrownianMotion.ExponentialMartingale

/-! # Checks of the definitions of the limit game

The checks of AGENTS.md §6.4 for the definitions of `Incognita.StochasticBandits.LimitGame`
[INC-P001, Definitions `def:alloc`, `def:limit`, `def:risk`, `def:batched`].

A limit policy needs a Brownian motion: `X_k` is a continuous martingale with bracket `τ_k`, and
`∑_k τ_k(t) = t`. Mathlib defines Brownian motion (`ProbabilityTheory.IsPreBrownianReal`,
`IsBrownianReal`) but does not construct one, so the witness is stated for any Brownian motion
`W` relative to a filtration (Tau Ceti's `IsFilteredPreBrownianReal`) with continuous paths
starting at `0`: the policy that gives all the time to one arm `k₀` and observes `W` on it is a
limit policy (`isLimitPolicy_singleArmPolicy`). Its risk is the regret of always pulling `k₀`,
`max_i h_i - h_{k₀}` (`risk_singleArmPolicy`).

## Main statements

* `singleArm_mem_allocations` (witness), `uniform_mem_allocations` (known case: the uniform
  allocation `τ_k(t) = t / K`), `zero_not_mem_allocations` (exclusion).
* `isLimitPolicy_singleArmPolicy` (witness, given a Brownian motion),
  `IsLimitPolicy.integral_sq_eq` (known case: Wald's identity `E[X_k(t)²] = E[τ_k(t)]`),
  `not_isLimitPolicy_dirac` (exclusion: allocating time without observing anything is not a
  limit policy).
* `risk_zero` (known case: the instance `h = 0` has no regret), `risk_singleArmPolicy` (known
  case: the regret `max_i h_i - h_{k₀}` of always pulling `k₀`; exclusion: it is positive when
  `k₀` is not optimal, so the risk is not identically `0`).
* `value_eq_valueOn_univ`, `valueOn_mono`, `bayesValue_dirac`, `localValue_le_value` (known
  cases: `V_K = V_K(ℝ^K)`, monotonicity in `H`, the Bayes value of a point mass is the value of
  the point, `V_K^loc ≤ V_K`), `valueOn_singleton_zero` (witness, given a Brownian motion:
  `V_K({0}) = 0`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory TauCeti.Probability

open scoped ENNReal NNReal unitInterval

namespace Incognita.StochasticBandits.LimitGame

variable (α : Type*) [Fintype α]

/-! ### Allocations -/

/-- The values of an allocation lie in `[0, 1]`. -/
lemma mem_Icc_of_mem_allocations {τ : C(I, α → ℝ)} (hτ : τ ∈ allocations α) (t : I) (k : α) :
    τ t k ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨hmono, h0, hsum⟩ := hτ
  have hnn : ∀ j, 0 ≤ τ t j := fun j ↦ by
    simpa [h0] using hmono j (unitInterval.nonneg' (t := t))
  refine ⟨hnn k, ?_⟩
  calc τ t k ≤ ∑ j, τ t j := Finset.single_le_sum (fun j _ ↦ hnn j) (Finset.mem_univ k)
    _ = t := hsum t
    _ ≤ 1 := t.2.2

/-- The set of the pairs `(X, τ)` with `X(0) = 0` and `τ` an allocation is closed, hence
measurable. -/
lemma measurableSet_setOf_mem_allocations :
    MeasurableSet {ω : Omega α | ω.1 0 = 0 ∧ ω.2 ∈ allocations α} := by
  rw [Set.ofPred_and]
  refine IsClosed.measurableSet (IsClosed.inter ?_ ?_)
  · exact isClosed_eq (by fun_prop) continuous_const
  · have h1 : IsClosed {ω : Omega α | ∀ k, Monotone fun t ↦ ω.2 t k} := by
      simp only [Monotone, Set.ofPred_forall]
      exact isClosed_iInter fun k ↦ isClosed_iInter fun s ↦ isClosed_iInter fun t ↦
        isClosed_iInter fun _ ↦ isClosed_le (by fun_prop) (by fun_prop)
    have h2 : IsClosed {ω : Omega α | ω.2 0 = 0} := isClosed_eq (by fun_prop) continuous_const
    have h3 : IsClosed {ω : Omega α | ∀ t, ∑ k, ω.2 t k = t} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun t ↦ isClosed_eq (by fun_prop) continuous_const
    have : {ω : Omega α | ω.2 ∈ allocations α} =
        {ω : Omega α | ∀ k, Monotone fun t ↦ ω.2 t k} ∩ {ω : Omega α | ω.2 0 = 0} ∩
          {ω : Omega α | ∀ t, ∑ k, ω.2 t k = t} := by
      ext ω
      simp [allocations, and_assoc]
    rw [this]
    exact (h1.inter h2).inter h3

/-- **Known case**: the uniform allocation `τ_k(t) = t / K`, which plays the arms in turn. -/
lemma uniform_mem_allocations [Nonempty α] :
    (⟨fun t _ ↦ (t : ℝ) / Fintype.card α, by fun_prop⟩ : C(I, α → ℝ)) ∈ allocations α := by
  refine ⟨fun k s t hst ↦ ?_, ?_, fun t ↦ ?_⟩
  · simp only [ContinuousMap.coe_mk]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hst) (Nat.cast_nonneg _)
  · ext k
    simp
  · simp only [ContinuousMap.coe_mk, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp

/-- **Exclusion**: the zero path allocates no time, so it is not an allocation. -/
lemma zero_not_mem_allocations : (0 : C(I, α → ℝ)) ∉ allocations α := by
  rintro ⟨-, -, h⟩
  simpa using h 1

/-! ### Martingales on the canonical space -/

variable {α}

/-- A continuous function of the coordinate `(X(t), τ(t))` is `𝓕_t`-measurable. -/
lemma stronglyMeasurable_comp_coord {g : (α → ℝ) × (α → ℝ) → ℝ} (hg : Continuous g) (t : I) :
    StronglyMeasurable[filtration α t] fun ω : Omega α ↦ g (ω.1 t, ω.2 t) :=
  hg.comp_stronglyMeasurable (Filtration.stronglyAdapted_natural
    (fun t ↦ (measurable_coord α t).stronglyMeasurable) t)

/-- The preimage of a set of `𝓕_s` by a map whose coordinates up to time `s` are
`G`-measurable is `G`-measurable. -/
lemma measurableSet_preimage_of_coord {Ω' : Type*} {G : MeasurableSpace Ω'} {Φ : Ω' → Omega α}
    {s : I} (hΦ : ∀ r ≤ s, Measurable[G] fun ω ↦ ((Φ ω).1 r, (Φ ω).2 r)) {A : Set (Omega α)}
    (hA : MeasurableSet[filtration α s] A) : MeasurableSet[G] (Φ ⁻¹' A) := by
  have hle : (filtration α s).comap Φ ≤ G := by
    change (⨆ r ≤ s, MeasurableSpace.comap (fun ω : Omega α ↦ (ω.1 r, ω.2 r)) inferInstance).comap
      Φ ≤ G
    simp_rw [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
    exact iSup₂_le fun r hr ↦ (hΦ r hr).comap_le
  exact hle _ ⟨A, hA, rfl⟩

/-- A process `f` on the canonical space is a martingale under the image `P.map Φ` of a finite
measure as soon as it is adapted, the `f t ∘ Φ` are integrable, and they have the martingale
set-integral identities on the preimages of the sets of `𝓕_s`. -/
lemma martingale_map {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω'} [IsFiniteMeasure P]
    {Φ : Ω' → Omega α} (hΦ : Measurable Φ) {f : I → Omega α → ℝ}
    (hf : StronglyAdapted (filtration α) f) (hint : ∀ t, Integrable (fun ω ↦ f t (Φ ω)) P)
    (hset : ∀ s t, s ≤ t → ∀ A, MeasurableSet[filtration α s] A →
      ∫ ω in Φ ⁻¹' A, f t (Φ ω) ∂P = ∫ ω in Φ ⁻¹' A, f s (Φ ω) ∂P) :
    Martingale f (filtration α) (P.map Φ) := by
  have hm : ∀ t, AEStronglyMeasurable (f t) (P.map Φ) := fun t ↦
    ((hf t).mono ((filtration α).le t)).aestronglyMeasurable
  have hint' : ∀ t, Integrable (f t) (P.map Φ) := fun t ↦
    (integrable_map_measure (hm t) hΦ.aemeasurable).2 (hint t)
  refine ⟨hf, fun s t hst ↦ ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq ((filtration α).le s) (hint' t)
    (fun A _ _ ↦ (hint' s).integrableOn) (fun A hA _ ↦ ?_) (hf s).aestronglyMeasurable).symm
  have hA' := (filtration α).le s A hA
  rw [setIntegral_map hA' (hm s) hΦ.aemeasurable, setIntegral_map hA' (hm t) hΦ.aemeasurable]
  exact (hset s t hst A hA).symm

/-- The integrand of the risk is measurable. -/
lemma measurable_likelihood_mul_loss (h : α → ℝ) :
    Measurable fun ω : Omega α ↦ ENNReal.ofReal (likelihood α h ω * loss α h ω) :=
  ENNReal.measurable_ofReal.comp (Continuous.measurable (by unfold likelihood loss; fun_prop))

/-- **Known case**: in the instance `h = 0` all the arms are optimal, and the risk is `0`. -/
lemma risk_zero (Q : Measure (Omega α)) : risk α Q 0 = 0 := by
  simp [risk, loss]

variable (α) [DecidableEq α]

/-- The allocation that gives all the time to the arm `k₀`: `τ(t) = t e_{k₀}`. -/
noncomputable def singleArm (k₀ : α) : C(I, α → ℝ) :=
  ⟨fun t ↦ Pi.single k₀ (t : ℝ), (continuous_single k₀).comp continuous_subtype_val⟩

/-- **Witness**: `t ↦ t e_{k₀}` is an allocation. -/
lemma singleArm_mem_allocations (k₀ : α) : singleArm α k₀ ∈ allocations α := by
  refine ⟨fun k s t hst ↦ ?_, ?_, fun t ↦ ?_⟩
  · simp only [singleArm, ContinuousMap.coe_mk]
    by_cases hk : k = k₀
    · subst hk
      simpa using hst
    · simp [hk]
  · ext k
    simp [singleArm]
  · simp [singleArm]

variable {α}

/-! ### Limit policies -/

section Policy

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω'} {ℱ : Filtration ℝ≥0 mΩ'}
  {W : ℝ≥0 → Ω' → ℝ}

/-- The path `t ↦ W(t) e_{k₀}` of the policy that observes `W` on the arm `k₀`. -/
noncomputable def singlePath (hcont : ∀ ω, Continuous (W · ω)) (k₀ : α) (ω : Ω') :
    C(I, α → ℝ) :=
  ⟨fun t ↦ Pi.single k₀ (W (t : ℝ).toNNReal ω),
    (continuous_single k₀).comp ((hcont ω).comp (by fun_prop))⟩

variable (α) in
/-- The map `ω ↦ (W e_{k₀}, t e_{k₀})` to the canonical space. -/
noncomputable def singleArmMap (hcont : ∀ ω, Continuous (W · ω)) (k₀ : α) (ω : Ω') :
    Omega α :=
  (singlePath hcont k₀ ω, singleArm α k₀)

/-- The policy `Q = law of (W e_{k₀}, t e_{k₀})`, which gives all the time to the arm `k₀` and
observes `W` on it. -/
noncomputable def singleArmPolicy (P : Measure Ω') (hcont : ∀ ω, Continuous (W · ω)) (k₀ : α) :
    Measure (Omega α) :=
  P.map (singleArmMap α hcont k₀)

omit [Fintype α] in
lemma singleArmMap_coord (hcont : ∀ ω, Continuous (W · ω)) (k₀ : α) (ω : Ω') (t : I) (k : α) :
    (singleArmMap α hcont k₀ ω).1 t k = (if k = k₀ then W (t : ℝ).toNNReal ω else 0) ∧
    (singleArmMap α hcont k₀ ω).2 t k = (if k = k₀ then (t : ℝ) else 0) := by
  simp [singleArmMap, singlePath, singleArm, Pi.single_apply]

omit [Fintype α] in
lemma singleArmMap_mul (hcont : ∀ ω, Continuous (W · ω)) (k₀ k j : α) (ω : Ω') (t : I) :
    (singleArmMap α hcont k₀ ω).1 t k * (singleArmMap α hcont k₀ ω).1 t j -
      (if k = j then (singleArmMap α hcont k₀ ω).2 t k else 0) =
    if k = k₀ ∧ j = k₀ then W (t : ℝ).toNNReal ω ^ 2 - t else 0 := by
  rw [(singleArmMap_coord hcont k₀ ω t k).1, (singleArmMap_coord hcont k₀ ω t j).1,
    (singleArmMap_coord hcont k₀ ω t k).2]
  by_cases hk : k = k₀ <;> by_cases hj : j = k₀
  · subst hk hj
    simp [sq]
  · subst hk
    simp [hj, Ne.symm hj]
  · subst hj
    simp [hk]
  · simp [hk, hj]

omit [Fintype α] in
lemma measurable_coord_singleArmMap [Finite α] (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ ω, Continuous (W · ω)) (k₀ : α) {r s : I} (hr : r ≤ s) :
    Measurable[ℱ (s : ℝ).toNNReal] fun ω ↦
      ((singleArmMap α hcont k₀ ω).1 r, (singleArmMap α hcont k₀ ω).2 r) := by
  refine Measurable.prodMk ?_ measurable_const
  have hm : Measurable[ℱ (s : ℝ).toNNReal] (W (r : ℝ).toNNReal) :=
    (hW.adapted _).mono (ℱ.mono (Real.toNNReal_le_toNNReal hr)) le_rfl
  exact (continuous_single k₀).measurable.comp hm

omit [Fintype α] in
lemma measurable_singleArmMap [Finite α] (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ ω, Continuous (W · ω)) (k₀ : α) : Measurable (singleArmMap α hcont k₀) := by
  refine Measurable.prodMk (ContinuousMap.measurable_iff_eval.2 fun t ↦ ?_) measurable_const
  exact (continuous_single k₀).measurable.comp (hW.measurable _)

/-- **Witness**: for a Brownian motion `W` relative to a filtration, with continuous paths starting
at `0`, the policy that gives all the time to the arm `k₀` and observes `W` on it is a limit
policy. -/
theorem isLimitPolicy_singleArmPolicy (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ ω, Continuous (W · ω)) (h0 : ∀ ω, W 0 ω = 0) (k₀ : α) :
    IsLimitPolicy α (singleArmPolicy P hcont k₀) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hΦ := measurable_singleArmMap hW hcont k₀
  have hpre : ∀ s : I, ∀ A, MeasurableSet[filtration α s] A →
      MeasurableSet[ℱ (s : ℝ).toNNReal] (singleArmMap α hcont k₀ ⁻¹' A) := fun s A hA ↦
    measurableSet_preimage_of_coord (fun r hr ↦ measurable_coord_singleArmMap hW hcont k₀ hr) hA
  have hst' : ∀ s t : I, s ≤ t → (s : ℝ).toNNReal ≤ (t : ℝ).toNNReal :=
    fun s t hst ↦ Real.toNNReal_le_toNNReal hst
  have hcoe : ∀ t : I, (((t : ℝ).toNNReal : ℝ≥0) : ℝ) = t := fun t ↦ Real.coe_toNNReal _ t.2.1
  refine ⟨by unfold singleArmPolicy; infer_instance, ?_, fun k ↦ ?_, fun k j ↦ ?_⟩
  · refine (ae_map_iff hΦ.aemeasurable (measurableSet_setOf_mem_allocations α)).2
      (ae_of_all _ fun ω ↦ ⟨?_, singleArm_mem_allocations α k₀⟩)
    ext k
    simp [singleArmMap, singlePath, h0]
  · refine martingale_map hΦ (fun t ↦ stronglyMeasurable_comp_coord (g := fun p ↦ p.1 k)
      (by fun_prop) t) (fun t ↦ ?_) (fun s t hst A hA ↦ ?_)
    · simp only [(singleArmMap_coord hcont k₀ _ t k).1]
      by_cases hk : k = k₀
      · simp only [hk, ↓reduceIte]
        exact (hW.memLp _).integrable one_le_two
      · simp only [hk, ↓reduceIte]
        exact integrable_const 0
    · simp only [(singleArmMap_coord hcont k₀ _ _ k).1]
      by_cases hk : k = k₀
      · simp only [hk, ↓reduceIte]
        exact hW.setIntegral_eq (hst' s t hst) (hpre s A hA)
      · simp only [hk, ↓reduceIte]
  · have hg : Continuous fun p : (α → ℝ) × (α → ℝ) ↦
        p.1 k * p.1 j - if k = j then p.2 k else 0 := by
      by_cases hkj : k = j
      · simp only [hkj, ↓reduceIte]
        fun_prop
      · simp only [hkj, ↓reduceIte]
        fun_prop
    refine martingale_map hΦ (fun t ↦ stronglyMeasurable_comp_coord hg t)
      (fun t ↦ ?_) (fun s t hst A hA ↦ ?_)
    · simp only [singleArmMap_mul]
      by_cases hc : k = k₀ ∧ j = k₀
      · simp only [hc.1, hc.2, and_self, ↓reduceIte]
        exact (hW.memLp _).integrable_sq.sub (integrable_const _)
      · simp only [hc, ↓reduceIte]
        exact integrable_const 0
    · simp only [singleArmMap_mul]
      by_cases hc : k = k₀ ∧ j = k₀
      · simp only [hc.1, hc.2, and_self, ↓reduceIte]
        have := hW.setIntegral_sq_sub_eq (hst' s t hst) (hpre s A hA)
        rwa [hcoe, hcoe] at this
      · simp only [hc, ↓reduceIte]

end Policy

/-- **Known case**: Wald's identity `E_Q[X_k(t)²] = E_Q[τ_k(t)]` for a limit policy. -/
lemma IsLimitPolicy.integral_sq_eq {Q : Measure (Omega α)} (hQ : IsLimitPolicy α Q) (k : α)
    (t : I) : ∫ ω, ω.1 t k ^ 2 ∂Q = ∫ ω, ω.2 t k ∂Q := by
  have := hQ.isProbabilityMeasure
  have h : ∫ ω, (ω.1 0 k * ω.1 0 k - ω.2 0 k) ∂Q = ∫ ω, (ω.1 t k * ω.1 t k - ω.2 t k) ∂Q := by
    simpa using (hQ.martingale_mul k k).setIntegral_eq (unitInterval.nonneg' (t := t))
      MeasurableSet.univ
  have h0 : ∫ ω, (ω.1 0 k * ω.1 0 k - ω.2 0 k) ∂Q = 0 := by
    refine integral_eq_zero_of_ae (hQ.ae_mem.mono fun ω hω ↦ ?_)
    simp [hω.1, hω.2.2.1]
  have hτ : Integrable (fun ω : Omega α ↦ ω.2 t k) Q :=
    Integrable.of_mem_Icc 0 1 (by fun_prop)
      (hQ.ae_mem.mono fun ω hω ↦ mem_Icc_of_mem_allocations α hω.2 t k)
  have hM : Integrable (fun ω : Omega α ↦ ω.1 t k * ω.1 t k - ω.2 t k) Q := by
    simpa using (hQ.martingale_mul k k).integrable t
  have hsq : (fun ω : Omega α ↦ ω.1 t k ^ 2) =
      fun ω ↦ (ω.1 t k * ω.1 t k - ω.2 t k) + ω.2 t k := by
    ext ω
    ring
  rw [hsq, integral_add hM hτ, ← h, h0, zero_add]

/-- **Exclusion**: the Dirac mass at `(0, t e_{k₀})`, which allocates all the time to `k₀`
without observing anything, is not a limit policy (`X_{k₀}² - τ_{k₀} = -t` is not a
martingale). -/
lemma not_isLimitPolicy_dirac (k₀ : α) :
    ¬ IsLimitPolicy α (Measure.dirac ((0 : C(I, α → ℝ)), singleArm α k₀)) := by
  intro hQ
  have h : ∫ ω, (ω.1 0 k₀ * ω.1 0 k₀ - ω.2 0 k₀) ∂Measure.dirac ((0 : C(I, α → ℝ)), singleArm α k₀)
      = ∫ ω, (ω.1 1 k₀ * ω.1 1 k₀ - ω.2 1 k₀)
        ∂Measure.dirac ((0 : C(I, α → ℝ)), singleArm α k₀) := by
    simpa using (hQ.martingale_mul k₀ k₀).setIntegral_eq (unitInterval.nonneg' (t := 1))
      MeasurableSet.univ
  have hm : ∀ t : I, StronglyMeasurable fun ω : Omega α ↦ ω.1 t k₀ * ω.1 t k₀ - ω.2 t k₀ :=
    fun t ↦ (Continuous.measurable (by fun_prop)).stronglyMeasurable
  rw [integral_dirac' _ _ (hm 0), integral_dirac' _ _ (hm 1)] at h
  simp [singleArm] at h

/-! ### Risk -/

/-- **Known case**: the risk of the policy that gives all the time to the arm `k₀` is the regret
`max_i h_i - h_{k₀}` of always pulling `k₀`. It is positive when `k₀` is not optimal
(**exclusion**: the risk is not identically `0`). -/
lemma risk_singleArmPolicy {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω'}
    {ℱ : Filtration ℝ≥0 mΩ'} {W : ℝ≥0 → Ω' → ℝ} (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ ω, Continuous (W · ω)) (k₀ : α) (h : α → ℝ) :
    risk α (singleArmPolicy P hcont k₀) h = ENNReal.ofReal ((⨆ i, h i) - h k₀) := by
  have hΦ := measurable_singleArmMap hW hcont k₀
  have hc : 0 ≤ (⨆ i, h i) - h k₀ := sub_nonneg.2 (le_ciSup (Set.finite_range h).bddAbove k₀)
  have hpt : ∀ ω, likelihood α h (singleArmMap α hcont k₀ ω) * loss α h (singleArmMap α hcont k₀ ω)
      = exponentialMartingale (h k₀) W 1 ω * ((⨆ i, h i) - h k₀) := fun ω ↦ by
    simp [likelihood, loss, singleArmMap, singlePath, singleArm, Pi.single_apply,
      exponentialMartingale_def]
  rw [risk, singleArmPolicy, lintegral_map (measurable_likelihood_mul_loss h) hΦ]
  simp_rw [hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal
      ((hW.toIsPreBrownianReal.integrable_exponentialMartingale _ _).mul_const _)
      (ae_of_all _ fun ω ↦ mul_nonneg (exponentialMartingale_pos _ _ _ _).le hc),
    integral_mul_const, hW.toIsPreBrownianReal.integral_exponentialMartingale, one_mul]

/-! ### Values -/

variable (α)

/-- **Known case**: `V_K = V_K(ℝ^K)`. -/
lemma value_eq_valueOn_univ : value α = valueOn α Set.univ := by
  simp [value, valueOn]

/-- **Known case**: `V_K(H)` is nondecreasing in `H`. -/
lemma valueOn_mono {H H' : Set (α → ℝ)} (hH : H ⊆ H') : valueOn α H ≤ valueOn α H' :=
  iInf₂_mono fun _ _ ↦ biSup_mono hH

/-- **Known case**: the Bayes value of the point mass at `h` is the value of the point `{h}`. -/
lemma bayesValue_dirac (h : α → ℝ) : bayesValue α (Measure.dirac h) = valueOn α {h} := by
  simp [bayesValue, valueOn, lintegral_dirac]

/-- **Known case**: `V_K^loc ≤ V_K`. -/
lemma localValue_le_value : localValue α ≤ value α :=
  iSup₂_le fun _ _ ↦ (valueOn_mono α (Set.subset_univ _)).trans (value_eq_valueOn_univ α).ge

/-- **Witness**, given a Brownian motion: `V_K({0}) = 0` (the instance `h = 0` has no regret, and
a limit policy exists). -/
lemma valueOn_singleton_zero {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω'}
    {ℱ : Filtration ℝ≥0 mΩ'} {W : ℝ≥0 → Ω' → ℝ} (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ ω, Continuous (W · ω)) (h0 : ∀ ω, W 0 ω = 0) (k₀ : α) :
    valueOn α {0} = 0 := by
  refine le_antisymm ((iInf₂_le (singleArmPolicy P hcont k₀)
    (isLimitPolicy_singleArmPolicy hW hcont h0 k₀)).trans ?_) bot_le
  simp [risk_zero]

end Incognita.StochasticBandits.LimitGame
