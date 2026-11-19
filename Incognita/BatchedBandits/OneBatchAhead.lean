/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.MaskedHistory
public import Incognita.BatchedBandits.Consistency
public import Incognita.BatchedBandits.Instances
public import Incognita.BatchedBandits.KInf

/-! # One batch ahead: the lower bound `liminf E[N_a(t_ℓ)] / log t_(ℓ+1) ≥ 1 / 𝒦_inf`

The lower bound of [INC-P000, Lemma `lem:onebatch`]: for every grid, every batched learner
consistent on `𝒫`, every `ν ∈ 𝒫` and every suboptimal arm `a`,
`liminf_ℓ E_ν[N_a(t_ℓ)] / log t_(ℓ+1) ≥ 1 / 𝒦_inf(ν_a, m⋆)`.

The proof is the change of measure of [INC-P000, Subsection `sec:pf-lem:onebatch`], with
Bretagnolle–Huber in place of data processing for the binary relative entropy. Let `ν'` be `ν`
with the law of `a` replaced by a law `Q` on `[0, 1]` of mean above `m⋆`. The actions of the
rounds `< t (ℓ + 1)` see the rewards of the rounds `< t ℓ` only, so their law under `ν'` is their
law under the *switched* environment, which follows `ν'` before `t ℓ` and `ν` afterwards
(`map_history_maskFeedback_eq`); the divergence between `ν` and the switched environment is
`E_ν[N_a(t ℓ)] KL(ν_a, Q)` (`klDiv_map_hist_switch`). The Bretagnolle–Huber inequality on the
event `{2 N_a(t (ℓ + 1)) ≥ t (ℓ + 1)}`, Markov's inequality and consistency under `ν` and `ν'`
conclude: the route of the sequential lower bound [LS, Theorem 16.2].

## Main statements

* `Incognita.BatchedBandits.exp_neg_le_of_seesRewardsUpTo`: the finite-horizon inequality
  `exp (-E_ν[N_a(r)] KL(ν_a, ν'_a)) / 2 ≤ 2 E_ν[N_a(M)] / M + 2 (M - E_ν'[N_a(M)]) / M` for a
  learner whose policies at the rounds `< M` see the rewards of the rounds `< r` only.
* `Incognita.BatchedBandits.integral_id_lt_one_of_klDiv_ne_top`: a law on `[0, 1]` at finite
  relative entropy from a law of mean `< 1` has mean `< 1`.
* `Incognita.BatchedBandits.eventually_lt_integral_pullCount_div_log_t_succ`: the lower bound one
  batch ahead.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Learning Bandits Filter Real Finset

open scoped ENNReal Topology

namespace Incognita.BatchedBandits

variable {α : Type*} [Finite α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- **Finite-horizon inequality one batch ahead.** Let the policies of `alg` at the rounds `n < M`
see the rewards of the rounds `< r` only, `r ≤ M`, `0 < M`, and let the bandits `ν`, `ν'` differ
only at the arm `a`, with `KL(ν_a, ν'_a) < ∞`. Then
`exp (-E_ν[N_a(r)] KL(ν_a, ν'_a)) / 2 ≤ 2 E_ν[N_a(M)] / M + 2 (M - E_ν'[N_a(M)]) / M`. -/
lemma exp_neg_le_of_seesRewardsUpTo {alg : Algorithm Unit α ℝ} {r M : ℕ} (hrM : r ≤ M)
    (hM : 0 < M) (halg : ∀ n < M, SeesRewardsUpTo alg n r) {ν ν' : Kernel α ℝ}
    [IsMarkovKernel ν] [IsMarkovKernel ν'] {a : α} (hνν' : ∀ b ≠ a, ν b = ν' b)
    (hD : klDiv (ν a) (ν' a) ≠ ∞) :
    exp (-((∫ ω, (pullCount IT.action a r ω : ℝ) ∂(trajMeasure alg (Environment.bandit ν))) *
        (klDiv (ν a) (ν' a)).toReal)) / 2 ≤
      2 * (∫ ω, (pullCount IT.action a M ω : ℝ) ∂(trajMeasure alg (Environment.bandit ν))) / M +
        2 * (M - ∫ ω, (pullCount IT.action a M ω : ℝ)
          ∂(trajMeasure alg (Environment.bandit ν'))) / M := by
  set P := trajMeasure alg (Environment.bandit ν)
  set P' := trajMeasure alg (Environment.bandit ν')
  set T := ∫ ω, (pullCount IT.action a r ω : ℝ) ∂P
  set D := (klDiv (ν a) (ν' a)).toReal
  -- The switched environment: `ν'` before `r`, `ν` afterwards.
  let env₂ : Environment Unit α ℝ :=
    { obs := fun _ ↦ Kernel.const _ (Measure.dirac ())
      feedback := fun n ↦ if n < r then ν'.prodMkLeft _ else ν.prodMkLeft _
      isMarkovKernel_feedback := fun n ↦ by
        by_cases hn : n < r
        · simp only [hn, ↓reduceIte]
          infer_instance
        · simp only [hn, ↓reduceIte]
          infer_instance }
  -- The masked history: the rewards of the rounds `≥ r` are replaced by `0`.
  set Ym : ℕ → (ℕ → Round Unit α ℝ) → ℝ := fun n ↦ if n < r then IT.feedback n else fun _ ↦ 0
    with hYm
  have hYmm : ∀ n, Measurable (Ym n) := fun n ↦ by
    by_cases hn : n < r
    · simp only [hYm, hn, ↓reduceIte]
      exact IT.measurable_feedback n
    · simp only [hYm, hn, ↓reduceIte]
      exact measurable_const
  set mask := history IT.obs IT.action Ym M with hmask
  have hmaskm : Measurable mask :=
    measurable_history IT.measurable_obs IT.measurable_action hYmm M
  have hfac : mask = (fun (h : Hist Unit α ℝ M) (i : Fin M) ↦
      if (i : ℕ) < r then h i else ((), (h i).action, (0 : ℝ))) ∘ IT.hist M := by
    funext ω
    exact history_maskFeedback r 0 M ω
  -- Under `ν'` and under the switched environment, the masked histories have the same law.
  have hlaw : (trajMeasure alg env₂).map mask = P'.map mask :=
    map_history_maskFeedback_eq alg (fun n hn ↦ by simp [env₂, hn]) halg 0
  -- The divergence between the laws of the masked histories is at most `T D`.
  have hKL : klDiv (P.map mask) (P'.map mask) ≤ ENNReal.ofReal (T * D) := by
    rw [← hlaw, hfac, ← Measure.map_map (measurable_maskFeedback r M 0) (IT.measurable_hist M),
      ← Measure.map_map (measurable_maskFeedback r M 0) (IT.measurable_hist M)]
    refine (klDiv_map_le _ _ (measurable_maskFeedback r M 0)).trans ?_
    rw [klDiv_map_hist_switch alg ν ν' hrM (fun n hn ↦ by simp [env₂, hn])
      (fun n hn ↦ by simp [env₂, not_lt.mpr hn])]
    exact (IT.isAlgEnvSeq_trajMeasure alg _).klDiv_map_history_le_ofReal_integral_pullCount_mul
      (IT.isAlgEnvSeq_trajMeasure alg _) hνν' (ENNReal.ofReal_toReal hD).ge r
  have hKLne : klDiv (P.map mask) (P'.map mask) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hKL
  have hTD : 0 ≤ T * D := mul_nonneg (integral_nonneg fun _ ↦ Nat.cast_nonneg _)
    ENNReal.toReal_nonneg
  -- Bretagnolle–Huber on the event `{M ≤ 2 N_a(M)}`.
  set E : Set (Hist Unit α ℝ M) := {h | (M : ℝ) ≤ 2 * (pullCount' M h a : ℝ)} with hEdef
  have hE : MeasurableSet E := measurableSet_le measurable_const
    ((Measurable.of_discrete.comp (measurable_pullCount' M a)).const_mul 2)
  have hBH := LMLExplore.exp_neg_klDiv_div_two_le hE hKLne
  have hle : exp (-(T * D)) ≤ exp (-(klDiv (P.map mask) (P'.map mask)).toReal) :=
    exp_le_exp.mpr (neg_le_neg (ENNReal.toReal_le_of_le_ofReal hTD hKL))
  have hpc : ∀ ω, pullCount' M (mask ω) a = pullCount IT.action a M ω := fun ω ↦
    (pullCount_eq_pullCount' (O := IT.obs) (R' := Ym)).symm
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  -- Markov's inequality under `ν`.
  have h1 : (P.map mask).real E ≤ 2 * (∫ ω, (pullCount IT.action a M ω : ℝ) ∂P) / M := by
    rw [map_measureReal_apply hmaskm hE]
    have hpre : mask ⁻¹' E = {ω | (M : ℝ) / 2 ≤ (pullCount IT.action a M ω : ℝ)} := by
      ext ω
      simp only [Set.mem_preimage, hEdef, Set.mem_ofPred_eq, hpc]
      constructor <;> intro h <;> linarith
    rw [hpre, le_div_iff₀ hMpos]
    have hmk := mul_meas_ge_le_integral_of_nonneg (μ := P)
      (f := fun ω ↦ (pullCount IT.action a M ω : ℝ)) (ae_of_all _ fun _ ↦ Nat.cast_nonneg _)
      (integrable_pullCount IT.measurable_action a M) ((M : ℝ) / 2)
    linarith
  -- Markov's inequality under `ν'`, for `M - N_a(M)`.
  have h2 : (P'.map mask).real Eᶜ ≤
      2 * (M - ∫ ω, (pullCount IT.action a M ω : ℝ) ∂P') / M := by
    rw [map_measureReal_apply hmaskm hE.compl]
    have hsub : mask ⁻¹' Eᶜ ⊆ {ω | (M : ℝ) / 2 ≤ (M : ℝ) - (pullCount IT.action a M ω : ℝ)} := by
      intro ω hω
      simp only [Set.mem_preimage, Set.mem_compl_iff, hEdef, Set.mem_ofPred_eq, hpc,
        not_le] at hω
      simp only [Set.mem_ofPred_eq]
      linarith
    have hmk := mul_meas_ge_le_integral_of_nonneg (μ := P')
      (f := fun ω ↦ (M : ℝ) - (pullCount IT.action a M ω : ℝ))
      (ae_of_all _ fun ω ↦ sub_nonneg.mpr (by exact_mod_cast pullCount_le a M ω))
      ((integrable_const _).sub (integrable_pullCount IT.measurable_action a M)) ((M : ℝ) / 2)
    rw [integral_sub (integrable_const _) (integrable_pullCount IT.measurable_action a M),
      integral_const, probReal_univ, one_smul] at hmk
    have hmono := measureReal_mono (μ := P') hsub
    rw [le_div_iff₀ hMpos]
    nlinarith
  calc exp (-(T * D)) / 2 ≤ exp (-(klDiv (P.map mask) (P'.map mask)).toReal) / 2 := by
        gcongr
    _ ≤ (P.map mask).real E + (P'.map mask).real Eᶜ := hBH
    _ ≤ _ := add_le_add h1 h2

omit [Finite α] [DecidableEq α] [MeasurableSingletonClass α] in
/-- A law `Q` on `[0, 1]` at finite relative entropy from a probability law `P` of mean `< 1` has
mean `< 1`: a law on `[0, 1]` of mean `1` is `δ_1`, and `P ≪ δ_1` would give `P = δ_1`. -/
lemma integral_id_lt_one_of_klDiv_ne_top {P Q : Measure ℝ} [IsProbabilityMeasure P]
    (hQ : Q ∈ unitLaws) (hD : klDiv P Q ≠ ∞) (hP : P[id] < 1) : Q[id] < 1 := by
  have := hQ.1
  refine lt_of_le_of_ne (integral_id_mem_Icc_of_mem_unitLaws hQ).2 fun h1 ↦ ?_
  have hint : Integrable (fun x : ℝ ↦ x) Q := integrable_id_of_mem_unitLaws hQ
  have h0 : ∫ x, (1 - x) ∂Q = 0 := by
    rw [integral_sub (integrable_const 1) hint, integral_const, probReal_univ, one_smul]
    simp only [id] at h1
    rw [h1, sub_self]
  have hae : (fun x : ℝ ↦ 1 - x) =ᵐ[Q] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (hQ.2.mono fun x hx ↦ by simp [hx.2])
      ((integrable_const 1).sub hint)).mp h0
  have hPae : ∀ᵐ x ∂P, x = 1 :=
    (klDiv_ne_top_iff.mp hD).1.ae_le (hae.mono fun x hx ↦ by simp at hx; linarith)
  have : P[id] = 1 := by
    rw [integral_congr_ae (hPae.mono fun x hx ↦ (by simp [hx] : id x = (1 : ℝ)))]
    simp
  linarith

/-- **One batch ahead** [INC-P000, Lemma `lem:onebatch`]. For every grid `g`, every learner
batched on `g` and consistent at the batch ends of `g` on `𝒫`, every `ν ∈ 𝒫` and every arm `a`
with `gap ν a > 0`: `liminf_ℓ E_ν[N_a(t ℓ)] / log t (ℓ + 1) ≥ 1 / 𝒦_inf(ν_a, m⋆)`, written
`∀ c < 1 / 𝒦_inf(ν_a, m⋆), ∀ᶠ ℓ, c < E_ν[N_a(t ℓ)] / log t (ℓ + 1)`, with
`𝒦_inf(ν_a, m⋆) = dInf unitLaws (ν a) m⋆` (its `toReal`; for `dInf = ∞` the bound is `0`). -/
lemma eventually_lt_integral_pullCount_div_log_t_succ {K : ℕ} (g : Grid K)
    {alg : Algorithm Unit α ℝ} (hb : IsBatched alg g)
    (hc : IsConsistentAtBatchEnds alg g (unitBandits α)) {ν : Kernel α ℝ} [IsMarkovKernel ν]
    (hν : ν ∈ unitBandits α) {a : α} (ha : 0 < gap ν a) :
    ∀ c < 1 / (LMLExplore.Bandits.dInf unitLaws (ν a) (⨆ b, ∫ y, id y ∂(ν b))).toReal,
      ∀ᶠ ℓ in atTop, c < (∫ ω, (pullCount IT.action a (g.t ℓ) ω : ℝ)
          ∂(trajMeasure alg (Environment.bandit ν))) / Real.log (g.t (ℓ + 1)) := by
  intro c hcd
  have := Fintype.ofFinite α
  have hlogpos : ∀ ℓ, 0 < Real.log (g.t (ℓ + 1)) := fun ℓ ↦ Real.log_pos (by
    have := g.two_le_t (ℓ := ℓ + 1) (by omega)
    exact_mod_cast (show 1 < g.t (ℓ + 1) by omega))
  rcases lt_or_ge c 0 with hc0 | hc0
  · exact Eventually.of_forall fun ℓ ↦ hc0.trans_le
      (div_nonneg (integral_nonneg fun _ ↦ Nat.cast_nonneg _) (hlogpos ℓ).le)
  set m := ⨆ b, ∫ y, id y ∂(ν b) with hm
  set d := (LMLExplore.Bandits.dInf unitLaws (ν a) m).toReal with hd_def
  have hd : 0 < d := by
    have h1 : 0 < 1 / d := hc0.trans_lt hcd
    rwa [one_div_pos] at h1
  have hdtop : LMLExplore.Bandits.dInf unitLaws (ν a) m ≠ ∞ := fun h ↦ by
    simp [hd_def, h] at hd
  obtain ⟨c', hcc', hc'd⟩ := exists_between hcd
  have hc'0 : 0 < c' := hc0.trans_lt hcc'
  have hdc' : d < 1 / c' := by
    rw [lt_div_iff₀ hc'0]
    rwa [lt_div_iff₀ hd, mul_comm] at hc'd
  -- A law `Q` on `[0, 1]` with mean above `m⋆` and `KL(ν_a, Q) < 1 / c'`.
  have hlt : LMLExplore.Bandits.dInf unitLaws (ν a) m < ENNReal.ofReal (1 / c') := by
    rw [← ENNReal.ofReal_toReal hdtop]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hdc'
  obtain ⟨Q, hQ, hQm, hQD⟩ := LMLExplore.Bandits.dInf_lt_iff.mp hlt
  have hDne : klDiv (ν a) Q ≠ ∞ := ne_top_of_lt hQD
  set D := (klDiv (ν a) Q).toReal with hD_def
  have hD0 : 0 ≤ D := ENNReal.toReal_nonneg
  have hc'D : c' * D < 1 := by
    have : D < 1 / c' := ENNReal.toReal_lt_of_lt_ofReal hQD
    rwa [lt_div_iff₀ hc'0, mul_comm] at this
  have hmean_le : ∀ b, (ν b)[id] ≤ m := fun b ↦
    le_ciSup (f := fun b ↦ (ν b)[id]) (Set.finite_range _).bddAbove b
  have hQ1 : Q[id] < 1 :=
    integral_id_lt_one_of_klDiv_ne_top hQ hDne ((hmean_le a).trans_lt hν.2)
  -- The alternative instance `ν'`: `ν` with the law of `a` replaced by `Q`.
  have := hQ.1
  have hupd : ∀ b, IsProbabilityMeasure (Function.update (fun b ↦ ν b) a Q b) := fun b ↦ by
    rcases eq_or_ne b a with rfl | hb
    · rwa [Function.update_self]
    · rw [Function.update_of_ne hb]
      infer_instance
  set ν' := Kernel.ofFunOfCountable (Function.update (fun b ↦ ν b) a Q) with hν'_def
  have hν'a : ν' a = Q := by simp [ν']
  have hν' : ∀ b ≠ a, ν b = ν' b := fun b hb ↦ by simp [ν', Function.update_of_ne hb]
  have hν'mem : ν' ∈ unitBandits α := by
    refine ⟨fun b ↦ ?_, ?_⟩
    · rcases eq_or_ne b a with rfl | hb
      · rwa [hν'a]
      · rw [← hν' b hb]
        exact hν.1 b
    · have : Nonempty α := ⟨a⟩
      obtain ⟨b₀, hb₀⟩ := exists_eq_ciSup_of_finite (f := fun b ↦ (ν' b)[id])
      rw [← hb₀]
      rcases eq_or_ne b₀ a with rfl | hb
      · rwa [hν'a]
      · rw [← hν' b₀ hb]
        exact (hmean_le b₀).trans_lt hν.2
  have hgap' : ∀ b ≠ a, 0 < gap ν' b := fun b hb ↦ by
    have h1 := LMLExplore.Bandits.sub_le_gap ν' b a
    rw [hν'a, ← hν' b hb] at h1
    linarith [hmean_le b]
  -- The exponent `p` and the accuracy `δ` of consistency.
  set p := (1 - c' * D) / 2 with hp_def
  have hp : 0 < p := by rw [hp_def]; linarith
  have hKα : (0 : ℝ) < Fintype.card α := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨a⟩
  set δ := 1 / (8 * (Fintype.card α : ℝ)) with hδ_def
  have hδ : 0 < δ := by positivity
  have hA := (tendsto_order.1 ((hc ν hν a ha p hp).comp (tendsto_add_atTop_nat 1))).2 δ hδ
  have hB : ∀ᶠ ℓ in atTop, ∀ b, b ≠ a →
      (∫ ω, (pullCount IT.action b (g.t (ℓ + 1)) ω : ℝ)
        ∂(trajMeasure alg (Environment.bandit ν'))) / (g.t (ℓ + 1) : ℝ) ^ p < δ := by
    refine eventually_all.2 fun b ↦ ?_
    by_cases hba : b = a
    · exact Eventually.of_forall fun _ h ↦ absurd hba h
    · exact ((tendsto_order.1 ((hc ν' hν'mem b (hgap' b hba) p hp).comp
        (tendsto_add_atTop_nat 1))).2 δ hδ).mono fun _ h _ ↦ h
  filter_upwards [hA, hB] with ℓ hAℓ hBℓ
  simp only [Function.comp_apply] at hAℓ
  set M := g.t (ℓ + 1) with hM_def
  set r := g.t ℓ with hr_def
  have hrM : r ≤ M := g.strictMono.monotone (Nat.le_succ ℓ)
  have hM2 : 2 ≤ M := g.two_le_t (by omega)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hM1 : (1 : ℝ) < M := by exact_mod_cast (show 1 < M by omega)
  -- During the rounds `< t (ℓ + 1)`, the learner sees the rewards of the rounds `< t ℓ` only.
  have halg : ∀ n < M, SeesRewardsUpTo alg n r := by
    intro n hn
    refine (hb n).mono (g.strictMono.monotone ?_)
    have h1 := g.t_batchOf_sub_one_le n
    have h2 : g.batchOf n - 1 < ℓ + 1 := g.strictMono.lt_iff_lt.mp (h1.trans_lt hn)
    omega
  have hDne' : klDiv (ν a) (ν' a) ≠ ∞ := by rwa [hν'a]
  have key := exp_neg_le_of_seesRewardsUpTo hrM (by omega) halg hν' hDne'
  rw [hν'a, ← hD_def] at key
  -- Bounding the right-hand side by consistency.
  set T := ∫ ω, (pullCount IT.action a r ω : ℝ) ∂(trajMeasure alg (Environment.bandit ν))
  set Na := ∫ ω, (pullCount IT.action a M ω : ℝ) ∂(trajMeasure alg (Environment.bandit ν))
  set Na' := ∫ ω, (pullCount IT.action a M ω : ℝ) ∂(trajMeasure alg (Environment.bandit ν'))
  have hMp : 0 < (M : ℝ) ^ p := Real.rpow_pos_of_pos hMpos p
  have hNa : Na ≤ δ * (M : ℝ) ^ p := by
    have := (div_lt_iff₀ hMp).mp hAℓ
    linarith
  have hsum : (M : ℝ) - Na' = ∑ b ∈ univ.erase a,
      ∫ ω, (pullCount IT.action b M ω : ℝ) ∂(trajMeasure alg (Environment.bandit ν')) := by
    have htot : ∑ b, ∫ ω, (pullCount IT.action b M ω : ℝ)
        ∂(trajMeasure alg (Environment.bandit ν')) = M := by
      rw [← integral_finsetSum Finset.univ fun b _ ↦ integrable_pullCount IT.measurable_action b M]
      have : (fun ω : ℕ → Round Unit α ℝ ↦ ∑ b : α, (pullCount IT.action b M ω : ℝ)) =
          fun _ ↦ (M : ℝ) := by
        funext ω
        have := sum_pullCount (A := (IT.action : ℕ → (ℕ → Round Unit α ℝ) → α)) (t := M) (ω := ω)
        exact_mod_cast this
      rw [this, integral_const, probReal_univ, one_smul]
    rw [← htot, ← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
    ring
  have hNa' : (M : ℝ) - Na' ≤ Fintype.card α * (δ * (M : ℝ) ^ p) := by
    rw [hsum]
    calc ∑ b ∈ univ.erase a, ∫ ω, (pullCount IT.action b M ω : ℝ)
          ∂(trajMeasure alg (Environment.bandit ν'))
        ≤ ∑ b ∈ univ.erase a, δ * (M : ℝ) ^ p := by
          refine Finset.sum_le_sum fun b hb ↦ ?_
          have := (div_lt_iff₀ hMp).mp (hBℓ b (Finset.ne_of_mem_erase hb))
          linarith
      _ ≤ ∑ b : α, δ * (M : ℝ) ^ p :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            fun _ _ _ ↦ by positivity
      _ = Fintype.card α * (δ * (M : ℝ) ^ p) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hK1 : (1 : ℝ) ≤ Fintype.card α := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨a⟩
  have hδK : Fintype.card α * δ = 1 / 8 := by
    rw [hδ_def]
    field_simp
  have hexp : exp (-(T * D)) ≤ (M : ℝ) ^ p / M := by
    have h2 : 2 * Na / M + 2 * (M - Na') / M ≤ (M : ℝ) ^ p / M / 2 := by
      have e : (M : ℝ) ^ p / M / 2 = ((M : ℝ) ^ p / 2) / M := by ring
      rw [e, ← add_div]
      refine div_le_div_of_nonneg_right ?_ hMpos.le
      have h3 : δ * (M : ℝ) ^ p ≤ Fintype.card α * (δ * (M : ℝ) ^ p) :=
        le_mul_of_one_le_left (by positivity) hK1
      have h4 : (Fintype.card α : ℝ) * (δ * (M : ℝ) ^ p) = (M : ℝ) ^ p / 8 := by
        rw [← mul_assoc, hδK]
        ring
      linarith
    linarith
  -- Taking logarithms: `T D ≥ (1 - p) log M`.
  have hlog : (1 - p) * Real.log M ≤ T * D := by
    have := Real.log_le_log (exp_pos _) hexp
    rw [Real.log_exp, Real.log_div hMp.ne' hMpos.ne', Real.log_rpow hMpos] at this
    linarith
  have hlogM : 0 < Real.log M := Real.log_pos hM1
  have h1p : c' * D < 1 - p := by rw [hp_def]; linarith
  have hT0 : 0 ≤ T := integral_nonneg fun _ ↦ Nat.cast_nonneg _
  have hDpos : 0 < D := by
    rcases hD0.eq_or_lt with h | h
    · rw [← h] at hlog h1p
      nlinarith
    · exact h
  have hT : c' * Real.log M < T := by
    have : c' * D * Real.log M < T * D := lt_of_lt_of_le
      (mul_lt_mul_of_pos_right h1p hlogM) hlog
    nlinarith
  rw [lt_div_iff₀ hlogM]
  nlinarith

/-- **The lower bound `1 / 𝒦_inf` on every grid** [INC-P000, Theorem `thm:lower`(i) and the remark
"on every grid"]: under the hypotheses of `eventually_lt_integral_pullCount_div_log_t_succ`,
`liminf_ℓ E_ν[N_a(t ℓ)] / log t ℓ ≥ 1 / 𝒦_inf(ν_a, m⋆)`, because `log t ℓ ≤ log t (ℓ + 1)`. No
hypothesis on the ratios of the grid is needed. -/
lemma eventually_lt_integral_pullCount_div_log_t {K : ℕ} (g : Grid K)
    {alg : Algorithm Unit α ℝ} (hb : IsBatched alg g)
    (hc : IsConsistentAtBatchEnds alg g (unitBandits α)) {ν : Kernel α ℝ} [IsMarkovKernel ν]
    (hν : ν ∈ unitBandits α) {a : α} (ha : 0 < gap ν a) :
    ∀ c < 1 / (LMLExplore.Bandits.dInf unitLaws (ν a) (⨆ b, ∫ y, id y ∂(ν b))).toReal,
      ∀ᶠ ℓ in atTop, c < (∫ ω, (pullCount IT.action a (g.t ℓ) ω : ℝ)
          ∂(trajMeasure alg (Environment.bandit ν))) / Real.log (g.t ℓ) := by
  intro c hcK
  filter_upwards [eventually_lt_integral_pullCount_div_log_t_succ g hb hc hν ha c hcK,
    eventually_ge_atTop 1] with ℓ hℓ hℓ1
  refine hℓ.trans_le (div_le_div_of_nonneg_left (integral_nonneg fun _ ↦ Nat.cast_nonneg _)
    (g.logEnd_pos hℓ1) (Real.log_le_log (g.logEnd_pos hℓ1 |> fun h ↦ ?_) ?_))
  · have := g.two_le_t hℓ1
    exact_mod_cast (show 0 < g.t ℓ by omega)
  · exact_mod_cast g.strictMono.monotone (Nat.le_succ ℓ)

end Incognita.BatchedBandits
