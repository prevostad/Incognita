/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.LMLHistory
public import TauCeti.InformationTheory.KullbackLeibler.ChainRule

/-! # The divergence of the online phase of a transfer game

[INC-P003, lem:online-kl] and the chain rule of [INC-P003, proof of thm:main]: the divergence
between the laws of two games with the same size map and learner is the divergence between the
laws of the source data plus `∑_k E_P[N_k(T)] KL(ν_k, ν₂_k)`.

For a fixed source data `s`, the learner `π` plays the LML bandit algorithm
`π(s) : n, (h, o) ↦ π_n(s, histPairs h)`; its online law is LML's law of the first `T` pairs
(`onlineKernel_apply_eq_map_trajMeasure`), whose divergence decomposition is LML's
`IsAlgEnvSeq.klDiv_map_history_bandit`.

## Main statements

* `onlineKernel_apply_congr`: `κ^T_{π,ν}(s)` depends only on the kernels of `π` at `s`.
* `klDiv_onlineKernel_apply`: for every `s`,
  `KL(κ^T_{π,ν}(s), κ^T_{π,ν₂}(s)) = ∑_k E_{κ^T_{π,ν}(s)}[N_k(T)] KL(ν_k, ν₂_k)`.
* `klDiv_gameMeasure_eq_add`: `KL(P, P₂) = KL(P^D_{ν',N'}, P^D_{ν₂',N'}) +
  ∑_k E_P[N_k(T)] KL(ν_k, ν₂_k)`, for every size map.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Learning

open scoped ENNReal

namespace Incognita.TransferBandits

variable {α : Type*} [MeasurableSpace α]

/-- The kernel `κ^T_{π,ν}` at the source data `s` depends only on the kernels of `π` at `s`. -/
lemma onlineKernel_apply_congr {π π' : TransferAlgorithm α} (ν : Kernel α ℝ) [IsMarkovKernel ν]
    {s : Source α} (h : ∀ n (x : Fin n → α × ℝ), π.policy n (s, x) = π'.policy n (s, x)) :
    ∀ T, onlineKernel π ν T s = onlineKernel π' ν T s
  | 0 => rfl
  | T + 1 => by
    have hstep : Kernel.sectR (stepKernel π ν T) s = Kernel.sectR (stepKernel π' ν T) s := by
      ext x : 1
      rw [Kernel.sectR_apply, Kernel.sectR_apply, stepKernel, stepKernel,
        Kernel.compProd_apply_eq_compProd_sectR, Kernel.compProd_apply_eq_compProd_sectR, h]
    rw [onlineKernel, onlineKernel, Kernel.map_apply _ (MeasurableEquiv.measurable _),
      Kernel.map_apply _ (MeasurableEquiv.measurable _), Kernel.compProd_apply_eq_compProd_sectR,
      Kernel.compProd_apply_eq_compProd_sectR, onlineKernel_apply_congr ν h T, hstep]

/-- For a fixed source data `s`, the online law of `π` is LML's law of the first `T` pairs of any
bandit algorithm whose policy at round `n` is `π_n(s, ·)` read on pairs. -/
lemma onlineKernel_apply_eq_map_trajMeasure (π : TransferAlgorithm α) (ν : Kernel α ℝ)
    [IsMarkovKernel ν] (s : Source α) (alg : Algorithm Unit α ℝ)
    (halg : ∀ n (x : Fin n → α × ℝ), alg.policy n (pairsHist x, ()) = π.policy n (s, x))
    (T : ℕ) :
    onlineKernel π ν T s =
      (trajMeasure alg (Environment.bandit ν)).map (fun ω ↦ histPairs (IT.hist T ω)) := by
  exact (onlineKernel_apply_congr ν (fun n x ↦ (halg n x).symm) T).trans
    (onlineKernel_ofAlgorithm_apply (IT.isAlgEnvSeq_trajMeasure _ _) T s)

/-- For every source data `s` there is an LML bandit algorithm playing `π_n(s, ·)`. -/
lemma exists_algorithm_section (π : TransferAlgorithm α) (s : Source α) :
    ∃ alg : Algorithm Unit α ℝ,
      ∀ n (x : Fin n → α × ℝ), alg.policy n (pairsHist x, ()) = π.policy n (s, x) :=
  ⟨{ policy := fun n ↦ (π.policy n).comap
        (fun p : Hist Unit α ℝ n × Unit ↦ (s, histPairs p.1)) (by fun_prop)
     isMarkovKernel_policy := fun n ↦ Kernel.IsMarkovKernel.comap _ (by fun_prop) },
    fun _ _ ↦ rfl⟩

/-- The divergence between the laws of the first `T` (action, reward) pairs is that between the
LML histories: forgetting the trivial observations is invertible. -/
lemma klDiv_map_histPairs {n : ℕ} (μ μ' : Measure (Hist Unit α ℝ n)) [IsFiniteMeasure μ]
    [IsFiniteMeasure μ'] :
    klDiv (μ.map histPairs) (μ'.map histPairs) = klDiv μ μ' := by
  refine le_antisymm (klDiv_map_le _ _ (measurable_histPairs n)) ?_
  have hid : ∀ ρ : Measure (Hist Unit α ℝ n), (ρ.map histPairs).map pairsHist = ρ := fun ρ ↦ by
    rw [Measure.map_map (measurable_pairsHist n) (measurable_histPairs n)]
    exact Measure.map_id
  calc klDiv μ μ' = klDiv ((μ.map histPairs).map pairsHist) ((μ'.map histPairs).map pairsHist) := by
        rw [hid, hid]
  _ ≤ _ := klDiv_map_le _ _ (measurable_pairsHist n)

/-- The expected divergence of the reward laws at the actions of the first `T` rounds of an LML
trajectory is `∑_k E[N_k(T)] KL(ν_k, ν₂_k)`. -/
lemma sum_lintegral_klDiv_action_eq [Fintype α] [DecidableEq α] [MeasurableSingletonClass α]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {A : ℕ → Ω → α} (hA : ∀ t, Measurable (A t))
    (ν ν₂ : Kernel α ℝ) (T : ℕ) :
    ∑ t ∈ Finset.range T, ∫⁻ ω, klDiv (ν (A t ω)) (ν₂ (A t ω)) ∂P =
      ∑ a, (∫⁻ ω, (pullCount A a T ω : ℝ≥0∞) ∂P) * klDiv (ν a) (ν₂ a) := by
  have hind : ∀ t a, Measurable fun ω ↦ (if A t ω = a then (1 : ℝ≥0∞) else 0) := fun t a ↦
    Measurable.ite (hA t (measurableSet_singleton a)) measurable_const measurable_const
  have hkl : ∀ t ω, klDiv (ν (A t ω)) (ν₂ (A t ω)) =
      ∑ a, (if A t ω = a then (1 : ℝ≥0∞) else 0) * klDiv (ν a) (ν₂ a) := fun t ω ↦ by
    rw [Finset.sum_eq_single (A t ω) (fun b _ hb ↦ by simp [Ne.symm hb]) (by simp)]
    simp
  have hcount : ∀ a ω, (pullCount A a T ω : ℝ≥0∞) =
      ∑ t ∈ Finset.range T, (if A t ω = a then (1 : ℝ≥0∞) else 0) := fun a ω ↦ by
    rw [pullCount, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    split_ifs <;> simp
  simp_rw [hkl, hcount]
  rw [Finset.sum_congr rfl fun t _ ↦ lintegral_finsetSum _ fun a _ ↦ (hind t a).mul_const _,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [lintegral_finsetSum _ fun t _ ↦ hind t a, Finset.sum_mul]
  exact Finset.sum_congr rfl fun t _ ↦ lintegral_mul_const _ (hind t a)

/-- **Divergence of the online phase** at a fixed source data [INC-P003, lem:online-kl, inner
identity]: `KL(κ^T_{π,ν}(s), κ^T_{π,ν₂}(s)) = ∑_k E_{κ^T_{π,ν}(s)}[N_k(T)] KL(ν_k, ν₂_k)`. -/
lemma klDiv_onlineKernel_apply [Fintype α] [MeasurableSingletonClass α] (π : TransferAlgorithm α)
    (ν ν₂ : Kernel α ℝ) [IsMarkovKernel ν] [IsMarkovKernel ν₂] (s : Source α) (T : ℕ) :
    klDiv (onlineKernel π ν T s) (onlineKernel π ν₂ T s) =
      ∑ a, (∫⁻ h, (onlineCount a h : ℝ≥0∞) ∂(onlineKernel π ν T s)) * klDiv (ν a) (ν₂ a) := by
  classical
  obtain ⟨alg, halg⟩ := exists_algorithm_section π s
  rw [onlineKernel_apply_eq_map_trajMeasure π ν s alg halg T,
    onlineKernel_apply_eq_map_trajMeasure π ν₂ s alg halg T]
  have h := IT.isAlgEnvSeq_trajMeasure alg (Environment.bandit ν)
  have h₂ := IT.isAlgEnvSeq_trajMeasure alg (Environment.bandit ν₂)
  have hhist : Measurable (IT.hist (𝓞 := Unit) (𝓐 := α) (𝓨 := ℝ) T) := IT.measurable_hist T
  have e : (fun ω ↦ histPairs (IT.hist T ω)) =
      histPairs ∘ IT.hist (𝓞 := Unit) (𝓐 := α) (𝓨 := ℝ) T := rfl
  rw [e, ← Measure.map_map (measurable_histPairs T) hhist,
    ← Measure.map_map (measurable_histPairs T) hhist, klDiv_map_histPairs,
    ← IT.history_obs_action_feedback, h.klDiv_map_history_bandit h₂,
    sum_lintegral_klDiv_action_eq _ (fun t ↦ IT.measurable_action t)]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  congr 1
  rw [IT.history_obs_action_feedback, Measure.map_map (measurable_histPairs T) hhist,
    lintegral_map (f := fun h : Fin T → α × ℝ ↦ (onlineCount a h : ℝ≥0∞))
      (measurable_from_top.comp (measurable_onlineCount a)) ((measurable_histPairs T).comp hhist)]
  simp_rw [Function.comp_apply, onlineCount_histPairs_hist]

/-- **Chain rule for the law of the game** [INC-P003, proof of thm:main, with lem:online-kl]: for
every size map, `KL(P, P₂) = KL(P^D_{ν',N'}, P^D_{ν₂',N'}) + ∑_k E_P[N_k(T)] KL(ν_k, ν₂_k)`. -/
lemma klDiv_gameMeasure_eq_add [Fintype α] [MeasurableSingletonClass α]
    (N : SourceSpace α → α → ℕ) (π : TransferAlgorithm α) (T : ℕ) (ν ν' ν₂ ν₂' : Kernel α ℝ)
    [IsMarkovKernel ν] [IsMarkovKernel ν'] [IsMarkovKernel ν₂] [IsMarkovKernel ν₂'] :
    klDiv (gameMeasure ν' N ν π T) (gameMeasure ν₂' N ν₂ π T) =
      klDiv (sourceLaw ν' N) (sourceLaw ν₂' N) +
        ∑ a, (∫⁻ x, (onlineCount a x.2 : ℝ≥0∞) ∂(gameMeasure ν' N ν π T)) * klDiv (ν a) (ν₂ a) := by
  rw [gameMeasure, gameMeasure, TauCeti.klDiv_compProd_eq_add_lintegral]
  congr 1
  simp_rw [klDiv_onlineKernel_apply]
  have hm : ∀ a, Measurable fun s ↦
      ∫⁻ h, (onlineCount a h : ℝ≥0∞) ∂(onlineKernel π ν T s) := fun a ↦
    (measurable_from_top.comp (measurable_onlineCount a)).lintegral_kernel
  rw [lintegral_finsetSum _ fun a _ ↦ (hm a).mul_const _]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [lintegral_mul_const _ (hm a),
    Measure.lintegral_compProd (f := fun x : Source α × (Fin T → α × ℝ) ↦
      (onlineCount a x.2 : ℝ≥0∞))
      ((measurable_from_top.comp (measurable_onlineCount a)).comp measurable_snd)]

end Incognita.TransferBandits
