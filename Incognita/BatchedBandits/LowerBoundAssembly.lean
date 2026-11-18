/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.BatchedBandits.OneBatchAhead

/-! # Assembling the lower bounds of P000

The deterministic steps of the proof of [INC-P000, Theorem `thm:lower`] (Subsection
`sec:app-lb-assembly`), in the eventual forms of the frozen statements
(`liminf_ℓ u_ℓ ≥ L` is `∀ c < L, ∀ᶠ ℓ, c < u_ℓ`; `limsup_ℓ u_ℓ ≥ L` is `∀ c < L, ∃ᶠ ℓ, c < u_ℓ`).

* `eventually_lt_sum_mul`: the `liminf` of a finite sum `∑ w_i u_i` with positive weights is at
  least `∑ w_i liminf u_i` (the regret, Theorem `thm:lower`(iii)).
* `eventually_lt_mul_of_tendsto`: `liminf (f g) ≥ (liminf f) B` when `g → B > 0` and `f ≥ 0`.
* `Grid.tendsto_log_t_add_two_div_log_t`: `log t_(ℓ+2) / log t_ℓ = x_(ℓ+1) x_(ℓ+2) → x²` on a grid
  with `x_ℓ → x`.
* `eventually_lt_div_log_t_of_eventually_lt_div_log_t_add_two`: Case A of the proof of
  Theorem `thm:lower`(ii): a lower bound `liminf u_ℓ / log t_(ℓ+2) ≥ A` (the output of Lemma
  `lem:twobatches`(ii) at the index `ℓ + 1`) gives `liminf u_ℓ / log t_ℓ ≥ x² A`.
* `frequently_lt_div_log_t_of_not_isBigO`: Case B: a nonnegative sequence that is not
  `O(log t_ℓ)` has `limsup u_ℓ / log t_ℓ = ∞`.
* `eventually_lt_regret_div_log_t`: the regret lower bound with the constant `C_1` on every grid,
  from Lemma `lem:onebatch`: `liminf_ℓ ℜ(t_ℓ) / log t_ℓ ≥ ∑_{c : Δ_c > 0} Δ_c / 𝒦_inf(ν_c, m⋆)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Bandits Filter Real Finset

open scoped Topology

namespace Incognita.BatchedBandits

/-- **`liminf` of a finite weighted sum.** If, for every `i ∈ S`, `liminf_ℓ u_i(ℓ) ≥ L_i` and
`w_i > 0`, then `liminf_ℓ ∑_{i ∈ S} w_i u_i(ℓ) ≥ ∑_{i ∈ S} w_i L_i`. -/
lemma eventually_lt_sum_mul {ι : Type*} (S : Finset ι) {w L : ι → ℝ} {u : ι → ℕ → ℝ}
    (hw : ∀ i ∈ S, 0 < w i) (hu : ∀ i ∈ S, ∀ b < L i, ∀ᶠ ℓ in atTop, b < u i ℓ) :
    ∀ b < ∑ i ∈ S, w i * L i, ∀ᶠ ℓ in atTop, b < ∑ i ∈ S, w i * u i ℓ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro b hb
    simp only [Finset.sum_empty] at hb ⊢
    exact Eventually.of_forall fun _ ↦ hb
  | insert i S hi ih =>
    intro b hb
    rw [Finset.sum_insert hi] at hb
    simp only [Finset.sum_insert hi]
    set s := ∑ j ∈ S, w j * L j
    set δ := (w i * L i + s - b) / 2 with hδ
    have hwi := hw i (Finset.mem_insert_self i S)
    have h1 : (b - (s - δ)) / w i < L i := by
      rw [div_lt_iff₀ hwi]
      linarith
    have hA := hu i (Finset.mem_insert_self i S) _ h1
    have hB := ih (fun j hj ↦ hw j (Finset.mem_insert_of_mem hj))
      (fun j hj ↦ hu j (Finset.mem_insert_of_mem hj)) (s - δ) (by linarith)
    filter_upwards [hA, hB] with ℓ hAℓ hBℓ
    rw [div_lt_iff₀ hwi] at hAℓ
    linarith

/-- **`liminf` of a product with a convergent factor.** If `f ≥ 0` eventually,
`liminf_ℓ f(ℓ) ≥ A` and `g(ℓ) → B > 0`, then `liminf_ℓ f(ℓ) g(ℓ) ≥ A B`. -/
lemma eventually_lt_mul_of_tendsto {f g : ℕ → ℝ} {A B : ℝ} (hB : 0 < B)
    (hf0 : ∀ᶠ ℓ in atTop, 0 ≤ f ℓ) (hf : ∀ c < A, ∀ᶠ ℓ in atTop, c < f ℓ)
    (hg : Tendsto g atTop (𝓝 B)) :
    ∀ c < A * B, ∀ᶠ ℓ in atTop, c < f ℓ * g ℓ := by
  intro c hc
  have hgpos : ∀ᶠ ℓ in atTop, 0 < g ℓ := hg.eventually (lt_mem_nhds hB)
  rcases lt_or_ge c 0 with hc0 | hc0
  · filter_upwards [hf0, hgpos] with ℓ h1 h2
    exact hc0.trans_le (mul_nonneg h1 h2.le)
  have hcA : c / B < A := by rwa [div_lt_iff₀ hB]
  obtain ⟨A', hA'1, hA'2⟩ := exists_between hcA
  have hA'0 : 0 < A' := (div_nonneg hc0 hB.le).trans_lt hA'1
  have hcB : c / A' < B := by
    rw [div_lt_iff₀ hA'0, mul_comm]
    rwa [div_lt_iff₀ hB] at hA'1
  obtain ⟨B', hB'1, hB'2⟩ := exists_between hcB
  have hB'0 : 0 < B' := (div_nonneg hc0 hA'0.le).trans_lt hB'1
  have hcAB : c < A' * B' := by
    rw [div_lt_iff₀ hA'0, mul_comm] at hB'1
    exact hB'1
  filter_upwards [hf A' hA'2, hg.eventually (lt_mem_nhds hB'2)] with ℓ h1 h2
  exact hcAB.trans (mul_lt_mul'' h1 h2 hA'0.le hB'0.le)

variable {K : ℕ}

/-- On a grid with `x_ℓ → x`, `log t_(ℓ+2) / log t_ℓ = x_(ℓ+1) x_(ℓ+2) → x²`. -/
lemma Grid.tendsto_log_t_add_two_div_log_t (g : Grid K) {x : ℝ}
    (hg : Tendsto g.ratio atTop (𝓝 x)) :
    Tendsto (fun ℓ ↦ Real.log (g.t (ℓ + 2)) / Real.log (g.t ℓ)) atTop (𝓝 (x ^ 2)) := by
  have h2 : Tendsto (fun ℓ ↦ g.ratio (ℓ + 2) * g.ratio (ℓ + 1)) atTop (𝓝 (x * x)) :=
    (hg.comp (tendsto_add_atTop_nat 2)).mul (hg.comp (tendsto_add_atTop_nat 1))
  rw [sq]
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with ℓ hℓ
  have hpos1 := g.logEnd_pos (ℓ := ℓ + 1) (by omega)
  have hpos0 := g.logEnd_pos hℓ
  simp only [Grid.ratio, show ¬ (ℓ + 2 ≤ 1) by omega, show ¬ (ℓ + 1 ≤ 1) by omega,
    ↓reduceIte, show ℓ + 2 - 1 = ℓ + 1 by omega, Nat.add_sub_cancel]
  unfold Grid.logEnd at hpos0 hpos1 ⊢
  field_simp

/-- **Case A of the proof of [INC-P000, Theorem `thm:lower`(ii)].** On a grid with `x_ℓ → x > 0`,
a nonnegative sequence with `liminf_ℓ u_ℓ / log t_(ℓ+2) ≥ A` has
`liminf_ℓ u_ℓ / log t_ℓ ≥ x² A`. With `u_ℓ = E_ν[N_a(t_ℓ)]` and `A = 1 / 𝒦_inf(ν_a, m⋆)`, the
hypothesis is the conclusion of Lemma `lem:twobatches`(ii) at the index `ℓ + 1`. -/
lemma eventually_lt_div_log_t_of_eventually_lt_div_log_t_add_two (g : Grid K) {x : ℝ}
    (hx : 0 < x) (hg : Tendsto g.ratio atTop (𝓝 x)) {u : ℕ → ℝ} (hu0 : ∀ ℓ, 0 ≤ u ℓ) {A : ℝ}
    (hA : ∀ c < A, ∀ᶠ ℓ in atTop, c < u ℓ / Real.log (g.t (ℓ + 2))) :
    ∀ c < x ^ 2 * A, ∀ᶠ ℓ in atTop, c < u ℓ / Real.log (g.t ℓ) := by
  intro c hc
  have hlog2 : ∀ ℓ, 0 < Real.log (g.t (ℓ + 2)) := fun ℓ ↦ g.logEnd_pos (ℓ := ℓ + 2) (by omega)
  have h := eventually_lt_mul_of_tendsto (pow_pos hx 2)
    (Eventually.of_forall fun ℓ ↦ div_nonneg (hu0 ℓ) (hlog2 ℓ).le) hA
    (g.tendsto_log_t_add_two_div_log_t hg) c (by rwa [mul_comm])
  filter_upwards [h] with ℓ hℓ
  rwa [div_mul_div_cancel₀ (hlog2 ℓ).ne'] at hℓ

/-- **Case B of the proof of [INC-P000, Theorem `thm:lower`(ii)].** A nonnegative sequence that is
not `O(log t_ℓ)` has `limsup_ℓ u_ℓ / log t_ℓ = ∞`. -/
lemma frequently_lt_div_log_t_of_not_isBigO (g : Grid K) {u : ℕ → ℝ} (hu0 : ∀ ℓ, 0 ≤ u ℓ)
    (hu : ¬ Asymptotics.IsBigO atTop u fun ℓ ↦ Real.log (g.t ℓ)) (c : ℝ) :
    ∃ᶠ ℓ in atTop, c < u ℓ / Real.log (g.t ℓ) := by
  refine fun hne ↦ hu (Asymptotics.IsBigO.of_bound |c| ?_)
  filter_upwards [hne, eventually_ge_atTop 1] with ℓ h1 h2
  have hlog := g.logEnd_pos h2
  unfold Grid.logEnd at hlog
  rw [not_lt, div_le_iff₀ hlog] at h1
  rw [Real.norm_of_nonneg (hu0 ℓ), Real.norm_of_nonneg hlog.le]
  exact h1.trans (mul_le_mul_of_nonneg_right (le_abs_self c) hlog.le)

variable {α : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- **The regret one batch ahead, on every grid** [INC-P000, Theorem `thm:lower`(iii) for `x = 1`,
which holds on every grid]: for a learner batched on `g` and consistent at the batch ends of `g` on
`𝒫`, and `ν ∈ 𝒫`, `liminf_ℓ ℜ(t_ℓ) / log t_ℓ ≥ C_1 = ∑_{c : Δ_c > 0} Δ_c / 𝒦_inf(ν_c, m⋆)`, with
`ℜ(t) = ∑_c Δ_c E_ν[N_c(t)]`. -/
lemma eventually_lt_regret_div_log_t (g : Grid K) {alg : Algorithm Unit α ℝ}
    (hb : IsBatched alg g) (hc : IsConsistentAtBatchEnds alg g (unitBandits α))
    {ν : Kernel α ℝ} [IsMarkovKernel ν] (hν : ν ∈ unitBandits α) :
    ∀ c' < ∑ c ∈ Finset.univ.filter (fun c ↦ 0 < gap ν c),
        gap ν c / (LMLExplore.Bandits.dInf unitLaws (ν c) (⨆ b, ∫ y, id y ∂(ν b))).toReal,
      ∀ᶠ ℓ in atTop, c' < (∑ c, gap ν c * ∫ ω, (pullCount IT.action c (g.t ℓ) ω : ℝ)
          ∂(trajMeasure alg (Environment.bandit ν))) / Real.log (g.t ℓ) := by
  intro c' hc'
  set S := Finset.univ.filter (fun c ↦ 0 < gap ν c)
  have hsum := eventually_lt_sum_mul S (w := fun c ↦ gap ν c)
    (L := fun c ↦ 1 / (LMLExplore.Bandits.dInf unitLaws (ν c) (⨆ b, ∫ y, id y ∂(ν b))).toReal)
    (u := fun c ℓ ↦ (∫ ω, (pullCount IT.action c (g.t ℓ) ω : ℝ)
      ∂(trajMeasure alg (Environment.bandit ν))) / Real.log (g.t ℓ))
    (fun c hcS ↦ (Finset.mem_filter.mp hcS).2)
    (fun c hcS ↦ eventually_lt_integral_pullCount_div_log_t g hb hc hν
      (Finset.mem_filter.mp hcS).2) c' (by simpa only [mul_one_div] using hc')
  filter_upwards [hsum] with ℓ hℓ
  have hsplit : (∑ c, gap ν c * ∫ ω, (pullCount IT.action c (g.t ℓ) ω : ℝ)
      ∂(trajMeasure alg (Environment.bandit ν))) / Real.log (g.t ℓ) =
      ∑ c ∈ S, gap ν c * ((∫ ω, (pullCount IT.action c (g.t ℓ) ω : ℝ)
        ∂(trajMeasure alg (Environment.bandit ν))) / Real.log (g.t ℓ)) := by
    rw [Finset.sum_div, ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun c ↦ 0 < gap ν c)]
    have h0 : ∑ c ∈ Finset.univ.filter (fun c ↦ ¬ 0 < gap ν c),
        gap ν c * (∫ ω, (pullCount IT.action c (g.t ℓ) ω : ℝ)
          ∂(trajMeasure alg (Environment.bandit ν))) / Real.log (g.t ℓ) = 0 := by
      refine Finset.sum_eq_zero fun c hcS ↦ ?_
      have : gap ν c = 0 := le_antisymm (not_lt.mp (Finset.mem_filter.mp hcS).2) gap_nonneg
      simp [this]
    rw [h0, add_zero]
    exact Finset.sum_congr rfl fun c _ ↦ by ring
  rw [hsplit]
  exact hℓ

end Incognita.BatchedBandits
