/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.Setting

/-! # Prior bandit games on the source stacks, stopped or not

The objects of [INC-P003, def:prior-game and def:stopped-game] (paper `P003-transfer-setting`).

A prior bandit game over `T'` rounds is played on the source stacks before the online game: at
round `r` (0-based; the paper's round `r + 1`) the strategy chooses an arm `A'_r` from the
randomisation and the previous pairs (arm, value), and observes the next unread value of the
stack of that arm. Its counts are a size rule (lem:prior-game (b)); stopped at a stopping time of
its own observations, its counts are still a size rule (prop:stopped-games (a)).

## Main definitions

* `PriorStrategy α`: measurable maps `α_r : [0,1]^ℕ × (α × ℝ)^r → α`, one for each round `r`.
* `PriorStrategy.state g ω r`: the counts `C(r)` and the history `(A'_i, Y'_i)_{i < r}` after `r`
  rounds; `PriorStrategy.counts g T'`: the counts `C(T')` of the game over `T'` rounds.
* `PriorStrategy.histSigma g r`: the σ-algebra `𝓕'_r` of the randomisation and the first `r`
  rounds.
* `PriorStrategy.IsStoppingTime g T' τ`: `τ : Ω' → {0, …, T'}` with `{τ = r} ∈ 𝓕'_r`;
  `PriorStrategy.stoppedCounts g τ`: the stopped counts `C(τ)`.

The strategy is given at every round `r : ℕ`; the game over `T'` rounds uses the rounds `r < T'`
only, so this is the paper's family `(α_r)_{r = 1, …, T'}` extended arbitrarily.

## Main statements

* `PriorStrategy.ext`; `PriorStrategy.state_zero`, `PriorStrategy.state_succ`: the recursion
  defining the state of the game.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

open scoped unitInterval

namespace Incognita.TransferBandits

variable {α : Type*} [MeasurableSpace α]

/-- A strategy of a **prior bandit game** [INC-P003, def:prior-game]: for each round `r`
(0-based), a measurable map from the randomisation and the `r` previous pairs (arm, value) to the
arms. -/
structure PriorStrategy (α : Type*) [MeasurableSpace α] where
  /-- The arm chosen at round `r` given the randomisation and the previous rounds. -/
  act : (r : ℕ) → (ℕ → I) × (Fin r → α × ℝ) → α
  /-- Each choice is measurable. -/
  measurable_act : ∀ r, Measurable (act r)

namespace PriorStrategy

variable [DecidableEq α]

/-- The state of the prior game after `r` rounds on the source point `ω`: the counts
`C_k(r)` (the number of rounds `i < r` with `A'_i = k`) and the history `(A'_i, Y'_i)_{i < r}`.
At the 0-based round `r` the arm `A'_r = act r (U', history)` is chosen and the value observed is
`Y'_r = ω.2 A'_r (C_{A'_r}(r)) = X'_{A'_r, C_{A'_r}(r)}` (0-based stack index), the next unread
value of its stack; then the count of `A'_r` is incremented. In the paper's rounds and stack
indices, both from `1`, this is `Y'_{r+1} = X'_{A'_{r+1}, C_{A'_{r+1}}(r+1)}`. -/
def state (g : PriorStrategy α) (ω : SourceSpace α) : (r : ℕ) → (α → ℕ) × (Fin r → α × ℝ)
  | 0 => (0, fun i ↦ i.elim0)
  | r + 1 =>
    let st := state g ω r
    let a := g.act r (ω.1, st.2)
    (Function.update st.1 a (st.1 a + 1),
      (MeasurableEquiv.finSuccProd (α × ℝ) r).symm (st.2, (a, ω.2 a (st.1 a))))

/-- The counts `N'_k = C_k(T')` of the prior game over `T'` rounds [INC-P003, def:prior-game]. -/
def counts (g : PriorStrategy α) (T' : ℕ) (ω : SourceSpace α) : α → ℕ := (state g ω T').1

/-- The σ-algebra `𝓕'_r = σ(U', (A'_i, Y'_i)_{i < r})` of the randomisation and of the first `r`
rounds of the prior game [INC-P003, def:stopped-game] (the paper's `(A'_i, Y'_i)_{i ≤ r}`, rounds
from `1`). -/
@[instance_reducible]
def histSigma (g : PriorStrategy α) (r : ℕ) : MeasurableSpace (SourceSpace α) :=
  MeasurableSpace.comap (fun ω ↦ (ω.1, (state g ω r).2)) inferInstance

/-- A **stopping time of the prior game** over `T'` rounds [INC-P003, def:stopped-game]: a map
`τ : Ω' → {0, …, T'}` with `{τ = r} ∈ 𝓕'_r` for every `r`. -/
structure IsStoppingTime (g : PriorStrategy α) (T' : ℕ) (τ : SourceSpace α → ℕ) : Prop where
  /-- The game is stopped by round `T'`. -/
  le : ∀ ω, τ ω ≤ T'
  /-- The decision to stop after `r` rounds reads only the randomisation and these rounds. -/
  measurableSet_eq : ∀ r, MeasurableSet[histSigma g r] {ω | τ ω = r}

/-- The stopped counts `N'_k = C_k(τ)` [INC-P003, def:stopped-game]. -/
def stoppedCounts (g : PriorStrategy α) (τ : SourceSpace α → ℕ) (ω : SourceSpace α) : α → ℕ :=
  (state g ω (τ ω)).1

/-! ### Basic API -/

omit [DecidableEq α] in
/-- Two strategies of a prior game with the same choices are equal. -/
@[ext]
lemma ext {g g' : PriorStrategy α} (h : ∀ r, g.act r = g'.act r) : g = g' := by
  obtain ⟨act, _⟩ := g
  obtain ⟨act', _⟩ := g'
  obtain rfl : act = act' := funext h
  rfl

/-- Before the first round, the counts are zero and the history is empty. -/
@[simp]
lemma state_zero (g : PriorStrategy α) (ω : SourceSpace α) :
    g.state ω 0 = (0, fun i ↦ i.elim0) := rfl

/-- One round of the prior game: the arm `A'_r = act r (U', history)` is chosen, its count is
incremented, and the pair `(A'_r, X'_{A'_r, C_{A'_r}(r)})` is appended to the history. -/
lemma state_succ (g : PriorStrategy α) (ω : SourceSpace α) (r : ℕ) :
    g.state ω (r + 1) =
      let st := g.state ω r
      let a := g.act r (ω.1, st.2)
      (Function.update st.1 a (st.1 a + 1),
        (MeasurableEquiv.finSuccProd (α × ℝ) r).symm (st.2, (a, ω.2 a (st.1 a)))) :=
  rfl

end PriorStrategy

end Incognita.TransferBandits
