/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Incognita.TransferBandits.Examples
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.Distributions.Bernoulli

/-! # P003, thm:main (b): the decomposition fails for the look-ahead map

[INC-P003, Theorem (thm:main), part (b)]. The look-ahead map `N^la` (`lookahead a₁`: size `1` on
arm `a₁` if the second value of its stack exceeds `1/2`, `2` otherwise, `0` on the other arms) is
a bounded size map and not a size rule. For all `p ≠ q` in `(0,1)`, every transfer learner `π`,
every horizon `T`, every target instance `ν` and all source laws of the other arms, if
`ν'_{a₁} = Ber(p)`, `ν₂'_{a₁} = Ber(q)`, `ν₂'_k = ν'_k` for `k ≠ a₁`, and the target instance is the
same (`ν̃ = ν`), then `KL(P, P₂) = 2 kl(p, q)`, while the right-hand side of eq:main equals
`(2 - p) kl(p, q) < 2 kl(p, q)`.

Differences of form with the paper:

* the paper's arm `1` is an arbitrary arm `a₁`, and its second value `X'_{1,2}` is the value of
  index `1` of the stack (indices from `0`); the paper's `ν̃'` is `ν₂'`;
* `Ber(p)` is Mathlib's `Ber((1 : ℝ), 0, p)` (mass `p` at `1`), with `p q : I`;
  `kl(p, q) = KL(Ber(p), Ber(q))` as in def:laws;
* "bounded" is `∃ M, ∀ ω a, N^la ω a ≤ M`; the right-hand side of eq:main is written out, with
  `KL(ν_k, ν_k)` for the target term since `ν̃ = ν`;
* `(2 - p)` is `ENNReal.ofReal (2 - p)`;
* the hypothesis that the source laws are on `[0,1]` is `ν' ∈ unitBandits α` (the paper asks it of
  `ν'_2, …, ν'_K`; for `ν'_{a₁} = Ber(p)` it holds anyway); the law `ν₂'` is determined by the
  hypotheses.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Incognita.TransferBandits

open scoped ENNReal unitInterval

namespace Incognita.Statements.P003

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
  sorry

end Incognita.Statements.P003
