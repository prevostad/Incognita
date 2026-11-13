# Programme: structured bandits and the Graves–Lai bound

| | |
|---|---|
| Status | **draft**, proposed by Claude, awaiting approval by a human owner |
| Owner | to be decided (proposed to Adrien Prevost) |
| Written | 2026-11-13 by Claude (Anthropic), at the owner's request ("carte blanche") |
| arXiv class | `math.ST` (secondary `math.OC`, `stat.ML`) |

## Motivation

When the arms share a known structure (linear, Lipschitz, unimodal, combinatorial...), pulling one
arm informs about others, and the optimal asymptotic regret is no longer a sum of per-arm terms:
it is the value of an optimisation problem over exploration allocations (Graves and Lai). Optimism,
which is optimal without structure, can then be arbitrarily far from optimal. The questions are which
algorithms are optimal, how simple they can be, and what the regret looks like before the asymptotic
regime. This is a natural next step after the unstructured theory, and it is outside the scope of
LMLExplore's Bandits roadmap, which explicitly leaves out asymptotic lower bounds for linear bandits.

## Setting and pinned conventions

- **Model.** A finite set of arms $\mathcal A$ and a set $\Theta$ of parameters; arm $a$ under
  $\theta \in \Theta$ has a reward distribution $\nu_a(\theta)$ in a fixed one-parameter family (first
  Gaussian with known variance, then exponential families). The structure is the set $\Theta$, known to
  the learner. $\mu_a(\theta)$, $\mu^\star(\theta)$, $\Delta_a(\theta)$ as usual; a unique optimal arm
  $a^\star(\theta)$ unless a question says otherwise.
- **Alternatives.** $\mathrm{Alt}(\theta) := \lbrace \lambda \in \Theta : \nu_{a^\star(\theta)}(\lambda) = \nu_{a^\star(\theta)}(\theta),\ a^\star(\lambda) \ne a^\star(\theta)\rbrace$.
- **Graves–Lai constant.**
  $C(\theta) := \inf\big\lbrace \sum_a w_a \Delta_a(\theta) : w \in [0,\infty]^{\mathcal A},\ \forall \lambda \in \mathrm{Alt}(\theta),\ \sum_a w_a\, \mathrm{KL}(\nu_a(\theta), \nu_a(\lambda)) \ge 1\big\rbrace$.
- **Consistency.** Regret $o(T^\alpha)$ for every $\alpha > 0$ and every $\theta \in \Theta$.
- **Lean.** LMLExplore's Bandits roadmap conventions; a structure is a set `Θ` with a map to
  `α → Measure ℝ` (or a kernel), so that unstructured bandits are the special case of the product
  structure.

## What is known

- Graves and Lai (1997, SIAM J. Control Optim.): for consistent algorithms,
  $\liminf_T R_T / \log T \ge C(\theta)$, in a general setting of controlled Markov chains.
- Combes, Magureanu, Proutière (2017, NeurIPS), OSSB: an algorithm attaining $C(\theta)$ for general
  structures, by tracking the optimal allocation with forced exploration.
- Lattimore and Szepesvári (2017, AISTATS), "The End of Optimism?": for linear bandits, optimistic
  algorithms and Thompson sampling can have regret arbitrarily larger than $C(\theta)\log T$; an
  asymptotically optimal algorithm.
- Degenne, Shao, Koolen (2020, ICML), structure-adaptive algorithms: optimality through a game
  between allocations and alternatives, with optimism used inside the game.
- Unimodal and Lipschitz structures: optimal algorithms that exploit the structure directly
  (Combes and Proutière, 2014, for unimodal bandits).

Agents must read the exact statements in the sources before using or formalising them.

## Known results to formalise

1. The Graves–Lai lower bound for finite-armed structured bandits with Gaussian rewards (then
   exponential families), as a consequence of the change of measure already used for the
   unstructured lower bound; the unstructured bound as the special case of the product structure.
2. Basic properties of $C(\theta)$: existence of an optimal allocation (or of an
   $\varepsilon$-optimal one), continuity in $\theta$ where it holds, the formula for linear
   structures.
3. The "end of optimism" example: a linear instance where an optimistic algorithm's regret exceeds
   $c \cdot C(\theta)\log T$ for a given $c > 1$ (a refutation-type result).

## Open directions

1. **When is optimism enough?** Characterise the structures for which an optimistic index policy
   (without forced exploration) attains $C(\theta)$.
2. **How much forced exploration?** The minimal rate of forced exploration an asymptotically optimal
   algorithm needs, as a function of the structure; is $o(\log T)$ always enough, and is any
   necessary?
3. **Finite-time behaviour.** Non-asymptotic upper bounds of the form
   $C(\theta)\log T + o(\log T)$ with explicit remainders, and lower bounds on the second-order term
   (link with the RegretShape programme).
4. **Simple optimal algorithms.** Optimal algorithms that solve the Graves–Lai problem only
   approximately, or rarely, with a proven cost of the approximation.
5. **Degenerate cases.** Several optimal arms, alternatives at the boundary of $\Theta$, infinite
   $C(\theta)$.

## What would be an important result

A characterisation for direction 1 or 2; an explicit non-asymptotic bound matching $C(\theta)$ at
first order with a reasonable remainder; a formal counterexample to a plausible conjecture (for
instance that some simple algorithm is optimal on a class of structures).

## Out of scope

Contextual bandits with changing contexts, infinitely many arms, reinforcement learning, pure
exploration (LML's identification framework covers best-arm identification).

## Criteria for validating a question of this programme

1. It names the class of structures precisely and checks that the product structure (or another
   known case) is inside or outside it.
2. It states the consistency class and the criterion.
3. It exhibits one structure and one instance satisfying all hypotheses.
4. It says which known result it extends, and why it is not a corollary.
5. "No" is a possible answer, and the natural fallback is stated.
