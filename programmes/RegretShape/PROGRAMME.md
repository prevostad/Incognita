# Programme: the shape of regret beyond the first order

| | |
|---|---|
| Status | **draft**, awaiting approval by its owner |
| Owner | Adrien Prevost (GitHub: prevostad) |
| Written | 2026-11-13, with AI assistance (Claude) |
| arXiv class | `math.ST` (secondary `stat.ML`) |

## Motivation

The first-order behaviour of the problem-dependent regret is settled: for consistent algorithms,
$\mathbb E N_a(T) \sim \log T / \mathcal K_{\inf}(\nu_a, \mu^\star)$, and several algorithms attain
it. Garivier, Ménard and Stoltz (2019) showed that the regret has a richer shape: almost linear
while the horizon is too short to tell the arms apart, then a transition, then logarithmic, with a
second-order term of order $\log\log T$ in their lower bound. This programme asks for the exact
shape: the order, the sign and the constant of the second-order term, how they depend on the class
of algorithms, and when the transition happens.

## Setting and pinned conventions

- **Model.** $K \ge 2$ arms, each in a model $\mathcal D$ (Bernoulli, distributions on $[0,1]$, or a
  one-parameter exponential family; each question says which). $\mu^\star := \max_a \mu_a$,
  $\Delta_a := \mu^\star - \mu_a$, $\mathcal K_{\inf}(\nu_a, \mu) := \inf\{\mathrm{KL}(\nu_a, \nu') : \nu' \in \mathcal D,\ \mathbb E \nu' > \mu\}$.
- **Classes of algorithms.** Consistency classes are those of Garivier–Ménard–Stoltz (2019):
  uniformly fast convergent, uniformly super-fast convergent (copy their definitions, with the
  constants they carry, into the first definition pull request). A question about another class
  defines it.
- **Quantities.** $\mathbb E N_a(T)$ for a fixed suboptimal arm $a$, and the regret
  $\sum_a \Delta_a \mathbb E N_a(T)$, at every horizon $T$; bounds are non-asymptotic whenever
  possible, with explicit constants.
- **Lean.** LMLExplore's Bandits roadmap conventions (rounds from 0, `Fintype α` arms, LML's
  `regret`). Its Layer 4 (lower bounds for finitely many arms) may already plan some of the
  material below: check it first, follow its names and statement shapes, never duplicate what
  exists at the pinned version.

## What is known

- Lai–Robbins (1985), Burnetas–Katehakis (1996): the first-order lower bound.
- Garivier, Ménard, Stoltz, *Explore first, exploit next: the true shape of regret in bandit
  problems*, Math. Oper. Res. 44(2), 2019 (arXiv:1602.07182):
  - a fundamental inequality: for every $Z \in [0,1]$ measurable with respect to the history,
    $\sum_a \mathbb E_\nu[N_a(T)]\,\mathrm{KL}(\nu_a, \nu'_a) \ge \mathrm{kl}(\mathbb E_\nu Z, \mathbb E_{\nu'} Z)$;
  - lower bounds for small horizons (almost linear regret) valid for all bandit problems under
    mild symmetry assumptions on the strategies;
  - a non-asymptotic lower bound for large horizons, for uniformly super-fast convergent
    strategies, whose second-order term is of order $-\log\log T$;
  - re-derivations of the asymptotic bound and of the distribution-free $\sqrt{KT}$ lower bound.
- Upper bounds with explicit second-order terms: KL-UCB (Cappé, Garivier, Maillard, Munos, Stoltz
  2013), IMED (Honda–Takemura 2015), KL-UCB++ (Ménard–Garivier 2017), Thompson sampling
  (Kaufmann, Korda, Munos 2012; Agrawal–Goyal). The exact second-order terms differ between these
  algorithms and models.
- Weakly consistent policies and their selectivity: Salomon, Audibert, El Alaoui (2013).

Agents must read the exact statements in the sources before using or formalising them; this list
gives pointers, not statements.

## Known results to formalise

1. The fundamental inequality of Garivier–Ménard–Stoltz, for LML's bandit histories.
2. Their non-asymptotic large-horizon lower bound (the theorem and its corollary with the
   $\log\log T$ term), with all constants explicit as in the paper.
3. Their small-horizon lower bounds.
4. The asymptotic Lai–Robbins / Burnetas–Katehakis bound as a corollary of item 2, unless
   LMLExplore already has it.
5. One upper bound with an explicit second-order term (KL-UCB or IMED on $[0,1]$), to have both
   sides of the question in the library.

## Open directions

1. **Order and sign of the second-order term.** Within a given consistency class, is the optimal
   $\mathbb E N_a(T)$ equal to $\log T/\mathcal K_{\inf} - \Theta(\log\log T)$, to
   $\log T/\mathcal K_{\inf} + \Theta(\log\log T)$, or something else? Is there an algorithm whose
   upper bound has a negative second-order term?
2. **The constant.** The best constant in front of the second-order term, as a function of the
   class (rate of consistency) and of the instance.
3. **Trade-off with the rate of consistency.** How the uniform rate required by the class
   constrains the second-order term; whether faster consistency forces a larger second-order term.
4. **The transition.** The horizon at which the regret leaves the almost linear regime, up to
   constants, as a function of the instance (for example of $\sum_a \Delta_a^{-2}$ and of the
   divergences).
5. **Model dependence.** Bernoulli versus general $[0,1]$ versus Gaussian: does the second-order
   term change?
6. **Beyond the classical bandit.** The same questions for batched and transfer bandits (link with
   the BatchedBandits and TransferBandits programmes).

## What would be an important result

Matching upper and lower bounds at second order (order, sign and constant) in one model and one
class; a formal proof that a classical algorithm's second-order term is not optimal; an exact
description of the transition horizon.

## Out of scope

The constant of the minimax regret $\sqrt{KT}$ (the owner studies it separately); adversarial
bandits; high-probability bounds.

## Criteria for validating a question of this programme

1. It states the model, the class of algorithms (with its rate), and whether the bound is
   asymptotic or non-asymptotic.
2. It says which known first- or second-order result it refines and why it is not a corollary.
3. Its hypotheses are jointly satisfiable: one explicit instance, and one algorithm of the class.
4. For a lower bound, the class of algorithms is explicit; for an upper bound, the algorithm is
   defined completely.
5. "No" is a possible answer, and the natural fallback is stated.
