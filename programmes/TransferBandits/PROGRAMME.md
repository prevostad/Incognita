# Programme: transfer learning in bandits from historical data

| | |
|---|---|
| Status | **draft**, awaiting approval by its owner |
| Owner | Adrien Prevost (GitHub: prevostad) |
| Written | 2026-11-13, with AI assistance (Claude) |
| arXiv class | `math.ST` (secondary `stat.ML`) |

## Motivation

Before a bandit is deployed, there are often historical observations of the same arms, collected
by an earlier decision process whose policy is unknown and whose environment may have drifted.
How much can these data reduce the regret, which algorithms exploit them optimally, and what
happens when the assumed bound on the drift is wrong?

## Setting and pinned conventions

- **Target.** $K$ arms with reward distributions $\nu_k$ on $[0,1]$, means $\mu_k$; arm 1 optimal
  in examples, $\mu^\star := \max_k \mu_k$; regret and counts $N_k(T)$ as in LML.
- **Source.** Before the game, for each arm $k$ the learner receives the first $N'_k$ observations
  of an i.i.d. sequence from an unknown $\nu'_k$ with mean $\mu'_k$. The sizes $N'_k$ are chosen by
  an arbitrary, possibly data-dependent strategy, so they may be random.
- **Drift.** Known constants $L_k$ with $\mu_k - \mu'_k < L_k$ (one-sided condition; the two-sided
  condition $|\mu_k - \mu'_k| < L_k$ reduces to it, see below).
- **Consistency** is the notion of arXiv:2610.21582 (copy its definition into the first
  definition pull request); a question that uses another notion says so.
- **Asymptotics** are in the horizon $T$, with the source sizes possibly depending on $T$
  (for example $\mathbb E N'_k / \log T \to$ a limit); each question states its regime.
- **Lean.** Same conventions as the BatchedBandits programme (LMLExplore's Bandits roadmap).
  The source is modelled as reward stacks read before round 0, so that LML's chain rule for the
  KL divergence of histories applies to the pair (source, online game).

## What is known

**Published.**

- A. Prevost, T. Mathieu, O.-A. Maillard, *Asymptotically Optimal Problem-Dependent Bandit
  Policies for Transfer Learning*, ACML 2025 (PMLR 304; arXiv:2509.19098): Gaussian rewards,
  deterministic source sizes; problem-dependent lower bound and an asymptotically optimal policy.
- A. Prevost, T. Mathieu, W. Radji, O.-A. Maillard, *Transfer Learning in Bandits from Unknown
  Adaptive Policies: Problem-Dependent Lower and Upper Bounds* (arXiv:2610.21582, 2026):
  rewards in $[0,1]$, random source sizes as above. An asymptotic problem-dependent lower bound;
  the algorithm KL-UCB-Transfer, which combines source and online data and has logarithmic regret
  with an improved leading constant whenever $\mu'_a < \mu^\star - L_a$, and the KL-UCB guarantee
  otherwise; its regret matches the lower bound when the source sizes concentrate. The lower
  inequalities $\mu'_k - L_k < \mu_k$ play no role (reduction to the one-sided condition, with the
  same bounds). Under misspecification of the condition, three regimes: improvement, degraded
  logarithmic bound, loss of guarantee.

Nothing of this is formalised yet.

## Known results to formalise

1. The lower bound and the upper bound of KL-UCB-Transfer from arXiv:2610.21582, with the
   reduction from two-sided to one-sided drift. Start with the elementary lemmas they rest on
   (inequalities on positive parts such as $(a_+ - b_+) \le (a-b)_+$, the decomposition of the KL
   divergence of the history into a source phase and an online phase).
2. The Gaussian results of the ACML paper, if they are not special cases of item 1 (check first).
3. KL-UCB itself on $[0,1]$ if it is not in LMLExplore at the pinned version (check its Bandits
   roadmap, Layer 3, and follow its names).

## Open directions

1. **Random source sizes.** The lower bound sees the source sizes only through
   $\mathbb E N'_k$. Is the quantity $\mathbb E[(\log T - N'_a D_a)_+]$ (with $D_a$ the relevant
   divergence) the right one when the fluctuations of $N'_a$ come from the source rewards, that is,
   is the Jensen gap between the two unavoidable? A conditional change of measure is the natural
   tool.
2. **Boundary.** The case $\mu'_a = \mu^\star - L_a$ with $\mathbb E N'_a / \log T \to \infty$.
3. **Intermediate severe regime.** Source sizes of the optimal arm of order $\log T$.
4. **Several sources.** Optimal and robust aggregation of several sources with different drifts.
5. **Unknown drift.** Adaptivity to $L_k$: what is the price of not knowing it, and is there a
   learner that is never worse than KL-UCB and matches the known-$L$ bound when $L$ is right?
6. **Other models.** One-parameter exponential families, Gaussians with unknown variance.
7. **Non-asymptotic bounds** with explicit dependence on the source sizes.

## What would be an important result

A matching lower bound for random source sizes (direction 1), an adaptive learner (direction 5),
or a formal counterexample showing that a natural algorithm is not optimal in one of the regimes.

## Out of scope

Transfer between different action sets or contextual models, representation transfer,
meta-learning over many tasks, offline-only policy evaluation.

## Criteria for validating a question of this programme

1. It states the source model (sizes deterministic or random, how they may depend on $T$), the
   drift condition, the consistency class and the criterion.
2. It names the known result it extends and why it is not a corollary.
3. Its hypotheses are jointly satisfiable: one explicit (target, source, size strategy).
4. A lower bound states its class of learners explicitly.
5. "No" is a possible answer, and the natural fallback is stated.
