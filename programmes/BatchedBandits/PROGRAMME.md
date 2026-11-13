# Programme: batched bandits on an imposed grid

| | |
|---|---|
| Status | **draft**, awaiting approval by its owner |
| Owner | Adrien Prevost (GitHub: prevostad) |
| Written | 2026-11-13, with AI assistance (Claude) |
| arXiv class | `math.ST` (secondary `stat.ML`) |

A programme is approved by a human and then left to agents: they propose questions inside it, a
question reviewer validates them against the criteria at the end of this file, and validated
questions are worked on under the rules of [AGENTS.md](../../AGENTS.md). See
[programmes/README.md](../README.md) for what a programme must contain.

## Motivation

In clinical trials, A/B tests or any system that redeploys a policy periodically, a bandit learner
can update its decisions only at the end of batches, and the ends of the batches are imposed by the
environment rather than chosen. The question of this programme is: **how much does the
problem-dependent asymptotic regret degrade as a function of the imposed grid, and which
algorithms achieve the optimal degradation?** The aim is a complete answer, verified in Lean, and
algorithms that are optimal *and* usable in practice.

## Setting and pinned conventions

Every question of this programme uses these conventions unless it says explicitly which one it
changes and why.

- **Arms and rewards.** $K \ge 2$ arms; arm $a$ has a reward distribution $\nu_a$ on $[0,1]$ with
  mean $m_a$; $m^\star := \max_a m_a < 1$. For a suboptimal arm $a$,
  $K_a := \mathcal K_{\inf}(\nu_a, m^\star)$ (Burnetas–Katehakis; Honda–Takemura), the infimum of
  $\mathrm{KL}(\nu_a, \nu')$ over distributions $\nu'$ on $[0,1]$ with mean $> m^\star$.
- **Grid.** Batch sizes $B_\ell \ge 1$, batch ends $t_\ell := B_1 + \dots + B_\ell$, with
  $B_1 \ge \max(2, K)$. Write $L_\ell := \log t_\ell$ and $x_\ell := L_\ell / L_{\ell-1}$ for
  $\ell \ge 2$, $x_1 := 1$.
- **Learner.** The arms pulled during batch $\ell + 1$ are measurable with respect to the
  observations up to $t_\ell$ and to internal randomisation.
- **Information models.** In model $M_k$, during batch $j+1$ the learner knows
  $t_1, \dots, t_{j+k}$ and the current round. $M_0$ knows nothing ahead (doubly anytime), $M_1$
  knows the end of the current batch (single anytime).
- **Consistency at batch ends.** $\mathbb E\, N_c(t_\ell) = o(t_\ell^\alpha)$ for every
  $\alpha > 0$, every instance and every suboptimal arm $c$, where $N_c(t)$ is the number of pulls
  of $c$ up to round $t$.
- **Criterion.** Unless stated otherwise, limits of $K_a\, \mathbb E\, N_a(t_\ell) / L_\ell$ along
  batch ends. A question about all rounds, or about the regret
  $\sum_c \Delta_c\, \mathbb E\, N_c(T)$, says so.
- **Lean.** Follow the conventions section of LMLExplore's Bandits roadmap
  (`LMLRoadmaps/Bandits/README.md`): rounds numbered from 0, arms as a `Fintype α` (never `Fin K`),
  bounded rewards as `∀ a, ∀ᵐ x ∂(ν a), x ∈ Set.Icc 0 1`, LML's environments and regret. The
  translation of the grid to 0-based rounds is fixed once, in the first definition pull request,
  and then reused.

## What is known

**Published.**

- Fully sequential, any consistent algorithm:
  $\liminf_T \mathbb E\, N_a(T) / \log T \ge 1 / K_a$ (Lai–Robbins 1985; Burnetas–Katehakis 1996).
  IMED (Honda–Takemura 2015) and KL-UCB (Cappé et al. 2013) attain it.
- Batched bandits with grids *chosen* by the learner: Perchet, Rigollet, Chassang, Snowberg (2016);
  Gao, Han, Ren, Zhou (2019). Not this programme's setting: here the grid is imposed.

**The owner's unpublished results (2026).** Status tags: **[Lean]** formalised without `sorry` in
the owner's private Lean project, to be ported here; **[paper]** proved on paper, proofs checked by
independent AI agents only, no Lean.

- **[Lean]** Grids with $x_\ell \to 1$: IMED with statistics frozen during each batch is optimal,
  $\lim_\ell K_a\, \mathbb E\, N_a(t_\ell) / L_\ell = 1$, with no assumption beyond $m^\star < 1$.
- **[Lean]** Grids with $x_\ell \to x \in [1, \infty)$: every consistent learner, in every
  information model, has $\limsup_\ell K_a\, \mathbb E\, N_a(t_\ell)/L_\ell \ge x^2$ ("explore two
  batches ahead"); a hybrid algorithm HY in $M_0$ attains $x^2$. HY's second-order terms are
  astronomical.
- **[paper]** Non-convergent grids: on $\{\limsup_\ell x_\ell \le X\}$ the minimax constant is
  $X^2$ in every information model, attained by an epoch-based learner in $M_0$ that knows only $X$;
  no learner in $M_{\le 2}$ adapts to $\limsup_\ell x_\ell$; with unbounded ratios there is no
  first-order constant.
- **[paper]** Batched best-arm identification (Gaussian, fixed confidence): the two-batches-ahead
  phenomenon appears only if the last batch must be announced one batch in advance; the
  lower-bound technique is Lorden's (1983).

## Open directions

Questions are welcome in these directions; this list is not exhaustive.

1. **Practical optimality for $x > 1$.** Is there an algorithm in $M_0$ (or $M_1$) that attains
   $x^2$ with explicit second-order terms of reasonable size? Or a lower bound on the second-order
   term that shows a price for not knowing the grid?
2. **Non-asymptotic bounds.** Explicit bounds at batch ends, valid for every grid, that match the
   first-order constants above.
3. **Mixed regime.** When $\liminf_\ell x_\ell = 1 < \limsup_\ell x_\ell$: a grid-by-grid
   benchmark is known from below only; is there a matching upper bound?
4. **Existence frontier.** The exact class of grids that admit a consistent learner with
   logarithmic counts. Candidate: $\log L_{\ell+2} = o(L_\ell)$.
5. **Beyond $[0,1]$.** One-parameter exponential families, Gaussians with unknown variance, heavy
   tails: does the constant $x^2 / \mathcal K_{\inf}$ persist, with the matching $\mathcal K_{\inf}$?
6. **All rounds.** The same questions for $\mathbb E\, N_a(t)$ at every round $t$, in each
   information model.
7. **Batched best-arm identification** on imposed grids: non-Gaussian rewards, upper bounds in
   expectation.
8. **Verification of [paper] results.** Formalising one of them counts as a result of this
   programme: a formal proof, or a counterexample.

## What would be an important result

- Matching bounds that close one of the directions above.
- An algorithm that is optimal and practical (explicit, moderate constants; simulations are a
  supplement, never a substitute).
- A formal refutation of a natural conjecture, for example that a simple algorithm is optimal.

Not important on their own: rederiving known bounds with worse constants; generalising a lemma
that nothing uses.

## Out of scope

Grids chosen by the learner (except as a point of comparison), minimax $\sqrt T$-type results,
adversarial, contextual and linear bandits, reinforcement learning. They may become programmes of
their own.

## Lean prerequisites

Before defining anything, search Mathlib, Tau Ceti, LML and LMLExplore at the pinned versions.
If $\mathcal K_{\inf}$, or batched learners, are missing there, building them with their basic API
is the first library task of this programme. If LMLExplore's Bandits roadmap plans an object, follow
the name and statement shape it fixes, so that adopting LMLExplore's version later is a deletion
plus an import.

## Criteria for validating a question of this programme

The question reviewer accepts a question only if:

1. it states its information model, its class of instances and grids, and its criterion
   (batch ends or all rounds; $\limsup$ or $\liminf$; counts or regret);
2. it names the known result it extends, and says why its answer is not a corollary of the
   catalogue (the reviewer tries a short proof from the catalogue and fails);
3. its hypotheses are jointly satisfiable: the question exhibits one grid and one instance that
   satisfy all of them at once;
4. for a lower bound, the class of learners is explicit (which consistency notion, which
   information model);
5. it is a question, not a conclusion: its statement allows "no" as an answer, and says which
   variant would be the natural fallback.
