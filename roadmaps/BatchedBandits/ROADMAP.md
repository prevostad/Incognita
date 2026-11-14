# Roadmap: batched bandits on an imposed grid

| | |
|---|---|
| Status | **approved** (by the owner, 2026-11-13, as the v1 programme; migrated to a roadmap on 2026-11-14 without change of content, except direction D9) |
| Owner | Adrien Prevost (GitHub: prevostad) |
| Written | 2026-11-13, with AI assistance (Claude); migrated from `programmes/BatchedBandits/PROGRAMME.md` and `HY.md` by Claude on 2026-11-14 |
| KNOWN.md | [KNOWN.md](KNOWN.md) (papers are written once its first line reads `Reviewed by owner: <date>`) |
| Domain | `stochastic-bandits` (see roadmaps/README.md, "Domains") |
| arXiv class | `math.ST` (secondary `stat.ML`) |

Owner decisions pending (DECISIONS v3.1): whether agent papers that extend the owner's unpublished
results are public; whether P000's definitions are written by agents or ported from the owner's
private Lean project; what of the owner's notes is published in KNOWN.md.

## Motivation

In clinical trials, A/B tests or any system that redeploys a policy periodically, a bandit learner
can update its decisions only at the end of batches, and the ends of the batches are imposed by the
environment rather than chosen. The question of this roadmap is: **how much does the
problem-dependent asymptotic regret degrade as a function of the imposed grid, and which
algorithms achieve the optimal degradation?** The aim is a complete answer, verified in Lean, and
algorithms that are optimal *and* usable in practice.

## Pinned conventions

Every paper of this roadmap uses these conventions unless it says explicitly which one it changes
and why.

- **Arms and rewards.** $K \ge 2$ arms; arm $a$ has a reward distribution $\nu_a$ on $[0,1]$ with
  mean $m_a$; $m^\star := \max_a m_a < 1$. For a suboptimal arm $a$,
  $K_a := \mathcal K_{\inf}(\nu_a, m^\star)$ (Burnetas–Katehakis; Honda–Takemura), the infimum of
  $\mathrm{KL}(\nu_a, \nu')$ over distributions $\nu'$ on $[0,1]$ with mean $> m^\star$. Appendix A
  also writes $d_a := K_a$.
- **Grid.** Batch sizes $B_\ell \ge 1$, batch ends $t_\ell := B_1 + \dots + B_\ell$, with
  $B_1 \ge \max(2, K)$. Write $L_\ell := \log t_\ell$ and $x_\ell := L_\ell / L_{\ell-1}$ for
  $\ell \ge 2$, $x_1 := 1$.
- **Learner.** The arms pulled during batch $\ell + 1$ are measurable with respect to the
  observations up to $t_\ell$ and to internal randomisation.
- **Information models.** In model $M_k$, during batch $j+1$ the learner knows
  $t_1, \dots, t_{j+k}$ and the current round. $M_0$ knows nothing ahead (doubly anytime), $M_1$
  knows the end of the current batch (single anytime); $M_\infty$ knows the whole grid.
- **Consistency at batch ends.** $\mathbb E\, N_c(t_\ell) = o(t_\ell^\alpha)$ for every
  $\alpha > 0$, every instance and every suboptimal arm $c$, where $N_c(t)$ is the number of pulls
  of $c$ up to round $t$.
- **Criterion.** Unless stated otherwise, limits of $K_a\, \mathbb E\, N_a(t_\ell) / L_\ell$ along
  batch ends. A paper about all rounds, or about the regret
  $\sum_c \Delta_c\, \mathbb E\, N_c(T)$, says so.
- **Lean.** Follow the conventions of LMLExplore's Bandits roadmap (`LMLRoadmaps/Bandits/README.md`):
  rounds numbered from 0, arms as a `Fintype α` (never `Fin K`), bounded rewards as
  `∀ a, ∀ᵐ x ∂(ν a), x ∈ Set.Icc 0 1`, LML's environments and regret. The translation of the grid
  to 0-based rounds is fixed once, by P000 (F0), and then reused.

## Definitions

The core objects, with their planned Lean names. The setting paper P000 (item F0) formalises them;
it may change a name or a shape only with a justification in its Setting. Names of the dependencies
were read on LMLExplore's `main` on 2026-11-14: check them at the pinned revision.

| Object | Convention | Planned Lean name |
|---|---|---|
| arms | a type `α` with `[Fintype α]`, $K$ = its cardinality $\ge 2$ | — |
| instance | an LML bandit `ν : Kernel α ℝ`, rewards in $[0,1]$ almost surely, $m^\star < 1$; the class $\mathcal P$ of such instances | `Incognita.BatchedBandits.unitBandits α : Set (Kernel α ℝ)` |
| $K_a$ | `LMLExplore.Bandits.dInf M (ν a) m⋆` with `M` the probability measures on ℝ concentrated on $[0,1]$ (an `ℝ≥0∞`) | reuse `LMLExplore.Bandits.dInf` |
| grid | batch ends $0 = t_0 < t_1 < t_2 < \dots$, strictly increasing, $t_1 \ge \max(2, K)$; in 0-based rounds, batch $\ell \ge 1$ is the set of rounds $t_{\ell-1}, \dots, t_\ell - 1$ | `Incognita.BatchedBandits.Grid` (structure), `Grid.batchOf` (the batch of a round) |
| $L_\ell$, $x_\ell$ | $L_\ell = \log t_\ell$ (`Real.log`), $x_\ell = L_\ell / L_{\ell-1}$ for $\ell \ge 2$, $x_1 = 1$ | `Grid.logEnd`, `Grid.ratio` |
| learner | an LML algorithm (`Algorithm`, histories via `IsAlgEnvSeq`, law `trajMeasure`) | reuse |
| batched learner on a grid | the action at a round of batch $\ell + 1$ depends on the history only through the observations of rounds $< t_\ell$, its own past actions and its internal randomisation | `Incognita.BatchedBandits.IsBatched` |
| information model $M_k$ | a learner is a family `π : Grid → Algorithm …` batched on each grid; during batch $j+1$ the action depends on the grid only through $t_1, \dots, t_{j+k}$ and the current round; $M_\infty$: no restriction | `Incognita.BatchedBandits.InfoModel` (with $k : ℕ∞$) |
| counts, regret | LML's `pullCount` (pulls in rounds $0, \dots, t-1$, so the paper's $N_a(t_\ell)$ is `pullCount … a (t ℓ)`), `regret`, `gap` | reuse |
| consistency at batch ends | $\mathbb E\, N_c(t_\ell) = o(t_\ell^\alpha)$ for all $\alpha > 0$, every instance of a class $E$, every suboptimal $c$ | `Incognita.BatchedBandits.IsConsistentAtBatchEnds` |

P000 also proves the basic relations: $M_k$ is contained in $M_{k+1}$; on the grid whose batches
after the first have size 1, a batched learner is a sequential one and consistency at batch ends
relates to LMLExplore's `IsConsistent` (consistency at every round), so that LMLExplore's lower
bounds apply; a witness and an exclusion for each definition (for example, a learner that reacts to
a reward inside its batch is not batched on a grid with a batch of size $\ge 2$; a learner that reads
$t_{j+1}$ during batch $j+1$ is in $M_1$ but not in $M_0$).

## What is known

**Published.**

- Fully sequential, any consistent algorithm:
  $\liminf_T \mathbb E\, N_a(T) / \log T \ge 1 / K_a$ (Lai–Robbins 1985; Burnetas–Katehakis 1996).
  IMED (Honda–Takemura 2015) and KL-UCB (Cappé et al. 2013) attain it.
- Batched bandits with grids *chosen* by the learner: Perchet, Rigollet, Chassang, Snowberg (2016);
  Gao, Han, Ren, Zhou (2019). Not this roadmap's setting: here the grid is imposed.

**The owner's unpublished results (2026).** Status tags: **[Lean]** formalised without `sorry` in
the owner's private Lean project; **[paper]** proved on paper, proofs checked by independent AI
agents only, no Lean.

- **[Lean]** Grids with $x_\ell \to 1$: IMED with statistics frozen during each batch is optimal,
  $\lim_\ell K_a\, \mathbb E\, N_a(t_\ell) / L_\ell = 1$, with no assumption beyond $m^\star < 1$.
- **[Lean]** Grids with $x_\ell \to x \in [1, \infty)$: every consistent learner, in every
  information model, has $\limsup_\ell K_a\, \mathbb E\, N_a(t_\ell)/L_\ell \ge x^2$ ("explore two
  batches ahead"); a hybrid algorithm HY in $M_0$ attains $x^2$. HY's second-order terms are
  astronomical.
- **[paper]** Non-convergent grids: on $\lbrace \limsup_\ell x_\ell \le X\rbrace$ the minimax
  constant is $X^2$ in every information model, attained by an epoch-based learner in $M_0$ that
  knows only $X$; no learner in $M_{\le 2}$ adapts to $\limsup_\ell x_\ell$; with unbounded ratios
  there is no first-order constant.
- **[paper]** Batched best-arm identification (Gaussian, fixed confidence): the two-batches-ahead
  phenomenon appears only if the last batch must be announced one batch in advance; the
  lower-bound technique is Lorden's (1983).

The algorithm HY, the exact statements and the proof routes are in Appendices A and B. Everything
else the owner knows is in [KNOWN.md](KNOWN.md).

## Known results to formalise

Each item becomes a paper (AGENTS.md §5.1) whose novelty is not checked, only its fidelity to the
source; then it is formalised. In order:

- **F0. The setting** (paper `P000-setting`, kind `definitions`): the Definitions above, their basic
  relations, witnesses and exclusions. Its statements pull request is merged by the owner, who may
  instead port his private definitions (decision pending).
- **F1. The one-batch lower bound**, Appendix A, item 1, case $x = 1$ (kind `internal`, source: this
  roadmap): every batched learner consistent at batch ends, even one that knows the grid, has
  $\liminf_\ell \mathbb E N_a(t_\ell)/L_\ell \ge 1/d_a$, on every grid. It rests on the
  fundamental inequality of Garivier–Ménard–Stoltz [GMS19, (6)] applied to batched learners
  (a cited node; check first what LMLExplore's `InstanceDependentLowerBound` and `LaiRobbins` already
  provide). Proof route: Appendix B, "Lower bound".
- **F2. $\mathcal K_{\inf}$ on $[0,1]$** (kind `external`): dual formula, continuity, deviation
  inequalities for $n\,\mathcal K_{\inf}(\hat\nu_n, \mu)$ (Honda–Takemura 2010, 2015). Shared with
  StochasticBandits (its F10, owner decision of 2026-11-14): written once, by whichever roadmap
  comes first, and reused by the other.
- **F3. Batched IMED with frozen statistics, optimal when $x_\ell \to 1$** (kind `internal`, the
  owner's **[Lean]** result above). Open only once a KNOWN entry gives the algorithm by its formula;
  until then, skip it.
- **F4. The lower bound $x^2/K_a$ and the upper bound of HY** (Appendix A, items 1–3). **On hold**:
  the owner may port his private formalisation instead.
- **F5. The [paper] results above**: here formalisation is a verification; a failure is recorded as
  an erratum (AGENTS.md §6.6, case b), never resolved by weakening silently.

## Open directions

Papers are welcome in these directions; this list is not exhaustive.

- **D1. Practical optimality for $x > 1$.** Is there an algorithm in $M_0$ (or $M_1$) that attains
  $x^2$ with explicit second-order terms of reasonable size? Or a lower bound on the second-order
  term that shows a price for not knowing the grid?
- **D2. Non-asymptotic bounds.** Explicit bounds at batch ends, valid for every grid, that match the
  first-order constants above.
- **D3. Mixed regime.** When $\liminf_\ell x_\ell = 1 < \limsup_\ell x_\ell$: a grid-by-grid
  benchmark is known from below only; is there a matching upper bound?
- **D4. Existence frontier.** The exact class of grids that admit a consistent learner with
  logarithmic counts. Candidate: $\log L_{\ell+2} = o(L_\ell)$.
  *Agent's note (unverified, from v1 question Q001):* forced exploration in $M_2$ looks consistent
  at batch ends whenever $\log L_{\ell+1} = o(L_\ell)$, without logarithmic counts; the owner may
  want to say which count condition D4 means.
- **D5. Beyond $[0,1]$.** One-parameter exponential families, Gaussians with unknown variance, heavy
  tails: does the constant $x^2 / \mathcal K_{\inf}$ persist, with the matching $\mathcal K_{\inf}$?
- **D6. All rounds.** The same questions for $\mathbb E\, N_a(t)$ at every round $t$, in each
  information model. In particular: for $x > 1$, HY sits at $x^2/K_a$ at every round, while the
  lower bound only forces $\liminf_t K_a\,\mathbb E\, N_a(t)/\log t \ge x$; can a learner of $M_0$
  have both $\limsup = x^2$ and $\liminf = x$?
- **D7. Batched best-arm identification** on imposed grids: non-Gaussian rewards, upper bounds in
  expectation.
- **D8. Verification of [paper] results**: see F5.
- **D9. All rounds in $M_1$** — *proposed by an agent; reframing of D6 from $M_0$ to $M_1$,
  pending owner decision: not open for papers.* Fix $K \ge 2$ and $x \in (1, \infty)$. Is there a
  learner of $M_1$ (it may depend on $K$ and $x$) such that, on every grid with $x_\ell \to x$ and
  every instance of $\mathcal P$: (1) it is consistent at batch ends; (2)
  $\lim_\ell K_a\, \mathbb E N_a(t_\ell)/L_\ell = x^2$; (3)
  $\limsup_t K_a\, \mathbb E N_a(t)/\log t = x^2$; (4)
  $\liminf_t K_a\, \mathbb E N_a(t)/\log t = x$? Under (2), $\liminf_t \ge x$ always holds, so (4)
  asks whether this trivial bound is attained. The proposer's remarks, unverified: in $M_0$, a
  diagonal construction of the grid (ending a batch where the expected count is low) seems to make
  (2) and (4) incompatible, which is why the question is posed in $M_1$; in $M_1$, playing HY's pulls
  of each batch with the leader first and the other arms last is a possible route to "yes"; a
  change of measure at a mid-batch horizon gives nothing beyond $\liminf_t \ge x$. Proposed by
  Claude Opus 5.5 on 2026-11-13 as question Q001 (v1, file
  `programmes/BatchedBandits/questions/Q001-m1-all-rounds-liminf.md` in the git history).

## What would be an important result

- Matching bounds that close one of the directions above.
- An algorithm that is optimal and practical (explicit, moderate constants; simulations are a
  supplement, never a substitute).
- A formal refutation of a natural conjecture, for example that a simple algorithm is optimal.

Not important on their own: rederiving known bounds with worse constants; generalising a lemma
that nothing uses.

## Out of scope

Grids chosen by the learner (except as a point of comparison), minimax $\sqrt T$-type results,
adversarial, contextual and linear bandits, reinforcement learning. They may become roadmaps of
their own.

## Acceptance criteria for papers

Besides AGENTS.md §5, the referees check that a paper of this roadmap:

1. states, in its Main result, its information model, its class of instances and grids, and its
   criterion (batch ends or all rounds; $\limsup$ or $\liminf$; counts or regret);
2. names, in Closest known, the known results and KNOWN entries it extends, and shows why it is not
   a corollary of them;
3. exhibits, in Sanity checks, one grid and one instance that satisfy all its hypotheses at once,
   and checks the cases $x = 1$ (or $x_\ell \to 1$), $K = 2$ and Bernoulli rewards against the
   bounds $1/K_a$ and $x^2/K_a$;
4. for a lower bound, makes the class of learners explicit (consistency notion, information model,
   what the learner knows of the grid);
5. for an upper bound, defines the algorithm completely by its formula (parameters, tie rules,
   initialisation) and checks that it belongs to the information model claimed;
6. gives the first-order constant explicitly, and says whether the second-order terms are explicit
   or existential;
7. never defines "optimal": optimality is a corollary pairing a lower and an upper bound in one
   class;
8. serving a direction, is not one of the "not important on their own" results above.

## Appendix A. The algorithm HY and the statements to reach

Source: A. Prevost, *Batched bandits on an unknown imposed grid: the optimal constant x²/K_inf for
every x ≥ 1* (manuscript, 2026), whose statements are verified in the owner's private Lean project
(`Bandits/Batch/PaperHY/`, without `sorry`, remainders existential). Everything here uses the
conventions above, with $d_a := K_{\inf}(\nu_a, m^\star)$.

### Statements

On every grid with $x_\ell \to x \in [1, \infty)$, every $\nu$ with rewards in $[0,1]$ and
$m^\star < 1$, every suboptimal arm $a$:

1. **Lower bound, "explore two batches ahead".** Every batched learner that is consistent at batch
   ends, even one that knows the grid, has
   - if $x = 1$: $\liminf_\ell \mathbb E N_a(t_\ell)/L_\ell \ge 1/d_a$ (this holds on every grid);
   - if $x > 1$: $\limsup_\ell \mathbb E N_a(t_\ell)/L_\ell \ge x^2/d_a$, and the same with
     $\liminf$ if $\mathbb E N_a(t_\ell) = O(L_\ell)$;
   - for the regret: $\liminf_\ell \mathrm{Reg}(t_\ell)/L_\ell \ge x^2 \sum_{c:\Delta_c>0} \Delta_c / K_{\inf}(\nu_c, m^\star)$
     when $x = 1$, or when $x > 1$ and every suboptimal count is $O(L_\ell)$.
2. **Upper bound.** HY with its default parameters (below) is a deterministic learner of $M_0$,
   consistent, with $\lim_\ell \mathbb E N_a(t_\ell)/L_\ell = x^2/d_a$ and the matching regret limit.
   Non-asymptotic forms: for $x = 1$,
   $\mathbb E N_a(t_L) \le L_L/d_a + (2/d_a + 4c^\star/d_a^2)\,\varepsilon L_L + R_1(\varepsilon)$
   for every $\varepsilon \in (0, \varepsilon_0]$ and every $L$, with $c^\star := (2-m^\star)/(1-m^\star)$;
   for $x > 1$, with a constant margin $\omega$,
   $\mathbb E N_a(t_\ell) \le (1+\omega)(1/d_a + 3c^\star\varepsilon/d_a^2)\,H_\ell + R_x(\varepsilon)$
   where $H_\ell := \max_{k \le \ell} y_{k-1} L_k$ and $H_\ell/L_\ell \to x^2$. The remainders do
   not depend on $L$ or $\ell$ and are astronomically large.
3. **All rounds.** HY also has $\lim_t \mathbb E N_a(t)/\log t = x^2/d_a$ over all rounds.

### HY$(w_0, \beta, \omega, \vartheta, \gamma)$

Parameters: pseudo-count $w_0 \ge 0$, net exponent $\beta \ge 2$, non-increasing margins
$\omega_\ell \in (0,1]$, activation exponents $\vartheta_\ell \in (0,1]$, consistency margins
$\gamma_\ell \in (0, 1/2]$, all functions of $t_1, \dots, t_\ell$.
Defaults: $w_0 := 1$, $\beta := 2$, $\omega_\ell := 2^{-k_\ell}$ with
$k_\ell := \lfloor \frac14 \log_2 \max(L_\ell, 1) \rfloor$, $\vartheta_\ell := 1/\log\log t_\ell$
if $t_\ell \ge e^e$ and $1$ otherwise, $\gamma_\ell := \min(1/2, \max(L_\ell,1)^{-1/4})$.

Batch 1 pulls the arms in turn. At each batch end $t_\ell$, with $N_c := N_c(t_\ell)$:

- $y_\ell := x_\ell^2$, $U_{\ell+1} := \lceil L_\ell^\beta \rceil$ ($U_1 := 1$, $y_0 := 1$),
  $s_\ell := \lfloor t_\ell^{1+\vartheta_\ell} \rfloor$.
- **Pseudo-observation.** $\tilde\nu_c := (N_c \hat\nu_c + w_0 \delta_0)/(N_c + w_0)$, with mean
  $\tilde m_c$.
- **Leader and IMED divergences.** $\hat c_\ell \in \arg\max_c \tilde m_c$ (fixed tie rule),
  $\tilde K_\ell(c) := K_{\inf}(\tilde\nu_c, \tilde m_{\hat c_\ell})$.
- **Test divergences.** Well-sampled arms $W_\ell := \lbrace c : N_c \ge U_\ell/2\rbrace$; reference
  $r_\ell \in \arg\max_{c \in W_\ell} \tilde m_c$ ($\hat c_\ell$ if $W_\ell = \emptyset$); test level
  $\hat\mu_\ell := \tilde m_{r_\ell}$; $\hat K_\ell(c) := K_{\inf}(\tilde\nu_c, \hat\mu_\ell)$.

In batch $\ell+1$, at round $t$ (the learner knows $t$, not $t_{\ell+1}$):

- **IMED phase, $t \le s_\ell$.** Pull a minimiser of
  $N_c(t-1)\tilde K_\ell(c) + y_\ell \log N_c(t-1)$, the leader if it is one.
- **Paced phase, $t > s_\ell$**, using only data up to $t_\ell$:
  - consistency threshold: $\hat\Lambda_1 := L_1$; for $\ell \ge 2$, with
    $Q_\ell := \lbrace c \notin W_\ell : c \ne \hat c_{\ell-1}\rbrace$,
    $\hat\Lambda_\ell := \min\big(L_\ell, \min_{c \in Q_\ell}[N_c \hat K_{\ell-1}(c)/y_{\ell-1} + \log N_c]\big)$,
    and $h_\ell := (1-\gamma_\ell)\, y_{\ell-1} \hat\Lambda_\ell$;
  - verdicts: $c \ne \hat c_\ell$ is *rejected* if $\hat K_\ell(c) > 0$ and $N_c \hat K_\ell(c) \ge h_\ell$,
    *ambiguous* otherwise;
  - paced targets: $n_{\ell,c}(t) := K - 1 + U_{\ell+1}$ if ambiguous, and
    $K - 1 + \min(U_{\ell+1}, \lceil (1+\omega_\ell) y_\ell \log t / \hat K_\ell(c) \rceil)$ if rejected;
  - rule: pull the first $c \ne \hat c_\ell$ (fixed order) with $N_c(t-1) < n_{\ell,c}(t)$, else the
    leader.

Each test costs $K$ evaluations of $K_{\inf}$ (one-dimensional concave maximisations); each round
$O(K)$ operations. $K_{\inf}$ is used through its dual form
$K_{\inf}(G,\mu) = \sup_{\lambda \in [0, 1/(1-\mu))} \mathbb E_G \log(1 - \lambda(X-\mu))$
(Honda–Takemura 2010).

## Appendix B. Proof routes

**Lower bound.** For $x = 1$, the classical change of measure (Lai–Robbins; Garivier–Ménard–Stoltz
2019, fundamental inequality) applied to the observations available at the end of batch
$\ell + 1$: they contain the actions of batch $\ell+1$ but only the rewards of batches $\le \ell$, so
$N_a(t_\ell)$ must pay for the horizon $t_{\ell+1}$. For $x > 1$, a sharper change of measure tilts
only the rewards of $a$ in batch $\ell$ towards a distribution $G$ of mean exactly $m^\star$ with
$\mathrm{KL}(\nu_a, G) \approx d_a$ ("boundary tilt"). The instances where $\nu_a$ is replaced by
$(1-s)G + s\delta_0$ (barely suboptimal) or $(1-s)G + s\delta_1$ (barely optimal) explain these
histories equally well; giving or not giving the bulk of batch $\ell+1$ to $a$ is a polynomial loss
under one of them, so consistency forces $N_a(t_{\ell-1}) d_a \gtrsim L_{\ell+1}$, that is
$N_a(t_\ell) \gtrsim L_{\ell+2}/d_a \approx x^2 L_\ell/d_a$. The mechanism is Lorden's (1983,
proof of Theorem 3). Logarithmic counts are used for the tightness of the number of pulls of $a$
in batch $\ell$, which is decided at $t_{\ell-1}$.

**Upper bound, $x > 1$.** Decompose $N_a(t)$ over batches. (i) Structure: a queue lemma shows every
demand is served after an initial burst $O(K U_{\ell+1})$; an arm not well sampled at $t_{\ell+1}$
was rejected at $t_\ell$; from some rank the threshold is deterministic ($\hat\Lambda_\ell = L_\ell$).
(ii) Leader: a suboptimal leader requires an optimal arm rejected at the previous test against a
level below the second mean plus $\varepsilon$, or a poorly sampled suboptimal arm above
$m^\star - 3\varepsilon$; both have probability $\lesssim t_{\ell+1}^{-(1+\eta)}$ thanks to a strict
gain $\eta > 0$ in the deviation inequalities of $nK_{\inf}$. (iii) Good batches: the plan evaluated
at the actual end aims above the present threshold, so $a$ is planned at
$(1+\omega) y_\ell \log t / d_a$ up to $\varepsilon$; other mistakes cost a polylogarithmic net,
summed by a layer-cake argument.

**Upper bound, $x = 1$: the water level.** A batch of IMED rounds satisfies a deterministic
property: every arm pulled in it had, at the start, a logarithmic count below the final water level
of the batch. With $x_\ell \to 1$ this gives many "high" batches whose leaders have $t^{1-\delta}$
observations; a chain argument shows that an arm with few observations was explored at level
$\approx \log t_j$ in each high batch. HY keeps this property because an activated batch first runs
$\approx t_\ell^{1+\vartheta_\ell}$ IMED rounds, whose most-pulled arm certifies a water level above
$\log t_\ell$.

**Consistency threshold.** An ambiguous arm costs a net $\approx L_\ell^\beta$. If $a \in Q_\ell$, then
$N_a \hat K_{\ell-1}(a) \ge y_{\ell-1}(\hat\Lambda_\ell - \log N_a)$ by definition, and $a$ is rejected
as soon as $\hat K_\ell(a) \ge (1 - \gamma_\ell/2)\hat K_{\ell-1}(a)$, which fails with probability
$e^{-c\sqrt{L_\ell}/\log^2 L_\ell}$; activated batches are sparse on the logarithmic scale, so the
nets are summable.
