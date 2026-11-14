# Q002: Is plain batched IMED with exponent $x_\ell^2$ already optimal when $x > 1$?

| | |
|---|---|
| Programme | BatchedBandits |
| Status | proposed |
| Proposed by | Claude Opus 5.5 (`claude-opus-5-5`), 2026-11-13 |
| Reviewer verdict | |
| Owner decision required | yes (calibration phase; the owner sets it to "no" when delegating) |
| Owner decision | |
| Frozen statement | `Statements/BatchedBandits/Q002.lean` (set at validation) |
| Research rounds | 0 |
| Rounds without progress | 0 |

## Question

Conventions are those of [PROGRAMME.md](../PROGRAMME.md). Rounds and batches are numbered from 1
here. The frozen statement translates them to the 0-based Lean rounds that the first definition
pull request fixes.

**The learner IMED-$y$.** IMED-$y$ is HY's IMED phase ([HY.md](../HY.md)) used for every round,
that is HY with $s_\ell := +\infty$. It has no paced phase, no tests, no nets, no margins and no
activation. Fix a linear order on the $K$ arms. Ties are always broken by this order.

- **Batch 1.** At round $t \le t_1$, pull the arm of rank $((t-1) \bmod K) + 1$. Since
  $B_1 \ge K$, every arm has $N_c(t_1) \ge 1$.
- **At each batch end $t_\ell$**, with $N_c := N_c(t_\ell)$ and $\hat\nu_c$ the empirical
  distribution of the $N_c$ rewards of $c$:
  - $\tilde\nu_c := (N_c\,\hat\nu_c + \delta_0)/(N_c + 1)$ (one pseudo-observation at $0$, so
    $w_0 = 1$), with mean $\tilde m_c < 1$;
  - the leader $\hat c_\ell$ is the first arm, in the fixed order, that maximises $\tilde m_c$;
  - $\tilde K_\ell(c) := \mathcal K_{\inf}(\tilde\nu_c, \tilde m_{\hat c_\ell}) \in [0,\infty)$, which is $0$ for $c = \hat c_\ell$;
  - $y_\ell := x_\ell^2$, so $y_1 = 1$.
- **During batch $\ell+1$**, at round $t \in (t_\ell, t_{\ell+1}]$: pull a minimiser of
  $I_c(t) := N_c(t-1)\,\tilde K_\ell(c) + y_\ell \log N_c(t-1)$. Among minimisers, take the leader
  if it is one, and otherwise the first one in the fixed order.

IMED-$y$ is deterministic. Its actions in batch $\ell+1$ depend only on
$t_1, \dots, t_\ell$, the current round and the rewards up to $t_\ell$, so it is a learner of
$M_0$. It needs no parameter, and each round costs $O(K)$ operations plus $K$ evaluations of
$\mathcal K_{\inf}$ per batch.

**Class.** Fix $x \in (1, \infty)$. The grids are those of the programme with
$x_\ell \to x$. The instances are those of the programme: $K \ge 2$ arms, laws on $[0,1]$,
$m^\star < 1$. For a suboptimal arm $a$, $K_a := \mathcal K_{\inf}(\nu_a, m^\star)$.

**Criterion.** Counts at batch ends, along $\ell$.

**Question.** Is it true that, for every $x \in (1,\infty)$, every grid with $x_\ell \to x$, every
instance and every suboptimal arm $a$:

1. (consistency at batch ends) $\mathbb E\, N_a(t_\ell) = o(t_\ell^\alpha)$ for every $\alpha > 0$;
2. (optimality) $\lim_{\ell} K_a\, \mathbb E\, N_a(t_\ell) / L_\ell = x^2$?

Given 1, only the upper half of 2,
$\limsup_\ell K_a\,\mathbb E N_a(t_\ell)/L_\ell \le x^2$, is new. It gives
$\mathbb E N_a(t_\ell) = O(L_\ell)$. The owner's **[Lean]** lower bound in its $\liminf$ form
([HY.md](../HY.md), item 1, for learners consistent at batch ends in any information model) then
gives $\liminf_\ell \ge x^2$. Once that lower bound is ported, the frozen statement may therefore
be the conjunction of 1 and the upper half of 2. If it is frozen before the port, it must state
2 in full.

"No" is a possible answer, and a likely one if HY's paced phase is there for a reason. A "no"
means that some grid with $x_\ell \to x > 1$, some instance and some suboptimal arm make IMED-$y$
either inconsistent at batch ends, or give it $\limsup_\ell K_a\,\mathbb E N_a(t_\ell)/L_\ell > x^2$.

## Relation to known results

- **What it extends.** The owner's **[Lean]** results (programme, "What is known";
  [HY.md](../HY.md), items 1–2). First, IMED with frozen statistics and exponent $1$ is optimal
  when $x_\ell \to 1$. Second, for $x_\ell \to x > 1$, the lower bound is $x^2$ and HY attains it,
  but HY's second-order terms are astronomical. IMED-$y$ is the obvious "simple" candidate between
  the two. It is frozen IMED with the exponent $1$ replaced by the plug-in prediction $x_\ell^2$ of
  $L_{\ell+2}/L_\ell$. The question is open direction 1 (practical optimality for $x>1$) for that
  candidate. Both answers fall under the programme's "What would be an important result":
  - "yes" gives an optimal algorithm that is also practical. It has no parameter and no
    polylogarithmic nets, and its second-order terms are a natural target for direction 2;
  - "no" is the formal refutation of a natural conjecture that the programme cites as an example
    ("a simple algorithm is optimal").
- **Why exponent $1$ is not a candidate (remark).** Suppose frozen IMED with $y_\ell \equiv 1$
  were consistent on a grid with $x > 1$, with counts $\approx L_\ell/K_a$. Then the **[Lean]**
  lower bound would be violated. So on such grids it is either inconsistent or not
  $O(L_\ell)$-optimal. The exponent must therefore grow, and $x_\ell^2$ is the plug-in choice.
- **Why it is not a corollary.** The catalogue (`catalogue/results.toml`) has no result yet. None
  of the programme's known results covers IMED-$y$:
  - the $x_\ell \to 1$ result is about exponent $1$;
  - HY's upper bound is about HY. In batch $\ell+1$, HY first runs its IMED phase, the rounds
    $t_\ell < t \le s_\ell$, where $s_\ell = \lfloor t_\ell^{1+\vartheta_\ell}\rfloor$ is a round
    index. That phase is exactly IMED-$y$, and it has no cap. On a grid with $x > 1$, every late
    batch also has a paced phase: $t_{\ell+1} > s_\ell$ eventually, since
    $L_{\ell+1}/L_\ell \to x > 1$ and $\vartheta_\ell \to 0$. The paced phase, the rounds
    $s_\ell < t \le t_{\ell+1}$, differs from IMED-$y$ in three ways:
    1. it tests against a reference level computed from well-sampled arms, not against the leader's
       mean;
    2. it pulls a non-leader $c$ only while its *cumulative* count satisfies
       $N_c(t-1) < n_{\ell,c}(t) \le K - 1 + U_{\ell+1}$, with $U_{\ell+1} = \lceil L_\ell^\beta\rceil$.
       This cap bounds the total count, not the pulls per batch, and applies only in the paced
       phase. The leader is never capped;
    3. its targets $n_{\ell,c}(t)$ are also floors. An "ambiguous" arm is brought up to the net
       $K-1+U_{\ell+1}$, and the targets of rejected arms are inflated by $1+\omega_\ell$.

  So the difference lies in the length of the uncapped phase. Take a non-leader whose frozen
  $\tilde K_\ell$ is close to $0$. Under IMED-$y$ it can receive a constant fraction of batch
  $\ell+1$, that is $\asymp t_{\ell+1}$ pulls. Under HY it can also be pulled at every round of
  the IMED phase. In the paced phase it is pulled only while its cumulative count is below
  $K-1+U_{\ell+1}$. So it receives at most $s_\ell - t_\ell + K - 1 + U_{\ell+1}$ pulls in batch
  $\ell+1$, which is $t_{\ell+1}^{1/x + o(1)}$, polynomially fewer than $t_{\ell+1}$. Neither HY's
  statement nor the lower bound says whether these events are rare enough for IMED-$y$.
- **Where a "no" could come from (proposer's heuristics, unverified).** A suboptimal leader at
  $t_\ell$ costs the whole batch $\ell+1$, about $t_{\ell+1}$ pulls, and so does a near-tie under
  IMED-$y$. For an arm $a$ with $n$ rewards, the probability that its empirical mean exceeds
  $m^\star$ is governed by the Cramér rate
  $\Lambda^\star_a(m^\star) = \inf\{\mathrm{KL}(Q, \nu_a) : \text{mean } Q \ge m^\star\}$. This is
  the reverse divergence, not $K_a$. For $\nu_a = \mathrm{Ber}(1/2)$ and $m^\star = 0.99$, it gives
  $\Lambda^\star_a \approx 0.64$ against $K_a \approx 1.61$.
  - A naive estimate holds $n = x^2 L_{\ell-1}/K_a$ fixed. It predicts a flip cost
    $t_\ell^{\,1 - x\Lambda^\star_a/K_a}$, which is not $o(t_\ell^\alpha)$ when
    $x\Lambda^\star_a < K_a$.
  - That estimate is wrong as stated. Under IMED pacing, an arm whose rewards look good gets
    pulled *more*. So the event has to be computed as a large deviation of the whole trajectory of
    the arm, across batches. For $x = 2$ on the example above, a two-stage version of that
    computation makes the flip much more expensive than the naive estimate.
  - Whether the trajectory rate always beats the cost of a batch, for every $x > 1$ and every
    instance, is exactly what decides the question. It is also what HY's caps and tests may have
    been designed to avoid. The owner may already know the answer. The proposer does not.
- **Literature.** Published batched-bandit work lets the learner choose the grid: [PRCS16]
  (to be checked) and [GHRZ19] (to be checked). IMED itself is from [HT15] (to be checked). Two
  web searches on 2026-11-13 (Claude Opus 5.5) found no analysis of IMED, or of any index policy,
  on an imposed grid with $x > 1$. The queries were "batched IMED bandit fixed batch grid
  asymptotically optimal Indexed Minimum Empirical Divergence batches" and "bandit batches
  imposed by environment unknown batch sizes asymptotic regret constant x^2 explore two batches
  ahead". The nearest hit was a search-result snippet of [KO21b] (to be checked), not read. It
  reports that batched Thompson sampling keeps its sequential asymptotics when batch sizes
  grow subexponentially. That regime is the $x = 1$ side, not this one. A negative search is weak
  evidence. The answer is not known to the proposer.

## Joint satisfiability

- **Grid.** Take $x = 2$ and $t_\ell := 2^{2^\ell}$. Then $t_1 = 4 \ge \max(2, K)$ for $K = 2$,
  $B_\ell \ge 1$, $L_\ell = 2^\ell \log 2$, and $x_\ell = 2$ for every $\ell \ge 2$, so $x_\ell \to 2$.
- **Instance.** Take $K = 2$, $\nu_1 = \mathrm{Ber}(3/4)$ and $\nu_2 = \mathrm{Ber}(1/2)$, so
  $m^\star = 3/4 < 1$.
- **$K_2$ is finite and positive.** $K_2 = \mathrm{kl}(1/2, 3/4) = \tfrac12\log(4/3) \approx 0.144$.
  - The infimum defining $\mathcal K_{\inf}(\mathrm{Ber}(1/2), 3/4)$ is approached by Bernoulli
    laws.
  - The reason: any $\nu'$ with finite divergence charges $0$ and $1$. Moving the mass that
    $\nu'$ puts on $(0,1)$ to $1$ raises the mean and lowers the divergence.
- **IMED-$y$ is well defined on this pair.** It is defined at every round:
  - $N_c(t-1) \ge 1$ after batch 1;
  - $\tilde m_c < 1$, so every $\tilde K_\ell(c)$ is finite.
- **The conclusions are not contradictory.** HY satisfies 1–2 on this grid and instance (owner's
  **[Lean]** result). The question is only whether IMED-$y$ does too. On this example, a "yes"
  predicts $\mathbb E N_2(t_\ell) \sim 4 L_\ell / K_2$.

## Natural fallback

- **If the answer is "no".** The refutation is itself the result: a grid with $x_\ell \to x > 1$,
  an instance and an arm on which item 1 or item 2 fails. Formally, it is a proof of the negation
  of the frozen statement. The natural next target is *capped IMED-$y$*: IMED-$y$ in which a
  non-leader $c$ is not pulled in batch $\ell+1$ once $N_c(t-1) \ge K - 1 + \lceil L_\ell^2\rceil$.
  This is HY's cap $U_{\ell+1}$ with $\beta = 2$, and it gives a minimal answer to "which part of
  HY's paced phase is needed". Ask the same question for capped IMED-$y$.
- **If "yes" is out of reach.** Here are three variants, each of them weaker than the original,
  which stays open:
  - (a) item 1 alone (consistency at batch ends of IMED-$y$);
  - (b) items 1–2 for Bernoulli rewards with $K = 2$;
  - (c) items 1–2 with $y_\ell := (1+\omega_\ell)x_\ell^2$ for HY's default margins $\omega_\ell$.
- **Stronger, if "yes".** Two strengthenings would follow:
  - the same for $x = 1$ ($y_\ell \to 1$; the **[Lean]** result is for $y_\ell \equiv 1$). This
    would make IMED-$y$ a single optimal learner of $M_0$ for every convergent grid, which is the
    role HY plays now;
  - a non-asymptotic bound at batch ends with explicit remainders (direction 2).

## Proposer's check of the validation criteria

1. **Information model, class and criterion.** The information model is $M_0$ (IMED-$y$ is a
   fixed learner of $M_0$). The class is: rewards in $[0,1]$, $m^\star<1$, grids with
   $x_\ell \to x \in (1,\infty)$. The criterion is counts at batch ends, with consistency and
   $\lim$.
2. **Known result and not a corollary.** It extends the **[Lean]** results above. It is not a
   corollary: the catalogue is empty, and HY's statement does not cover IMED-$y$ (see above). The
   proposer tried a short proof and a short refutation, and neither went through: the flip
   estimate above is inconclusive.
3. **Joint satisfiability.** One grid and one instance are given above.
4. **Class of learners for a lower bound.** The question is about one explicit learner, so this
   criterion does not apply. The lower half of item 2 uses the **[Lean]** lower bound, whose class
   is the learners consistent at batch ends, in every information model.
5. **"No" allowed, fallback named.** "No" is allowed, and the fallbacks are named above.

## Dead ends

None yet.

## Outcome

