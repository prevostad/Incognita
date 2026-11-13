# Q001: All rounds in $M_1$: can the in-batch dip reach $x/K_a$ while staying optimal at batch ends?

| | |
|---|---|
| Programme | BatchedBandits |
| Status | proposed |
| Proposed by | Claude Opus 5.5 (`claude-opus-5-5`), 2026-11-13 |
| Reviewer verdict | |
| Owner decision required | yes (calibration phase; the owner sets it to "no" when delegating) |
| Owner decision | |
| Frozen statement | `Statements/BatchedBandits/Q001.lean` (set at validation) |
| Research rounds | 0 |
| Rounds without progress | 0 |

## Question

Conventions are those of [PROGRAMME.md](../PROGRAMME.md), with no change.

- **Instances.** $\mathcal V_K$: $K \ge 2$ arms, $\nu_a$ a probability measure on $[0,1]$, $m^\star < 1$.
  For a suboptimal arm $a$, $K_a := \mathcal K_{\inf}(\nu_a, m^\star) \in (0, \infty)$.
- **Grids.** For $x \in (1, \infty)$, $\mathcal G_x$: integer batch sizes $B_\ell \ge 1$ with
  $B_1 \ge \max(2, K)$, and $x_\ell = L_\ell / L_{\ell-1} \to x$.
- **Information model $M_1$.** At a round $t$ of batch $\ell + 1$, the arm pulled is measurable with
  respect to $t_1, \dots, t_{\ell+1}$, $t$, the observations up to $t_\ell$ and internal
  randomisation (the learner knows the end of the current batch, not later ones).
- **Criterion.** All rounds, $\liminf_{t \to \infty}$ (and $\limsup$) of $K_a\, \mathbb E\, N_a(t)/\log t$, for a
  learner that is also optimal at batch ends.

**Question.** Fix $K \ge 2$ and $x \in (1, \infty)$. Does there exist a learner $\pi$ of $M_1$ (it
may depend on $K$ and $x$, see below) such that, for every grid in $\mathcal G_x$ and every $\nu \in \mathcal V_K$:

1. $\pi$ is consistent at batch ends: $\mathbb E\, N_c(t_\ell) = o(t_\ell^\alpha)$ for every $\alpha > 0$ and every
   suboptimal $c$;
2. for every suboptimal $a$, $\lim_\ell K_a\, \mathbb E\, N_a(t_\ell) / L_\ell = x^2$;
3. for every suboptimal $a$, $\limsup_{t} K_a\, \mathbb E\, N_a(t) / \log t = x^2$;
4. for every suboptimal $a$, $\liminf_{t} K_a\, \mathbb E\, N_a(t) / \log t = x$?

Under 2, $\liminf_t \ge x$ always holds: for $t_\ell < t \le t_{\ell+1}$,
$\mathbb E\, N_a(t) \ge \mathbb E\, N_a(t_\ell)$ and $\log t \le L_{\ell+1} = (x + o(1)) L_\ell$. So item 4 asks
whether the trivial bound is attained. "No" is a possible answer: it would mean that in $M_1$, too,
optimality at batch ends forces a strictly positive gap above $x$ inside batches.

**Why $\pi$ may depend on $x$.** Direction 6 does not say whether the learner knows $x$, and HY
does not need to. Letting $\pi$ depend on $x$ is a deliberate choice, for two reasons.

- **For "no".** The answer becomes the strongest lower bound: no learner of $M_1$ has 1–4, not
  even one that is told $x$.
- **For "yes".** It isolates the in-batch timing from the estimation of $x$. During batch $\ell+1$,
  a learner of $M_1$ knows $L_{\ell+1}$. But the batch-end target
  $N_a(t_{\ell+1}) \approx x^2 L_{\ell+1}/K_a$ anticipates $L_{\ell+3}$, which it does not know.
  It must predict $x_{\ell+2} x_{\ell+3}$, either by $x^2$ if it knows $x$, or by an estimate such
  as $x_{\ell+1}^2$, the way HY uses $y_\ell = x_\ell^2$. Since $x_\ell \to x$, the estimate is
  expected to suffice at first order, but this is not checked.

So a "yes" with an $x$-dependent learner is a priori weaker than the uniform statement, which is
variant (c) below. Variant (c) is the literal $M_1$ analogue of direction 6.

## Relation to known results

- It extends the owner's **[Lean]** results for $x_\ell \to x > 1$ (programme, "What is known";
  [HY.md](../HY.md), items 1–3). The lower bound makes item 2 optimal among consistent learners.
  HY is a learner of $M_0 \subset M_1$ that satisfies 1–3, but its all-rounds limit is
  $\lim_t = x^2/K_a$ (HY.md item 3), so HY has $\liminf_t = x^2 \ne x$. HY does not answer the question.
- It is the $M_1$ case of open direction 6 ("can a learner have both $\limsup = x^2$ and
  $\liminf = x$?"), and it bears on direction 1 (a price for not knowing the grid).
- **Why not a corollary.** The catalogue (`catalogue/results.toml`) has no result yet. Among the
  programme's known results, the lower bounds give only $\liminf_t \ge x$ (see above). The upper
  bounds concern HY, whose $\liminf_t$ is $x^2$. A positive answer needs a learner that
  *delays* the pulls of suboptimal arms to the end of each batch, and a proof that this delay costs
  nothing at batch ends and leaves no mass in expectation mid-batch. No stated result gives this.
  A negative answer needs a lower bound inside batches that the known change-of-measure arguments
  do not give.
- **Why $M_1$ and not $M_0$ (remark: proposer's sketch, unverified, not a result, not a claim
  about direction 6).** The proposer believes, but has not checked, that in $M_0$ items 2 and 4
  cannot hold together on every grid of $\mathcal G_x$. The idea is a short diagonal argument.
  In $M_0$ the law of the actions up to a round $t$ of batch $\ell+1$ does not depend on
  $t_{\ell+1}$, provided $t \le t_{\ell+1}$. Fix a learner, $\nu$ and a suboptimal $a$, and build
  a grid $G^\star$ batch by batch:
  1. Start at a level $k_0$ with $x - 1/k_0 > 1$, and set $k = k_0$.
  2. After $t_\ell$, look for a round $t > t_\ell$ with $\log t / L_\ell \in [x - 1/k, x + 1/k]$
     and $K_a \mathbb E N_a(t)/\log t \le x + 1/k$. If there is one, end the batch at the first
     such round ("trap", $t_{\ell+1} := t$) and set $k := k + 1$.
  3. Otherwise set $t_{\ell+1} := \lceil t_\ell^x \rceil$.

  Then $G^\star \in \mathcal G_x$. If there are infinitely many traps, every trap end
  $t_{\ell+1}$ has $K_a \mathbb E N_a(t_{\ell+1})/L_{\ell+1} \le x + 1/k$, which contradicts
  item 2 directly, since $x < x^2$. If there are finitely many, let $k_1$ be the final level.
  From some batch on, every round $t$ of batch $\ell+1$ either lies in the window (so its ratio is
  $> x + 1/k_1$) or has $\log t < (x - 1/k_1) L_\ell$. In the second case, item 2 gives the ratio
  $\ge (x^2 - o(1))/(x - 1/k_1)$, which is eventually $> x + 1/k_1$ because $x^2 > x^2 - 1/k_1^2$.
  This contradicts item 4. In $M_1$ the trap fails: the learner knows $t_{\ell+1}$ and can keep
  $N_a$ at its batch-start level until the last $O(L_\ell)$ rounds of the batch. This is why the
  question is posed in $M_1$. The remark does not settle direction 6, which is the owner's. It
  needs an independent check, and if it is worth pursuing it should be a separate $M_0$
  question.
- **Possible route for "yes" (proposer's guess).** In $M_1$, at $t_\ell$ the learner knows
  $t_{\ell+1}$. So it can compute the whole multiset of HY's batch-$(\ell+1)$ pulls, which is
  determined by the data up to $t_\ell$ and by $t_{\ell+1}$. It can then play the leader's pulls
  first and the other arms' pulls last. Under the reward-table model, the batch-end data have the
  same law as for HY, so items 1–2 carry over. Item 4 then needs control, in expectation, of the
  event that HY's non-leader pulls in a batch are polynomially many (IMED phase, suboptimal
  leader). HY's stated bounds do not give this control, so it would come from HY's proof or from a
  new, simpler $M_1$ learner. HY's upper bound is "on hold" for porting (programme, known result
  4). A researcher may therefore prefer a direct $M_1$ learner that sets its targets at
  $\log t_{\ell+1}$ directly.
- **Literature.** The published batched-bandit work named in the programme lets the learner
  choose the grid: [PRCS16] (to be checked) and [GHRZ19] (to be checked). So does the anytime work
  on asymptotic optimality with few batches: [JTXHXG21] (to be checked) and [KO21a] (to be
  checked). [KO21b] (to be checked) seems to treat given batch sizes that grow subexponentially,
  which is closer to the regime $x_\ell \to 1$ than to $x > 1$. These three are known only from
  search-result snippets. They have not been read, and their metadata is unchecked. Web searches
  on 2026-11-13 (Claude Opus 5.5) found no work on imposed grids with all-rounds asymptotic
  constants, or with information models $M_k$. The queries were:
  - "batched bandits fixed imposed grid asymptotic regret all rounds lower bound batch ends unknown
    to learner";
  - "bandit delayed feedback batches imposed by environment unknown batch sizes asymptotically
    optimal Lai-Robbins constant".

  A negative search is weak evidence. The answer is not known to the proposer.

## Joint satisfiability

- **Grid and instance.** Take $x = 2$, $t_\ell := \lceil \exp(2^\ell) \rceil$ for $\ell \ge 1$, so
  $t_1 = 8 \ge \max(2, K)$ and $B_\ell \ge 1$. Also $L_\ell \in [2^\ell, 2^\ell + e^{-2^\ell}]$, so
  $x_\ell \to 2$. Take $K = 2$ with $\nu_1 = \mathrm{Ber}(1/2)$ and $\nu_2 = \mathrm{Ber}(1/4)$, so
  $m^\star = 1/2 < 1$.
- **$K_2$ is finite and positive.** It is finite because
  $\nu' = \tfrac12 \nu_2 + \tfrac12 \delta_1$ has mean $5/8 > 1/2$ and
  $\mathrm{KL}(\nu_2, \nu') \le \log 2$. It is positive because KL is weakly lower semicontinuous,
  the set of laws on $[0,1]$ with mean $\ge 1/2$ is weakly compact, and that set does not contain
  $\nu_2$.
- **Items 1–3 are satisfiable together.** HY, a learner of $M_0 \subset M_1$, satisfies items 1–3
  on this grid and instance (owner's **[Lean]** result, HY.md items 2–3).
- **What the question asks.** Only whether item 4 can be added. The question is therefore not
  vacuous in the "yes" direction for 1–3, and a "no" answer is a real lower bound.

## Natural fallback

If the answer is "no", or a full proof is out of reach, the fallbacks are, in order:

1. **Approximate dip.** For every $\eta > 0$, a learner $\pi_\eta$ of $M_1$ satisfying 1–3 and
   $\liminf_t K_a \mathbb E N_a(t)/\log t \le x + \eta$. This is an "original still open" variant.
2. **Matching lower bound for "no".** A constant $c(x) > 0$ with the following property. For every
   learner of $M_1$ that satisfies 1–2 on every grid of $\mathcal G_x$ and every
   $\nu \in \mathcal V_K$, there are a grid in $\mathcal G_x$, an instance $\nu \in \mathcal V_K$
   and a suboptimal arm $a$ with $\liminf_t K_a \mathbb E N_a(t)/\log t \ge x + c(x)$.
3. **Variant (a): $M_2$.** The same question in $M_2$.
4. **Variant (b): upper halves only.** A learner of $M_1$ with item 1, $\limsup_\ell K_a \mathbb E
   N_a(t_\ell)/L_\ell \le x^2$, $\limsup_t K_a \mathbb E N_a(t)/\log t \le x^2$ and
   $\liminf_t K_a \mathbb E N_a(t)/\log t \le x$. Here item 2 is only an upper bound, so the
   argument "$\liminf_t \ge x$" above no longer applies, and item 4 must be read as "$\le x$". It
   is not a weaker question in substance: the second condition gives $\mathbb E N_a(t_\ell) =
   O(L_\ell)$, so the owner's **[Lean]** lower bound in its $\liminf$ form (HY.md item 1) gives
   $\liminf_\ell \ge x^2$, and then items 2–4 hold with equality. Variant (b) is the main
   question with the lower-bound halves left to that result. Its use is that a Lean proof of it
   does not need the lower bound to be ported first (programme, known result 4, on hold).

**Stronger variant (c): uniform learner.** One learner of $M_1$, depending on $K$ only, that
satisfies 1–4 for every $x \in (1, \infty)$, every grid of $\mathcal G_x$ and every
$\nu \in \mathcal V_K$. A "yes" to (c) implies a "yes" to the question, and a "no" to the
question implies a "no" to (c).

## Dead ends

None yet.

## Outcome

