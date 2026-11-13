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

Conventions are those of [PROGRAMME.md](../PROGRAMME.md), except that the learner $\pi$ may
depend on $K$ and $x$ (see "Why $\pi$ may depend on $x$" below).

- **Instances.** $\mathcal V_K$: $K \ge 2$ arms, $\nu_a$ a probability measure on $[0,1]$, $m^\star < 1$.
  For a suboptimal arm $a$, $K_a := \mathcal K_{\inf}(\nu_a, m^\star) \in (0, \infty)$.
- **Grids.** For $x \in (1, \infty)$, $\mathcal G_x$: integer batch sizes $B_\ell \ge 1$ with
  $B_1 \ge \max(2, K)$, and $x_\ell = L_\ell / L_{\ell-1} \to x$.
- **Information model $M_1$.** At a round $t$ of batch $\ell + 1$, the arm pulled is measurable with
  respect to $t_1, \dots, t_{\ell+1}$, $t$, the observations up to $t_\ell$ and internal
  randomisation (the learner knows the end of the current batch, not later ones).
- **Criterion.** All rounds, $\liminf_{t \to \infty}$ (and $\limsup$) of $K_a\, \mathbb E\, N_a(t)/\log t$, for a
  learner that is also optimal at batch ends.
- **Indexing.** Rounds and batches are numbered from 1, as in the programme. $N_a(t)$ counts the
  pulls of $a$ in rounds $1, \dots, t$. In $\lim_t$, $\limsup_t$ and $\liminf_t$, $t$ ranges over
  the integers $t \ge 2$, so that $\log t > 0$. This does not change the limits. When the
  question is frozen, these indices are translated to the programme's 0-based Lean rounds, using
  the translation that the first definition pull request fixes. The frozen statement must say
  which round set the $\liminf_t$ ranges over.

**Question.** Fix $K \ge 2$ and $x \in (1, \infty)$. Does there exist a learner $\pi$ of $M_1$ (it
may depend on $K$ and $x$, see below) such that, for every grid in $\mathcal G_x$ and every $\nu \in \mathcal V_K$:

1. $\pi$ is consistent at batch ends: $\mathbb E\, N_c(t_\ell) = o(t_\ell^\alpha)$ for every $\alpha > 0$ and every
   suboptimal $c$;
2. for every suboptimal $a$, $\lim_\ell K_a\, \mathbb E\, N_a(t_\ell) / L_\ell = x^2$;
3. for every suboptimal $a$, $\limsup_{t} K_a\, \mathbb E\, N_a(t) / \log t = x^2$;
4. for every suboptimal $a$, $\liminf_{t} K_a\, \mathbb E\, N_a(t) / \log t = x$?

Under 2, $\liminf_t \ge x$ always holds: for $t_\ell < t \le t_{\ell+1}$,
$\mathbb E\, N_a(t) \ge \mathbb E\, N_a(t_\ell)$ and $\log t \le L_{\ell+1} = (x + o(1)) L_\ell$. So item 4 asks
whether the trivial bound is attained. Likewise, the lower half of item 3,
$\limsup_t \ge x^2$, already follows from item 2 by taking $t = t_\ell$; only its upper half is
a new condition. "No" is a possible answer: it would mean that in $M_1$, too,
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
  do not give, as the next point explains.
- **Change of measure at a mid-batch horizon (attempt, unverified).** Apply the fundamental
  inequality [GMS19, inequality (6)] at a round $t = t_{\ell+1} - c L_\ell$ of batch $\ell+1$, to
  the learner's information at $t$. That information is the observations up to $t_\ell$, the
  actions up to $t$, $t_{\ell+1}$ and $U$. In $M_1$, the actions of rounds $t_\ell+1, \dots, t$
  are functions of the rest, and none of their rewards is observed before $t_{\ell+1}$. So the
  divergence side is the same as at $t_\ell$: $\sum_c \mathbb E_\nu N_c(t_\ell)\,
  \mathrm{KL}(\nu_c, \nu'_c)$ for the plain change of measure, and only the pulls of $a$ in batch
  $\ell$ for the boundary tilt of HY.md. On the other side, take $Z = N_a(t)/t$. Under an
  alternative $\nu'$ where $a$ is the only optimal arm, consistency at $t_{\ell+1}$ forces
  $\mathbb E_{\nu'} Z \ge 1 - o(t_{\ell+1}^\alpha)/t$, while under $\nu$ consistency gives
  $\mathbb E_\nu Z \to 0$. With [GMS19, inequality (11)] applied to $1 - Z$, this gives
  $K_a\, \mathbb E_\nu N_a(t_\ell) \gtrsim \log t$, a bound on the data at $t_\ell$, and the
  boundary tilt gives at best the $x^2$ bound at $t_\ell$ again. Combined with
  $N_a(t) \ge N_a(t_\ell)$, this returns $\liminf_t \ge x$ and nothing more. The reason is
  structural. Two learners of $M_1$ that differ only by a reordering of the rounds inside each
  batch, chosen from the data up to $t_\ell$ and from $t_{\ell+1}$, have the same law of
  batch-end histories (in the reward-table model). So every bound that uses only those laws and
  consistency at batch ends holds equally for both, while their in-batch profiles differ. A "no"
  must use something else, for example the cost of rare events with polynomially many non-leader
  pulls (see the route for "yes" below).
- **Why $M_1$ and not $M_0$ (remark: proposer's sketch, unverified, not a result, not a claim
  about direction 6).** The proposer believes, but has not checked, that in $M_0$ items 2 and 4
  cannot hold together on every grid of $\mathcal G_x$. The idea is a short diagonal argument.

  *Why the construction is legitimate.* In $M_0$, the action at a round $t$ of batch $\ell+1$
  is a measurable function of $t_1, \dots, t_\ell$, $t$, the observations up to $t_\ell$ and the
  learner's internal randomisation $U$, which is independent of the rewards. By induction on
  $\ell$, the joint law of $U$, the actions up to $t$ and the observations up to $t_\ell$, for
  $t_\ell < t \le t_{\ell+1}$, is determined by the learner, $\nu$ and $t_1, \dots, t_\ell$.
  It does not depend on $t_{\ell+1}$ or later batch ends. So, for such $t$, $\mathbb E N_a(t)$ is
  a function $e_\ell(t)$ of $t_1, \dots, t_\ell$ and $t$, known before $t_{\ell+1}$ is chosen.

  Fix a learner, $\nu$ and a suboptimal $a$, and build a grid $G^\star$ batch by batch:
  1. Set $t_1 := \max(2, K)$, so $B_1 \ge \max(2, K)$ and $L_1 > 0$. Choose a level $k_0$ with
     $x - 1/k_0 > 1$ and $x + 1/k_0 < x^2$, and set $k := k_0$.
  2. Given $t_1, \dots, t_\ell$, the window is the finite set of integers $t$ with
     $\log t / L_\ell \in [x - 1/k, x + 1/k]$. Each such $t$ is $> t_\ell$, since $x - 1/k > 1$.
     If some $t$ in the window has $K_a\, e_\ell(t)/\log t \le x + 1/k$, end the batch at the
     smallest one ("trap", $t_{\ell+1} := t$) and set $k := k + 1$.
  3. Otherwise set $t_{\ell+1} := \lceil t_\ell^x \rceil$, which is $> t_\ell$ since $t_\ell \ge 2$.

  *$G^\star \in \mathcal G_x$.* Every batch is nonempty, so $t_\ell \to \infty$ and
  $L_\ell \to \infty$. A non-trap batch has
  $x \le x_{\ell+1} \le x + \log(1 + t_\ell^{-x})/L_\ell$, which tends to $x$. A trap batch has
  $|x_{\ell+1} - x| \le 1/k$, where $k$ is the level at that trap. The $n$-th trap is at level
  $k_0 + n - 1$. So, for every $\varepsilon > 0$, only finitely many traps have $1/k > \varepsilon$.
  Both kinds of batches therefore give $x_{\ell} \to x$, whether traps and non-traps interleave
  or not.

  *Contradiction.* If there are infinitely many traps, every trap end $t_{\ell+1}$ has
  $K_a \mathbb E N_a(t_{\ell+1})/L_{\ell+1} \le x + 1/k_0 < x^2$. This contradicts item 2
  directly. If there are finitely many, let $k_1$ be the final level, and take a non-trap batch
  $\ell + 1$ far enough that $L_\ell > k_1 \log 2$. Every round $t$ of that batch has
  $\log t \le x L_\ell + \log 2 < (x + 1/k_1) L_\ell$. So either it lies in the window (and its
  ratio is $> x + 1/k_1$, since there was no trap), or $\log t < (x - 1/k_1) L_\ell$. In the
  second case, $\mathbb E N_a(t) \ge \mathbb E N_a(t_\ell)$ and item 2 give a ratio
  $\ge (x^2 - o(1))/(x - 1/k_1)$. This is eventually $> x + 1/k_1$, because
  $(x + 1/k_1)(x - 1/k_1) = x^2 - 1/k_1^2 < x^2$. So $\liminf_t \ge x + 1/k_1 > x$, which
  contradicts item 4. In $M_1$ the trap fails: the learner knows $t_{\ell+1}$ and can keep
  $N_a$ at its batch-start level until the last $O(L_\ell)$ rounds of the batch. This is why the
  question is posed in $M_1$.

  *Hypotheses used.* The sketch uses items 2 and 4 as stated here, with $\lim_\ell = x^2$ at
  batch ends. It does not use the lower bound. Direction 6 asks only for $\limsup_t = x^2$ over
  all rounds (and $\liminf_t = x$). To reach item 2 from there, one more step is needed. At
  batch ends, $\limsup_t \le x^2$ gives $\limsup_\ell K_a \mathbb E N_a(t_\ell)/L_\ell \le x^2$,
  hence $\mathbb E N_a(t_\ell) = O(L_\ell)$. For a learner consistent at batch ends, the
  owner's **[Lean]** lower bound in its $\liminf$ form (HY.md item 1) then gives
  $\liminf_\ell \ge x^2$, hence $\lim_\ell = x^2$. So the sketch would apply to the $M_0$ case of
  direction 6 for consistent learners only through that lower bound.

  The remark does not settle direction 6, which is the owner's. It needs an independent check,
  and if it is worth pursuing it should be a separate $M_0$ question.
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
- **The in-batch profile item 4 needs.** A learner with 1–4 must have, for each suboptimal $a$,
  $\mathbb E N_a(t) \approx x^2 L_\ell/K_a$ for most of batch $\ell+1$, up to
  $t_{\ell+1} - O(L_\ell)$, and then a rise to $\approx x^2 L_{\ell+1}/K_a \approx x^3 L_\ell/K_a$
  at $t_{\ell+1}$. On the example, write $n_\ell := \lceil 4 L_\ell/K_2 \rceil$ and
  $m_\ell := n_{\ell+1} - n_\ell$, which is $\approx 4 \cdot 2^\ell/K_2$. Define the target
  $n(t) := n_\ell$ for $t_\ell < t \le t_{\ell+1} - m_\ell$, and $n(t) := n_\ell + (t - t_{\ell+1} +
  m_\ell)$ on the last $m_\ell$ rounds. This fits in the batch, since
  $B_{\ell+1} \ge e^{2^{\ell+1}} - e^{2^\ell} - 1 \gg m_\ell$. Since $\log(t_{\ell+1} - m_\ell) =
  L_{\ell+1} - o(1)$ and $L_{\ell+1}/L_\ell \to 2$, the ratio $K_2\, n(t)/\log t$
  - equals $4 + o(1)$ at batch ends (item 2);
  - lies in $[2 - o(1), 4]$ on the flat part, and comes within $o(1)$ of $2$ just before the
    rise (item 4);
  - is $\le K_2\, n_{\ell+1}/(L_{\ell+1} - o(1)) = 4 + o(1)$ on the rise (item 3).

  *Compatibility with the known lower bounds.* At batch ends the profile meets the
  explore-two-ahead bound with equality: $K_2\, n_\ell \approx 4 \cdot 2^\ell \approx
  L_{\ell+2}$. Inside batch $\ell+1$ the learner observes nothing new, so the only known
  constraint is $\mathbb E N_a(t) \ge \mathbb E N_a(t_\ell)$ (see "Change of measure at a
  mid-batch horizon"), which the flat part meets with equality. Placing the rise needs $t_{\ell+1}$,
  which $M_1$ provides. This shows that items 2–4 are compatible as a sequence of expected counts
  on this grid and instance. It is not a learner: a learner must reach this profile in
  expectation, from data, on every instance at once, and that is the question.

## Natural fallback

The fallbacks depend on which way the answer seems to go.

1. **If "yes" is out of reach: approximate dip.** For every $\eta > 0$, a learner $\pi_\eta$ of
   $M_1$ satisfying 1–3 and $\liminf_t K_a \mathbb E N_a(t)/\log t \le x + \eta$, on every grid
   of $\mathcal G_x$, every $\nu \in \mathcal V_K$ and every suboptimal $a$. This is an "original
   still open" variant.
2. **If the answer is "no": a quantitative gap.** A constant $c(x) > 0$ with the following
   property. For every learner of $M_1$ that satisfies 1–2 on every grid of $\mathcal G_x$ and
   every $\nu \in \mathcal V_K$, there are a grid in $\mathcal G_x$, an instance
   $\nu \in \mathcal V_K$ and a suboptimal arm $a$ with
   $\liminf_t K_a \mathbb E N_a(t)/\log t \ge x + c(x)$.
3. **Either way: variant (a), $M_2$.** The same question in $M_2$.

**How fallbacks 1 and 2 relate.** They cannot both hold. If fallback 2 holds with $c(x)$, take
$\eta < c(x)$: the learner $\pi_\eta$ of fallback 1 satisfies 1–2, so on some grid, instance and
arm its $\liminf_t$ is $\ge x + c(x) > x + \eta$, and fallback 1 fails. They are not exact
negations of each other: fallback 2 ranges over the learners that satisfy 1–2, a larger class
than the learners that satisfy 1–3. The negation of fallback 1 is fallback 2 restricted to the
learners that satisfy 1–3.

**Reformulation, not a fallback: variant (b), upper halves only.** A learner of $M_1$ with item 1,
$\limsup_\ell K_a \mathbb E N_a(t_\ell)/L_\ell \le x^2$,
$\limsup_t K_a \mathbb E N_a(t)/\log t \le x^2$ and
$\liminf_t K_a \mathbb E N_a(t)/\log t \le x$. Given the owner's **[Lean]** lower bound, (b) is
equivalent to the question, so it has the same answer and is no fallback if the answer is "no".
Indeed the second condition gives $\mathbb E N_a(t_\ell) = O(L_\ell)$, so the lower bound in its
$\liminf$ form (HY.md item 1) gives $\liminf_\ell \ge x^2$, and then items 2–4 hold with equality.
Its use is as a proof strategy for "yes": a Lean proof of (b) does not need the lower bound to be
ported first (programme, known result 4, on hold).

**Stronger variant (c): uniform learner.** One learner of $M_1$, depending on $K$ only, that
satisfies 1–4 for every $x \in (1, \infty)$, every grid of $\mathcal G_x$ and every
$\nu \in \mathcal V_K$. A "yes" to (c) implies a "yes" to the question, and a "no" to the
question implies a "no" to (c).

## Side note: direction 4 (outside this question, unverified)

Seen while writing this question, and recorded here so that it is not lost. It is not part of
Q001, and it could become a separate question. Consider forced exploration in $M_2$: by
$t_{\ell+1}$, every arm has $g_\ell L_{\ell+2}$ pulls, where $g_\ell \to \infty$ slowly, and
otherwise the learner follows the leader. This looks consistent at batch ends on every grid with
$\log L_{\ell+1} = o(L_\ell)$. The one-batch lower bound ($N_a(t_\ell)$ pays for the horizon
$t_{\ell+1}$, HY.md "Proof routes") makes that condition necessary for consistency. If this holds,
the frontier for plain consistency at batch ends is $\log L_{\ell+1} = o(L_\ell)$, not the
candidate $\log L_{\ell+2} = o(L_\ell)$ of direction 4. This is not a contradiction: direction 4
asks for consistency *with logarithmic counts*, and forced exploration has
$N_c(t_{\ell+1}) \ge g_\ell L_{\ell+2}$, which is not $O(L_{\ell+1})$ since $g_\ell \to \infty$. The note only suggests that the owner say which count condition
direction 4 means. Not checked by anyone.

## Dead ends

None yet.

## Outcome

