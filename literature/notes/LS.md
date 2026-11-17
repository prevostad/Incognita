# LS: Bandit Algorithms

| | |
|---|---|
| Work | T. Lattimore, Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 |
| Identifiers | DOI 10.1017/9781108571401 |
| Read | Session of 2026-11-15 (Claude Opus 5.5, revise, P001): the free online edition, https://tor-lattimore.com/downloads/book/book.pdf ("This is the (free) online edition"; PDF dated 12 Aug 2024), read as extracted text (via r.jina.ai), not as page images; page numbers are those of this edition, inferred from running headers, and the online edition states that its page numbers differ from the print edition. Parts read: Chapter 4 title; §4.6 heading, first two sentences and the stack-of-rewards passage; Chapter 9 title; §9.1 Algorithm "MOSS" (numbered Algorithm 7 in this edition) and Theorem 9.1; Chapter 15 title; text before Theorem 15.2, Theorem 15.2 and the paragraph after it; Exercise 15.2 (setup, displays of parts (a)–(c), part (d)). Read earlier, see index.md: §9.2; §9.3 Notes 1–3; §15.1 Lemma 15.1 statement; §16.1–16.4 parts; Exercise 16.4; §25; §36.5–36.6. Not read: the proofs of Theorems 9.1 and 15.2. Session of 2026-11-16 (Claude Opus 5.5, write-paper, P005): the free online PDF (text layer): §3.3 Theorem 3.9 (maximal inequality); §16.1 Definition 16.1, the definition of $d_{\inf}$ and Theorem 16.2 with the start of its proof; §16.3 Notes 1–3; §16.4. Session of 2026-11-17 (Claude Opus 5.5, revise, P006): the free online PDF (text layer): §4.6 pp. 63–65 in full (Definition 4.7, conditions (a)–(b), Proposition 4.8, the density (4.7), the random-table and reward-stack models and the sentence on their equivalence); §4.10 Exercises 4.1–4.4 (p. 69) |
| By, date | agent (roadmap draft), 2026-11-14; Claude Opus 5.5 (revise, P001), 2026-11-15; Claude Opus 5.5 (write-paper, P005), 2026-11-16 (the results from §3.3 and §16); Claude Opus 5.5 (revise, P006), 2026-11-17 (§4.6 in full, Exercises 4.1–4.4) |

## Results

The quotations come from the extracted text. Fractions were flattened in extraction (for example
"127" for $\frac1{27}$), so the fraction layout below is reconstructed and has to be checked on a page
image before it is quoted as printed.

- **Chapter 4, "Stochastic Bandits"; §4.6, "The Canonical Bandit Model", pp. 63–65.** The section opens: "In
  most cases the underlying probability space that supports the random rewards and actions is never
  mentioned. Occasionally, however, it becomes convenient to choose a specific probability space,
  which we call the canonical bandit model". The alternative model with a table of rewards: "Define a
  collection of independent random variables $(X_{si})_{s\in[n],i\in[k]}$ such that the law of $X_{ti}$ is
  $P_i$." This "corresponds to sampling a stack of rewards for each arm at the beginning of the
  game. Each time the learner chooses an action, they receive the reward on top of the stack."
  (p. 65), with $X_t = X_{T_{A_t}(t),A_t}$ (extracted as "Xt = XTAt (t),A t").
- **§4.6, the rest, pp. 64–65 (read 2026-11-17, Claude Opus 5.5, revise, P006; text layer of the
  online PDF).** Definition 4.7: "A policy π is a sequence $(\pi_t)_{t=1}^n$, where $\pi_t$ is a
  probability kernel from $(\Omega_{t-1},\mathcal F_{t-1})$ to $([k],2^{[k]})$", with
  $\Omega_t=([k]\times\mathbb R)^t$. The two conditions: "(a) the conditional distribution of action
  $A_t$ given $A_1,X_1,\dots,A_{t-1},X_{t-1}$ is $\pi_t(\cdot\mid A_1,X_1,\dots,A_{t-1},X_{t-1})$
  almost surely. (b) the conditional distribution of reward $X_t$ given $A_1,X_1,\dots,A_t$ is
  $P_{A_t}$ almost surely." Proposition 4.8 (proof: Exercise 4.2): "Suppose that P and Q are
  probability measures on an arbitrary measurable space $(\Omega,\mathcal F)$ and
  $A_1,X_1,\dots,A_n,X_n$ are random variables on Ω, where $A_t\in[k]$ and $X_t\in\mathbb R$. If both
  P and Q satisfy (a) and (b), then the law of the outcome $(A_1,X_1,\dots,A_n,X_n)$ under P is the
  same as under Q". The canonical measure is given by the density (4.7),
  $p_{\nu\pi}=\prod_t\pi(a_t\mid a_1,x_1,\dots)p_{a_t}(x_t)$ with respect to $(\rho\times\lambda)^n$.
  The random-table model ($X_t=X_{tA_t}$) and the reward-stack model ($X_t=X_{T_{A_t}(t),A_t}$),
  with $(X_{si})_{s\in[n],i\in[k]}$ independent, $X_{ti}$ of law $P_i$, then: "All of these models
  are convenient from time to time. The important thing is that it does not matter which model we
  choose because the quantity of ultimate interest (usually the regret) only depends on the law of
  $A_1,X_1,\dots,A_n,X_n$, and this is the same for all choices (Exercise 4.4)." Infinite horizon
  (p. 66): existence "follows directly from the theorem of Ionescu–Tulcea (Theorem 3.3)".
- **§4.10, Exercises, p. 69.** "4.2 (Uniqueness of law) Prove Proposition 4.8." "4.3 (Definition of
  canonical probability measure) Prove that the measure defined in terms of the density in Eq. (4.7)
  satisfies the conditions (a) and (b) in Section 4.6." "4.4 (Random table versus stacked-reward
  models) Show that both the random-table and the stacked-reward models give rise to a probability
  distribution that satisfy the condition (b) in Section 4.6. Hint When reasoning about the
  stacked-reward model, use Doob's optional stopping theorem (Theorem 3.8), which continues to hold
  if N in the theorem is replaced by [t] for some t ∈ N+ assuming that τ ≤ t".
- **Chapter 9, "The Upper Confidence Bound Algorithm: Minimax Optimality"; §9.1, "The MOSS Algorithm",
  Algorithm 7 (MOSS) of this edition, p. 123.** Index: $A_t = \operatorname{argmax}_i\ \hat\mu_i(t-1) +
  \sqrt{\frac{4}{T_i(t-1)}\log^+\!\left(\frac{n}{kT_i(t-1)}\right)}$, where $\log^+(x) = \log\max\{1,x\}$
  (extracted as "√4 / Ti(t − 1) log+( nk / Ti(t − 1) )": the placement of $k$ in the denominator is a
  reconstruction).
- **Theorem 9.1, p. 124.** "For any 1-subgaussian bandit, the regret of Algorithm 7 satisfies
  $R_n \le 39\sqrt{kn} + \sum_{i=1}^k \Delta_i$."
- **Chapter 15, "Minimax Lower Bounds"; §15.2, pp. 199–200.** The text before the theorem: "Recall that
  $\mathcal E^k_{\mathcal N}(1)$ is the class of Gaussian bandits with unit variance, which can be
  parameterised by their mean vector $\mu\in\mathbb R^k$. Given $\mu\in\mathbb R^k$, let $\nu_\mu$ be the
  Gaussian bandit for which the $i$th arm has reward distribution $\mathcal N(\mu_i,1)$."
- **Theorem 15.2, pp. 199–200.** "Let $k > 1$ and $n \ge k-1$. Then, for any policy $\pi$, there exists
  a mean vector $\mu\in[0,1]^k$ such that $R_n(\pi,\nu_\mu)\ge\frac1{27}\sqrt{(k-1)n}$." It is followed
  by: "Since $\nu_\mu\in\mathcal E^k_{\mathcal N}(1)$, it follows that the minimax regret for
  $\mathcal E^k_{\mathcal N}(1)$ is lower-bounded by the right-hand side of the above display as soon
  as $n\ge k-1$: $R^*_n(\mathcal E^k_{\mathcal N}(1))\ge\frac1{27}\sqrt{(k-1)n}$."
- **Exercise 15.2, "(Alternative proof of Theorem 15.2)", pp. 203–204.** "Here you will prove Theorem 15.2
  with a different method." "Let $c>0$ and $\Delta = 2c\sqrt{k/n}$, and for each
  $i\in\{0,1,\dots,k\}$, let $\mu^{(i)}\in\mathbb R^k$ satisfy $\mu^{(i)}_j = \mathbb I\{i=j\}\Delta$.
  Further abbreviate the notation in the proof of Theorem 15.2 by letting
  $\mathbb E_i[\cdot]=\mathbb E_{\mu^{(i)}}[\cdot]$."
  (a) (with Pinsker's inequality, Lemma 15.1 and Exercise 14.4, per the summary of the fetch tool)
  $\mathbb E_i[T_i(n)] \le \mathbb E_0[T_i(n)] + n\sqrt{\tfrac14\Delta^2\mathbb E_0[T_i(n)]} =
  \mathbb E_0[T_i(n)] + c\sqrt{nk\,\mathbb E_0[T_i(n)]}$.
  (b) $\sum_{i=1}^k\mathbb E_i[T_i(n)] \le n + c\sum_{i=1}^k\sqrt{nk\,\mathbb E_0[T_i(n)]} \le n + ckn$.
  (c) "Let $R_i = R_n(\pi, G_{\mu^{(i)}})$." "Find a choice of $c>0$ for which"
  $\sum_{i=1}^k R_i = \Delta\sum_{i=1}^k(n-\mathbb E_i[T_i(n)]) \ge \Delta(nk-n-ckn) =
  2c\sqrt{k/n}\,(nk-n-ckn) \ge \frac{nk}{8}\sqrt{k/n}$.
  (d) "Conclude that there exists an $i\in[k]$ such that $R_i\ge\frac18\sqrt{kn}$."
  The exercise states no hypothesis on $n$ (no $n\ge k$); the Gaussian unit-variance model is not
  restated in it, but it comes through "the notation in the proof of Theorem 15.2" ($G_{\mu^{(i)}}$
  is not defined in the text read). The last inequality of (c) does not hold for every $k$: with
  $c=\frac14$ it reads $\frac12\sqrt{k/n}\,n(\frac{3k}4-1)\ge\frac{nk}8\sqrt{k/n}$, that is $k\ge2$
  (our check, not the book's text). The average is over the position $i$ of the good arm.

Statements copied from the text layer of the free PDF (session of 2026-11-16); formulas rebuilt in LaTeX with the book's symbols
($R_n(\pi,\nu)$ the expected regret after $n$ rounds, $D$ the relative entropy, $\mu(P)$ the mean of $P$).

- **Theorem 3.9 (Maximal inequality).** "Let $(X_t)_{t=0}^\infty$ be a supermartingale with $X_t\ge0$ almost surely
  for all $t$. Then for any $\varepsilon>0$, $\mathbb P\big(\sup_{t\in\mathbb N}X_t\ge\varepsilon\big)\le\frac{\mathbb E[X_0]}{\varepsilon}$."
- **Definition 16.1.** "A policy $\pi$ is called consistent over a class of bandits $\mathcal E$ if for all $\nu\in\mathcal E$
  and $p>0$, it holds that $\lim_{n\to\infty}\frac{R_n(\pi,\nu)}{n^p}=0$. (16.1) The class of consistent policies over
  $\mathcal E$ is denoted by $\Pi_{\mathrm{cons}}(\mathcal E)$."
- **Definition of $d_{\inf}$ (§16.1).** "Let $\mathcal M$ be a set of distributions with finite means, and let
  $\mu:\mathcal M\to\mathbb R$ be the function that maps $P\in\mathcal M$ to its mean. Let $\mu^*\in\mathbb R$ and $P\in\mathcal M$
  have $\mu(P)<\mu^*$ and define $d_{\inf}(P,\mu^*,\mathcal M)=\inf_{P'\in\mathcal M}\{D(P,P'):\mu(P')>\mu^*\}$."
- **Theorem 16.2.** "Let $\mathcal E=\mathcal M_1\times\dots\times\mathcal M_k$ and $\pi\in\Pi_{\mathrm{cons}}(\mathcal E)$ be a consistent
  policy over $\mathcal E$. Then, for all $\nu=(P_i)_{i=1}^k\in\mathcal E$, it holds that
  $\liminf_{n\to\infty}\frac{R_n}{\log(n)}\ge c^*(\nu,\mathcal E)=\sum_{i:\Delta_i>0}\frac{\Delta_i}{d_{\inf}(P_i,\mu^*,\mathcal M_i)}$, (16.2)
  where $\Delta_i$ is the suboptimality gap of the $i$th arm in $\nu$ and $\mu^*$ is the mean of the optimal arm."
  The proof shows, for every suboptimal arm $i$, $\liminf_{n\to\infty}\mathbb E_{\nu\pi}[T_i(n)]/\log(n)\ge1/d_{\inf}(P_i,\mu^*,\mathcal M_i)$,
  and uses the regret decomposition (Lemma 4.5).
- **§16.3, Note 1.** Burnetas and Katehakis [1996] is the original source of Theorem 16.2. **Note 3.** The
  non-parametric classes analysed exactly are bounded and semi-bounded supports; for bounded kurtosis
  the book refers to Lattimore [2017].
- **§16.4.** Classes with bounded kurtosis are "only understood up to constant factors" (citing Lattimore
  [2017]); "plenty of open questions" remain for non-parametric classes.

## Techniques

Minimax lower bound by change of measure between a base instance and instances where one arm is
raised (Theorem 15.2: two instances, Fig. 15.1, "the evil antagonist picks another environment";
Exercise 15.2: averaging over the $k$ positions of the raised arm, with Pinsker, the divergence
decomposition Lemma 15.1, Jensen and $\sum_i\mathbb E_0[T_i(n)]=n$). Canonical model as a table of
independent rewards, one stack per arm (§4.6). MOSS: UCB with a $\log^+(n/(kT_i))$ exploration bonus
(§9.1).

Change of measure on one arm (Lemma 15.1, Theorem 14.2) for Theorem 16.2.

## Where Incognita uses it

- `papers/P001-minimax-constant/`: thm:bounds, Main result (Context), Closest known, sec:app-exp (MOSS).
- `papers/P005-bounded-kurtosis/`: node `cite:LS-16.2` (the lower bound paired with the main theorem); the
  maximal inequality (Theorem 3.9), used by name in the proof of the upper deviation.
- `roadmaps/StochasticBandits/KNOWN.md`: K1, K43, K63.
