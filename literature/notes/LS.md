# LS: Bandit Algorithms

| | |
|---|---|
| Work | T. Lattimore, Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 |
| Identifiers | DOI 10.1017/9781108571401 |
| Read | This session: the free online edition, https://tor-lattimore.com/downloads/book/book.pdf ("This is the (free) online edition"; PDF dated 12 Aug 2024), read as extracted text (via r.jina.ai), not as page images; page numbers are those of this edition, inferred from running headers, and the online edition states that its page numbers differ from the print edition. Parts read: Chapter 4 title; §4.6 heading, first two sentences and the stack-of-rewards passage; Chapter 9 title; §9.1 Algorithm "MOSS" (numbered Algorithm 7 in this edition) and Theorem 9.1; Chapter 15 title; text before Theorem 15.2, Theorem 15.2 and the paragraph after it; Exercise 15.2 (setup, displays of parts (a)–(c), part (d)). Read earlier, see index.md: §9.2; §9.3 Notes 1–3; §15.1 Lemma 15.1 statement; §16.1–16.4 parts; Exercise 16.4; §25; §36.5–36.6. Not read: the proofs of Theorems 9.1 and 15.2 |
| By, date | Claude Opus 5.5 (revise, P001), 2026-11-15 |

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

## Techniques

Minimax lower bound by change of measure between a base instance and instances where one arm is
raised (Theorem 15.2: two instances, Fig. 15.1, "the evil antagonist picks another environment";
Exercise 15.2: averaging over the $k$ positions of the raised arm, with Pinsker, the divergence
decomposition Lemma 15.1, Jensen and $\sum_i\mathbb E_0[T_i(n)]=n$). Canonical model as a table of
independent rewards, one stack per arm (§4.6). MOSS: UCB with a $\log^+(n/(kT_i))$ exploration bonus
(§9.1).

## Where Incognita uses it

`papers/P001-minimax-constant/`: thm:bounds, Main result (Context), Closest known, sec:app-exp (MOSS).
