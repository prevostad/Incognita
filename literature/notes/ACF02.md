# ACF02: Finite-time analysis of the multiarmed bandit problem (UCB1)

| | |
|---|---|
| Work | P. Auer, N. Cesa-Bianchi, P. Fischer, *Finite-time Analysis of the Multiarmed Bandit Problem*, Machine Learning 47, 235–256, 2002 |
| Identifiers | DOI 10.1023/A:1013689704352 (not printed on the PDF read; from the Crossref record cited in `index.md`) |
| Read | Author's PDF homes.di.unimi.it/~cesabian/Pubblicazioni/ml-02.pdf (journal layout, header "Machine Learning, 47, 235–256, 2002"), page images: pp. 235–244 (abstract; §1; §2 with Theorem 1, Figure 1, (2), Theorems 2–4 and Figures 2–4 as statements; §3 opening, (5), Facts 1–2, proof of Theorem 1, beginning of the proof of Theorem 3), pp. 255–256 (end of the proof of Theorem 4, Note 1, references, received/accepted dates). Not read: pp. 245–254 (rest of the proof of Theorem 3, proofs of Theorems 2 and 4, Conjectures 1–2, experiments) |
| By, date | Claude Opus 5.5 (revise, P006), 2026-11-17 (Read, first reading: Author PDF (homes.di.unimi.it/~cesabian/Pubblicazioni/ml-02.pdf, the journal pages with the Kluwer header): §1, the model and the regret (p. 235–236); the definition of $\Delta_i$ (p. 237); §2, Theorem 1 and Figure 1 (p. 237, page image); the remark at the end of §2 (p. 239). Proofs not read.); Claude Opus 5.5 (revise, P007), 2026-11-17 (Read, as above) |

## Results

Statements copied from the page images; mathematics in LaTeX, with the printed symbols
($I\!E$ for expectation, $I\!P$ for probability, braces $\{\Pi(x)\}$ for indicators) kept.

### Setting (§1, pp. 235–236)

- **Rewards.** "In its most basic formulation, a $K$-armed bandit problem is defined by random
  variables $X_{i,n}$ for $1\le i\le K$ and $n\ge1$, where each $i$ is the index of a gambling
  machine (i.e., the "arm" of a bandit). Successive plays of machine $i$ yield rewards
  $X_{i,1},X_{i,2},\ldots$ which are independent and identically distributed according to an
  unknown law with unknown expectation $\mu_i$. Independence also holds for rewards across
  machines; i.e., $X_{i,s}$ and $X_{j,t}$ are independent (and usually not identically distributed)
  for each $1\le i<j\le K$ and each $s,t\ge1$."
- **Policy, counts, regret.** "A *policy*, or *allocation strategy*, $A$ is an algorithm that chooses
  the next machine to play based on the sequence of past plays and obtained rewards. Let $T_i(n)$
  be the number of times machine $i$ has been played by $A$ during the first $n$ plays. Then the
  *regret* of $A$ after $n$ plays is defined by
  $\mu^*n-\mu_j\sum_{j=1}^K I\!E[T_j(n)]$ where $\mu^*\overset{\text{def}}{=}\max_{1\le i\le K}\mu_i$
  and $I\!E[\cdot]$ denotes expectation." (As printed, $\mu_j$ stands outside the sum: a misprint
  for $\sum_j\mu_jI\!E[T_j(n)]$; the paper's own rewriting is (5) below.)
- **Gaps (p. 237).** "$\Delta_i\overset{\text{def}}{=}\mu^*-\mu_i$ where, we recall, $\mu_i$ is the
  reward expectation for machine $i$ and $\mu^*$ is any maximal element in the set
  $\{\mu_1,\ldots,\mu_K\}$."
- **§3 opening (p. 241).** "Recall that, for each $1\le i\le K$, $I\!E[X_{i,n}]=\mu_i$ for all
  $n\ge1$ and $\mu^*=\max_{1\le i\le K}\mu_i$. Also, for any fixed policy $A$, $T_i(n)$ is the number
  of times machine $i$ has been played by $A$ in the first $n$ plays. Of course, we always have
  $\sum_{i=1}^KT_i(n)=n$. We also define the r.v.'s $I_1,I_2,\ldots$, where $I_t$ denotes the
  machine played at time $t$." "Note that the regret after $n$ plays can be written as
  $\sum_{j:\mu_j<\mu^*}\Delta_jI\!E[T_j(n)]$ (5)".

### UCB1 (§2, p. 237)

- **Figure 1** (boxed; caption "Sketch of the deterministic policy UCB1 (see Theorem 1)."):
  "Deterministic policy: UCB1.
  Initialization: Play each machine once.
  Loop:
  – Play machine $j$ that maximizes $\bar x_j+\sqrt{\frac{2\ln n}{n_j}}$, where $\bar x_j$ is the
  average reward obtained from machine $j$, $n_j$ is the number of times machine $j$ has been
  played so far, and $n$ is the overall number of plays done so far."
- **Convention for $n$.** In the index, $n$ is the total number of plays made before the current
  one (all arms together). The proof of Theorem 1 agrees: play $t\ge K+1$ compares
  $\bar X^*_{T^*(t-1)}+c_{t-1,T^*(t-1)}$ with $\bar X_{i,T_i(t-1)}+c_{t-1,T_i(t-1)}$, where
  $c_{t,s}=\sqrt{(2\ln t)/s}$. Ties are not discussed. The policy does not use the horizon.
- **Theorem 1.** "For all $K>1$, if policy UCB1 is run on $K$ machines having arbitrary reward
  distributions $P_1,\ldots,P_K$ with support in $[0,1]$, then its expected regret after any number
  $n$ of plays is at most
  $$\Bigl[8\sum_{i:\mu_i<\mu^*}\Bigl(\frac{\ln n}{\Delta_i}\Bigr)\Bigr]+\Bigl(1+\frac{\pi^2}{3}\Bigr)\Bigl(\sum_{j=1}^K\Delta_j\Bigr)$$
  where $\mu_1,\ldots,\mu_K$ are the expected values of $P_1,\ldots,P_K$."
- **(2), p. 238.** "To prove Theorem 1 we show that, for any suboptimal machine $j$,
  $I\!E[T_j(n)]\le\frac{8}{\Delta_j^2}\ln n$ (2) plus a small constant." The end of the proof (p. 243)
  gives, for a suboptimal $i$,
  "$I\!E[T_i(n)]\le\bigl\lceil\frac{8\ln n}{\Delta_i^2}\bigr\rceil+\sum_{t=1}^\infty\sum_{s=1}^{t-1}\sum_{s_i=\lceil(8\ln n)/\Delta_i^2\rceil}^{t-1}\bigl(I\!P\{\bar X^*_s\le\mu^*-c_{t,s}\}+I\!P\{\bar X_{i,s_i}\ge\mu_i+c_{t,s_i}\}\bigr)\le\bigl\lceil\frac{8\ln n}{\Delta_i^2}\bigr\rceil+\sum_{t=1}^\infty\sum_{s=1}^t\sum_{s_i=1}^t2t^{-4}\le\frac{8\ln n}{\Delta_i^2}+1+\frac{\pi^2}{3}$".
  So the per-arm bound is $I\!E[T_i(n)]\le\frac{8\ln n}{\Delta_i^2}+1+\frac{\pi^2}{3}$, and Theorem 1
  follows by (5).
- **Remark on the hypotheses (p. 241).** "As a final remark for this section, note that Theorems 1–3
  also hold for rewards that are not independent across machines, i.e. $X_{i,s}$ and $X_{j,t}$ might
  be dependent for any $s$, $t$, and $i\ne j$. Furthermore, we also do not need that the rewards of a
  single arm are i.i.d., but only the weaker assumption that
  $I\!E[X_{i,t}\mid X_{i,1},\ldots,X_{i,t-1}]=\mu_i$ for all $1\le t\le n$."
- **Fact 1 (Chernoff-Hoeffding bound), p. 242.** "Let $X_1,\ldots,X_n$ be random variables with
  common range $[0,1]$ and such that $I\!E[X_t|X_1,\ldots,X_{t-1}]=\mu$. Let
  $S_n=X_1+\cdots+X_n$. Then for all $a\ge0$
  $I\!P\{S_n\ge n\mu+a\}\le e^{-2a^2/n}$ and $I\!P\{S_n\le n\mu-a\}\le e^{-2a^2/n}$". Credited to
  "the appendix of Pollard, 1984".
- Theorems 2 (UCB2, leading constant arbitrarily close to $1/(2\Delta_i^2)$ per arm, for
  $n\ge\max_{i:\mu_i<\mu^*}1/(2\Delta_i^2)$), 3 ($\varepsilon_n$-GREEDY, with a lower bound $d$ on the gaps
  as input) and 4 (UCB1-NORMAL, normal rewards, proof relying on Conjectures 1–2 checked only
  numerically) were read as statements only; their proofs (except the start of that of Theorem 3)
  were not read.

## Techniques

- Index policy: empirical mean plus a confidence width from the Chernoff–Hoeffding bound (Fact 1).
  The authors say (p. 237) "The policy UCB1 (sketched in figure 1) is derived from the index-based
  policy of Agrawal (1995)", and (p. 236) "In Theorem 1 we show that a simple variant of Agrawal's
  index-based policy has finite-time regret logarithmically bounded for arbitrary sets of reward
  distributions with bounded support". On Agrawal (1995) (p. 236): "More recently, Agrawal (1995)
  introduced a family of policies where the index can be expressed as simple function of the total
  reward obtained so far from the machine." Reference list (p. 255): "Agrawal, R. (1995). Sample
  mean based index policies with $O(\log n)$ regret for the multi-armed bandit problem. *Advances in
  Applied Probability*, *27*, 1054–1078." Note 1 (p. 255): "Similar extensions of Lai and Robbins'
  results were also obtained by Yakowitz and Lowe (1991), and by Burnetas and Katehakis (1996)."
- Proof of Theorem 1 (pp. 242–243): $T_i(n)\le\ell+\sum_t\{I_t=i,\ T_i(t-1)\ge\ell\}$; the event that
  arm $i$ is chosen forces one of (7) $\bar X^*_s\le\mu^*-c_{t,s}$, (8)
  $\bar X_{i,s_i}\ge\mu_i+c_{t,s_i}$, (9) $\mu^*<\mu_i+2c_{t,s_i}$; (9) is false for
  $\ell=\lceil(8\ln n)/\Delta_i^2\rceil$, (7) and (8) have probability at most $t^{-4}$ by Fact 1, and
  a union bound over the unknown counts $s,s_i$.
- The lower bound $D(p_j\|p^*)\ge2\Delta_j^2$, "where the constant 2 is the best possible" (p. 238),
  stated without proof.

## Where Incognita uses it

- `papers/P006-batched-setting/`: `cite:ACF02-thm1` (the witness `cor:ucb`).
- `papers/P007-stochastic-setting/`: requested by its referee (crediting UCB1 and its finite-time
  bound).
- `literature/index.md` records that P003 cites it as a classic for the regret bound of UCB.
