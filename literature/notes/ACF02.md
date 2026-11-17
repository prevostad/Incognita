# ACF02: finite-time analysis of the multiarmed bandit problem

| | |
|---|---|
| Work | P. Auer, N. Cesa-Bianchi, P. Fischer, *Finite-time Analysis of the Multiarmed Bandit Problem*, Machine Learning 47, 235–256, 2002 |
| Identifiers | DOI 10.1023/A:1013689704352 |
| Read | Author PDF (homes.di.unimi.it/~cesabian/Pubblicazioni/ml-02.pdf, the journal pages with the Kluwer header): §1, the model and the regret (p. 235–236); the definition of $\Delta_i$ (p. 237); §2, Theorem 1 and Figure 1 (p. 237, page image); the remark at the end of §2 (p. 239). Proofs not read. |
| By, date | Claude Opus 5.5 (revise, P006), 2026-11-17 |

## Results

Quoted from the PDF (Theorem 1 and Figure 1 read on the page image of p. 237).

- **Model (§1).** "Successive plays of machine $i$ yield rewards $X_{i,1}, X_{i,2},\dots$ which are
  independent and identically distributed according to an unknown law with unknown expectation
  $\mu_i$. Independence also holds for rewards across machines; i.e., $X_{i,s}$ and $X_{j,t}$ are
  independent (and usually not identically distributed) for each $1\le i<j\le K$ and each
  $s,t\ge1$." "Let $T_i(n)$ be the number of times machine $i$ has been played by $A$ during the
  first $n$ plays. Then the regret of $A$ after $n$ plays is defined by
  $\mu^*n-\sum_{j=1}^K\mu_j\,\mathbb E[T_j(n)]$ where $\mu^*\overset{\mathrm{def}}{=}\max_{1\le i\le K}\mu_i$."
- **$\Delta_i$ (p. 237).** "$\Delta_i\overset{\mathrm{def}}{=}\mu^*-\mu_i$ where, we recall, $\mu_i$ is
  the reward expectation for machine $i$ and $\mu^*$ is any maximal element in the set
  $\{\mu_1,\dots,\mu_K\}$."
- **Figure 1.** "Deterministic policy: UCB1. Initialization: Play each machine once. Loop: – Play
  machine $j$ that maximizes $\bar x_j+\sqrt{\frac{2\ln n}{n_j}}$, where $\bar x_j$ is the average
  reward obtained from machine $j$, $n_j$ is the number of times machine $j$ has been played so far,
  and $n$ is the overall number of plays done so far." (No tie rule and no order of the
  initialization are specified.)
- **Theorem 1.** "For all $K>1$, if policy UCB1 is run on $K$ machines having arbitrary reward
  distributions $P_1,\dots,P_K$ with support in $[0,1]$, then its expected regret after any number
  $n$ of plays is at most
  $$\Bigl[8\sum_{i:\mu_i<\mu^*}\Bigl(\frac{\ln n}{\Delta_i}\Bigr)\Bigr]+\Bigl(1+\frac{\pi^2}{3}\Bigr)\Bigl(\sum_{j=1}^K\Delta_j\Bigr)$$
  where $\mu_1,\dots,\mu_K$ are the expected values of $P_1,\dots,P_K$."
- **Remark at the end of §2.** Theorems 1–3 also hold for rewards that are not independent across
  machines, and only $\mathbb E[X_{i,t}\mid X_{i,1},\dots,X_{i,t-1}]=\mu_i$ is needed for a single
  arm.

## Techniques

Chernoff–Hoeffding bounds for the index (Fact 1, not read); the proof of Theorem 1 bounds
$\mathbb E[T_j(n)]$ by $\frac{8\ln n}{\Delta_j^2}+1+\frac{\pi^2}{3}$ (first line of the proof only).

## Where Incognita uses it

- `papers/P006-batched-setting/`: `cite:ACF02-thm1` (the witness `cor:ucb`); P003 cites it as a
  classic.
