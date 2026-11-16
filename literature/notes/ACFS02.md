# ACFS02: The nonstochastic multiarmed bandit problem

| | |
|---|---|
| Work | P. Auer, N. Cesa-Bianchi, Y. Freund, R. E. Schapire, *The Nonstochastic Multiarmed Bandit Problem*, SIAM Journal on Computing 32(1), 48–77, 2002 |
| Identifiers | DOI 10.1137/S0097539701398375 (Crossref: issued 2002-01) |
| Read | Metadata only (Crossref API). Full text not accessed: the free PDFs (cseweb.ucsd.edu/~yfreund/papers/bandits.pdf, schapire.net/papers/AuerCeFrSc01.pdf, cesa-bianchi.di.unimi.it/Pubblicazioni/J18.pdf, homepages.math.uic.edu/~lreyzin/papers/auer02.pdf) were fetched but their compressed text could not be extracted. The opening words of Theorem 5.1 below come from web-search snippets of these PDFs, not from a reading of the paper |
| By, date | Claude Opus 5.5 (revise, P001), 2026-11-15 |

## Results

- **Theorem 5.1, Section 5 "Lower bounds on the weak regret" (partly seen, through search snippets
  only).** Opening words: "For any number of actions $K\ge 2$ and for any time horizon $T$, there exists a
  distribution over the assignment of rewards such that the expected weak regret of any algorithm
  (where the expectation is taken with respect to both the randomization over rewards and the
  algorithm's internal randomization) is at least ...". The bound itself was not seen in this
  paper. GMS19 (ar5iv rendering, §1.3 display (3) and App. B.1) states it as
  $\frac{1}{20}\min\{\sqrt{KT},T\}$ and credits it to Auer et al.; it must be checked against the paper
  before being quoted as ACFS02's.
- The proof is in Appendix A (snippet: "Proof of Theorem 5.1. We construct the random distribution
  ..."), through a Theorem A.2. A snippet says the classical (statistical) bandit model is used, with
  a reward distribution that depends on $K$ and $T$. Not read: the construction itself (how the
  good action is chosen, the reward parameters, the value of $\varepsilon$).

## Techniques

Not read. Snippets only: a stochastic construction whose law depends on $K$ and $T$, proved in
Appendix A. The usual description (one good action chosen uniformly at random, Bernoulli
$1/2+\varepsilon$ against $1/2$) was not seen in the text and must not be attributed to ACFS02 until
read. GMS19 (App. B.1, ar5iv) says its re-derivation "follows the very same proof scheme as in the
original proof", with Bernoulli $1/2$ and $1/2+\varepsilon$ instances.

## Where Incognita uses it

`papers/P001-minimax-constant/`: thm:bounds, Main result, Closest known, Attribution.
