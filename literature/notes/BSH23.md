# BSH23: a general recipe for randomized bandit algorithms

| | |
|---|---|
| Work | Dorian Baudry, Kazuya Suzuki, Junya Honda, *A General Recipe for the Analysis of Randomized Multi-Armed Bandit Algorithms*, arXiv preprint, 2023 |
| Identifiers | arXiv 2303.06058 (v1 10 Mar 2023, v2 21 Dec 2023, v3 13 Nov 2024) |
| Read | arXiv:2303.06058v3 HTML, through extracts of a fetch tool (displays as returned by the tool, prose paraphrased): abstract; §1 (the $h$-moment families); (2); the titles of §4.1–4.5; §4.4 (the family $\mathcal F_{h,B}$, the corollary on MED) |
| By, date | Claude Opus 5.5 (revise, P004), 2026-11-16 |

## Results

- **(2).** $\mathcal{K}_{\inf}^{\mathcal{F}}(F_k,\mu^\star)=\inf_{G\in\mathcal{F}}\{\mathrm{KL}(F_k,G):\mathbb{E}_{X\sim G}[X]>\mu^\star\}$ (strict inequality).
- **§4 families:** 4.1 single-parameter exponential families; 4.2 Gaussian laws with unknown
  variances (a known bound on the variances, a known lower bound on the means); 4.3 laws on
  $[0,B]$; 4.4 laws under an $h$-moment condition; 4.5 summary. None is a family of laws bounded
  above and unbounded below without a known moment bound.
- **§4.4 (uncentered).** $h$ a positive convex function known to the learner with
  $h(|x|)/|x|^{1+\eta}\to+\infty$ for some $\eta>0$, $B>0$ known, and
  $$\mathcal{F}_{h,B}=\left\{F:\ \mathbb{E}_{X\sim F}[h(|X|)]<B,\ \mathbb{E}_{X\sim F}[h(|X|)^{2+\epsilon_F}]<+\infty \text{ for some } \epsilon_F>0\right\}.$$
  A centered variant replaces $|X|$ by $|X-\mathbb E X|$ and assumes a known lower bound on the
  means; §4.4.2 gives a known bound $B$ on the variance as an example.
- **Corollary (§4.4, "instance-dependent optimality of MED on $\mathcal F_{h,B}$"):** MED is
  asymptotically optimal on $\mathcal F_{h,B}$, through the general Theorem 5,
  $\mathbb E[N_k(T)]\le(1+c)\log T/D_\pi(F_k,\mu^\star)+o_c(\log T)$, with the divergence
  $\mathcal K_{\inf}^{\mathcal F_{h,B}}$ (Lemma 18). Not read in detail.

## Techniques

Sufficient conditions on the sampling probabilities of a randomized algorithm and on the family
(Theorem 5), checked family by family. Not read beyond the statements above.

## Where Incognita uses it

- P004 (`sec:related`, paragraph "Heavy-tailed bandits"): MED optimal under a known $h$-moment bound,
  a different model from the semi-bounded one, where no bound is known.
- P004 (`oq:finite-mean`): Remark 1 and Appendix B.4 (read 2026-11-16 in the v3 PDF) are the
  precedent of a robust mean estimate as the reference of MED: a two-sided truncated mean
  $\frac1n\sum_iX_i\mathbb 1(|X_i|\le u_n)$, under a known bound $\mathbb E|X|^{1+\delta}\le B$, whose
  deviations below the mean are bounded by Bernstein's inequality; the proof of their Theorem 1
  does not use the form of the estimate.
