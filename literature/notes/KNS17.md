# KNS17: Two-armed bandit, data processing, and parallel mirror descent

| | |
|---|---|
| Work | A. Kolnogorov, A. Nazin, D. Shiyan, *Two-Armed Bandit Problem, Data Processing, and Parallel Version of the Mirror Descent Algorithm*, arXiv preprint, 2017 (11 pages, 13 figures; math.ST) |
| Identifiers | arXiv 1705.09977 (v1, 28 May 2017, the only version); DOI 10.48550/arXiv.1705.09977. No journal-ref on the arXiv page; a published version was not searched for |
| Read | whole (arXiv:1705.09977v1, PDF, pp. 1–11), from https://arxiv.org/pdf/1705.09977; metadata from https://arxiv.org/abs/1705.09977 |
| By, date | Claude Opus 5.5 (revise, P001), 2026-11-15 |

## Results

Setting: Bernoulli two-armed bandit, $\Theta=\{0\le p_\ell\le1\}$, regret $L_N(\sigma,\theta)$, minimax risk
$R^{(0)}_N(\Theta)=\inf_{\Sigma_0}\sup_\Theta L_N(\sigma,\theta)$ (1) over all strategies $\Sigma_0$.

- **Theorem 1, §1, p. 2: quoted from Vogel and Bather (not proved here).** Introduced by "the following
  asymptotic minimax theorem was proved by W. Vogel in [9]." Statement: "Theorem 1. The following
  estimates of the minimax risk (1) hold as $N\to\infty$ for Bernoulli two-armed bandit:
  $0.612\le(DN)^{-1/2}R^{(0)}_N(\Theta)\le0.752$ (2) with $D=0.25$ being the maximal possible variance of
  one-step income." Followed by: "Presented here the lower estimate was obtained in [10]. The upper
  estimate was obtained in [9] for the following strategy." ([9] = Vogel, Ann. Math. Stat. 31 (1960)
  444–451; [10] = Bather, Lecture Notes in Statistics 20 (1983) 1–11.) Thresholding strategy with
  threshold $\alpha(DN)^{1/2}$: "The optimal value of $\alpha$ is $\alpha\approx0.584$ and the maximal value
  of the regret corresponds to $|p_1-p_2|\approx3.78(D/N)^{1/2}$ with additional requirement that
  $p_1,p_2$ are close to 0.5."
- **Theorem 2, §1, p. 2: quoted from Kolnogorov [12] (no proof here).** "In [12] the estimates (2) are
  improved as follows. Theorem 2. The following estimate of the minimax risk (1) holds for Gaussian
  two-armed bandit $\lim_{N\to\infty}(DN)^{-1/2}R^{(0)}_N(\Theta)=r_0$ (3) with $r_0\approx0.637$."
  [12] = A. V. Kolnogorov, *Contributions to the Asymptotic Minimax Theorem for the Two-Armed Bandit
  Problem*, Int. J. Math. Comput. Simul. 10 (2016) 129–132 (see note Kol16). Remark 1: "In [11], [12]
  the case $D=1$ is considered. However, all reasonings can be easily extended to distributions with
  arbitrary $D$." The method of [11], [12] is described as: "according to the main theorem of the theory
  of games the minimax risk for Gaussian two-armed bandit is sought for as Bayesian one corresponding
  to the worst-case prior distribution"; "It is shown that the worst-case prior is symmetric and
  asymptotically uniform".
- **Remark 2, p. 2.** "The estimates (2) can be easily extended to Gaussian two-armed bandit with a
  glance that the maximal value of the regret corresponds to $|m_1-m_2|\approx3.78(D/N)^{1/2}$ in this
  case. ... The estimate (3) can be in turn extended to Bernoulli two-armed bandit by usage of parallel
  processing of data." (Asserted, not proved.)
- **Theorem 3, §2, p. 4: quoted from Juditsky et al. [16].** Mirror descent (Algorithm 1) with
  $\beta_n=\beta^*\{D(n+1)\}^{1/2}$, $\beta^*=(8/\log2)^{1/2}$, $D=0.25$:
  $R^{(1)}_N(\Theta)\le r_1^*\{D(N+1)\}^{1/2}$ with $r_1^*=4(2\log2)^{1/2}\approx4.710$; "approximately 7.39
  times worse than the estimate (3)". Monte Carlo: $r_1\approx2.0$ (p. 4).
- **Theorem 4, §3, p. 6 (proved).** For Algorithm 3 (Gaussian parallel MDA, $T$ fixed), the normalized
  loss does not depend on $N,M,p,\hat D$.
- **Theorem 5, §4, p. 8–9 (proof given; it ends "This proves theorem 4", a typo).** For Algorithm 4
  with Gaussian $\chi_t^{(\ell)}$, asymptotically the normalized loss does not depend on $N,M$.
- **Remarks 6, 7, pp. 6–9: stated without proof.** Limiting SDE descriptions of Algorithms 3 and 4:
  "However, we do not have a rigorous proof of this result." / "We do not have a rigorous proof of this
  result as well."
- Monte Carlo for the parallel MDA (§3): $r_2\approx1.1$ (p. 8).

Normalization: all constants are $(DN)^{-1/2}\times$ risk, $D$ the one-step variance ($D=0.25$ for
Bernoulli near $1/2$), i.e. $R/(\sigma\sqrt N)$.

## Techniques

Survey of the Vogel–Bather bounds and of Kolnogorov's game-theoretic (worst-case prior) approach, then
mirror descent (Juditsky, Nazin, Tsybakov, Vayatis [16]; idea credited to Nemirovski–Yudin [18]),
batched variants, invariance arguments by scaling (Theorems 4, 5), Monte Carlo estimation of
normalized regret.

## Where Incognita uses it

papers/P001-minimax-constant/: Main result (Context), Closest known, Attribution.
