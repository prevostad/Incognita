# Kol17: Batch data processing and Gaussian two-armed bandit

| | |
|---|---|
| Work | A. V. Kolnogorov, *Batch Data Processing and Gaussian Two-Armed Bandit*, arXiv preprint, 2017 (6 pages, 1 figure; math.ST) |
| Identifiers | arXiv 1704.03631 (v1, 12 Apr 2017, the only version); DOI 10.48550/arXiv.1704.03631. No journal-ref on the arXiv page; a journal or proceedings version was not searched for |
| Read | whole (arXiv:1704.03631v1, PDF, pp. 1–6, including Appendix A), from https://arxiv.org/pdf/1704.03631; metadata from https://arxiv.org/abs/1704.03631 |
| By, date | Claude Opus 5.5 (revise, P001), 2026-11-15 |

## Results

Setting (§1): Gaussian two-armed bandit with unit variances, $\Theta=\{\theta:|m_1-m_2|\le2C\}$, loss
$L_N(\sigma,\theta)=N(m_1\vee m_2)-\mathbb E_{\sigma,\theta}(\sum_{n=1}^N\xi_n)$ (1), minimax risk
$R^M_N(\Theta)=\inf_\Sigma\sup_\Theta L_N(\sigma,\theta)$ (2), Bayesian risk (4); batches of $M$ items.

- **(3), §1, p. 2: Vogel and Bather, quoted (not proved here).** "However, an asymptotic minimax theorem
  was proved in Vogel (1960) using some indirect techniques. This theorem states that the following
  estimates hold as $N\to\infty$: $0.612\le(DN)^{-1/2}R^M_N(\Theta)\le0.752$, (3) where $D=0.25$ is the
  maximal variance of one-step income. Presented here the lower estimate was obtained in Bather (1983).
  The maximal value of expected losses corresponds to $|p_1-p_2|\approx3.78(D/N)^{1/2}$ with additional
  requirement that $p_1,p_2$ are close to 0.5." (Context: Bernoulli bandit, $\Theta=\{0\le p_\ell\le1\}$.)
- **(5), §1, p. 2: minimax = Bayes, assumed.** "Minimax risk (2) and Bayesian risk (4) are related by
  the main theorem of the theory of games as follows: $R^M_N(\Theta)=R^B_N(\lambda_0)=\sup_\lambda R^B_N(\lambda)$,
  (5) where $\lambda_0$ is called the worst-case prior distribution." No proof or hypotheses given.
- **(10), §3, p. 3: worst-case prior, asserted.** Invariance of the Bayes risk under swapping arms and
  common shifts: "Like in Kolnogorov (2010), one can prove that the following transformations ... do
  not change the Bayesian risk"; then "Namely, asymptotically the worst-case prior distribution density
  can be chosen the following one: $\nu_a(m,v)=\kappa_a(m)\rho(v)$, (10) where $\kappa_a(m)$ is the uniform
  density on the interval $|m|\le a$, $\rho(v)$ is a symmetric density ... on the interval $|v|\le C$ and
  $a\to\infty$." (with $m_1=m+v$, $m_2=m-v$). Argued from concavity of the Bayes risk in the prior; no
  formal proof in this paper.
- **Theorem 1, §3, p. 3–4 (proved, Appendix A).** For the prior (10), after turn-by-turn play for
  $n\le2M$, the strategy is given by the recursion (11)–(14) in the state $(U,n_1,n_2)$,
  $U=(X_1n_2-X_2n_1)n^{-1}$, and the Bayesian risk by (15). "Proof of theorem is presented in Appendix A."
  (The appendix is headed "PROOF OF THEOREM 2" but derives (12) and (15), i.e. Theorem 1.)
- **Theorem 2, §4, p. 4 (proved by change of variables).** The invariant recursion (16)–(20) in
  $(u,t_1,t_2)$ with $\varepsilon=MN^{-1}$, $u=UN^{-1/2}$, $w=vN^{1/2}$, on the "close" set
  $\Theta_N=\{|m_1-m_2|\le2cN^{-1/2}\}$. "Proof. Is done by implementation of described above change of
  variables."
- **Theorem 3, §4, p. 4: stated without proof.** The paper says: "The following theorem is given without
  proof." Statement (verbatim): "Theorem 3. For all $u,t_1,t_2$, for which the solution to equation
  (16)-(18) is well defined, there exist limits $r(\varrho;u,t_1,t_2)=\lim_{\varepsilon\to0}r_\varepsilon(\varrho;u,t_1,t_2)$
  which can be extended by continuity to all $u,t_1,t_2$ ($t_1>0$, $t_2>0$, $t_1+t_2<1$). These limits are
  uniformly bounded and satisfy Lipschitz conditions in $u$. The minimax risk on the set of close
  expectations $\Theta_N=\{|m_1-m_2|\le2cN^{-1/2}\}$ satisfies the equality
  $\lim_{N\to\infty}N^{-1/2}R^M_N(\Theta_N)=\sup_\varrho r(\varrho;0,0,0)$, (21) where
  $r(\varrho;0,0,0)=\lim_{\varepsilon\to0}r(\varrho;0,\varepsilon,\varepsilon)$."
- **PDE (26)–(27), §4, p. 4: derived formally.** Under the assumption "Assume that $r_\varepsilon(u,t_1,t_2)$
  has continuous partial derivatives of proper orders", a Taylor expansion (22)–(25) gives "(as
  $\varepsilon\downarrow0$) the partial differential equation:
  $\min_{\ell=1,2}\big(\frac{\partial r}{\partial t_\ell}+\frac{t_{\bar\ell}^2}{2t^2}\times\frac{\partial^2r}{\partial u^2}+g^{(\ell)}(u,t_1,t_2)\big)=0$
  (26) with $\bar\ell=3-\ell$. Initial and boundary conditions take the form
  $r(u,t_1,t_2)\|_{t_1+t_2=1}=0$, $r(\infty,t_1,t_2)=r(-\infty,t_1,t_2)=0$. (27)" No convergence or
  well-posedness proof.
- **§5, p. 5: numerics.** With $\varepsilon=0.02$ (50 batches) and $\varrho$ two-point at $w=\pm d$: "The
  maximum is approximately equal to 0.65 at $d\approx1.6$." Limit: computed "according to (16), (23),
  (24), (27) with $\varepsilon=0.001$ for $|u|\le2.3$ ... $\Delta u=0.023$, $\Delta t=2000^{-1}$ ... For
  $0.5\le d\le2.5$ maximum of $2d\varepsilon+r(\varrho;0,\varepsilon,\varepsilon)$ was approximately equal
  to 0.637 at $d\approx1.57$. Hence, the minimax risk corresponding to batch processing in 50 stages is
  approximately 2% larger than the limiting value." Only two-point symmetric priors are searched.

Normalizations: 0.612 and 0.752 are $(DN)^{-1/2}R^M_N$ for the Bernoulli bandit with $D=0.25$, i.e.
$R/(\sigma\sqrt N)$ with $\sigma=1/2$; 0.65 and 0.637 are $N^{-1/2}\times$ risk for unit variance, i.e.
also $R/(\sigma\sqrt N)$. $d$ is the half-gap in units of $N^{-1/2}$ ($w=vN^{1/2}$, $m_1-m_2=2v$): the
worst gap is $|m_1-m_2|\approx3.14\,\sigma/\sqrt N$ (Vogel's Bernoulli value: $3.78(D/N)^{1/2}$).

## Techniques

Minimax risk computed as a Bayes risk for a worst-case prior (main theorem of game theory, taken as
given); reduction of the prior by symmetry and translation invariance to uniform-in-$m$ times symmetric
$\rho(v)$ (§3, credited to Kolnogorov (2010)); sufficient statistic $(U,n_1,n_2)$; diffusion scaling
$\varepsilon=M/N$, $u=UN^{-1/2}$, $w=vN^{1/2}$ (§4); formal Taylor expansion to a second-order HJB-type
PDE (22)–(26); finite-difference solution (§5). Earlier results credited to Kolnogorov (2010), (2012),
(2015) ("Here we combine and compare them").

## Where Incognita uses it

papers/P001-minimax-constant/: Main result (Context), Closest known, Attribution.
