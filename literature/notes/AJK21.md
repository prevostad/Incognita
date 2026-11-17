# AJK21: Regret minimization in heavy-tailed bandits

| | |
|---|---|
| Work | S. Agrawal, S. Juneja, W. M. Koolen, *Regret Minimization in Heavy-Tailed Bandits*, Proceedings of the 34th Conference on Learning Theory (COLT 2021), PMLR 134:26–62 |
| Identifiers | arXiv:2102.03734 (v1); PMLR v134 PDF (the version read on 2026-11-16) |
| Read | arXiv v1 (agent, roadmap draft, 2026-11-14): abstract, §1, §2 (3)–(4), §3 Algorithm 1 and (5), §3.1 Theorem 1, Corollary 2, Theorem 3, §3.2 Proposition 4. PMLR v134 PDF (Claude Opus 5.5, write-paper P005, 2026-11-16): abstract; §2 (1), (3)–(4); §3 Algorithm 1, (5); §3.1 Theorem 1, Corollary 2; §3.3 Proposition 5, Lemma 6 and the text around them; §3.5 (computational cost); §5 Conclusion (the four remarks); Appendix A Lemmas 7–8; Appendix B.1 Lemma 11, B.1.1 (proof of Proposition 5), Remark 12 |
| By, date | see the row above |

## Results

Statements copied from the PMLR text layer; formulas rebuilt in LaTeX with the paper's symbols. Here
$\mathcal L_B:=\{\eta\in\mathcal P(\mathbb R):\mathbb E_\eta|X|^{1+\epsilon}\le B\}$ ((1)), and
$\mathrm{KL}_{\inf}^{\mathcal L}(\eta,x):=\inf\{\mathrm{KL}(\eta,\kappa):\kappa\in\mathcal L,\ m(\kappa)\ge x\}$ ((3), a
**non-strict** inequality); arm 1 has the largest mean; $N_a(n)$ is the number of samples of arm $a$ in $n-1$
rounds.

- **Algorithm 1 (KLinf-UCB).** One sample per arm; then, repeatedly, compute
  $U_a(n)=\sup\{x\in\mathbb R:N_a(n)\,\mathrm{KL}_{\inf}(\hat\mu_a(n),x)\le g_a(n)\}$ for each arm, pick
  $A_n=\arg\max_aU_a(n)$ (ties arbitrary) and sample it for a batch of $B_j=\max\{1,\lceil\tilde\eta N_{A_n}(n)\rceil\}$
  trials. Equivalently (5): $U_a(n)=\max\{\mathbb E_\eta(X):\eta\in\mathcal L,\ N_a(n)\mathrm{KL}(\hat\mu_a(n),\eta)\le g_a(n)\}$.
- **Theorem 1.** "Let $T>K\ge2$, $\mu\in\mathcal L^K$, $\tilde\eta\ge0$, and
  $g_a(t)=\log(t)+2\log\log(t)+2\log(1+N_a(t))+1$. For each sub-optimal arm $a$,
  KLinf-UCB$(K,B,\epsilon,\tilde\eta,g_a(\cdot))$ has $\mathbb E(N_a(T))$ at most
  $(1+\tilde\eta)\Big(\frac{\log T}{\mathrm{KL}_{\inf}(\mu_a,m(\mu_1))}+\frac{3(\log T)^{2/3}(c'_\mu)^{1/3}}{2(\mathrm{KL}_{\inf}(\mu_a,m(\mu_1)))^{4/3}}+O((\log T)^{1/3})+O(\log\log(T))\Big)$."
  "$c'_\mu>0$ is a bandit instance-dependent constant."
- **Corollary 2.** "For $\mu\in\mathcal L^K$, $\tilde\eta\ge0$, and $g_a(t)=\log(t)+2\log\log(t)+2\log(1+N_a(t))+1$,
  KLinf-UCB, with inputs $(K,B,\epsilon,\tilde\eta,g_a(\cdot))$ is asymptotically optimal up to a factor of
  $(1+\tilde\eta)$, i.e., $\limsup_{T\to\infty}\frac{\mathbb E(N_a(T))}{\log(T)}\le\frac{1+\tilde\eta}{\mathrm{KL}_{\inf}(\mu_a,m(\mu_1))}$."
- **Proposition 5.** "For $x\ge0$, $b\in[K]$,
  $\mathbb P\big(\exists n\in\mathbb N:N_b(n)\,\mathrm{KL}_{\inf}(\hat\mu_b(n),m(\mu_b))-1-2\log(1+N_b(n))\ge x\big)\le e^{-x}$."
- **Lemma 6.** "For $\mu\in\mathcal L^K$, $0<\delta<\min_{a\ne1}\mathrm{KL}_{\inf}(\mu_a,m(\mu_1))$, and $b\in[K]$, there
  exists $c_\mu>0$ such that $\mathbb P\big(\mathrm{KL}_{\inf}(\hat\mu_{b,s},m(\mu_1))\le\mathrm{KL}_{\inf}(\mu_b,m(\mu_1))-\delta\big)\le e^{-sc_\mu\delta^2}$."
- **Lemma 7 (dual, from Agrawal et al. 2020a, Theorem 12).** For $\eta\in\mathcal P(\mathbb R)$ and $|x|^{1+\epsilon}<B$,
  $\mathrm{KL}_{\inf}(\eta,x)=\max_{(\lambda_1,\lambda_2)\in R(x,B)}\mathbb E_\eta\log\big(1-(X-x)\lambda_1-(B-|X|^{1+\epsilon})\lambda_2\big)$,
  with an explicit compact region $R(x,B)\subset[0,\infty)^2$ (Lemma 8); the maximiser is unique, and an
  optimal primal law has at most one atom outside $\mathrm{Supp}(\eta)$, where the dual integrand vanishes.
- **Lemma 11 (from Agrawal et al. 2020b, Lemma E.1).** "Let $\Lambda\subseteq\mathbb R^d$ be a compact and convex
  subset and let $q$ be the uniform distribution on $\Lambda$. Let $g_i:\Lambda\to\mathbb R$ be any series of
  exp-concave functions. Then $\max_{\lambda\in\Lambda}\sum_{i=1}^Tg_i(\lambda)\le\log\mathbb E_{\lambda\sim q}e^{\sum_{i=1}^Tg_i(\lambda)}+d\log(T+1)+1$."
- **Proof of Proposition 5 (B.1.1).** The dual of Lemma 7 at $x=m(\mu_b)$ writes $N_b\mathrm{KL}_{\inf}$ as a maximum of
  sums of logarithms of i.i.d. variables with mean at most 1; the mixture over the uniform prior on
  $R(m(\mu_b),B)$ is a nonnegative supermartingale; Lemma 11 and Ville's inequality conclude.
- **§3.5.** Computing the index of an arm costs time linear in its number of samples, so the unbatched
  algorithm ($\tilde\eta=0$) has a total cost quadratic in the number of rounds; the batched one is almost
  linear.
- **§5, third remark.** Extending the approach to a bounded *centred* moment is posed as a natural
  problem; such a constraint "is no longer a convex constraint in the distribution", so the class and
  the $\mathrm{KL}_{\inf}$ problem become non-convex, and handling this "would require development of more
  nuanced techniques". (In arXiv v1 the remark has only its first sentence.)
- **§5, fourth remark, and Remark 12.** The concentration proof of Proposition 5 only uses that the
  conditional mean is fixed and the conditional moment bounded.

## Techniques

- Dual formula of $\mathrm{KL}_{\inf}$ under a moment constraint, from Lagrangian duality (Lemma 7, credited to
  Agrawal et al. 2020a).
- Mixture of the supermartingales $\prod_i(\text{dual integrand})$ over a uniform prior on the compact
  dual region, with the universal-portfolio bound $d\log(T+1)+1$ (Lemma 11, credited to Agrawal et al.
  2020b and to universal portfolios), and Ville's inequality: an anytime upper deviation for
  $N\,\mathrm{KL}_{\inf}$ at the true mean (Proposition 5).
- Regret decomposition of KL-UCB type with the threshold $\log t+2\log\log t+2\log(1+N)+1$ (§3.3).

## Where Incognita uses it

- `papers/P005-bounded-kurtosis/`: node `cite:AJK21-cor2`; the algorithm and its threshold (Section 2),
  the comparison (Introduction), the proof of the upper deviation (technique credited), Appendix
  "Sources of the techniques".
- `roadmaps/StochasticBandits/KNOWN.md`: K17, K50.
