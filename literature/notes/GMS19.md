# GMS19: Explore first, exploit next

| | |
|---|---|
| Work | A. Garivier, P. Ménard, G. Stoltz, *Explore First, Exploit Next: The True Shape of Regret in Bandit Problems*, Mathematics of Operations Research 44(2), 2019 |
| Identifiers | DOI 10.1287/moor.2017.0928, arXiv 1602.07182 |
| Read | abstract and introduction (arXiv v3); inequalities (6) and (11); arXiv v3 §2.1: (8), Remark 2, Lemma 1; Appendix A, Lemma 5. Not read: Sections 3–4 in full, conclusion |
| By, date | an agent for the owner (inequalities (6), (11)), 2026-10-31; Claude (abstract, introduction), 2026-11-13; Claude Opus 5.5 (role revise, P000: arXiv v3, (8), Lemma 1, Remark 2, Lemma 5 of Appendix A), 2026-11-14 |

## Results

- **(6), fundamental inequality.** For every random variable $Z \in [0,1]$ measurable with respect to the
  history up to $T$: $\sum_a \mathbb E_\nu[N_a(T)]\,\mathrm{KL}(\nu_a, \nu'_a) \ge \mathrm{kl}(\mathbb E_\nu Z, \mathbb E_{\nu'} Z)$,
  with kl the Bernoulli divergence. Proof: chain rule (equality) and data processing (inequality).
- **(8), §2.1, p. 7 (arXiv v3).** $\sum_{a}\mathbb E_{\underline\nu}[N_{\psi,a}(T)]\mathrm{KL}(\nu_a,\nu'_a)=\mathrm{KL}(\mathbb P^{I_T}_{\underline\nu},\mathbb P^{I_T}_{\underline\nu'})\ge\mathrm{kl}(\mathbb E_{\underline\nu}[Z],\mathbb E_{\underline\nu'}[Z])$.
- **Lemma 1, §2.1, p. 8 (arXiv:1602.07182v3; the numbering of the PDF, which may differ from the
  ar5iv rendering).** "Consider a measurable space $(\Gamma,\mathcal G)$ equipped with two distributions
  $\mathbb P_1$ and $\mathbb P_2$, and any $\mathcal G$–measurable random variable $Z:\Omega\to[0,1]$. We denote
  respectively by $\mathbb E_1$ and $\mathbb E_2$ the expectations under $\mathbb P_1$ and $\mathbb P_2$. Then,
  $\mathrm{KL}(\mathbb P_1,\mathbb P_2)\ge\mathrm{kl}(\mathbb E_1[Z],\mathbb E_2[Z])$." (The domain "$\Omega$" is as
  printed; $\Gamma$ is meant.) Proof: on $\Gamma\times[0,1]$ with the Lebesgue measure on the second
  factor, the event $E=\{(\gamma,x):x\le Z(\gamma)\}$ and Lemma 5.
- **Lemma 5, Appendix A, p. 20 (data processing).** "Consider a measurable space $(\Gamma,\mathcal G)$
  equipped with two distributions $\mathbb P_1$ and $\mathbb P_2$, any other $(\Gamma',\mathcal G')$ measurable
  space, and any random variable $X:(\Gamma,\mathcal G)\to(\Gamma',\mathcal G')$. Then,
  $\mathrm{KL}(\mathbb P_1^X,\mathbb P_2^X)\le\mathrm{KL}(\mathbb P_1,\mathbb P_2)$".
- **Remark 2, p. 7.** Credits [KCG16, Lemma 1] for (8) at a stopping time. KCG16's Lemma 1 is the
  form with events ($\sup_{\mathcal E\in\mathcal F_\sigma}d(\mathbb P_\nu(\mathcal E),\mathbb P_{\nu'}(\mathcal E))$), not
  with a $[0,1]$-valued $Z$.
- **(11).** $\mathrm{kl}(p, q) \ge p \log(1/q) - \log 2$.
- Section 3 (not read in full): lower bounds for small horizons, almost linear regret, under mild
  symmetry assumptions on the strategies.
- Section 4 (not read in full): a non-asymptotic lower bound for large horizons (Theorem 4.3) for
  uniformly super-fast convergent strategies, with a second-order term of order $-\log\log T$
  (Remark 4.4). The exact constants must be read in the paper before any use.

## Techniques

Change of measure written as a single inequality (data processing applied to the law of the
history), valid for any pair of instances on the same history; it also gives the distribution-free
$\sqrt{KT}$ lower bound and the Lai–Robbins bound as corollaries.

## Where Incognita uses it

Roadmaps StochasticBandits (F1–F3; KNOWN K2, K4, K5; directions D1, D3; it absorbed the draft
RegretShape) and BatchedBandits (known result 1). Paper `papers/P000-hy-unknown-imposed-grid/`:
node `cite:garivier2019explore-dataprocessing` (Lemma 1), Lemma `lem:onebatch`.
