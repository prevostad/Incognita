# BSH23: a general recipe for randomized bandit algorithms

| | |
|---|---|
| Work | Dorian Baudry, Kazuya Suzuki, Junya Honda, *A General Recipe for the Analysis of Randomized Multi-Armed Bandit Algorithms*, arXiv preprint, 2023 |
| Identifiers | arXiv 2303.06058 (v1 10 Mar 2023, v2 21 Dec 2023, v3 13 Nov 2024) |
| Read | arXiv:2303.06058v3 HTML, through extracts of a fetch tool (displays as returned by the tool, prose paraphrased): abstract; §1 (the $h$-moment families); (2); the titles of §4.1–4.5; §4.4 (the family $\mathcal F_{h,B}$, the corollary on MED); and, for P005 (Claude Opus 5.5 (revise, P005), 2026-11-17, through a search agent of the session, page images of the PDF): arXiv v3 PDF: §4.4 (assumptions on $h$, family (18)); §4.4.2 in full (family (20), Lemma 9, Corollary 6 and the paragraph after it); opening of §5 (family $\mathcal F^B_m$); App. A, p. 46 (sentence on centred conditions); App. D.5 in full, pp. 65–67; text search of the HTML version for "kurtosis", "scale", "ratio", "variance" |
| By, date | Claude Opus 5.5 (revise, P004), 2026-11-16; Claude Opus 5.5 (revise, P005), 2026-11-17 |

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

### The centred family (§4.4.2, App. D.5), read for P005

Notation of the source: $\mathcal P$ the laws on $\mathbb R$, $\mu_F$ the mean of $F$, $h$ a known positive convex
function with $h(|x|)/|x|^{1+\eta}\to+\infty$ for some $\eta>0$, $B>0$ known.

- **Family (20), §4.4.2 (p. 30)**, verbatim: "The centered case, i.e. considering a moment condition of the
  form $E_{X\sim F}[h(|X-E_{X\sim F}[X]|)]\le B$, is more challenging because in general the space of
  distributions is no more convex nor compact. To overcome this technical difficulty, we further impose
  the knowledge of a lower bound of the possible means $\mu^-\in\mathbb R$, and consider a family of
  distributions defined as follows,
  $\mathcal F^c_{h,B}=\{F\in\mathcal P: E_F[h(|X-\mu_F|)]<B,\ E_F[h(|X|)^{2+\varepsilon_F}]<+\infty \text{ for some } \varepsilon_F>0,\ \mu_F\ge\mu^-\}$."
- **Lemma 9 (p. 30)**, verbatim: "Assumption 2 holds on $\mathcal F^c_{h,B}$ for the divergence
  $D:(F,\mu)\mapsto K_{\inf}^{\mathcal F^c_{h,B}}(F,\mu)\mathbb 1(F\in\mathcal F)$." (Assumption 2 is the list of
  conditions (A1)–(A4) of the general recipe.)
- **Corollary 6 (Instance-dependent optimality of MED on $\mathcal F^c_{h,B}$) (p. 30)**, verbatim: "The version
  of MED implemented with the divergence $D$ presented in Lemma 9, and $a_n=0$ for all $n$, is
  asymptotically optimal on $\mathcal F^c_{h,B}$." Asymptotically optimal means (eq. (2)) that
  $\limsup_T\mathbb E[N_k(T)]/\log T\le1/K_{\inf}^{\mathcal F}(F_k,\mu^\star)$, matching the Burnetas–Katehakis bound.
  The paragraph after it gives bounded variance ($h(x)=x^2$) and a sub-Gaussian characterisation as
  examples, and says that MED is the first algorithm with regret guarantees for bounded variance.
- **App. D.5 (pp. 65–67)**: for the centred family (with the integrability condition centred, and a known
  lower bound $\mu_0^-$ on the means, "in order use arguments based on compactness", verbatim),
  $K_{\inf}^{\mathcal F}(F,\mu_1)=\inf_{\mu\in[\mu_1,+\infty)}K(F,\mu)$ with
  $K(F,\mu)=\inf_{G\in\mathcal F}\mathrm{KL}(F,G)$ s.t. $E_G[X]=\mu$, $E_G[h(|X-\mu|)]\le B$; for fixed location the
  dual is $K(F_n,\mu)=\max_{(\lambda_1,\lambda_2)\in\mathcal R}E_{F_n}[\log(1-\lambda_1(X-\mu)-\lambda_2(B-h(|X-\mu|)))]$ over
  $\mathcal R=\{(\lambda_1,\lambda_2)\in\mathbb R\times\mathbb R^+:\ \forall x,\ 1-\lambda_1(x-\mu)-\lambda_2(B-h(|x-\mu|))\ge0\}$. Writing
  $K(F,\mu)=K_{\inf}^{\mathcal F_{uc}}(F_{-\mu},0)$ (translation by $-\mu$, the uncentred family), they state that $K(F,\mu)$
  is increasing in $\mu\ge\mu_F$, so that the infimum over the location is attained at $\mu_1$:
  $K_{\inf}^{\mathcal F}(F,\mu)=K(F,\mu)$. Condition (A3) uses compactness of the laws of the family with means in
  $[\mu_0^-,\mu_1-\varepsilon]$, asserted by reference to Agrawal et al. (2020), Theorem 12.

## Techniques

Sufficient conditions on the sampling probabilities of a randomized algorithm and on the family
(Theorem 5), checked family by family. The proof of the general theorem was not read (P004); for
the centred family, App. D.5 was read in full (P005):

- Reduction of a centred (non-convex) moment class to an outer minimisation over the location of a convex
  fixed-location problem, then to a translate of the uncentred problem (App. D.5); not credited to an
  earlier work.
- The fixed-location dual comes from the uncentred dual restated as Theorem 4 (p. 64), credited to
  Agrawal, Juneja and Glynn (2020), Theorem 12 and Lemma 4.
- A known lower bound on the means is assumed to obtain compactness (App. D.5).
- No kurtosis, no scale parameter and no ratio of moments: every moment constraint is of the form
  $E\,h(\cdot)<B$ with $B$ known (text search and the pages read).

## Where Incognita uses it

- P004 (`sec:related`, paragraph "Heavy-tailed bandits"): MED optimal under a known $h$-moment bound,
  a different model from the semi-bounded one, where no bound is known.
- P004 (`oq:finite-mean`): Remark 1 and Appendix B.4 (read 2026-11-16 in the v3 PDF) are the
  precedent of a robust mean estimate as the reference of MED: a two-sided truncated mean
  $\frac1n\sum_iX_i\mathbb 1(|X_i|\le u_n)$, under a known bound $\mathbb E|X|^{1+\delta}\le B$, whose
  deviations below the mean are bounded by Bernstein's inequality; the proof of their Theorem 1
  does not use the form of the estimate.
- `papers/P005-bounded-kurtosis/`: related work (Table 1, "Non-convex information functions", "Closest
  related work", "Gap with the literature"), the remarks after `lem:G` and `lem:repr`, `oq:profiled`, the
  appendix "Sources of the techniques".
