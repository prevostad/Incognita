# HZT26: Free exploration for regret minimisation

| | |
|---|---|
| Work | Y. Hou, Z. Zhong, V. Y. F. Tan, *On the Benefits of Free Exploration for Regret Minimization in Multi-Armed Bandits*, arXiv preprint, v1 of 25 May 2026 (55 pp., "Under review" on p. 1) |
| Identifiers | arXiv 2605.25789 (v1, the only version on the arXiv record read 2026-11-17) |
| Read | arXiv:2605.25789v1 PDF, page images: pp. 1–9 (abstract; §1, §1.1–1.3, Table 1; §2; §3, Definitions 1–3, (2)–(6), Remark 4; Algorithm 1 UFE); p. 13 (Remark 8, Corollaries 9–10, instance (12)); pp. 14–17 (§5: Lemma 11, (13)–(14), Figure 4, Theorem 12 with (15) and the discussion after it, §5.2 Corollary 13); pp. 28–29 (end of App. C, App. D.1 proof of Lemma 11, start of D.2); pp. 31–33 (end of D.2, start of D.3); pp. 38, 45 (glanced). The arXiv HTML rendering was used only for the list of appendix headings. Not read: §4 (pp. 9–12, Theorems 6–7 and the definition of $\overline{\mathfrak R}$), Theorem 14 (App. B), the rest of the appendices |
| By, date | Claude Opus 5.5 (revise, P008), 2026-11-17 |

## Setting (§2–§3)

- $L$ items, laws $\nu_i$ supported on $[0,1]$ from a single-parameter exponential family ("each $\nu_i$ is
  parameterized by its mean $\mu_i$ when the distribution family is specified"), variances bounded below by
  $\sigma^2_{\min}$; $\mu_1\ge\mu_2\ge\dots\ge\mu_L$. One horizon $T$; the first $T_{\mathrm{FE}}$ steps are the free-exploration
  (FE) phase, played by the same policy (adaptive, $\pi_{\mathrm{FE}}=(\pi_t)_{t=1}^{T_{\mathrm{FE}}}$), whose pulls are free; the
  regret counts only the RA phase:
  $R_{T_{\mathrm{FE}}+1:T}(\pi;\nu):=(T-T_{\mathrm{FE}})\cdot\mu_1-\mathbb E\Bigl[\sum_{t=T_{\mathrm{FE}}+1}^T\mu_{i^\pi_t}\Bigr]$.
  FE samples come from the same laws as the RA samples (no bias). $T_{i,t}$ counts pulls of $i$ up to $t$, FE
  included. The regime of interest is $T_{\mathrm{FE}}=g(T)$ with $T_{\mathrm{FE}}=O(\ln T)\cap\omega(1)$.
- Table 1 places CL24's MIN-UCB under "Warm-start RM" with a "Fixed/exogeneous" history and no adaptive FE.

## Results

- **Definition 1.** "A policy $\pi$ is called consistent over a class of bandit instances $\Lambda$ if for all
  $\nu\in\Lambda$ and $p>0$, $R_{T_{\mathrm{FE}}+1:T}(\pi;\nu)=o(T^p)$."
- **(2)** (§3, stated via Lemma 11): for any consistent policy and suboptimal $i$,
  $\liminf_{T\to\infty}\frac{\mathbb E[T_{i,T}]}{\ln T}\geq\frac{1}{D_{\mathrm{kl}}(\nu_i,\nu_1)}$.
- **(3), oracle saved regret.** $\mathrm{Save}^*(\nu,T_{\mathrm{FE}}):=\Delta_{i_{\mathrm{FE}}}\Bigl(T_{\mathrm{FE}}-\sum_{i=i_{\mathrm{FE}}+1}^L\frac{\ln T}{D_{\mathrm{kl}}(\nu_i,\nu_1)}\Bigr)+\sum_{i=i_{\mathrm{FE}}+1}^L\frac{\Delta_i\ln T}{D_{\mathrm{kl}}(\nu_i,\nu_1)}$,
  where $i_{\mathrm{FE}}:=\max\Bigl\{j\in[K]:\sum_{i=j}^L\frac{\ln T}{D_{\mathrm{kl}}(\nu_i,\nu_1)}\geq T_{\mathrm{FE}}\Bigr\}$ (as printed, $[K]$).
  On p. 7: $\underline{\mathfrak R}(\pi,\nu):=\liminf_{T\to\infty}\frac{R_{T_{\mathrm{FE}}+1:T}(\pi;\nu)}{\ln T}\geq\sum_{i:\Delta_i>0}\frac{\Delta_i}{D_{\mathrm{kl}}(\nu_i,\nu_1)}-\limsup_{T\to\infty}\frac{\mathrm{Save}^*(\nu,T_{\mathrm{FE}})}{\ln T}$
  "with $\pi^*_{\mathrm{FE}}$ as the FE policy".
- **(4).** $\widehat{\mathrm{Save}}(\pi;\nu,T_{\mathrm{FE}}):=\sum_{i:\Delta_i>0}\Delta_i\cdot\min\Bigl\{T_{i,T_{\mathrm{FE}}},\frac{\ln T}{D_{\mathrm{kl}}(\nu_i,\nu_1)}\Bigr\}$.
- **Definition 2 ($\alpha$-saving).** "Given $\alpha\in(0,1)$ and free exploration budget $T_{\mathrm{FE}}$, a policy $\pi$ is an
  $\alpha$-saving policy over a class of instance $\Lambda$ if for any instance $\{\nu_i\}_{i\in[L]}\in\Lambda$,
  $\liminf_{T\to\infty}\frac{\mathbb E[\widehat{\mathrm{Save}}(\pi;\nu,T_{\mathrm{FE}})]}{\mathrm{Save}^*(\nu,T_{\mathrm{FE}})}\geq\alpha$." (5)
- **Definition 3 ($(\alpha,\beta)$-probably saving).** "Given $\alpha,\beta\in(0,1)$ and free exploration budget $T_{\mathrm{FE}}$,
  a policy $\pi$ is an $(\alpha,\beta)$-probably-saving policy if for any instance $\{\nu_i\}_{i\in[L]}$ in the instance
  class $\Lambda$, as $T\to\infty$,
  $\mathbb P\bigl(\widehat{\mathrm{Save}}(\pi;\nu,T_{\mathrm{FE}})\geq\alpha\cdot\mathrm{Save}^*(\nu,T_{\mathrm{FE}})\bigr)\geq1-O(T^{-\beta})$." (6)
  (The proofs instantiate the failure probability as $T^{-\beta}/2.4$, App. D.2.)
- **§5.1.** $\widetilde{\mathrm{Save}}(\pi;\nu,T_{\mathrm{FE}}):=\sum_{i:\Delta_i>0}\Delta_i\min\Bigl\{\frac{\ln T}{D_{\mathrm{kl}}(\nu_i,\nu_1)},\mathbb E[T_{i,T_{\mathrm{FE}}}]\Bigr\}$.
- **Lemma 11.** "For any consistent algorithm $\pi$, given instance $\nu$ and free exploration budget
  $T_{\mathrm{FE}}=o(T)$, the expected number of pulls of item $i$ satisfies
  $\liminf_{T\to\infty}\frac{\mathbb E[T_{i,T}]}{\ln T}\geq\frac{1}{D_{\mathrm{kl}}(\nu_i,\nu_1)}$.
  Furthermore, $\underline{\mathfrak R}(\pi,\nu)\geq\sum_{i:\Delta_i>0}\frac{\Delta_i}{D_{\mathrm{kl}}(\nu_i,\nu_1)}-\limsup_{T\to\infty}\frac{\widetilde{\mathrm{Save}}(\pi;\nu,T_{\mathrm{FE}})}{\ln T}$."
- **Two-valued instance, (13)–(14).** $L_{\mathrm g}$ good items (mean $\mu_1$), $L_{\mathrm b}=L-L_{\mathrm g}$ bad ones (mean
  $\mu_L$); alternatives $\nu^{(j)}$, $j=1,2,3$, with means
  $\mu^{(1)}_i=\frac{\mu_1+\mu_L-\xi_1}{2}\mathbb 1\{i\in[L_{\mathrm g}]\}+\frac{\mu_1+\mu_L+\xi_1}{2}\mathbb 1\{i\notin[L_{\mathrm g}]\}$,
  $\mu^{(2)}_i=\mu_1\mathbb 1\{i\in[L'_{\mathrm g}]\}+(\mu_L-\xi_2)\mathbb 1\{i\in(L'_{\mathrm g},L_{\mathrm g}]\}+\mu_L\mathbb 1\{i\notin[L_{\mathrm g}]\}$,
  $\mu^{(3)}_i=(\mu_L-\xi_3)\mathbb 1\{i\in[L_{\mathrm g}]\}+\mu_L\mathbb 1\{i\notin[L_{\mathrm g}]\}$, (13)
  "where $\xi_1,\xi_2,\xi_3,L'_{\mathrm g}<L_{\mathrm g}$ are subject to the conditions
  $\xi_2\geq\frac{1-\alpha}{2\alpha-1}\Delta_L$, $\frac{(L_{\mathrm g}-L'_{\mathrm g})\ln T}{D_{\mathrm{kl}}(\nu^{(2)}_{L_{\mathrm g}},\nu^{(2)}_1)}\geq T_{\mathrm{FE}}$ and
  $\frac{L_{\mathrm g}\ln T}{D_{\mathrm{kl}}(\nu^{(j)}_1,\nu^{(j)}_L)}\geq T_{\mathrm{FE}}$ for $j=1,3$."
  With $T_{\mathrm{FE}}=\frac{\gamma L_{\mathrm b}\ln T}{D_{\mathrm{kl}}(\nu_L,\nu_1)}$:
  $\underline r_1:=\frac{\beta D_{\mathrm{kl}}(\nu_L,\nu_1)}{L_{\mathrm b}\max\{D_{\mathrm{kl}}(\nu_1,\nu^{(1)}_1),D_{\mathrm{kl}}(\nu_L,\nu^{(1)}_L)\}}$,
  $\underline r_2:=\min\Bigl\{1+\frac{\beta D_{\mathrm{kl}}(\nu_L,\nu_1)}{L_{\mathrm b}D_{\mathrm{kl}}(\nu_1,\nu^{(3)}_1)},\frac{\alpha}{1-\alpha}\Bigr\}$. (14)
- **Theorem 12.** "(i) If $\pi$ is an $(\alpha,\beta)$-probably-saving algorithm on instances $\nu$ and
  $\{\nu^{(j)}\}_{j\in[3]}$ with $\alpha>1/2$, then
  $$\overline{\mathfrak S}(\pi,\nu):=\limsup_{T\to\infty}\frac{\widetilde{\mathrm{Save}}(\pi;\nu,T_{\mathrm{FE}})}{\ln T}\leq\begin{cases}N.A.,&\gamma<\underline r_1,\\ \Delta_L\Bigl(\frac{\gamma L_{\mathrm b}}{D_{\mathrm{kl}}(\nu_L,\nu_1)}-\frac{\beta\ln T}{D_{\mathrm{kl}}(\nu_1,\nu^{(3)}_1)}\Bigr),&\underline r_1\leq\gamma\leq\underline r_2,\\ \Delta_L\cdot\frac{L_{\mathrm b}\ln T}{D_{\mathrm{kl}}(\nu_L,\nu_1)},&\gamma>\underline r_2,\end{cases}$$
  where N.A. indicates $\pi$ is not an $(\alpha,\beta)$-probably-saving algorithm for the given $T_{\mathrm{FE}}$ (or
  equivalently $\gamma$).
  (ii) Furthermore, when $\nu^{(2)}$ exists, then for $\underline r_1\leq\gamma\leq1$,
  $$\overline{\mathfrak S}(\pi,\nu)\leq\Delta_L\cdot\Bigl(\frac{\gamma L_{\mathrm b}}{D_{\mathrm{kl}}(\nu_L,\nu_1)}-\frac{\zeta\cdot L_{\mathrm g}\cdot\beta}{D_{\mathrm{kl}}(\nu_{L_{\mathrm g}},\nu^{(2)}_{L_{\mathrm g}})}\Bigr),\qquad(15)$$
  where $\zeta=\min\Bigl\{\frac{D_{\mathrm{kl}}(\nu_L,\nu_1)}{\gamma L_{\mathrm b}\cdot D_{\mathrm{kl}}(\nu^{(2)}_{L_{\mathrm g}},\nu^{(2)}_1)},1\Bigr\}$."
  (Copied as printed, including the $\ln T$ factors in the second and third cases of (i), inside a bound
  on a quantity already divided by $\ln T$.) Combined with Lemma 11, this bounds $\underline{\mathfrak R}$ from below.
  Proof in App. D.3 (only its outline, p. 32, read).
- **Corollary 13** (gap between UFE-KLUCB-H and any consistent $(\alpha,\beta)$-probably saving policy on
  instance (12): Bernoulli, $\mu_i=\frac12+\varepsilon$ for $i\in[L_{\mathrm g}]$, $\frac12$ otherwise) read, not copied.

## Techniques

- **Lemma 11 (App. D.1)**: "extends the standard argument of Lattimore and Szepesvári (2020, Theorem 16.2)":
  one item $j$ moved to $\mu'_j>\mu_1$ with $D_{\mathrm{kl}}(\nu_j,\nu^{(j)}_j)\le D_{\mathrm{kl}}(\nu_j,\nu_1)+\xi$; divergence
  decomposition (LS20, Lemma 15.1) and Bretagnolle–Huber (LS20, Theorem 14.2) with the event
  $\{T_{j,T}>T/2\}$; the FE pulls are inside $T_{i,T}$, and $T_{\mathrm{FE}}=o(T)$ is used through the factor
  $\frac{T-2T_{\mathrm{FE}}}{2}$. So the FE samples count like online pulls in the total.
- **Theorem 12**: multi-item perturbations (several items moved at once) and Kaufmann et al. (2016,
  Lemma 1) applied to the FE counts $T_{i,T_{\mathrm{FE}}}$ under the $(\alpha,\beta)$-probably saving event.

Remark (not in the source): the FE samples are drawn from the target laws (no drift), so Lemma 11 is
the case $L_a=0$ of a bound like P008's with the free samples counted in $N_a$; the paper's new lower
bounds (Theorem 12) concern how much regret the FE phase can save, under the $(\alpha,\beta)$-probably
saving restriction.

## Where Incognita uses it

`papers/P008-transfer-lower-bound/` (revision of 2026-11-17, related work).
