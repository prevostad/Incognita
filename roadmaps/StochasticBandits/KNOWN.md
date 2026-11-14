Reviewed by owner: 2026-11-14 (approved in a conversation with Claude; the entries were written by an agent from the published literature and were not checked one by one by the owner)

# KNOWN: roadmap StochasticBandits

What is already known in this roadmap, **negative results, impossibilities and open problems
included**, so that agents neither propose nor re-derive it. This list contains **only published
results**, read by the agent who wrote it (Claude Opus 5.5, 2026-11-14), in the parts recorded in
[SOURCES.md](SOURCES.md); it contains no result of the owner. The owner may add his own entries
(dead ends, conjectures, directions judged uninteresting) at any time. The sources of direction
D19 (the constant of the minimax regret) were not read for this list: see D19 in
[ROADMAP.md](ROADMAP.md).

For agents: read every entry before writing or refereeing a paper. A paper answered by an entry, or
by a short combination of entries, is not written (and is rejected if submitted). A paper that
extends an entry cites its id and says exactly what is new. Cite entries by id (`K12`). This list is
not exhaustive: search the literature that cites these sources before claiming novelty.

## Format of an entry

```
- **K<n>.** [status] <Statement: classes of instances and algorithms, criterion, every algorithm
  by its formula.> — *Source:* [KEY, exact part]. — *Settles:* <one line>.
```

- Status: `[published]` a result of the published literature, read in the source as recorded in
  [SOURCES.md](SOURCES.md) (the version read is named when it is a preprint; theorem numbers refer to it);
  the template's `[Lean]`, `[paper]`, `[sketch]`, `[belief]` are for the owner's entries. A part
  that could not be read is marked `(to be checked)`.
- Statements are transcribed in the source's notation, translated to the roadmap's conventions
  where noted ($\mathcal K_{\inf}$ with a strict inequality; $N_a(T)$ pulls of $a$ in the first $T$
  rounds; $\Delta_a$ gap; $m^\star$ or $\mu^\star$ best mean). "Consistent" is [LS, Definition 16.1]
  unless the entry says otherwise.
- "In Lean" names a declaration of LMLExplore at Incognita's pinned revision `b4e0ab9`.
- Numbers K1, K2, … are never reused or renumbered; a withdrawn entry stays, marked `withdrawn`.

## Positive results

### Lower bounds, unstructured classes

- **K1.** [published] Let $\mathcal E = \mathcal M_1\times\dots\times\mathcal M_k$ be an unstructured
  class of laws with finite means and $\pi$ consistent over $\mathcal E$. For every
  $\nu = (P_i)_i\in\mathcal E$: $\liminf_n R_n/\log n \ge \sum_{i:\Delta_i>0}\Delta_i/d_{\inf}(P_i,\mu^\star,\mathcal M_i)$
  with $d_{\inf}(P,\mu^\star,\mathcal M) := \inf_{P'\in\mathcal M}\lbrace \mathrm{KL}(P,P') : \mu(P') > \mu^\star\rbrace$
  [LS, Theorem 16.2], and in count form $\liminf_n \mathbb E N_i(n)/\log n\ge 1/d_{\inf}$ (shown in the
  proof). [GMS19, Theorem 1] proves the count form for every model $\mathcal D$ and every
  uniformly fast convergent strategy ($\mathbb E N_a(T) = o(T^\alpha)$ for all $\alpha\in(0,1]$ and
  all suboptimal $a$, [GMS19, Definition 1]). In Lean: LMLExplore
  `eventually_mul_log_le_integral_pullCount_of_isConsistent`,
  `eventually_mul_log_le_integral_regret_of_isConsistent`. — *Source:* [LS, Definition 16.1,
  Theorem 16.2]; [GMS19, Theorem 1]; originals [LR85] and [BK96] (to be checked: not read). —
  *Settles:* the first-order lower bound in every unstructured class.
- **K2.** [published] **Fundamental inequality.** For every strategy, all instances $\nu,\nu'$ on the
  same arms and every $Z\in[0,1]$ measurable with respect to the history up to $T$:
  $\sum_a\mathbb E_\nu[N_a(T)]\,\mathrm{KL}(\nu_a,\nu'_a)\ge\mathrm{kl}(\mathbb E_\nu Z,\mathbb E_{\nu'}Z)$
  [GMS19, (6)], through the equality
  $\sum_a\mathbb E_\nu[N_a(T)]\,\mathrm{KL}(\nu_a,\nu'_a) = \mathrm{KL}(P^{I_T}_\nu,P^{I_T}_{\nu'})$ of the laws of
  the history (chain rule) followed by data processing [GMS19, (8)]; [GMS19, Remark 2] notes that
  (8) holds at stopping times. Stopping-time form [KCG16, Lemma 1]: if $\nu_a$ and $\nu'_a$ are
  mutually absolutely continuous for every $a$ and $\sigma$ is an almost surely finite stopping time,
  $\sum_a\mathbb E_\nu[N_a(\sigma)]\,\mathrm{KL}(\nu_a,\nu'_a)\ge\sup_{E\in\mathcal F_\sigma}\mathrm{kl}(P_\nu(E),P_{\nu'}(E))$. Also
  [GMS19, (11)]: $\mathrm{kl}(p,q)\ge p\log(1/q)-\log 2$. — *Source:* [GMS19, (6), (8), Remark 2,
  (11)]; [KCG16, Lemma 1]. — *Settles:* the reusable change of measure; LMLExplore has the
  divergence decomposition [LS, Lemma 15.1] and Bretagnolle–Huber, not this form (F1).
- **K3.** [published] **Finite-time lower bounds.** If $\nu,\nu'$ differ only in arm $i$, $i$ is
  suboptimal in $\nu$ and uniquely optimal in $\nu'$, and $\lambda := \mu_i(\nu')-\mu_i(\nu)$, then for
  every policy
  $\mathbb E_\nu[T_i(n)]\ge\big(\log(\min\lbrace\lambda-\Delta_i,\Delta_i\rbrace/4)+\log n-\log(R_n(\nu)+R_n(\nu'))\big)/\mathrm{KL}(P_i,P'_i)$
  [LS, Lemma 16.3]. For Gaussian bandits with unit variance: if $R_n(\nu')\le Cn^p$ for all $n$ in a set
  $N$ and all $\nu'$ with means in $\prod_i[\mu_i,\mu_i+2\Delta_i]$, then for every $\varepsilon\in(0,1]$
  and $n\in N$,
  $R_n(\nu)\ge\frac{2}{(1+\varepsilon)^2}\sum_{i:\Delta_i>0}\big((1-p)\log n+\log(\varepsilon\Delta_i/(8C))\big)/\Delta_i$
  [LS, Theorem 16.4] (as read in the text extraction; LMLExplore states it with a positive part).
  In Lean: LMLExplore
  `log_div_le_integral_pullCount`, `le_integral_regret_gaussianBandit` (with $2$ and $4C$ in place of
  $4$ and $8C$). — *Source:* [LS, Lemma 16.3, Theorem 16.4]. — *Settles:* the finite-time analogue of
  K1 under a worst-case constraint, for Gaussian product classes.
- **K4.** [published] **Initial (almost linear) regime** [GMS19, Section 3], for every model
  $\mathcal D$ and $T\ge 1$. (i) If the strategy is *smarter than the uniform strategy*
  ($\mathbb E N_{a^\star}(T)\ge T/K$ for every optimal arm $a^\star$, every instance, every $T$,
  [GMS19, Definition 2]), then for every arm $a$:
  $\mathbb E N_a(T)\ge\frac TK\big(1-\sqrt{2T\,\mathcal K_{\inf}(\nu_a,\mu^\star,\mathcal D)}\big)$; in
  particular $\mathbb E N_a(T)\ge T/(2K)$ when $T\le 1/(8\mathcal K_{\inf})$ [GMS19, Theorem 2].
  (ii) If it is *pairwise symmetric for optimal arms* (two optimal arms with the same law have
  exchangeable counts, [GMS19, Definition 3]), then for every suboptimal $a$ and optimal $a^\star$:
  either $\mathbb E N_a(T)\ge T/K$ or
  $\mathbb E\big[\max\lbrace N_a(T),1\rbrace/\max\lbrace N_{a^\star}(T),1\rbrace\big]\ge 1-2\sqrt{2T\,\mathrm{KL}(\nu_a,\nu_{a^\star})/K}$
  [GMS19, Theorem 3]. (iii) If it is moreover *monotonic* ([GMS19, Definition 4]), then
  $\sum_{a\notin\mathcal A^\star}\mathbb E N_a(T)\ge T\big(1-\frac{A^\star}{K}-\frac{A^\star\sqrt{2T\mathcal K^{\max}}}{K}-\frac{2A^\star T\mathcal K^{\max}}{K}\big)$,
  with $A^\star := |\mathcal A^\star(\nu)|$ and $\mathcal K^{\max} := \min_{w\in\mathcal W(\nu)}\max_{a^\star\in\mathcal A^\star}\mathrm{KL}(\nu_w,\nu_{a^\star})$
  ($\mathcal W(\nu)$ the worst arms); in particular the sum is at least $\frac T2(1-A^\star/K)$ for
  $T\le K/(8A^\star\mathcal K^{\max})$ [GMS19, Theorem 4]. — *Source:* [GMS19, Definitions 2–4,
  Theorems 2–4]. — *Settles:* the regret is almost linear before a horizon of order
  $1/\mathcal K$, for all bandit problems (not only well-chosen ones).
- **K5.** [published] **Second-order lower bound.** A model is *well behaved* if there are
  $\varepsilon_{\mathcal D}>0$ and $\omega_{\mathcal D}$ with
  $\mathcal K_{\inf}(\nu_a,x+\varepsilon,\mathcal D)\le\mathcal K_{\inf}(\nu_a,x,\mathcal D)+\varepsilon\,\omega_{\mathcal D}(\nu_a,x)$
  for $\varepsilon<\varepsilon_{\mathcal D}(x)$ [GMS19, Definition 5]; a strategy is *uniformly
  super-fast convergent* if there is $C_{\psi,\mathcal D}$ with
  $\mathbb E N_a(T)\le C_{\psi,\mathcal D}\ln T/\Delta_a^2$ for all instances, suboptimal arms and
  $T\ge 2$ [GMS19, Definition 6]. Then for every such strategy on a well-behaved model, every
  instance and suboptimal arm:
  $\mathbb E N_a(T)\ge\frac{\ln T}{\mathcal K_{\inf}(\nu_a,\mu^\star,\mathcal D)}(1-(a_T+b_T+c_T))-\frac{\ln 2}{\mathcal K_{\inf}(\nu_a,\mu^\star,\mathcal D)}$
  for $T\ge 2$ large enough that $(\ln T)^{-4}<\varepsilon_{\mathcal D}(\mu^\star)$ and
  $a_T = \frac{\omega_{\mathcal D}(\nu_a,\mu^\star)}{\mathcal K_{\inf}(\nu_a,\mu^\star,\mathcal D)}(\ln T)^{-4}$,
  $b_T = C_{\psi,\mathcal D}H(\nu)\frac{\ln T}{T}$,
  $c_T = \frac{\ln(KC_{\psi,\mathcal D}(\ln T)^9)}{\ln T}$ are all smaller than 1, where
  $H(\nu) := \sum_{a\notin\mathcal A^\star}\Delta_a^{-2}$ [GMS19, Theorem 5]; hence
  $\mathbb E N_a(T)\ge\ln T/\mathcal K_{\inf}-O(\ln\ln T)$ [GMS19, Remark 3]. Bounded-support models
  and regular exponential families are well behaved [GMS19, Section 4.2, Lemmas 3–4] (statements
  to be checked: only their headings were read). — *Source:* [GMS19, Definitions 5–6, Theorem 5,
  Remark 3]. — *Settles:* the second-order term of a super-fast convergent strategy cannot be
  below $-O(\log\log T)$; with K11 and K21, its order is $\log\log T$ and its sign negative.
- **K6.** [published] **$\alpha$-consistent algorithms.** A policy is $\alpha$-consistent if
  $\mathbb E[R_n] = o(n^a)$ for every $a>\alpha$ and every environment of the class
  [SAE13, Definition 5]. If the class has the product property, then for every $\alpha$-consistent
  policy, environment $\theta$ and arm $k$ with $\Delta_k>0$ and $0<D_k(\theta)<\infty$:
  $P\big(T_k(n)\ge(1-\varepsilon)(1-\alpha)\log n/D_k(\theta)\big)\to 1$ for every $\varepsilon>0$, hence
  $\liminf_n\mathbb E[T_k(n)]/\log n\ge(1-\alpha)/D_k(\theta)$, where $D_k(\theta)$ is the Burnetas–Katehakis
  $\mathcal K_{\inf}$ [SAE13, Theorem 6]. For every $\rho\in(0,1/2]$, the policy UCB($\rho$) of [SAE13]
  (its definition was not read) is
  $(1-2\rho)$-consistent and not $\alpha$-consistent for $\alpha<1-2\rho$ [SAE13, Section 4] (only the
  sentence recalling this was read; its proof is to be checked). — *Source:* [SAE13, Definition 5, Theorem 6]. — *Settles:* the first-order
  lower bound degrades exactly by $(1-\alpha)$ under weaker consistency.
- **K7.** [published] **Finite-time lower bound, unit-variance Gaussians.** For every strategy and
  $\mu\in\mathbb R^k$ with $n\Delta_i^2\ge 2k_i\log n$ and $\Delta_i\le 1$ for every $i$ with
  $\Delta_i>0$, where $k_i := \sum_{j=1}^k\min\lbrace 1,\Delta_i/\Delta_j\rbrace$, one of the following holds:
  (a) $R_n(\mu)\ge\frac12\sum_{i:\Delta_i>0}\frac1{\Delta_i}\log\big(\frac{n\Delta_i^2}{2k_i\log n}\big)$;
  (b) some $\mu'$ with $\mu'_i = \mu_i+2\Delta_i$ and $\mu'_j = \mu_j$ ($j\ne i$) has
  $R_n(\mu')\ge\frac14\sum_{i:\Delta'_i>0}\frac{\log n}{\Delta'_i}$ [L18, Theorem 10]. — *Source:*
  [L18, Theorem 10]. — *Settles:* the finite-time upper bound of ADA-UCB (K22) is close to optimal,
  including a $-\log\log n$ correction.
- **K8.** [published] **Heavy tails, lower bound.** For every $\Delta\in(0,1/4)$ there are two laws
  $\nu_1,\nu_2$ with $\mathbb E|X|^{1+\varepsilon}\le 1$ and $\mu_1-\mu_2 = \Delta$ such that every algorithm
  with $\mathbb E T_2(n) = o(n^a)$ for all $a>0$ on every two-armed problem of this class with arm 2
  suboptimal satisfies $\liminf_n R_n/\log n\ge 0.4/\Delta^{1/\varepsilon}$ on $(\nu_1,\nu_2)$; and for every
  $n$ there are $K$ such laws with $R_n\ge 0.01K^{\varepsilon/(1+\varepsilon)}n^{1/(1+\varepsilon)}$ for every
  algorithm [BCL13, Theorem 2], $\varepsilon\in(0,1]$. — *Source:* [BCL13, Theorem 2] (arXiv v1). —
  *Settles:* with only $1+\varepsilon$ moments, the dependence $\Delta^{-1/\varepsilon}$ is necessary.

### Upper bounds: one-parameter families and bounded rewards

- **K9.** [published] **KL-UCB, exponential families.** If all arms belong to a canonical regular
  exponential family indexed by its natural parameter, kl-UCB with the family divergence $d$ and
  $f(t) = \log t+3\log\log t$ ($t\ge 3$, $f(1)=f(2)=f(3)$) satisfies, for every suboptimal $a$ and
  $T\ge 3$:
  $\mathbb E[N_a(T)]\le\frac{\log T}{d(\mu_a,\mu^\star)}+2\sqrt{\frac{2\pi\sigma^2_{a,\star}(d'(\mu_a,\mu^\star))^2}{(d(\mu_a,\mu^\star))^3}}\sqrt{\log T+3\log\log T}+\big(4e+\frac{3}{d(\mu_a,\mu^\star)}\big)\log\log T+8\sigma^2_{a,\star}\big(\frac{d'(\mu_a,\mu^\star)}{d(\mu_a,\mu^\star)}\big)^2+6$,
  with $\sigma^2_{a,\star} := \max\lbrace\mathrm{Var}(\nu_\theta):\mu_a\le E(\nu_\theta)\le\mu^\star\rbrace$ and $d'$ the
  derivative of $d(\cdot,\mu^\star)$ [CGMMS13, Theorem 1]. In Lean: LMLExplore `klucbFam`,
  `tendsto_klucbFam_regret_div_log` (first order). — *Source:* [CGMMS13, Theorem 1] (arXiv v4). —
  *Settles:* finite-time first-order optimality in exponential families, second-order term
  $O(\sqrt{\log T})$.
- **K10.** [published] **Empirical KL-UCB.** For finitely supported laws on $[0,1]$ with
  $\mu_a>0$ and $\mu^\star<1$, empirical KL-UCB (K44) with $f(t) = \log t+\log\log t$ has
  $\mathbb E[N_a(T)]\le\log T/\mathcal K_{\inf}(\nu_a,\mu^\star)+O((\log T)^{4/5}\log\log T)$ with explicit
  constants [CGMMS13, Theorem 2]. For all laws on $[0,1]$ (not necessarily finitely supported), with
  $g_a(t) = \log t+\log\log t$:
  $\mathbb E(N_a(T))\le\log T/\big(\mathcal K_{\inf}(\mu_a,m(\mu_1))-O((\log T)^{-1/5}(\log\log T)^{1/5})\big)+O((\log T)^{4/5}(\log\log T)^{1/5})$
  [AJK21, Proposition 4], which settles the conjecture of [CGMMS13, Sections 6.2 and 8] (K59). —
  *Source:* [CGMMS13, Theorem 2]; [AJK21, Section 3.2, Proposition 4] (arXiv v1). — *Settles:*
  first-order optimality of empirical KL-UCB on $\mathcal P[0,1]$.
- **K11.** [published] **IMED.** Let $\mathcal A$ be the laws on $(-\infty,1]$, $\mathcal A_a$ those on
  $[a,1]$. (i) $D_{\inf}(F,\mu;\mathcal A_a) = D_{\inf}(F,\mu;\mathcal A)$ for $F\in\mathcal A_a$, and for
  $\mu<1$, $D_{\inf}(F,\mu;\mathcal A) = \max_{0\le\nu\le 1/(1-\mu)}\mathbb E_F[\log(1-\nu(X-\mu))]$
  [HT15, Theorem 2]; for $\mathcal A_0$ this is [HT10, Theorem 5] as quoted in [HT15, Proposition 1]
  (HT10 to be checked). (ii) IMED (K46) on $\mathcal A$: if $\mu^\star<1$ and
  $\mathbb E_{F_j}[e^{\lambda X}]<\infty$ near $\lambda = 0$ for some optimal $j$, an explicit finite-time bound
  holds for every $0<\delta<\min_i\Delta_i/2$ [HT15, Theorem 3], giving
  $\mathbb E[R(n)] = \sum_{i:\mu_i<\mu^\star}\Delta_i\log n/D_{\inf}(F_i,\mu^\star)+O((\log n)^{10/11})$
  [HT15, Corollary 4]. (iii) If $\mu^\star<1$ and every arm has a moment generating function near 0,
  $\mathbb E[R(n)] = \sum_{i:\mu_i<\mu^\star}\Delta_i\log n/D_{\inf}(F_i,\mu^\star)+O(1)$; if moreover every
  arm has bounded support, there is $C>0$ with
  $\mathbb E[R(n)]\le\sum_{i:\mu_i<\mu^\star}\Delta_i\log n/D_{\inf}(F_i,\mu^\star)-C\log\log n$ for all
  sufficiently large $n$ [HT15, Theorem 5]. — *Source:* [HT15, Theorems 2, 3, 5, Corollary 4,
  Proposition 1]. — *Settles:* an anytime algorithm with first-order optimality on semi-bounded laws
  and a negative $\log\log$ second-order term on bounded supports (constant existential).
- **K12.** [published] **Thompson sampling, Bernoulli rewards.** With the uniform Beta(1,1) prior
  (K47): $\mathbb E[R(T)]\le(1+\varepsilon)\sum_{i\ge 2}\frac{\ln T}{d(\mu_i,\mu_1)}\Delta_i+O(N/\varepsilon^2)$
  [AG13, Theorem 1] and $\mathbb E[R(T)]\le O(\sqrt{NT\ln T})$ [AG13, Theorem 2] ($N$ arms, arm 1 the
  unique optimal arm); also, for every $\varepsilon>0$,
  $R(T)\le(1+\varepsilon)\sum_{a:\mu_a\ne\mu^\star}\Delta_a(\ln T+\ln\ln T)/K(\mu_a,\mu^\star)+C(\varepsilon,\mu)$ with
  the count form [KKM12, Theorems 1, 2]. — *Source:* [AG13, Theorems 1–2] (arXiv v1);
  [KKM12, Theorems 1–2] (arXiv v2). — *Settles:* Thompson sampling is asymptotically optimal for
  Bernoulli rewards and minimax up to $\sqrt{\log T}$.
- **K13.** [published] **Thompson sampling, exponential families.** For a one-dimensional canonical
  exponential family and the Jeffreys prior,
  $\lim_T R(TS_J,T)/\ln T = \sum_a(\mu(\theta_{a^\star})-\mu(\theta_a))/K(\theta_a,\theta_{a^\star})$ [KKM13,
  Theorem 1], from a finite-time bound with a factor $(1+\varepsilon)/(1-\varepsilon)$ [KKM13, Theorem 2]
  (unique optimal arm). Planned in LMLExplore (Layer 5.3); Gaussian Thompson sampling is in Lean
  (`gaussianTS`). — *Source:* [KKM13, Theorems 1–2] (arXiv v1). — *Settles:* first-order optimality of
  Thompson sampling with the Jeffreys prior in exponential families.

### Beyond one-parameter families

- **K14.** [published] **Gaussian, unknown mean and variance: the constant and Thompson sampling.**
  For $\mathcal N(\mu_i,\sigma_i^2)$ arms with both parameters unknown,
  $\mathcal K_{\inf} = D_{\inf}(\Delta_i,\sigma_i^2) := \frac12\log(1+\Delta_i^2/\sigma_i^2)$ and the bound K1 reads
  $\liminf\mathbb E[\mathrm{Regret}(T)]/\log T\ge\sum_{i:\Delta_i>0}\Delta_i/D_{\inf}(\Delta_i,\sigma_i^2)$
  [HT14, (2)–(3)]. Thompson sampling with prior $\pi(\mu_i,\sigma_i^2)\propto(\sigma_i^2)^{-1-\alpha}$ and
  $\alpha<0$ (K47), with a unique optimal arm, has
  $\mathbb E[\mathrm{Regret}(T)]\le\sum_{i:\Delta_i>0}\Delta_i\log T/D_{\inf}(\Delta_i,\sigma_i^2)+O((\log T)^{4/5})$
  [HT14, Theorem 1]. — *Source:* [HT14, Section 2, Theorem 1] (arXiv v1). — *Settles:* first-order
  optimality is attainable for Gaussians with unknown variance (see K40 for priors that fail).
- **K15.** [published] **Gaussian, unknown variance: an index policy.** Policy CHK (K48) satisfies
  $\lim_n R_{CHK}(n)/\ln n = M_{BK}(\mu,\sigma^2) := \sum_{i:\mu_i\ne\mu^\star}2\Delta_i/\ln(1+\Delta_i^2/\sigma_i^2)$
  [CHK18, Theorem 4], and $R_{CHK}(n)\le M_{BK}\ln n+O((\ln n)^{3/4}\ln\ln n)$ with explicit terms
  [CHK18, Theorem 5]. — *Source:* [CHK18, Section 1, Theorems 4–5] (arXiv:1504.05823v2; JMLR
  numbering to be checked). — *Settles:* the open problem of [BK96] on normal populations with unknown
  variances (K71).
- **K16.** [published] **Non-parametric Thompson sampling on $[0,1]$.** For arms with laws on $[0,1]$,
  Non-parametric TS (K49) has
  $\mathbb E[R_T]\le\sum_{k:\Delta_k>0}\Delta_k\log T/\mathcal K_{\inf}(F_k,\mu^\star)+o(\log T)$
  [RH20, Theorem 5]; Multinomial TS has the analogous bound for multinomial laws on
  $\lbrace 0,\frac1M,\dots,1\rbrace$ [RH20, Theorem 4]. — *Source:* [RH20, Section 3, Theorems 4–5].
  — *Settles:* a randomized algorithm without optimization per round is first-order optimal on
  $\mathcal P[0,1]$.
- **K17.** [published] **Heavy tails, exact first order.** On
  $\mathcal L_B := \lbrace\eta : \mathbb E_\eta|X|^{1+\varepsilon}\le B\rbrace$ ($B,\varepsilon$ known),
  KLinf-UCB (K50) with batch factor $\tilde\varepsilon\ge 0$ and
  $g_a(t) = \log t+2\log\log t+2\log(1+N_a(t))+1$ has
  $\mathbb E(N_a(T))\le(1+\tilde\varepsilon)\big(\frac{\log T}{\mathrm{KL}_{\inf}(\mu_a,m(\mu_1))}+\frac{3(\log T)^{2/3}(c_\mu)^{1/3}}{2(\mathrm{KL}_{\inf}(\mu_a,m(\mu_1)))^{4/3}}+O((\log T)^{1/3})+O(\log\log T)\big)$
  [AJK21, Theorem 1], hence $\limsup_T\mathbb E(N_a(T))/\log T\le(1+\tilde\varepsilon)/\mathrm{KL}_{\inf}$
  [AJK21, Corollary 2]; KLinf-UCB2 (class parameter $B+\varepsilon_1$) gets arbitrarily close
  [AJK21, Theorem 3]. Here $\mathrm{KL}_{\inf}^{\mathcal L}(\eta,x) := \inf\lbrace\mathrm{KL}(\eta,\kappa):\kappa\in\mathcal L, m(\kappa)\ge x\rbrace$
  (non-strict). The exactly optimal version $\tilde\varepsilon = 0$ has a quadratic computational cost
  [AJK21, Section 3.1]. — *Source:* [AJK21, Sections 2–3, Theorems 1, 3, Corollary 2] (arXiv v1). —
  *Settles:* first-order optimality under a known moment bound of order $1+\varepsilon$.
- **K18.** [published] **Robust UCB.** If $\mathbb E|X_i|^{1+\varepsilon}\le u$ for every arm
  ($\varepsilon\in(0,1]$), Robust-UCB with the truncated empirical mean has
  $R_n\le\sum_{i:\Delta_i>0}\big(8(4u/\Delta_i)^{1/\varepsilon}\log n+5\Delta_i\big)$ [BCL13, Theorem 1]
  (exponent as read in arXiv v1; to be checked on the published version). — *Source:* [BCL13,
  Theorem 1]. — *Settles:* logarithmic regret with finite variance only, optimal in order (K8).
- **K19.** [published] **Bounded kurtosis.** If every arm has kurtosis at most a known $\kappa$, the
  algorithm of [L17, Section 2] (median-of-means based; not transcribed) satisfies
  $\limsup_n R_n/\log n\le C\sum_{i:\Delta_i>0}\Delta_i\big(\kappa-1+\sigma_i^2/\Delta_i^2\big)$ for a universal
  $C$, $\sigma_i^2$ the variance of arm $i$ [L17, Theorem 2]; the matching lower bound holds only up to
  constant factors [L17, Section 3, Theorem 9 (statement not read); Section 4]. [L17, Table 1] lists
  the known asymptotic constants by model (Bernoulli, bounded, semi-bounded, Gaussian with known or
  unknown variance, uniform with unknown support, sub-Gaussian, known variance). —
  *Source:* [L17, Assumption 1, Theorem 2, Section 4]. — *Settles:* logarithmic, scale-free regret on
  a non-parametric class; the exact constant is open (K62).

### Simultaneous minimax and problem-dependent guarantees, anytime algorithms

- **K20.** [published] **KL-UCB++** (horizon-dependent, K44), for exponential families with
  variance bound $V$: $R_T\le 76\sqrt{VKT}+(\mu^+-\mu^-)K$ [MG17, Theorem 1], and for every
  suboptimal $a$ and $\delta$ with $2\sqrt{2VK/T}\le\delta\le(\mu^\star-\mu_a)/3$:
  $\mathbb E N_a(T)\le\log T/\mathrm{kl}(\mu_a+\delta,\mu^\star-\delta)+O(\log\log T/\delta^2)$, which gives
  asymptotic optimality [MG17, Theorem 2]. On $[0,1]$-valued rewards (with $V = 1/4$) both bounds
  hold but the constant $1/\mathrm{kl}$ is not optimal [MG17, Section 3]. — *Source:* [MG17,
  Theorems 1–2] (arXiv v2). — *Settles:* first algorithm simultaneously minimax and asymptotically
  optimal (exponential families, horizon known).
- **K21.** [published] **KL-UCB-switch** (K45) on $\mathcal P[0,1]$. Horizon-dependent version:
  $R_T\le(K-1)+23\sqrt{KT}$ [GHMS22, Theorem 1], and for $\mu^\star\in(0,1)$, suboptimal $a$ and
  $T\ge K/\min\lbrace 1-\mu^\star,(\Delta_a/9)^{12}\rbrace$:
  $\mathbb E[N_a(T)]\le(\ln T-\ln\ln T)/\mathcal K_{\inf}(\nu_a,\mu^\star)+O_T(1)$ with a closed-form
  $O_T(1)$ [GHMS22, Theorem 2]. Anytime version: $R_T\le(K-1)+44\sqrt{KT}$ for all $T$
  [GHMS22, Theorem 3] and $\mathbb E[N_a(T)]\le\ln T/\mathcal K_{\inf}(\nu_a,\mu^\star)+O_T((\ln T)^{6/7})$
  [GHMS22, Theorem 4]. A standard doubling trick does not give both properties [GHMS22, Section 2.3].
  — *Source:* [GHMS22, Sections 2.1–2.3, Theorems 1–4] (arXiv v3). — *Settles:* bi-optimality on all
  laws on $[0,1]$, horizon-dependent with a $-\ln\ln T$ second-order term, anytime with a positive one.
- **K22.** [published] **ADA-UCB** (horizon-dependent, K51), unit-variance Gaussian rewards: for a
  universal $C$,
  $R_n(\mu)\le C\min_{i\in[k]}\big(n\bar\Delta_i+\sum_{m>i}\Delta_m\lambda_m\big)$ with
  $\bar\Delta_i := \frac1i\sum_{m\le i}\Delta_m$ and $\lambda_i := 1+\Delta_i^{-2}\,\overline{\log}(n\Delta_i^2/k_i)$
  ($\overline{\log}(x) := \log((x+e)\log^{1/2}(x+e))$, $k_i$ as in K7), whence (a)
  $\sup_\mu R_n\le C\sqrt{kn}$, (b) sub-UCB:
  $R_n(\mu)\le C\sum_m(\Delta_m+\log(n)/\Delta_m)$ over $\Delta_m>0$, (c)
  $\lim_n R_n(\mu)/\log n = \sum_{i:\Delta_i>0}2/\Delta_i$ [L18, Theorem 1] (arms ordered
  $\mu_1\ge\dots\ge\mu_k$ for the statement only). — *Source:* [L18, Section 2, Theorem 1]. — *Settles:* a strategy simultaneously
  minimax, sub-UCB and asymptotically optimal (Gaussian, horizon known).
- **K23.** [published] **MOTS and MOTS-J** (horizon-dependent, K52). For 1-sub-Gaussian rewards,
  $\rho\in(1/2,1)$, $\alpha\ge 4$: $R_\mu(T) = O(\sqrt{KT}+\sum_i\Delta_i)$ [JXSXG21, Theorem 1] and
  an asymptotic rate $\lim_T R_\mu(T)/\log T$ equal to the Gaussian lower bound $\sum_{i:\Delta_i>0}2/\Delta_i$
  up to the factor $1/\rho$ [JXSXG21, Theorem 2 and the comment after it; display partly garbled in
  the extraction]; with
  $\rho = 1-(\mathrm{ilog}^{(m)}(T)/40)^{-1/2}$, $R_\mu(T) = O(\sqrt{KT\,\mathrm{ilog}^{(m-1)}(T)}+\sum_i\Delta_i)$ and
  $\lim R_\mu(T)/\log T = \sum 2/\Delta_i$ [JXSXG21, Theorem 3]. For Gaussian $\mathcal N(\mu_i,1)$ rewards
  and $\alpha\ge 2$, MOTS-J has both $R_\mu(T) = O(\sqrt{KT}+\sum_i\Delta_i)$ and
  $\lim R_\mu(T)/\log T = \sum 2/\Delta_i$ [JXSXG21, Theorem 4]. — *Source:* [JXSXG21, Sections 3–4,
  Theorems 1–4] (arXiv v3). — *Settles:* a Thompson-type algorithm can be minimax and asymptotically
  optimal (Gaussian, horizon known).
- **K24.** [published] **MOSS is not asymptotically optimal as tuned.** For MOSS on 1-sub-Gaussian
  rewards, $\limsup_n R_n/\log n\le\sum_{i:\Delta_i>0}4/\Delta_i$ (twice the optimal Gaussian constant),
  and a variant with a slightly larger exploration function recovers the constant 2
  [LS, Section 9.3, Note 1] (claims of the notes; the book refers to Garivier (2013) for the
  details, not read). —
  *Source:* [LS, Section 9.3, Note 1]. — *Settles:* the asymptotic constant of MOSS as usually tuned.

### Structured classes

- **K25.** [published] **Graves–Lai lower bound.** For a structured class $\Theta$ with a unique
  optimal arm $x^\star(\theta)$ (Assumption 1) and every uniformly good algorithm
  ($R(T,\theta) = o(T^a)$ for all $a>0$, $\theta\in\Theta$):
  $\liminf_T R(T,\theta)/\ln T\ge C(\theta)$, the value of $\min_{\eta\ge 0}\sum_x\eta(x)(\mu^\star(\theta)-\mu(x,\theta))$
  subject to $\sum_x\eta(x)D(\theta,\lambda,x)\ge 1$ for all
  $\lambda\in\Lambda(\theta) := \lbrace\lambda\in\Theta : D(\theta,\lambda,x^\star(\theta)) = 0,\ x^\star(\theta)\ne x^\star(\lambda)\rbrace$
  [CMP17, Theorem 1], proved by applying [GL97, Theorem 1] (to be checked: GL97 not read)
  [CMP17, Appendix A]. Special cases: unstructured, $c(x,\theta) = 1/d(\theta(x),\theta(x^\star))$
  [CMP17, Section 4]; unimodal on a graph $G = (V,E)$ with a parametrized family, $c(\theta) = \sum_{(k,k^\star)\in E}(\mu^\star-\mu_k)/I_{\min}(\theta_k,\theta^\star)$
  (only neighbours of the optimal arm) [CP14, Theorem 4.1]; finite linear with Gaussian noise, a
  spanning finite action set and a unique optimal action: for consistent policies, with
  $\bar G_n := \mathbb E\sum_{t\le n}A_tA_t^\top$, $\limsup_n\log(n)\|x-x^\star\|^2_{\bar G_n^{-1}}\le\Delta_x^2/2$
  for every suboptimal $x$ [LS17, Theorem 1], and $\liminf_n\lambda_{\min}(\bar G_n)/\log n>0$ and
  $\limsup_n\log(n)\|a\|^2_{\bar G_n^{-1}}\le\Delta_a^2/2$ for every $a$ [LS, Theorem 25.1]; hence
  $\liminf_n R_n/\log n\ge c(\mathcal A,\theta) := \inf_{\alpha\in[0,\infty)^{\mathcal A}}\sum_a\alpha(a)\Delta_a$
  subject to $\|a\|^2_{H_\alpha^{-1}}\le\Delta_a^2/2$ for all $a$ with $\Delta_a>0$,
  $H_\alpha = \sum_a\alpha(a)aa^\top$ [LS, Corollary 25.2; LS17, Corollary 2], attained by some policy
  [LS, Theorem 25.3]. — *Source:* [CMP17, Section 4, Theorem 1, Appendix A]; [CP14, Theorem 4.1];
  [LS17, Theorem 1, Corollary 2] (arXiv v1); [LS, Theorems 25.1, 25.3, Corollary 25.2]. — *Settles:*
  the first-order lower bound for structured classes.
- **K26.** [published] **OSSB** (K53). For Bernoulli or unit-variance Gaussian observations, under
  Assumptions 1, 4, 5, 6 of the source (unique optimal arm; continuity of the divergence and of the
  mean map in the parameter; uniqueness of the solution of the Graves–Lai problem), OSSB$(\varepsilon,\gamma)$
  with $\varepsilon<1/|\mathcal X|$ satisfies $\limsup_T R(T)/\ln T\le C(\theta)F(\varepsilon,\gamma,\theta)$
  with $F(\varepsilon,\gamma,\theta)\to 1$ as $\varepsilon\to 0$ and $\gamma\to 0$ [CMP17, Theorem 2]; the proof gives
  the finite-time bound
  $R(T)\le\mu^\star(\theta)\big(G(\gamma,|\mathcal X|)+2|\mathcal X|/(\varepsilon\delta^2(\kappa))\big)+(C(\theta)(1+\kappa)+2\varepsilon\psi(\theta))(1+\gamma)\ln T$
  for every $\kappa>0$, and the continuity of $\theta\mapsto C(\theta)$ [CMP17, Section 6, Lemma 1]. —
  *Source:* [CMP17, Sections 5–6, Theorem 2, Lemma 1]. — *Settles:* the Graves–Lai constant is attainable up to a factor arbitrarily close to 1
  for general structures, by tracking with forced exploration.
- **K27.** [published] **Finite linear bandits, an optimal algorithm.** With a unique optimal action,
  Algorithm 1 of [LS17] (warm-up of length $d\log^{1/2}n$, success phase, recovery phase running UCB;
  horizon-dependent) satisfies $\limsup_n R_\theta(n)/\log n\le c(\mathcal A,\theta)$ for all $\theta$
  [LS17, Theorem 10]. — *Source:* [LS17, Theorem 10] (arXiv v1; algorithm not transcribed). —
  *Settles:* K25 is attained for finite linear bandits.
- **K28.** [published] **Saddle-point algorithms.** For one-parameter exponential-family arms and
  regular structures ([DSK20, Assumption 1], or Assumption 7 of its appendix, not read), the
  structure-adaptive algorithm of [DSK20] (an explore-or-exploit test as in OSSB; exploration plays a
  zero-sum game between allocations and alternatives with online learners), run with a $k$-learner or
  $\lambda$-learner of regret $O(\sqrt n)$, satisfies $\lim_T\mathbb E_\mu[R_T]/\ln T\le V_{\mathcal M}(\mu)$
  [DSK20, Theorem 3]; the $\varepsilon$-perturbed value satisfies $V_{\mathcal M}\le V^\varepsilon_{\mathcal M}\le V_{\mathcal M}+c\varepsilon V_{\mathcal M}$
  for small $\varepsilon$ [DSK20, Theorem 2]. — *Source:* [DSK20, Sections 1–2, Theorems 1–3]
  (arXiv v1). — *Settles:* asymptotic optimality for all regular structures without solving the
  Graves–Lai problem at every round.
- **K29.** [published] **OSUB, unimodal bandits.** For rewards in $[0,1]$ and unimodal means on a known
  graph $G$, OSUB (K54) pulls a suboptimal arm $k$ at most
  $(1+\varepsilon)\frac{\log T+c\log\log T}{I(\mu_k,\mu^\star)}+C_1\log\log T+\frac{C_2}{T^{\beta(\varepsilon)}}$ times in
  expectation if $(k,k^\star)\in E$, and $C_3/\Delta^2$ otherwise [CP14, Theorem 4.2]; for Bernoulli
  rewards $\limsup_T R/\log T\le c(\theta)$ [CP14, Corollary 4.4]. — *Source:* [CP14, Section 4]
  (arXiv v1). — *Settles:* optimism restricted to the neighbourhood of the leader is optimal for
  unimodal structures.
- **K30.** [published] **CROP, finite hypothesis classes.** For a finite class $\mathcal F$ of mean
  functions on a finite arm set, CROP (anytime, no forced sampling; definition in [JZ20, Section 3],
  not transcribed) has
  $\mathbb E\,\mathrm{Reg}_n\le c_1\big(P_1\ln n+P_2\ln\ln n+P_3\ln|\mathcal F|+\ln Q_1+K_\psi\Lambda_{\max}\big)$, with
  $P_1$ a constant-factor version of the Graves–Lai constant, and bounded regret when $\Lambda = 0$
  [JZ20, Theorem 1]. — *Source:* [JZ20, Section 4, Theorem 1] (arXiv v2). — *Settles:* constant-factor
  asymptotic optimality without forced sampling, with bounded regret when possible.
- **K31.** [published] **IDS, finite linear bandits.** The asymptotically optimal information-directed
  sampling of [KLVS21, Algorithm 1] has $R_n\le O(d\sqrt{n\log n})$ [KLVS21, Theorem 2] and, assuming
  $x^\star\ne 0$, $\lim_n R_n/\log n = c^\star$, the value of the Graves–Lai problem [KLVS21, Theorem 5].
  — *Source:* [KLVS21, Theorems 1, 2, 5] (arXiv v4). — *Settles:* asymptotic and near worst-case
  optimality together for finite linear bandits.

### The distribution of the regret

- **K32.** [published] **Polynomial tails of UCB-type algorithms.** For UCB-V with exploration function
  $\zeta\log t$ and $c\zeta>1$, a unique optimal arm with essential infimum $\underline\mu$ and a second
  best arm $\tilde k$: if $\underline\mu>\mu_{\tilde k}$ the pseudo-regret has exponentially small tails;
  if $\underline\mu<\mu_{\tilde k}$ it has a polynomial tail only [AMS09, Theorem 10]; "an entirely
  analogous result holds for UCB1" [AMS09, footnote 5]. Both terms of the UCB-V bound are
  unavoidable: no algorithm satisfies either of the bounds (40), (41) of [AMS09, Theorem 13] (a
  regret of order $b\log n$ per suboptimal arm, or of order $(\sigma_k^2/\Delta_k)\log n$) uniformly over
  laws on $[0,b]$ (exact displays to be checked: read in a text extraction). — *Source:* [AMS09, Section 1, Theorems 10, 13] (author's version, page numbers
  may differ from the journal). — *Settles:* logarithmic expected regret and exponentially concentrated regret are
  incompatible as soon as the optimal arm can underperform.
- **K33.** [published] **Robustness: anytime versus horizon-dependent.** A policy has *$f$-upper tailed
  regret* if there are $C,\tilde C>0$ such that for every environment with $\Delta\ne 0$ and every
  $n\ge 2$, $P(\hat R_n\ge C\log n/\Delta)\le\tilde C/f(n)$ (similarly for counts, with $\Delta_k^2$)
  [SA11, Definition 1]. Let $f\gg\log^\alpha$ for every $\alpha>0$. If the class contains $\theta,\tilde\theta$
  and an arm $k$ with $\nu_k = \tilde\nu_k$, $k$ optimal in $\theta$ and not in $\tilde\theta$, and
  $P_{\tilde\theta}(\frac{d\nu_\ell}{d\tilde\nu_\ell}(X_{\ell,1})>0)>0$ for every $\ell\ne k$, there is no anytime
  policy with $f$-upper tailed regret [SA11, Theorem 3.3]; in particular none on the set of all
  $K$-tuples of laws on $[0,1]$ [SA11, Corollary 3.4]. On the other hand the horizon policy ucb-h
  (K55) has $n^\beta$-upper tailed regret for every $\beta>0$ [SA11, Theorem 3.5], and the anytime
  ucb1($\rho$) has $\log^{2\rho-1}$-upper tailed regret for $\rho>1/2$ [SA11, Theorem 3.6]; if
  $f(n)\gg n^\alpha$ for every $\alpha>0$, no horizon policy has $f$-upper tailed counts on the set of all
  $K$-tuples of laws on $[0,1]$ [SA11, Theorem 5.1, Corollary 5.2]. — *Source:* [SA11, Definitions 1–3,
  Theorems 3.3, 3.5, 3.6, 5.1, Corollaries 3.4, 5.2] (arXiv:1107.4506v2). — *Settles:* the
  question of [AMS09] (K70): knowing the horizon is necessary for logarithmic regret with
  polynomially small failure probability.
- **K34.** [published] **Optimized algorithms have heavy-tailed regret.** For a one-parameter
  exponential family $P$ and an $\mathcal M_P$-optimized algorithm ($\lim_T\mathbb E N_i(T)/\log T = 1/d_P(\mu_i,\mu^\star)$
  for every instance and suboptimal arm [FG24, Definition 2]): for the $i$-th best arm $r(i)$,
  $\liminf_T\inf_{x\in B_\delta(T)}\log P(N_{r(i)}(T)>x)/\log x\ge-\sum_{j=1}^{i-1}\inf_{z<\mu_{r(i)}}d_P(z,\mu_{r(j)})/d_P(z,\mu_{r(i)})$
  with $B_\delta(T) = [\log^{1+\delta}T,(1-\delta)T]$; if $P$ is discrimination equivalent
  [FG24, Definition 3], $\log P(N_{r(2)}(T)>x)/\log x\to-1$ uniformly for $x\in[T^\delta,(1-\delta)T]$
  (truncated Cauchy tail) [FG24, Theorem 1]; near-equal top means give an exponent close to $-1$ for
  every optimized algorithm [FG24, Corollary 1]. Trade-off: if
  $\limsup_T\log P(N_i(T)>T/K)/f(T)\le-1$ for an increasing $f$ with $\liminf f(t)/\log t\ge 1$ and
  $f(t) = o(t)$, then $P(N_i(T)\ge(1-\delta)f(T)/D_{\inf}(P_i,\mu^\star,\mathcal M))\to 1$ and
  $\liminf_T\mathbb E N_i(T)/f(T)\ge 1/D_{\inf}$ [FG24, Theorem 4]. — *Source:* [FG24, Definitions 1–3,
  Theorem 1, Corollary 1, Theorem 4] (arXiv v8). — *Settles:* the price in tail of first-order
  optimality in exponential families, and a sharp tail–expectation trade-off.

## Negative results and counterexamples

- **K35.** [published] **Optimism and Thompson sampling are not optimal for linear bandits.** Take
  $d = 2$, $\mathcal A = \lbrace e_1,e_2,a_3 = (1-\varepsilon,\gamma\varepsilon)\rbrace$, $\theta = (1,0)$, so $\Delta_{e_2} = 1$,
  $\Delta_{a_3} = \varepsilon$. For $\varepsilon$ small relative to $\gamma$, $c(\mathcal A,\theta) = 2\gamma^2$ (K25), while
  every consistent optimistic algorithm whose confidence sets $\mathcal C_t$ contain $\theta$ for all
  $t\le n$ with probability at least $1-1/n$ and satisfy
  $\mathcal C_t\subseteq\lbrace\tilde\theta:\|\hat\theta_t-\tilde\theta\|^2_{V_t}\le c\log n\rbrace$ has, for $\gamma$
  large compared with $c^2$, $\limsup_n R_n/\log n = \Omega(1/\varepsilon)$ [LS, Section 25.2]; the same
  example with $a_3 = (1-\varepsilon,8\alpha\varepsilon)$, $c = 128\alpha^2$, and the same heuristic for Thompson
  sampling with a flat Gaussian prior, are in [LS17, Section 8]. The argument is partly informal
  (assumptions on $\mathcal C_t$, "a simple computation"). — *Source:* [LS, Section 25.2, Notes 25.3];
  [LS17, Section 8] (arXiv v1). — *Settles:* optimism can be arbitrarily far from optimal in structured
  classes (F8 formalises it).
- **K36.** [published] **Forced exploration of order $\log\log n$ can be necessary; the optimal
  allocation can be bad in finite time.** Roughly: there is a finite hypothesis class (Gaussian
  noise, $\sigma^2 = 1$) and an absolute constant such that an algorithm with regret $O(n^u)$,
  $u\in[0,1)$, must pull a non-informative arm (in the sense of the source)
  $\Omega(\ln(1+(1-u)\ln n))$ times on some instance of the class [JZ20, Theorem 2 (informal version,
  read in a garbled text extraction; the formal statement is in its appendix, to be checked)]. The
  clairvoyant oracle playing the asymptotically optimal allocation suffers a linear
  worst-case regret over a family of classes, including linear bandits [JZ20, Section 6]. — *Source:*
  [JZ20, Sections 5–6] (arXiv v2). — *Settles:* forced exploration cannot be $o(\log\log n)$ in general.
- **K37.** [published] **Explore-then-commit loses a factor 2.** For two Gaussian arms with unit
  variance, an ETC strategy is a pair $(\tau,\hat a)$ — $\tau$ an even stopping time, uniform sampling
  until $\tau$, then $\hat a$ forever — and "uniformly efficient on $\mathcal S$" means
  $R^\pi_\mu(T) = o(T^\alpha)$ for all $\alpha>0$, $\mu\in\mathcal S$ [GKL16, Section 2]. Every uniformly
  efficient ETC strategy on $\mathcal H = \mathbb R^2$ has $\liminf_T R(T)/\log T\ge 4/\Delta$
  [GKL16, Theorem 4], and on $\mathcal H_\Delta$ (known gap) $\ge 1/\Delta$ [GKL16, Theorem 3]; the optimal
  constants over all strategies are $2/\Delta$ and $1/(2\Delta)$, and $4/\Delta$ for fixed-design strategies
  on $\mathcal H_\Delta$ [GKL16, Section 2, table]. — *Source:* [GKL16, Section 2, Theorems 3–4] (arXiv
  v2). — *Settles:* separating exploration from exploitation costs a factor 2 even with an adaptive
  stopping time.
- **K38.** [published] **MOSS can be much worse than UCB.** For unit-variance Gaussian rewards,
  $n = k^3$, $\mu_1 = 0$, $\mu_2 = -\sqrt{k/n}$, $\mu_i = -1$ ($i>2$): $R^{\mathrm{UCB}}_n = O(k\log k)$ while
  $R^{\mathrm{MOSS}}_n = \Omega(\sqrt{kn}) = \Omega(k^2)$ for all versions of MOSS [LS, Section 9.2] (claimed;
  "a rigorous proof is quite delicate" and is not given there). — *Source:* [LS, Section 9.2]. —
  *Settles:* minimax optimality does not imply being sub-UCB (a formal proof would be new).
- **K39.** [published] **A conjectured form of the optimal regret is false.** No strategy satisfies
  $R_n(\mu)\le C\sum_{i:\Delta_i>0}(\Delta_i+\frac1{\Delta_i}\log\frac nH)$ for all $\mu$, $n$, $k$, with
  $H := \sum_{i:\Delta_i>0}\Delta_i^{-2}$ (conjecture of Bubeck and Cesa-Bianchi 2012) [L18, Theorem 11].
  — *Source:* [L18, Theorem 11 and proof]. — *Settles:* the finite-time optimal regret is not of the
  best-arm-identification form $\log(n/H)$.
- **K40.** [published] **Thompson sampling with non-informative priors is not optimal for Gaussians
  with unknown variance.** For $K = 2$, $\mu_1>\mu_2$, with arm 2 known exactly and the prior
  $(\sigma_1^2)^{-1-\alpha}$, $\alpha\ge 0$, on arm 1, there is $\xi>0$ independent of $\sigma_2$ with
  $\liminf_T\mathbb E[\mathrm{Regret}(T)]/\log T\ge\xi$; if $\alpha>0$, there are $\xi'>0$, $\eta>0$ with
  $\liminf\mathbb E[\mathrm{Regret}(T)]/T^\eta\ge\xi'$ [HT14, Theorem 2]. The reference ($\alpha = 0$) and
  Jeffreys ($\alpha = 1/2$) priors are covered. — *Source:* [HT14, Theorem 2, Remarks 1–2] (arXiv v1).
  — *Settles:* the asymptotic optimality of Thompson sampling depends on the prior in multi-parameter
  models.
- **K41.** [published] **The Burnetas–Katehakis sufficient condition fails for Gaussians.** The
  sufficient condition (A3) of [BK96] for their index policy BK (K48), in the form of [CHK18,
  Conjecture 1], is false [CHK18, Proposition 6]; this does not show that BK is suboptimal, only that
  the [BK96] technique does not apply [CHK18, Section 1]. — *Source:* [CHK18, Section 1, Proposition 6
  (statement only)] (arXiv v2). — *Settles:* why the CHK modification (K15) was needed.
- **K42.** [published] **Selectivity.** If the class has the Dirac/Bernoulli and product properties
  [SAE13], then for every consistent policy $\tilde A$ and $\rho\in(0,0.4)$, no policy $A$ satisfies
  $\limsup_n\mathbb E[R_n(A)]/\min(\mathbb E[R_n(\tilde A)],\mathbb E[R_n(\mathrm{UCB}(\rho))])\le 1$ for every
  environment [SAE13, Theorem 8]; consequently there is no optimal policy among $\alpha$-consistent
  policies for $\alpha>0.2$, nor among Hannan-consistent ones [SAE13, Section 4]. — *Source:* [SAE13,
  Theorem 8 and following paragraph]. — *Settles:* no policy adapts to the best of two policies.
- **K43.** [published] **Unknown scale.** (i) If a strategy has $\limsup_n R_n/\log n<\infty$ on some
  non-trivial bandit with kurtosis at most $\kappa$, it is not consistent over the union over $\kappa$ of
  these classes [L17, Theorem 7]. (ii) For the class of all sub-Gaussian laws with unknown constant,
  $d_{\inf}(P,\mu^\star,\mathcal M) = 0$, every consistent policy has $\liminf_n R_n/\log n = \infty$, and for
  every $f$ with $f(n)/\log n\to\infty$ some policy has $\limsup_n R_n/f(n) = 0$ [LS, Exercise 16.4]
  (an exercise: statements of the book, proofs left to the reader). — *Source:* [L17, Theorem 7,
  Remark 8]; [LS, Exercise 16.4]. — *Settles:* logarithmic regret needs a known scale-free constraint.

## Algorithms already studied

Notation of the sources: $N_a(t)$ pulls of $a$ before the decision at round $t$, $\hat\mu_a(t)$ the
empirical mean, $\hat\nu_a(t)$ the empirical law, $\log^+ := \max(\log,0)$.

- **K44.** [published] **KL-UCB family.** Generic KL-UCB: play
  $\arg\max_a U_a(t)$, $U_a(t) := \sup\lbrace E(\nu):\nu\in\mathcal D,\ \mathrm{KL}(\Pi_{\mathcal D}(\hat\nu_a(t)),\nu)\le f(t)/N_a(t)\rbrace$
  for a projection $\Pi_{\mathcal D}$ and non-decreasing $f$ [CGMMS13, Algorithm 1]; for an exponential
  family, $U_a(t) = \sup\lbrace\mu: d(\hat\mu_a(t),\mu)\le f(t)/N_a(t)\rbrace$ [CGMMS13, Section 4]. Empirical
  KL-UCB: each arm once, then
  $U_a(t) = \sup\lbrace E(\nu):\nu\in\mathcal M_1(\mathrm{Supp}(\hat\nu_a(t))\cup\lbrace 1\rbrace),\ \mathrm{KL}(\hat\nu_a(t),\nu)\le f(t)/N_a(t)\rbrace$
  [CGMMS13, Algorithm 3]. KL-UCB+ on $[0,1]$:
  $U^{kl}_a(t) = \sup\lbrace\mu\in[0,1]:\mathcal K_{\inf}(\hat\nu_a(t),\mu)\le\frac1{N_a(t)}\ln^+\frac{T}{KN_a(t)}\rbrace$
  [GHMS22, (6)]. kl-UCB++ (horizon $T$): $U_a(t) = \sup\lbrace\mu:\mathrm{kl}(\hat\mu_a(t),\mu)\le g(N_a(t))/N_a(t)\rbrace$ with
  $g(n) = \log^+\big(\frac{T}{Kn}(\log^2_+\frac{T}{Kn}+1)\big)$ [MG17, (2)–(3)]. LMLExplore's `klucbFam` uses
  $f(t) = 1+t\log^2 t$ inside the logarithm [LS, Algorithm 8].
- **K45.** [published] **MOSS and KL-UCB-switch** on $[0,1]$. MOSS index
  $U^m_a(t) = \hat\mu_a(t)+\sqrt{\frac{1}{2N_a(t)}\ln^+\frac{T}{KN_a(t)}}$ [GHMS22, (5)] (LMLExplore's `moss`
  is the sub-Gaussian version of [LS, Algorithm 7]). KL-UCB-switch: $U_a(t) = U^{kl}_a(t)$ if
  $N_a(t)\le f(T,K)$ and $U^m_a(t)$ otherwise, $f(T,K) = (T/K)^{1/5}$ [GHMS22, Section 2.1]. Anytime
  version: with $\varphi(x) = \ln^+(x(1+\ln^2_+x))$,
  $U^{kl\text{-}a}_a(t) = \sup\lbrace\mu:\mathcal K_{\inf}(\hat\nu_a(t),\mu)\le\frac1{N_a(t)}\varphi(\frac{t}{KN_a(t)})\rbrace$,
  $U^{m\text{-}a}_a(t) = \hat\mu_a(t)+\sqrt{\frac1{2N_a(t)}\varphi(\frac{t}{KN_a(t)})}$, switch at $f(t,K) = (t/K)^{1/5}$
  [GHMS22, (9)–(13)].
- **K46.** [published] **IMED and DMED.** IMED: pull each arm once, then pull an arm minimizing
  $I_i(n) := T_i(n)D_{\inf}(\hat F_i(n),\hat\mu^\star(n);\mathcal A)+\log T_i(n)$, ties arbitrary, where
  $\hat\mu^\star(n) := \max_i\hat\mu_i(n)$ [HT15, Algorithm 1]. DMED keeps the list of arms with
  $T_i(n)D_{\inf}(\hat F_i(n),\hat\mu^\star(n);\mathcal A_0)+\log T_i(n)\le\log n$ and pulls them in some order
  [HT15, (3)]. $D_{\inf}$ is computed by the one-dimensional dual of K11.
- **K47.** [published] **Thompson sampling.** Bernoulli: prior Beta(1,1) per arm; at each round sample
  $\theta_i(t)\sim\mathrm{Beta}(S_i+1,F_i+1)$ ($S_i, F_i$ successes and failures) and play
  $\arg\max_i\theta_i(t)$ [AG13, Algorithm 1]. Gaussian with unknown variance, parameter $\alpha\in\mathbb R$:
  pull each arm $n_0 = \max\lbrace 2,3-\lceil 2\alpha\rceil\rbrace$ times, then sample $\tilde\mu_i(t)$ from the posterior
  of $\mu_i$ under the prior $\pi(\mu_i,\sigma_i^2)\propto(\sigma_i^2)^{-1-\alpha}$ and pull $\arg\max_i\tilde\mu_i(t)$
  [HT14, Algorithm 1]; the marginal posterior is a Student law:
  $\sqrt{n(n+2\alpha-1)/S_{i,n}}\,(\mu_i-\bar x_{i,n})$ has the $t$ law with $n+2\alpha-1$ degrees of
  freedom [HT14, (5)], with $\hat\theta_{i,n} = (\bar x_{i,n},S_{i,n})$ the statistics of the source
  ($S_{i,n}$ not transcribed here).
- **K48.** [published] **Index policies for Gaussians with unknown variance.** With
  $\bar X^i_k$ the mean and $S_i^2(k) = \frac1k\sum_{t\le k}(X^i_t-\bar X^i_k)^2$: BK samples each bandit twice,
  then $\arg\max_i\bar X^i_{T_i(n)}+S_i(T_i(n))\sqrt{n^{2/T_i(n)}-1}$ [CHK18, (9)]; CHK samples each
  bandit three times, then $\arg\max_i\bar X^i_{T_i(n)}+S_i(T_i(n))\sqrt{n^{2/(T_i(n)-2)}-1}$ [CHK18, (11)].
- **K49.** [published] **Non-parametric Thompson sampling** on $[0,1]$: for an arm with observed rewards
  $r_1,\dots,r_n$, draw $L\sim\mathrm{Dir}(1,\dots,1)$ ($n+1$ components) and use the weighted average of
  $(1,r_1,\dots,r_n)$ with weights $L$; play the arm with the largest value; the point 1 in the support
  creates the exploration [RH20, Section 3; equivalent compressed form, Algorithm 3]. Multinomial TS:
  Dirichlet posteriors on $\lbrace 0,\frac1M,\dots,1\rbrace$, with randomized rounding for general laws
  [RH20, Remark 1, Lemma 6] (not transcribed).
- **K50.** [published] **KLinf-UCB** on $\mathcal L_B$: one sample per arm; then repeatedly compute
  $U_a(n) = \sup\lbrace x: N_a(n)\,\mathrm{KL}_{\inf}(\hat\eta_a(n),x)\le g_a(n)\rbrace$ for every arm, pick
  $A_n = \arg\max_a U_a(n)$, and pull $A_n$ for a batch of $B_j = \max\lbrace 1,\tilde\varepsilon N_{A_n}(n)\rbrace$ rounds
  (integer rounding as in the source) [AJK21, Algorithm 1]; equivalently
  $U_a(n) = \max\lbrace E(\kappa):\kappa\in\mathcal L,\ N_a(n)\mathrm{KL}(\hat\eta_a(n),\kappa)\le g_a(n)\rbrace$ [AJK21, (5)].
- **K51.** [published] **ADA-UCB** (horizon $n$): each arm once, then
  $\arg\max_i\gamma_i(t)$ with $\gamma_i(t) = \hat\mu_i(t-1)+\sqrt{\frac{2}{T_i(t-1)}\overline{\log}\big(\frac{n}{H_i(t-1)}\big)}$,
  $H_i(t) = T_i(t)K_i(t)$, $K_i(t) = \sum_{j=1}^k\min\lbrace 1,\sqrt{T_j(t)/T_i(t)}\rbrace$, $\overline{\log}$ as in K22
  [L18, Section 2]. It is not an index strategy in the strict sense: $\gamma_i$ depends on the other
  arms' counts.
- **K52.** [published] **MOTS and MOTS-J** (horizon $T$): each arm once; at round $t$, for each arm let
  $\tau_i(t) = \hat\mu_i(t)+\sqrt{\frac{\alpha}{T_i(t)}\log^+\frac{T}{KT_i(t)}}$, sample
  $\tilde\theta_i(t)\sim\mathcal N(\hat\mu_i(t),1/(\rho T_i(t)))$ (MOTS) or from the density
  $J(x)\propto|x-\hat\mu_i(t)|\exp(-\frac{T_i(t)}{2}(x-\hat\mu_i(t))^2)$ (MOTS-J), set
  $\theta_i(t) = \min\lbrace\tilde\theta_i(t),\tau_i(t)\rbrace$ and play $\arg\max_i\theta_i(t)$ [JXSXG21, (2)–(4), (8),
  Algorithm 2].
- **K53.** [published] **OSSB$(\varepsilon,\gamma)$**: at round $t$, compute the solution
  $(c(x,m(t)))_x$ of the Graves–Lai problem at the empirical means $m(t)$; if
  $N(x,t)\ge c(x,m(t))(1+\gamma)\ln t$ for every $x$, play the empirical best arm (exploitation); otherwise
  increment a counter $s(t)$, let $\underline X(t)$ be the least played arm and $\bar X(t)$ the arm minimizing
  $N(x,t)/c(x,m(t))$, and play $\underline X(t)$ if $N(\underline X(t),t)\le\varepsilon s(t)$ (estimation), else $\bar X(t)$
  (exploration) [CMP17, Algorithm 1].
- **K54.** [published] **OSUB** (graph $G$, maximal degree $\gamma$): with $L(n)$ the empirical leader and
  $l_k(n)$ the number of rounds $k$ has been leader, play $L(n)$ if $(l_{L(n)}(n)-1)/(\gamma+1)\in\mathbb N$,
  otherwise the arm of the neighbourhood $N(L(n))$ maximizing
  $b_k(n) = F(\hat\mu_k(n),t_k(n),l_{L(n)}(n))$, where
  $F(p,s,n) = \sup\lbrace q\ge p: sI(p,q)\le\log n+c\log\log n\rbrace$ ($I$ the Bernoulli divergence)
  [CP14, Section 4.2].
- **K55.** [published] **UCB1, ucb-h, ETC.** UCB1: each arm once, then
  $\arg\max_k\hat X_{k,T_k(t-1)}+\sqrt{2\log t/T_k(t-1)}$ [SA11, (2)]; UCB($\rho$) replaces $2\log t$ by
  $\rho\log t$ [SA11, Section 2]. ucb-h (horizon $n$): $\arg\max_k\hat X_{k,T_k(t-1)}+\sqrt{2\log n/T_k(t-1)}$
  [SA11, Section 3]. ETC (two arms): sample alternately until an even stopping time $\tau$, then play
  $\hat a$ [GKL16, Section 2].
- **K56.** [published] **Structured algorithms not transcribed here** (definitions in the sources):
  Algorithm 1 of [LS17] (K27); the saddle-point algorithms of [DSK20, Section 2] (K28); CROP
  [JZ20, Section 3] (K30); IDS [KLVS21, (3) and Algorithm 1] (K31); Robust-UCB [BCL13, Section 2]
  (K18); the kurtosis algorithm [L17, Section 2] (K19). A paper using one of them transcribes it from
  the source and records what it read.

## The owner's dead ends

None yet (to be written by the owner).

## Open problems stated in the literature

Each entry quotes the source's question in our words; the status is as far as this agent read on
2026-11-14 (later work may have answered it: search before writing).

- **K57.** [published] [L18, Section 2]: is there an index strategy (index of an arm from its own
  samples and $t$, or $n-t$) that is minimax optimal, sub-UCB and asymptotically optimal?
  [L18, Section 6]: generalize ADA-UCB's results to broader noise models (exponential families;
  unknown variance). Open as far as read (roadmap D4).
- **K58.** [published] [MG17, Section 6]: (a) an anytime variant of kl-UCB++ — answered for $[0,1]$
  rewards by the anytime KL-UCB-switch (K21); (b) adding finite-time instance near-optimality in
  the sense of Lattimore (2015) — open as far as read (D4, D5); (c) general bounded laws — answered by
  KL-UCB-switch (K21).
- **K59.** [published] [CGMMS13, Sections 6.2 and 8]: finite-time optimal bounds for empirical
  KL-UCB on general bounded laws — answered by [AJK21, Proposition 4] (K10) and by the KL-UCB
  analysis of [GHMS22] (K21).
- **K60.** [published] [HT15, Section 9]: can the moment-generating-function assumption of IMED be
  weakened to finite moments $\mathbb E[X^{2+p}]$? Conjectured yes; open as far as read (D9).
- **K61.** [published] [HT14, Section 5]: does Thompson sampling with non-informative priors fail in
  other multi-parameter models; can the technique be generalized? Open as far as read; later work
  exists (not read): search first (D10c).
- **K62.** [published] [L17, Section 4]: the optimal constants for bounded kurtosis (lower and upper
  bounds); a non-parametric Thompson sampling for this class. Open as far as read (D7, D8, D10).
- **K63.** [published] [LS, Section 16.4]: "plenty of open questions" on asymptotically optimal
  strategies for non-parametric classes; the semi-bounded case is "murky"; bounded kurtosis only up
  to constants. [LS, Exercise 19.5, remark]: simultaneous near-minimax and asymptotic optimality is
  settled for finite-armed stochastic bandits (only there).
- **K64.** [published] [LS, Section 25.3, Note 1]: a practical asymptotically optimal algorithm for
  linear bandits, also near-minimax — addressed for finite linear bandits under $x^\star\ne 0$ by K31,
  and for regular structures by K28; practicality in finite time remains open (D15, D16).
- **K65.** [published] [LS, Section 36.5, Note 2]: characterize the conditions under which Thompson
  sampling is close to optimal. Open (D6, D10).
- **K66.** [published] [JZ20, Section 6 and appendix "Future work"]: (a) an algorithm asymptotically
  optimal and no worse than UCB for every finite class (answered for one class $\mathcal F^{code}$ in
  its appendix, open in general); (b) asymptotic optimality with the standard worst-case regret for
  linear bandits; (c) the optimal number of pulls of non-informative arms; (d) avoiding forced
  sampling for linear and Lipschitz structures (D14, D16).
- **K67.** [published] [DSK20, Section 4]: characterize the problems on which structure-adaptive
  algorithms adapt at small horizons ("the most obvious open problem for structured bandits");
  structure-adapted concentration inequalities (D16).
- **K68.** [published] [KLVS21, after Theorem 5]: is the assumption $x^\star\ne 0$ necessary for the
  asymptotic optimality of IDS? (D16).
- **K69.** [published] [JXSXG21, Section 7]: is MOTS (clipped Gaussian) both minimax and
  asymptotically optimal? (D6).
- **K70.** [published] [AMS09, Section 1]: the conjecture that knowing the horizon significantly
  reduces the risk — answered by [SA11] (K33).
- **K71.** [published] [CHK18, title and Section 1]: the open problem of [BK96] (an asymptotically
  optimal policy for normal populations with unknown means and variances) — answered by [HT14,
  Theorem 1] (K14) and [CHK18, Theorem 4] (K15).

## Conjectures

None of the owner yet. Conjectures of the literature are listed with the open problems (K60, K70).

## Directions judged uninteresting

None yet (to be written by the owner).
