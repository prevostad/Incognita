# PMRM26: Transfer learning in bandits from unknown adaptive policies

| | |
|---|---|
| Work | A. Prevost, T. Mathieu, W. Radji, O.-A. Maillard, *Transfer Learning in Bandits from Unknown Adaptive Policies: Problem-Dependent Lower and Upper Bounds*, arXiv preprint, 2026 |
| Identifiers | arXiv 2610.21582 (v1, 15 Oct 2026, the only version on 2026-11-15) |
| Read | arXiv:2610.21582v1 HTML, through extracts of a fetch tool (short verbatim pieces, joined below): §3.1, §3.2, §4.1 (consistency and $\mathcal K_{\inf}$), §4.2 (the set $\mathcal P([0,1])_L$, the class $\mathcal C_L$, Theorem 2 statement, the sentence on Lemma 22), §7 (one-sided quantities). arXiv e-print of v1 (LaTeX source `main.tex`, read as text): §4.2 after Theorem 2; Appendix E (proof of Theorem 2), with Lemma 22 (label `lem:jointure`) and its proof |
| By, date | Claude Opus 5.5 (write-paper, P003), 2026-11-15; Claude Opus 5.5 (revise, P003), 2026-11-15 (Appendix E, Lemma 22); Claude Opus 5.5 (write-paper, P008), 2026-11-17: the arXiv v1 PDF (arxiv.org/pdf/2610.21582v1), text layer extracted with `pdftotext`: §4.1–§4.2 (Theorem 1, the class $\mathcal C_L$, Theorem 2 and the paragraphs after it), Appendix E in full (the single-game construction, Lemmas 22–24, the proof of Theorem 2, E.1 proof of Lemma 22, E.2 proof of Lemma 23), §6 (Theorem 3, Proposition 4), Appendix D (proof of Proposition 4); Claude Opus 5.5 (revise, P008, round 2), 2026-11-17: the same PDF, text layer (`pdftotext -layout`): §5.1 (KL-UCB, $U^{KL}$, the dual form of $\mathcal K_{\inf}$), §5.2 (the KL-UCB-Transfer index, $\delta_t$, Algorithm 1), §6 (Theorem 3, hypotheses re-checked), §9 (setup of the experiments); Claude Opus 5.5 (bibliographer), 2026-11-17: the same PDF, text layer (`pdftotext -layout`): §7 in full (Theorem 5, "Three regimes", the paragraphs after them), Appendix B opening (Lemmas 11–15 statements, the proof of Theorem 5), B.4 (Lemma 17 statement), B.6 (proof of Lemma 17), §9 paragraph "Interpretation of Figure 4"; the HTML rendering of v1 (fetch tool) for the display of Lemma 17 and the hypotheses of Theorem 5 |

The statements below are copied from the HTML rendering of v1, with the mathematics as written
there (LaTeX of the rendering); the notation $\mathcal P([0,1])$ is the set of probability laws on
$[0,1]$. KNOWN.md (K2, K7, K8 of `roadmaps/TransferBandits/`) summarises the same results.

## Definitions

- **Setting, §3.1.** "Let $\mathcal D$ be a known family of real-valued distributions and let the
  unknown arm distributions be $\nu=(\nu_1,\dots,\nu_K)\in\mathcal D^K$ with means
  $\mu_k=\mathbb E_{X\sim\nu_k}[X]$". "At each round $t\in\{1,\dots,T\}$ a learner $\pi$ selects an
  arm $a_t$ and observes reward $X_t\sim\nu_{a_t}$"; $N_k(T)=\sum_{t=1}^T\mathbf 1(a_t=k)$. "We assume
  without loss of generality that arm 1 is the arm with the highest mean, that is
  $\mu_1=\max_k\mu_k$." "We further assume that there is a single optimal arm (hence arm 1)".
  Regret: $R_{T,\nu}^{\pi}=\sum_{k=1}^K\mathbb E_{\nu,\pi}[N_k(T)](\mu_1-\mu_k)$.
- **Prior data, §3.2.** "Before interacting with the target environment $\nu$, for each arm $k$ the
  learner observes $N^{\prime}_{k}$ prior samples drawn i.i.d. from a source distribution
  $\nu^{\prime}_{k}$." "The counts $(N^{\prime}_{k})_{k}$ may themselves come from an online game,
  making them data-dependent on the prior observations." "The prior counts $(N'_k)_k$ may depend on
  $T$." "We do not assume knowledge of the strategy $\pi^{\prime}$ that determined the counts
  $(N^{\prime}_{k})_{k}$, so that the prior data may, for instance, originate from a bandit game."
  "We do, however, require that $(N^{\prime}_{k})_{k}$ be independent of the target distribution
  $\nu$ of the current game, making $(\nu^{\prime},\pi^{\prime})$ and $\nu$ independent;" "the only
  source of dependence between the prior observations and the current game comes through the pull
  counts $(N_k(T))_k$ chosen by the learner." The expectation "also accounts for the randomness of
  the unknown source $\nu'$ and unknown prior strategy $\pi'$."
- **Discrepancy bound, §3.2.** "We assume a known discrepancy bound between the mean of the source
  game and the target game: $|\mu_{k}-\mu^{\prime}_{k}|<L_{k},\qquad k=1,\ldots,K,$ where
  $(L_{k})_{k}$ are given constants."
- **Classical consistency, §4.1.** The set of consistent algorithms on $\mathcal D$: those $\pi$ with
  "$\forall \nu\in\mathcal{D}$, $\forall \text{ suboptimal arm }k$, $\forall\alpha>0$,
  $\mathbb{E}_{\nu,\pi}[N_k(T)]=o(T^{\alpha})$".
- **$\mathcal K_{\inf}$, §4.1.**
  $\mathcal{K}_{inf}(\nu_k,\mu_1,\mathcal{D}):=\inf_{\tilde{\nu}_k\in\mathcal{D},\ \tilde{\mu}_k>\mu_1}\mathrm{KL}(\nu_k,\tilde{\nu}_k)$.
- **The set $\mathcal P([0,1])_L$, §4.2.** "For convenience, introduce the set
  $\mathcal{P}([0,1])_{L}:=\left\{(\nu,\nu^{\prime})\in\mathcal{P}([0,1])^{K}\times\mathcal{P}([0,1])^{K}\;:\;\forall k,\ |\mu_{k}-\mu^{\prime}_{k}|\leq L_{k}\right\}.$"
- **The class $\mathcal C_L$, §4.2.** "We extend the notion of consistency to this transfer setting
  as follows." "We define our class of consistent algorithms as
  $\mathcal{C}_{L}:=\left\{\pi\;\middle|\;\begin{array}[]{l}\forall(\nu,\nu^{\prime})\in\mathcal{P}([0,1])_{L},\\\forall\text{ prior strategy }\pi^{\prime},\\\forall\text{ suboptimal arm }k,\\\forall\alpha>0\end{array},\ \mathbb{E}_{\nu^{\prime},\pi^{\prime},\nu,\pi}[N_{k}(T)]=o(T^{\alpha})\right\}.$"
  (The line breaks `\\` of the array are those of the rendering.) Note: §3.2 uses the strict
  bound $<$, §4.2 the non-strict $\le$; "prior strategy" is not defined formally.

## Results

- **Theorem 2, §4.2 (lower bound).** "For every algorithm $\pi\in\mathcal{C}_L$, for any
  $(\nu,\nu')\in\mathcal{P}([0,1])_L$, for any prior strategy $\pi'$ that comes from a bandit game
  played over $T'=f(T)$ rounds, for any suboptimal arm $a$:" (i) "If $\mu'_a\leq\mu_1-L_a$ and
  $\limsup_{T\to+\infty}\mathbb{E}_{\nu',\pi'}[N'_a]/\ln T<+\infty$, then
  $\liminf_{T\to+\infty}\frac{\mathbb{E}_{\nu',\pi',\nu,\pi}[N_a(T)]}{\ln T}\geq\liminf_{T\to+\infty}\left(1-\frac{\mathbb{E}_{\nu',\pi'}[N'_a]}{\ln T}\mathcal{K}_{inf}(\nu'_a,\mu_1-L_a)\right)_+\Big/\mathcal{K}_{inf}(\nu_a,\mu_1)$."
  (ii) "If $\mu'_a>\mu_1-L_a$, then
  $\liminf_{T\to+\infty}\frac{\mathbb{E}_{\nu',\pi',\nu,\pi}[N_a(T)]}{\ln T}\geq\frac{1}{\mathcal{K}_{inf}(\nu_a,\mu_1)}$."
  The proof is in Appendix E.
- **Lemma 22, Appendix E.** §4.2, paragraph on tightness: "The change-of-measure argument underlying
  Theorem 2 (Lemma 22) compares two adaptive bandit instances through a KL divergence that depends
  on the source sample size only through the expectation". Setting of Appendix E (summary): the
  prior game over $T'$ rounds and the online game over $T$ rounds are one game of $N:=T'+T$ rounds,
  with i.i.d. uniform $U_1,U_2,\dots$; $I_t:=(U_1,Y_1,\dots,Y_{t-1},U_t)$; $A_t=\pi^\dagger_t(I_t)$ with
  $\pi^\dagger_t:=\pi'$ for $t\le T'$ and $\pi$ for $t>T'$; $Y_t\sim\nu'_{A_t}$ for $t\le T'$, $\nu_{A_t}$
  after; $N'_k:=\sum_{t=1}^{T'}\mathbf 1(A_t=k)$, $N_k(T):=\sum_{t=T'+1}^{N}\mathbf 1(A_t=k)$. So for
  $t>T'$ the learner's input $I_t$ contains the whole ordered prior history. Statement, copied from
  the source (macro `\KL` of the source written $\mathrm{KL}$): "Taking an alternative instance
  $(\tilde \nu ,\tilde\nu')$ such that $\nu \ll \tilde \nu$ and $ \nu' \ll \tilde \nu'$ and using the
  same notation introduced before we have
  $$\mathrm{KL}\left(P^{I_{N+1}}_{( \nu,\nu'), \pi^{\dagger}},P^{I_{N+1}}_{(\tilde \nu,\tilde\nu'), \pi^{\dagger}}\right)  =  \sum_{i=1}^K \mathbb{E}_{\nu', \pi',\nu,\pi }[N_i(T) ]\mathrm{KL}\left(\nu_i, \tilde{\nu}_i\right) + \sum_{i=1}^K \mathbb{E}_{\nu', \pi' }[N'_i ]\mathrm{KL}\left(\nu'_i, \tilde{\nu}'_i\right).$$"
  Proof (summary): the chain rule round by round on $I_{t+1}=(I_t,Y_t,U_{t+1})$, the arm being the
  same function of $I_t$ under both instances, as in the classical case (the source cites GMS19 and
  LS); the case without absolute continuity is dismissed ("both sides of the identity are
  infinite").
- **Lemma 23, Appendix E** (copied from the text layer of the arXiv v1 PDF, 2026-11-17; the
  source writes $\mathcal K_{\inf}(\nu,(\mu,\mu'))$ for the infimum over laws with mean in the
  interval $(\mu,\mu')$): "For every $\nu\in\mathcal P([0,1])$ and $\mu\in(0,1)$ such that
  $\mathbb E[\nu]<\mu$, we can construct a sequence of distribution $(\tilde\nu^{(n)})_n$ such that
  we have two positive sequences $(\varepsilon_n)_n$, $(y_n)_n$ that converge to 0 and for all $n$,
  $\mathrm{KL}(\nu,\tilde\nu^{(n)})\le\mathcal K_{\inf}(\nu,\mu)+y_n$, $\tilde\mu^{(n)}=\mu+\varepsilon_n$.
  In particular we have for every $\mu'>\mu$, $\mathcal K_{\inf}(\nu,(\mu,\mu'))=\mathcal K_{\inf}(\nu,\mu)$."
  Proof (E.2, summary): a minimising sequence $\lambda^{(n)}$, the mixtures
  $\gamma^{(n)}_t:=(1-t)\lambda^{(n)}+t\nu$, a $t^*_n$ with mean $\mu+\varepsilon_n$, and convexity of
  $\mathrm{KL}$: $\mathrm{KL}(\nu,\tilde\nu^{(n)})\le(1-t^*_n)\mathrm{KL}(\nu,\lambda^{(n)})$.
- **Lemma 24, Appendix E** (same extraction): "For any $P\ll Q$ and any random variable $Z$ in
  $[0,1]$, $\mathrm{KL}(P,Q)\ge\mathrm{kl}(\mathbb E_P[Z],\mathbb E_Q[Z])$." Credited to
  "(Maillard, 2019, Lemma. 3.3)", "simply a corollary of the data-processing inequality".
- **Proof of Theorem 2, Appendix E** (same extraction, summary with the source's symbols). $G_a$ is
  the set of pairs $(\tilde\nu,\tilde\nu')$ with $\tilde\mu_a>\mu_1$, $\nu_a\ll\tilde\nu_a$,
  $\nu'_a\ll\tilde\nu'_a$, $|\tilde\mu_a-\tilde\mu'_a|\le L_a$ and $(\tilde\nu_k,\tilde\nu'_k)=(\nu_k,\nu'_k)$
  for $k\ne a$. Lemma 22 gives (5): the divergence of $I_{N+1}$ equals
  $\mathbb E[N_a(T)]\mathrm{KL}(\nu_a,\tilde\nu_a)+\mathbb E_{\nu',\pi'}[N'_a]\mathrm{KL}(\nu'_a,\tilde\nu'_a)$;
  Lemma 24 with $Z=N_a(T)/T$ gives (6); consistency gives $G_{1,T},G_{2,T}\to0$ with
  $\mathbb E[N_a(T)]=G_{1,T}T^\alpha$ and $T-\tilde{\mathbb E}[N_a(T)]=G_{2,T}T^\alpha$; then
  "$\mathrm{kl}(p,q)\ge(1-p)\log\frac1{1-q}-\log(2)$". Case 1 ($\mu'_a>\mu_1-L_a$): $\tilde\nu'_a:=\nu'_a$,
  $\tilde\mu_a\in(\mu_1,\mu'_a+L_a)$, limits $T\to\infty$ then $\alpha\to0$, supremum over $\tilde\nu_a$, and
  Lemma 23. Case 2 ($\mu'_a\le\mu_1-L_a$ and $\limsup_T\mathbb E_{\nu',\pi'}[N'_a]/\ln T=C<\infty$): the
  bound $(1-C\,\mathrm{KL}(\nu'_a,\tilde\nu'_a))_+/\mathrm{KL}(\nu_a,\tilde\nu_a)$, a supremum over $G_a$,
  sequences from Lemma 23 with $\tilde\mu^n_a=\mu_1+\varepsilon_n$, Lemma 23 again for
  $\mathcal K_{\inf}(\nu'_a,(\mu_1+\varepsilon_n-L_a,\mu_1+\varepsilon_n+L_a))$, the inequality
  $\frac1{x+y}\ge\frac1x-\frac y{x^2}$, and "continuity of the $\mathcal K_{\inf}$ on its second argument
  (see Honda and Takemura (2015))" to let $n\to\infty$; last display
  $(1-C\mathcal K_{\inf}(\nu'_a,\mu_1-L_a))_+=\liminf_T(1-\frac{\mathbb E[N'_a]}{\ln T}\mathcal K_{\inf}(\nu'_a,\mu_1-L_a))_+$.
- **§4.2, after Theorem 2** (PDF text layer, 2026-11-17): "Our lower bound applies only when the
  prior game is a classical regret-minimization bandit game, but we believe this could be extended
  to other prior game types (e.g. best-arm identification)." Then the paragraphs "Necessary and
  sufficient condition to have an improvement" and "Tightness of the lower bound" (the example with
  $N'_a=T$ with probability $\varepsilon$).
- **KL-UCB, §5.1** (PDF text layer, 2026-11-17, revise P008 round 2; displays rebuilt from the
  extraction): "In the case $\mathcal D=\mathcal P([0,1])$ we define
  $U^{KL}(N,\nu,\delta):=\max\{\mu\mid N\,\mathcal K_{\inf}(\nu,\mu)\le\delta\}$." The quantity
  $\mathcal K_{\inf}(\hat\nu_N,U)$ is computed by the dual form (credited to Honda and Takemura (2010)):
  $N\mathcal K_{\inf}(\hat\nu_N,U)=\max_{\lambda\in[0,\frac1{1-U}]}\sum_{i=1}^N\ln(1-\lambda(X_i-U))$.
  "With $\delta_t:=\ln t+\ln\ln t$, the index of KL-UCB is defined for each arm $a$ at each time $t$ as
  $U_a(t):=U^{KL}(N_a(t),\hat\nu_a(t),\delta_t)$."
- **KL-UCB-Transfer, §5.2** (same extraction). "If $N'_a=0$, we adopt the convention that the term
  $N'_a\mathcal K_{\inf}(\hat\nu'_a,\cdot)$ is equal to $0$, regardless of the (undefined) value of
  $\hat\nu'_a$." "[W]e redefine, for the remainder of the paper, the index $U_a(t)$ for each arm $a$
  at each time $t>K$ as
  $U_a(t):=\sup\{\mu\mid N_a(t)\mathcal K_{\inf}(\hat\nu_a(t),\mu)+N'_a\mathcal K_{\inf}(\hat\nu'_a,\mu-L_a)\le\delta_t\}$,
  with $\delta_t:=\ln t+\ln\ln t$." **Algorithm 1 (KL-UCB-Transfer)**, line by line: "1: Receive
  the number of arms $K$, prior observations $X'$, upper bound of the distance $L$ / 2: for
  $t=1,\dots,K$ do / 3: Pull each arm once / 4: end for / 5: for $t=K+1,\dots,T$ do / 6: for
  $a=1,\dots,K$ do / 7: Compute $U_a(t)$ / 8: end for / 9: Pull arm $a_t:=\arg\max_aU_a(t)$ (pull
  uniformly at random in arg max if it is not a singleton) / 10: end for".
- **Theorem 3, §6** (PDF text layer, 2026-11-17; displays rebuilt from the extraction; the strict
  hypothesis $|\mu_k-\mu'_k|<L_k$ for every $k$ and $T\ge3$ re-checked in round 2 of P008): "For all
  distributions $\nu,\nu'\in\mathcal P([0,1])$ such that for all $k$ we have $|\mu_k-\mu'_k|<L_k$, for
  every suboptimal arm $a$ and for every $T\ge3$, the algorithm KL-UCB-Transfer satisfies: (i) If
  $\mu'_a<\mu_1-L_a$, $\mathbb E_{\nu',\pi',\nu,\pi}[N_a(T)]\le\frac{\mathbb E_{\nu',\pi'}\big[(\ln T-N'_a\mathcal K_{\inf}(\nu'_a,\mu_1-L_a))_+\big]}{\mathcal K_{\inf}(\nu_a,\mu_1)}+h_1(T)$.
  (ii) If $\mu'_a\ge\mu_1-L_a$, $\mathbb E_{\nu',\pi',\nu,\pi}[N_a(T)]\le\frac{\ln T}{\mathcal K_{\inf}(\nu_a,\mu_1)}+h_2(T)$,
  where $h_1(T)=O\big((\ln T)^{4/5}(\ln\ln T)^{1/5}\big)$ and $h_2(T)=O\big((\ln T)^{4/5}(\ln\ln T)^{1/5}\big)$."
  The dependence of the constants in $O(\cdot)$ is not stated there.
- **Proposition 4, §6** (same extraction): "If $\mathbb E_{\pi',\nu'}\big|N'_a-\mathbb E_{\pi',\nu'}[N'_a]\big|=o(\ln T)$,
  then the lower bound of Theorem 2 matches the upper bound of Theorem 3, except possibly when
  $\mu'_a=\mu_1-L_a$." Proof (Appendix D): with $\delta:=\ln T$, $D:=\mathcal K_{\inf}(\nu'_a,\mu_1-L_a)$,
  $g(n):=(\delta-nD)_+$ is $D$-Lipschitz, so $\mathbb E[(\delta-ND)_+]-(\delta-\bar ND)_+\le D\,\mathbb E|N-\bar N|$.
- **§9 (numerical experiments)** (same extraction, round 2 of P008): "We evaluate KL-UCB-Transfer
  against classical KL-UCB (no transfer). All rewards are Beta distributions with variance fixed to
  $\sigma^2=0.05$ across all experiments (only the mean varies)." $M=100$ repetitions, horizon
  $T=10^5$, bands $\pm3\hat\sigma_M/\sqrt M$. §9.1: $K=4$, $\mu=(0.6,0.5,0.45,0.35)$, three sources
  (Table 2), with $N'_a=500$ (left panel) or the counts of KL-UCB played on $\mu'$ for $T'=2000$ rounds
  (right panel).
- **Theorem 5, §7 "Robustness to misspecification of L"** (arXiv v1 PDF, pp. 12–13, text layer
  (`pdftotext -layout`), bibliographer, 2026-11-17; displays rebuilt from the extraction, the
  subscripts $\nu',\pi',\nu,\pi$ of $\mathbb E$ as printed): "For all distributions
  $\nu,\nu'\in\mathcal P([0,1])$, for every suboptimal arm $a$ and for every $T\ge3$, the algorithm
  KL-UCB-Transfer (run with prior data and discrepancy bound $L$) satisfies the following. Let
  $\mu^\dagger\in(\mu_a,\mu_1]$ be any real number such that $\mu^\dagger<\mu'_1+L_1$. Then
  $$\mathbb E_{\nu',\pi',\nu,\pi}[N_a(T)]\le\frac{\ln T}{\mathcal K_{\inf}(\nu_a,\mu^\dagger)}+h_{\nu,\nu',\mu^\dagger,L}(T).$$
  If moreover $\mu'_a+L_a<\mu^\dagger$, then
  $$\mathbb E_{\nu',\pi',\nu,\pi}[N_a(T)]\le\frac{\mathbb E_{\nu',\pi'}\big[\big(\ln T-N'_a\mathcal K_{\inf}(\nu'_a,\mu^\dagger-L_a)\big)_+\big]}{\mathcal K_{\inf}(\nu_a,\mu^\dagger)}+g_{\nu,\nu',\mu^\dagger,L}(T),$$
  where $h_{\nu,\nu',\mu^\dagger,L}(T)=O\big((\ln T)^{4/5}(\ln\ln T)^{1/5}\big)$ and
  $g_{\nu,\nu',\mu^\dagger,L}(T)=O\big((\ln T)^{4/5}(\ln\ln T)^{1/5}\big)$." Then: "An explicit
  expression for both $h_{\nu,\nu',\mu^\dagger,L}$ and $g_{\nu,\nu',\mu^\dagger,L}$ is given in the proof
  in section B." "We remind that $\mu^\dagger$ is not an input of the algorithm. The algorithm only
  uses the prior data $(N'_a,\hat\nu'_a)_a$ and the discrepancy bounds $(L_a)_a$." No hypothesis
  $|\mu_k-\mu'_k|<L_k$ is made (unlike Theorem 3). The HTML rendering (fetch tool, 2026-11-17) gives
  the same hypotheses ($\mu^\dagger\in(\mu_a,\mu_1]$, $\mu^\dagger<\mu'_1+L_1$; second bound under
  $\mu'_a+L_a<\mu^\dagger$).
- **"Three regimes", §7, after Theorem 5** (same extraction): "In the well-specified regime, where
  $|\mu_a-\mu'_a|<L_a$ holds for all arms $a$, we in particular have $\mu_1<\mu'_1+L_1$, and choosing
  $\mu^\dagger:=\mu_1$ in Theorem 5 recovers Theorem 3. When this condition is violated, i.e.,
  $\mu'_1+L_1<\mu_1$, logarithmic regret may still hold as long as $\mu'_1+L_1>\mu_a$: any
  $\mu^\dagger\in(\mu_a,\mu'_1+L_1)$ yields a mildly misspecified regime with a degraded constant. If
  instead $\mu'_1+L_1\le\mu_a$, no admissible choice of $\mu^\dagger$ exists and our theorem gives no
  guarantee, a severely misspecified regime." The following paragraphs (summary): "Asymmetry of
  discrepancy requirements" (the bound $L_1$ on the optimal arm decides whether a logarithmic regime
  exists; the $L_a$, $a\ne1$, only affect the leading constant); "Favorable overestimation regime"
  (if $\mu'_a>\mu_a$ for all $a$, $L_a=0$ is valid); "Small number of prior data" (if $N'_k\le B$
  a.s. with $B$ independent of $T$, the classical KL-UCB rate is recovered even in the severely
  misspecified regime; stated without proof, "it can be deduced easily from the proof of Theorem 5
  by using Lemma 9"). §8 extends Theorem 5 to several sources ("Taking $M:=2$ recovers exactly
  Theorem 5"; not read further).
- **Lemma 17, Appendix B.4 "Proof of Lemma 14"** (arXiv v1 PDF, p. 31, text layer; the display is
  garbled in the extraction and was rebuilt with the HTML rendering of v1, whose LaTeX fragment
  `\left(1-e^{-2\eta^{2}}\right)^{3}` fixes the exponent and the power; bibliographer, 2026-11-17):
  "Lemma 17 For $\eta:=\mu'_1+L_1-\mu^\dagger+\varepsilon>0$
  $$\mathbb E_{\nu',\pi'}\Big[\exp\big(N'_1\mathcal K_{\inf}(\hat\nu'_1,\mu^\dagger-\varepsilon-L_1)\big)\Big]\le\frac{2+18\ln(1/(1-\mu'_1))}{\big(1-e^{-2\eta^2}\big)^3}+2."$$
  Context (Appendix B, proof of Theorem 5): the standing assumptions are those of Lemma 11:
  $\mu^\dagger>\mu_a$, $\mu^\dagger\le\mu_1$, $\mu^\dagger\le\mu'_1+L_1$, and
  "$\varepsilon>0$, $\varepsilon<\mu^\dagger$, $\varepsilon\le\frac{(1-\mu^\dagger)\mathcal K_{\inf}(\nu_a,\mu^\dagger)}4$";
  Lemma 17 itself states only $\eta>0$. It is used in the proof of Lemma 14 (the term of the optimal
  arm, $\sum_{t=K+1}^T\sum_{s=1}^t\mathbb 1\big(\mathcal K_{\inf}(\hat\nu_{1,s},\mu_1)>\frac{\delta_t-N'_1\mathcal K_{\inf}(\hat\nu'_1,\mu^\dagger-\varepsilon-L_1)}s+2\varepsilon^2\big)$),
  whose bound is $\big(\frac{2+18\ln(1/(1-\mu'_1))}{(1-e^{-2\eta^2})^3}+2\big)\frac{81(2+\ln\ln T)}{\varepsilon^4}$.
  In the proof of Theorem 5, $\varepsilon\asymp(\ln\ln T/\ln T)^{1/5}$ and $\eta\to\mu'_1+L_1-\mu^\dagger>0$.
  Proof (B.6, summary): write $\mu^\dagger-\varepsilon-L_1=\mu'_1-\eta$; on $\{\hat\mu'_1\ge\mu'_1-\eta\}$
  the exponent is $0$ (contributes $\le1$); on the complement, the second part of Lemma 10 gives
  $\mathcal K_{\inf}(\hat\nu'_1,\mu'_1-\eta)\le\mathcal K_{\inf}(\hat\nu'_1,\mu'_1)-2\eta^2$; the dependence
  on $\pi'$ is removed by summing over all sample sizes $s$ ("$\le1+\sum_{s=1}^{+\infty}\mathbb E_{\nu'}[\exp(s(\mathcal K_{\inf}(\hat\nu'_{1,s},\mu'_1)-2\eta^2))]$");
  each term by the tail integral, the bound $\mathcal K_{\inf}(\hat\nu'_{1,s},\mu'_1)\le\ln(1/(1-\mu'_1))$,
  the concentration Lemma 7 (a tail $e(2s+1)e^{-su}$), giving $s^2e^{-2s\eta^2}(1+9\ln(1/(1-\mu'_1)))$, then
  a sum over $s$. §9 ("Interpretation of Figure 4") remarks that the factor $(1-e^{-2\eta^2})^{-3}\approx(2\eta^2)^{-3}$ "diverges as
  $\eta\to0$" (Lemmas 14 and 17).
- **§7 (one-sided condition).** "The analysis only relies on the one-sided quantities
  $\mu_a'+L_a$, rather than on the symmetric discrepancies"; the lower inequalities
  $\mu'_a-L_a<\mu_a$ "play no role in the regret analysis".

## Techniques

Change of measure on the pair (prior data, online game), with the source entering through
$\mathbb E_{\nu',\pi'}[N'_a]$ (Lemma 22: the prior game and the online game written as one bandit
game, then the divergence decomposition of bandit histories); KL-UCB-type index penalised by the source
(KNOWN K8). Upper bounds (Theorems 3 and 5, Appendix B): the KL-UCB analysis of CGMMS13 with a
comparison level $\mu^\dagger$; the source sample of the optimal arm enters through the margin
$\eta=\mu'_1+L_1-\mu^\dagger+\varepsilon$ and the exponential moment of
$N'_1\mathcal K_{\inf}(\hat\nu'_1,\cdot)$ (Lemma 17), the dependence on the unknown prior strategy
being removed by a union over all sample sizes.

## Where Incognita uses it

Roadmap TransferBandits (KNOWN K2–K8; Definitions: consistency). Papers: P002 (Section 2, the class
$\mathcal C_L$); P003 (Definition `def:consistency`, copied from §4.2 above; Closest known); P008
(the blueprint of Theorem 2: Corollary `cor:source` is Theorem 2 in the setting of P003, with
learners that see the source data; Lemmas 23 and the two cases of Appendix E in `lem:window` and
`lem:alternative`; Lemma 22 replaced by Corollary 4.2 of P003; Algorithm 1 with $\delta_t$ of §5.2
simulated in Section `sec:examples`); P002 also cites Theorem 5 (its parameter $\mu^\dagger$, the
misspecification question) and Lemma 17 (the margin on the source of the optimal arm), statements
above.
