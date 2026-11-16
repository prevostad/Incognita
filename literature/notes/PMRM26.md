# PMRM26: Transfer learning in bandits from unknown adaptive policies

| | |
|---|---|
| Work | A. Prevost, T. Mathieu, W. Radji, O.-A. Maillard, *Transfer Learning in Bandits from Unknown Adaptive Policies: Problem-Dependent Lower and Upper Bounds*, arXiv preprint, 2026 |
| Identifiers | arXiv 2610.21582 (v1, 15 Oct 2026, the only version on 2026-11-15) |
| Read | arXiv:2610.21582v1 HTML, through extracts of a fetch tool (short verbatim pieces, joined below): §3.1, §3.2, §4.1 (consistency and $\mathcal K_{\inf}$), §4.2 (the set $\mathcal P([0,1])_L$, the class $\mathcal C_L$, Theorem 2 statement, the sentence on Lemma 22), §7 (one-sided quantities). arXiv e-print of v1 (LaTeX source `main.tex`, read as text): §4.2 after Theorem 2; Appendix E (proof of Theorem 2), with Lemma 22 (label `lem:jointure`) and its proof |
| By, date | Claude Opus 5.5 (write-paper, P003), 2026-11-15; Claude Opus 5.5 (revise, P003), 2026-11-15 (Appendix E, Lemma 22) |

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
- **§7 (one-sided condition).** "The analysis only relies on the one-sided quantities
  $\mu_a'+L_a$, rather than on the symmetric discrepancies"; the lower inequalities
  $\mu'_a-L_a<\mu_a$ "play no role in the regret analysis".

## Techniques

Change of measure on the pair (prior data, online game), with the source entering through
$\mathbb E_{\nu',\pi'}[N'_a]$ (Lemma 22: the prior game and the online game written as one bandit
game, then the divergence decomposition of bandit histories); KL-UCB-type index penalised by the source
(KNOWN K8).

## Where Incognita uses it

Roadmap TransferBandits (KNOWN K2–K8; Definitions: consistency). Papers: P002 (Section 2, the class
$\mathcal C_L$); P003 (Definition `def:consistency`, copied from §4.2 above; Closest known).
