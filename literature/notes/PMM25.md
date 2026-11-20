# PMM25: Asymptotically optimal problem-dependent bandit policies for transfer learning

| | |
|---|---|
| Work | A. Prevost, T. Mathieu, O.-A. Maillard, *Asymptotically Optimal Problem-Dependent Bandit Policies for Transfer Learning*, Proceedings of the 17th Asian Conference on Machine Learning (ACML 2025), PMLR 304:319–334, 2025 |
| Identifiers | arXiv 2509.19098 (v1, 23 Sep 2025, the only version); PMLR page proceedings.mlr.press/v304/prevost26a.html |
| Read | arXiv:2509.19098v1 PDF (arxiv.org/pdf/2509.19098v1), text layer (`pdftotext -layout`) for the whole paper, and page images of pp. 3–6 and 11–13 for every display copied below: abstract; §1 (contributions); §2 (paragraph "Non-contextual transfer bandits"); §3 in full ((1), the classical and the transfer setting); §4 in full (Remark 1, Definition 2, Theorem 3 in both forms, the paragraphs after it, §4.2 with Corollary 4, its proof sketch, (2), (3)); §5 in full (§5.1 KL-UCB, §5.2 $f^+_a$, index (4), Remark 5); §6 (Theorem 6 and the paragraph after it); §7 opening; reference list; Appendix A in full (Lemma 7, proof of Theorem 3, proof of Lemma 7); Appendix B opening (shorthand, Lemmas 8–11 statements, the proof outline, (5)–(6)). The proof of Theorem 6 after (6), B.1–B.4 and the detailed proofs of Lemmas 9–11 were not read. Also the PMLR PDF (raw.githubusercontent.com/mlresearch/v304/main/assets/prevost26a/prevost26a.pdf), text layer: header "Proceedings of Machine Learning Research 304, 2025", "Editors: Hung-yi Lee and Tongliang Liu"; the text from Remark 1 to the end of §4.2, §5.2, Theorem 6 and Appendix A, compared word by word with arXiv v1: the same words and the same numbers (only the layout of the extracted formulas differs) |
| By, date | Claude Opus 5.5 (bibliographer), 2026-11-20 |

The statements are copied from arXiv v1, as printed (the PDF page images); the PMLR version has the
same text and numbering for every item below. Earlier sessions read the same parts through the
HTML rendering and a fetch tool (`index.md`, row PMM25), without a note.

## Setting (§3)

- **Classical setting.** "We consider a known family of distributions $\mathcal D$ and unknown arm
  distributions $\nu=(\nu_1,\dots,\nu_K)\in\mathcal D^K$ with means $\mu_k$. At each round $t$, a
  learner selects arm $a_t$ and observes reward $X_t\sim\nu_{a_t}$. Assume w.l.o.g. that arm 1 has
  the highest mean. Let $\mathbf 1\{\cdot\}$ denote the indicator. the cumulative regret is
  $$R_T=\sum_{k=1}^K\mathbb E[N_k(T)]\,(\mu_1-\mu_k),\quad\text{where}\quad N_k(T)=\sum_{t=1}^T\mathbf 1\{a_t=k\}."$$
- **Consistency in the classical setting and (1).** "A strategy is *consistent* if for each
  suboptimal arm $k$, $\mathbb E[N_k(T)]=o(T^\alpha)$ for all $\alpha>0$. For any consistent
  algorithm and suboptimal arm $k$, the following asymptotic lower bound holds Lattimore and
  Szepesvári (2020):
  $$\liminf_{T\to\infty}\ \inf_{\substack{\tilde\nu_k\in\mathcal D\\ \mathbb E[\tilde\nu_k]>\mu_1}}\frac{\mathbb E[N_k(T)]\,\mathrm{KL}(\nu_k,\tilde\nu_k)}{\ln T}\ \ge\ 1,\qquad(1)$$"
- **Transfer learning setting.** "Before interacting with the target $\nu$, we observe $N'_k$ i.i.d.
  samples from related source distributions $\nu'=(\nu'_1,\dots,\nu'_K)\in\mathcal D'^K$ satisfying
  $d_k(\nu_k,\nu'_k)\le L_k$. The regret on $\nu$ remains $R_T$ as defined above." In §1 the
  learner "knows a family of (pseudo-)distance $d_k$ and upper bounds $L_k>0$".

## Results

- **Remark 1, §4.** "In the rest of the paper, all $o(\cdot)$ and $O(\cdot)$ notation refer to the
  limit $T\to\infty$. Since offline sample sizes $N'_k$ may depend arbitrarily on $T$ (or even be
  $+\infty$), any $o(\cdot)$ or $O(\cdot)$ usage must explicitly account for possible dependence on
  $N'_k$."
- **Definition 2, §4.1.** "An algorithm is said to be *consistent* (w.r.t.
  $(\mathcal D,\mathcal D',d,L,N')$) if for every pair $(\nu,\nu')\in\mathcal D^K\times\mathcal D'^K$
  and every suboptimal arm $k$,
  $$\forall\,\alpha>0,\quad\mathbb E[N_k(T)]=o(T^\alpha)\quad(T\to\infty)."$$
  As printed, the pairs range over all of $\mathcal D^K\times\mathcal D'^K$: the constraint
  $d_k(\nu_k,\nu'_k)\le L_k$ of §3 is not repeated in the definition ($d$ and $L$ appear only in
  "w.r.t.").
- **Theorem 3, §4.1.** "Let a consistent algorithm operate under $(\mathcal D,\mathcal D',d,L,N')$.
  For any suboptimal arm $k$,
  $$\liminf_{T\to\infty}\ \inf_{\substack{\tilde\nu_k\in\mathcal D,\ \tilde\nu'_k\in\mathcal D'\\ \mathbb E[\tilde\nu_k]>\mu_1,\ d_k(\tilde\nu_k,\tilde\nu'_k)\le L_k}}\ \frac{\mathbb E[N_k(T)]\ \mathrm{KL}(\nu_k,\tilde\nu_k)+N'_k\ \mathrm{KL}(\nu'_k,\tilde\nu'_k)}{\ln T}\ge1.$$
  Equivalently, defining $\mathcal K_{\inf}(\nu'_k;d_k,\tilde\nu_k,L_k):=\inf\{\mathrm{KL}(\nu'_k,\tilde\nu'_k)\mid\tilde\nu'_k\in\mathcal D',\ d_k(\tilde\nu_k,\tilde\nu'_k)\le L_k\}$,
  $$\liminf_{T\to\infty}\ \inf_{\substack{\tilde\nu_k\in\mathcal D\\ \mathbb E[\tilde\nu_k]>\mu_1}}\ \frac{\mathbb E[N_k(T)]\ \mathrm{KL}(\nu_k,\tilde\nu_k)+N'_k\,\mathcal K_{\inf}(\nu'_k;d_k,\tilde\nu_k,L_k)}{\ln T}\ge1."$$
  The paragraphs after it (summarised): $N'_k$ is "any non-negative integer (possibly depending on
  $T$) or even $+\infty$", deterministic; $N'_k=0$ or $N'_k=o(\ln T)$ recovers (1); $L_k\to\infty$
  makes $\mathcal K_{\inf}(\nu'_k;d_k,\tilde\nu_k,L_k)\to0$; $L_k=0$ with $d_k$ separating gives
  (1) with "effective sample size $\mathbb E[N_k(T)]+N'_k$"; prior data on the optimal arm do not
  change the bound. Proof: Appendix A (below).
- **Corollary 4 (Gaussian lower bound), §4.2.** The setting of §4.2: "$\mathcal D=\{\mathcal N(\mu,\sigma^2)\}$,
  $\mathcal D'=\{\mathcal N(\mu,\sigma'^2)\}$, $d_k(\mathcal N(\mu,\sigma^2),\mathcal N(\tilde\mu,\sigma'^2))=|\mu-\tilde\mu|$.
  Hence the constraint $|\tilde\mu_k-\tilde\mu'_k|\le L_k$. We will also note $(x)_+:=\max\{x,0\}$."
  Corollary 4: "Under the Gaussian setting with known variances and mean-based distance defined
  above, any consistent algorithm satisfies for each suboptimal arm $k$:
  $$\liminf_{T\to\infty}\frac{\mathbb E[N_k(T)]}{\ln T}\,\frac{(\mu_1-\mu_k)^2}{2\,\sigma^2}+\frac{N'_k}{\ln T}\,\frac{(\mu_1-\mu'_k-L_k)_+^2}{2\,\sigma'^2}\ge1.\qquad(2)"$$
  Only a proof sketch is given ("Apply Theorem 3 with $\mathrm{KL}(\mathcal N(\mu,\sigma^2),\mathcal N(\tilde\mu,\sigma^2))=\frac{(\mu-\tilde\mu)^2}{2\,\sigma^2}$,
  and similarly for source-to-source KL"). Then: "Equivalently, solving for the expected number of
  pulls yields:
  $$\mathbb E[N_k(T)]\ge\frac{2\,\sigma^2}{(\mu_1-\mu_k)^2}\Big(\ln T-N'_k\,\tfrac{(\mu_1-\mu'_k-L_k)_+^2}{2\sigma'^2}\Big)_++o(\ln T).\qquad(3)"$$
  (In (2) the $\liminf$ is printed before the first fraction only; the sum of the two terms is
  what is meant, as in Theorem 3.)
- **KL-UCB-Transfer, §5.2.** "assuming Gaussian distributions with known variance as in Section
  4.2, we define the cost function with respect to the prior data as follows:
  $$f^+_a(q):=N'_a\frac{(q-(\hat\mu'_a(t)+L_a))_+^2}{2\sigma'^2}$$
  In this setting, the index becomes:
  $$U_a(t):=\max\Big\{q\ \Big|\ N_a(t)\frac{(q-\hat\mu_a(t))_+^2}{2\sigma^2}+f^+_a(q)\le\delta_t\Big\},\qquad(4)$$
  with $\delta_t=\ln t+3\ln(\max(1,\ln t))$, we compute $U_a(t)$ each turn and pull the arm with
  highest index". Remark 5: "If there is no prior data, KL-UCB-Transfer reverts to classical
  KL-UCB." ($\hat\mu'_a$ is the mean of the $N'_a$ source samples; it does not change with $t$.)
  The experiments of §7 use $\delta_t=(1+\varepsilon)\log t$ with $\varepsilon=1/20$ instead.
- **Theorem 6 (KL-UCB-Transfer Regret Bound), §6.** "Suppose for each arm $k$ we have $N'_k$ i.i.d.
  samples from $\nu'_k=\mathcal N(\mu'_k,\sigma'^2)$ and that the true target law is
  $\nu_k=\mathcal N(\mu_k,\sigma^2)$ with $|\mu_k-\mu'_k|\le L_k$. Then under KL-UCB-Transfer, every
  suboptimal arm $a$ satisfies
  $$\mathbb E[N_a(T)]\ \le\ \frac{2\,\sigma^2}{(\mu_1-\mu_a)^2}\left(\ln T-N'_a\,\frac{\big(\mu_1-(\mu'_a+L_a)\big)_+^2}{2\,\sigma'^2}\right)_++O\big((\ln T)^{2/3}\big)."$$
  The paragraph after it: optimality "according to Eq (3)"; "The main challenge is handling
  $N'_a$, which may be arbitrarily large and depend on $T$." The statement does not say how the
  $O((\ln T)^{2/3})$ term depends on $N'_a$ or on the other parameters (Remark 1); its "exact
  expression" is said to be in the proof (Appendix B, not read beyond (6)).
- **Lemma 7, Appendix A.** "Let $(\nu,\nu')$ and $(\tilde\nu,\tilde\nu')$ be two sets of arm
  distributions in our setting. Denote by $\mathbb P_{(\nu,\nu')\pi,T}$ the canonical probability
  measure of the bandit model using strategy $\pi$ and arm distributions $(\nu,\nu')$ up to time
  $T$. Then,
  $$\mathrm{KL}(\mathbb P_{(\nu,\nu')\pi,T},\mathbb P_{(\tilde\nu,\tilde\nu')\pi,T})=\sum_{k=1}^K\mathbb E_{(\nu,\nu')}[N_k(T)]\,\mathrm{KL}(\nu_k,\tilde\nu_k)+\sum_{k=1}^KN'_k\,\mathrm{KL}(\nu'_k,\tilde\nu'_k)."$$
  Followed by: "This lemma parallels Lemma 15.1 in Lattimore and Szepesvári (2020), except for the
  term $\sum_{k=1}^KN'_k\,\mathrm{KL}(\nu'_k,\tilde\nu'_k)$ accounting for initial offline data."
- **Lemmas 8–11, Appendix B** (statements only; shorthand $f^+_a(q)=N'_a\frac{(q-(\hat\mu'_a+L_a))_+^2}{2\sigma'^2}$,
  $d(a,b)=\frac{(b-a)^2}{2\sigma^2}$, $d^+(a,b)=\frac{(b-a)_+^2}{2\sigma^2}$).
  Lemma 8: "For all $T>1$, for all arm $a\ne1$, we have the inequality
  $\sum_{t=1}^T\mathbf 1(A_t=a,\ \mu_1\le U_1(t))\le\sum_{s=1}^T\mathbf 1\big(s\,d^+(\hat\mu_{a,s},\mu_1)+f^+_a(\mu_1)\le\delta_T\big)$."
  Lemma 9: "For every $\delta_t\xrightarrow[T\to+\infty]{}+\infty$ and for all arm $a\ne1$, we have
  the inequality $\mathbb E\big[(\delta_T-f^+_a(\mu_1))_+\big]\le\Big(\delta_T-N'_a\frac{(\mu_1-(\mu'_a+L_a))_+^2}{2\sigma'^2}\Big)_++O(\sqrt{\delta_T})$."
  Lemma 10: "There exists $C'>0$ that depends only on $\sigma,\sigma',L_1,\mu_1,\mu'_1$, such that:
  $\mathbb E\big[\exp\big(f^+_1(\mu_1)\big)\big]\le C'$."
  Lemma 11: "For all $t\ge1$, using the choice $\delta_t:=\ln t+3\ln(\max(1,\ln t))$,
  $\mathbb P(\mu_1>U_1(t))=O\Big(\frac{\mathbb E[e^{f^+_1(\mu_1)}]}{t\ln t}\Big)$."
  Lemma 8 is proved in B.1; Lemmas 9–11 have proof sketches in B.2–B.4 and "full proofs in the
  Supplement" (none of these read).

## Techniques

- **Change of measure with the source samples as extra likelihood factors** (Lemma 7 and its proof,
  Appendix A, p. 12 of v1): the density of (offline data, actions, rewards) factorises as
  $\prod_k\prod_{i\le N'_k}p_{\nu'_k}(x'_{i,k})\prod_t\pi_t(a_t\mid\dots)p_{\nu_{a_t}}(x_t)$; the
  log-likelihood ratio and its expectation give the divergence decomposition with the extra term
  $\sum_kN'_k\mathrm{KL}(\nu'_k,\tilde\nu'_k)$. Credited to Lattimore and Szepesvári (2020), Lemma
  15.1 (`LS`, "We follow the same idea"). The sizes $N'_k$ are deterministic, which makes the
  source term a constant.
- **Data-processing inequality with $Z=N_k(T)/T$** (proof of Theorem 3, p. 11): "using the
  data-processing inequality (e.g., (Maillard, 2019, Lemma 3.3)) combined with the KL
  decomposition of Lemma 7", the bound
  $\mathbb E_{(\nu,\nu')}[N_k(T)]\,\mathrm{KL}(\nu_k,\tilde\nu_k)+N'_k\,\mathrm{KL}(\nu'_k,\tilde\nu'_k)\ge kl\Big(\frac{\mathbb E_{(\nu,\nu')}[N_k(T)]}{T},\frac{\mathbb E_{(\tilde\nu,\tilde\nu')}[N_k(T)]}{T}\Big)$,
  where the alternative changes only the pair of arm $k$ ("such that arm $k$ becomes optimal, while
  keeping the distributions $(\nu_i,\nu'_i)_{i\ne k}$ unchanged"). Maillard (2019) is the
  habilitation "Mathematics of Statistical Sequential Decision Making", Université de Lille, HAL
  tel-02162189 (reference list; not read).
- **Lower bound on kl** (same proof): "for all $p,q\in(0,1)$ we have
  $kl(p,q)=(1-p)\ln\big(\frac1{1-q}\big)+\underbrace{p\ln(1/q)}_{\ge0}+\underbrace{p\ln(p)+(1-p)\ln(1-p)}_{\ge-\ln2}$",
  giving the lower bound
  $\Big(1-\frac{\mathbb E_{(\nu,\nu')}[N_k(T)]}{T}\Big)\ln\Big(\frac{T}{T-\mathbb E_{(\tilde\nu,\tilde\nu')}[N_k(T)]}\Big)-\ln(2)$,
  then consistency under both instances and $\alpha\to0$. This is the identity (11) of GMS19 (the
  same three terms in another order, the same two marked $\ge0$ and $\ge-\ln2$; GMS19 states it on
  $[0,1]^2$, PMM25 on $(0,1)^2$) and the bound (10) of the proof of GMS19, Theorem 1
  (`notes/GMS19.md`). GMS19 is not in the reference list of PMM25, and no source is credited
  for this step.
- **Order of the infimum and the liminf.** The proof bounds the ratio for one fixed alternative
  and ends: "Since this is true for all $\alpha>0$, taking the infimum over all
  $(\tilde\nu,\tilde\nu')\in\mathcal D\times\mathcal D'$ such that arm $k$ becomes optimal (with all
  other arms unchanged) yields the result in Theorem 3." That argument gives
  $\inf_{\text{alt}}\liminf_T(\cdot)\ge1$; the statement of Theorem 3 writes
  $\liminf_T\inf_{\text{alt}}(\cdot)\ge1$, which the proof does not address. The consistency used
  is that of Definition 2 at the alternative pair $(\tilde\nu,\tilde\nu')$, which the printed
  definition grants for every pair of $\mathcal D^K\times\mathcal D'^K$; the constraint
  $d_k(\tilde\nu_k,\tilde\nu'_k)\le L_k$ of the infimum is not used in the proof as written.
- **Upper bound** (Appendix B outline, p. 13): the split (5) of $\mathbb E[N_a(T)]$ into the rounds
  where the optimal index underestimates $\mu_1$ (Lemmas 10–11, giving (6), $O(\ln\ln T)$) and the
  rounds where it does not (Lemma 8, a random threshold $M:=\frac{(\delta_T-f^+_a(\mu_1))_+}{(1-\varepsilon)^2d(\mu_a,\mu_1)}$,
  Lemma 9). Credited to Garivier and Cappé (2011) and Cappé et al. (2013) (`CGMMS13`): "The
  changes in the proof [...] include additional conditioning steps, Lemma 9, and Lemma 10, which
  arise from the inclusion of prior data"; Lemma 8 "mimes the one of Lemma 7 in Garivier and
  Cappé (2011)".

## Where Incognita uses it

- `papers/P002-transfer-drift-between-laws/`: `prop:lower` is stated as "a variant of
  [PMM25, Theorem 3]" with the same proof [PMM25, Appendix A]; the paragraph after it compares its
  class $\mathrm{Cons}(N')$ with [PMM25, Definition 2]; the introduction and related work cite
  Theorem 3, Theorem 6 and the index [PMM25, Section 5.2, (4)]; the appendix of the sources of the
  techniques credits the decomposition with a source to [PMM25, Appendix A].
- `papers/P003-transfer-setting/` (introduction, the model with deterministic source sizes,
  [PMM25, Section 3]) and `papers/P008-transfer-lower-bound/` (comparison with [PMM25, Theorem 3]).
- `roadmaps/TransferBandits/`: the published work listed in ROADMAP.md; item F2 ("The Gaussian
  results of the ACML paper, if they are not special cases of F1"); KNOWN.md K1. An external paper
  for F2 would formalise Corollary 4 and Theorem 6 from this note.
