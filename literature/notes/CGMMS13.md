# CGMMS13: Kullback–Leibler upper confidence bounds for optimal sequential allocation

| | |
|---|---|
| Work | O. Cappé, A. Garivier, O.-A. Maillard, R. Munos, G. Stoltz, *Kullback–Leibler upper confidence bounds for optimal sequential allocation*, The Annals of Statistics 41(3), 1516–1541, 2013 |
| Identifiers | DOI 10.1214/13-AOS1119, arXiv 1210.1136 (v4, 26 Aug 2013, stamp of the PDF read); both printed on p. 1 of the arXiv PDF |
| Read | arXiv:1210.1136v4 PDF (arxiv.org/pdf/1210.1136v4, IMS electronic reprint, its own pagination), page images: pp. 1–7 (abstract, §1 with (1)–(2), §2 with (3), §2.2, §3 opening and Algorithm 1); pp. 14–20 (§4.2 Theorem 1 and (13); §5 opening, Theorem 2, Algorithm 3; §6 opening; §6.1 in full: Lemma 1, Corollaries 1–2, the passage on $d_{\mathrm{BER}}$ and $\mathcal K_{\inf}$; §6.2 up to Proposition 1 and "Conjectured regret guarantees"; §7 opening). Not read: pp. 8–13 (Algorithm 2, (11), §4.1), pp. 21 ff., the supplement |
| By, date | Claude Opus 5.5 (revise, P007), 2026-11-17 |

## Results

Copied from the page images of arXiv v4; page numbers are those of the arXiv PDF, not of the
published article.

### Notation

- **$\mathcal K_{\inf}$, (2), p. 3.** "$\mathcal K_{\inf}(\nu,\mu)=\inf\{\mathrm{KL}(\nu,\nu'):\nu'\in\mathcal D\text{ and }\mathrm E(\nu')>\mu\}$,
  which measures the difficulty of the problem, is the minimal Kullback–Leibler divergence between
  the arm distribution $\nu$ and distributions in the model $\mathcal D$ that have expectations larger
  than $\mu$." **Strict inequality** $\mathrm E(\nu')>\mu$. No other definition of $\mathcal K_{\inf}$ appears
  on the pages read (§4.2 says that in the exponential-family case
  "$\mathcal K_{\inf}(\nu,\mu)=d(\mathrm E(\nu),\mu)$ when $\mathrm E(\nu)\in I$ and $\mu\in I$").
- **$\mathfrak M_1$, §3, p. 7.** "We fix an interval or discrete subset $\mathcal S\subseteq\mathbb R$ and denote by
  $\mathfrak M_1(\mathcal S)$ the set of all probability distributions over $\mathcal S$. For two distributions
  $\nu,\nu'\in\mathfrak M_1(\mathcal S)$, we denote by $\mathrm{KL}(\nu,\nu')$ their Kullback–Leibler divergence and
  by $\mathrm E(\nu)$ and $\mathrm E(\nu')$ their expectations."
- Model (§2, p. 5): "a model $\mathcal D$ is known: a family of probability distributions such that
  $\nu_a\in\mathcal D$ for all arms $a$." Regret (3), p. 6:
  $R_T\overset{\text{def}}{=}\mathbb E\bigl[T\mu^\star-\sum_{t=1}^TY_t\bigr]=\mathbb E\bigl[T\mu^\star-\sum_{t=1}^T\mu_{A_t}\bigr]=\sum_{a=1}^K\Delta_a\mathbb E[N_a(T)]$.

### §6.1 "The kl-UCB algorithm for bounded distributions" (pp. 16–18, verbatim)

- **Opening (p. 16).** "A careful reading of the proof of Theorem 1 (see the supplemental article
  [Cappé et al. (2013), Section A]) shows that kl-UCB enjoys regret guarantees in models with
  arbitrary bounded distributions $\nu$ over $[0,1]$ as long as it is used with a divergence $d$ over
  $[0,1]^2$ satisfying the following double property: there exists a family of strictly convex and
  continuously differentiable functions $\phi_\mu:\mathbb R\to[0,+\infty)$, indexed by $\mu\in[0,1]$, such that
  first, $d(\cdot,\mu)$ is the convex conjugate of $\phi_\mu$ for all $\mu\in[0,1]$; and, second, the
  domination condition $\mathcal L_\nu(\lambda)\le\phi_{\mathrm E(\nu)}(\lambda)$ for all $\lambda\in\mathbb R$ and all
  $\nu\in\mathfrak M_1([0,1])$ holds, where $\mathcal L_\nu$ denotes the moment-generating function of $\nu$,
  $\mathcal L_\nu:\lambda\in\mathbb R\longmapsto\mathcal L_\nu(\lambda)=\int_{[0,1]}e^{\lambda x}\,\mathrm d\nu(x)$."
- **Lemma 1 (p. 17).** "Let $\nu\in\mathfrak M_1([0,1])$ and let $\mu=\mathrm E(\nu)$. Then, for all $\lambda\in\mathbb R$,
  $$\mathcal L_\nu(\lambda)=\int_{[0,1]}e^{\lambda x}\,\mathrm d\nu(x)\le1-\mu+\mu\exp(\lambda)\le\exp(\lambda\mu+2\lambda^2).$$"
  Introduced by: "The following elementary lemma dates back to Hoeffding (1963); it upper bounds the
  moment-generating function of any probability distribution over $[0,1]$ with expectation $\mu$ by
  the moment-generating function of the Bernoulli distribution with parameter $\mu$, which is further
  bounded by the moment-generating function of the normal distribution with mean $\mu$ and variance
  $1/4$." Proof: "The proof of this lemma is straightforward; the first inequality is by convexity,
  as $e^{\lambda x}\le xe^\lambda+(1-x)$ for all $x\in[0,1]$, and the second inequality follows by
  standard analysis."
- **Corollary 1 (p. 17)** defines "$d_{\mathrm{BER}}(\mu,\mu')=\mu\log\frac{\mu}{\mu'}+(1-\mu)\log\frac{1-\mu}{1-\mu'}$"
  (kl-UCB with this divergence, $f(t)=\log(t)+3\log\log(t)$ for $t\ge3$, $f(1)=f(2)=f(3)$; bound
  on $\mathbb E[N_a(T)]$ for $T\ge3$ with leading term $\log(T)/d_{\mathrm{BER}}(\mu_a,\mu^\star)$).
- **The passage after the corollaries' preamble (p. 18), verbatim.** "We denote by
  $\phi_{\mathrm E(\nu)}=1-\mathrm E(\nu)+\mathrm E(\nu)\exp(\cdot)$ the upper bound on $\mathcal L_\nu$ exhibited in Lemma 1.
  Standard results on Kullback–Leibler divergences are that for all $\mu,\mu'\in[0,1]$ and all
  $\nu,\nu'\in\mathfrak M_1([0,1])$,
  $$d_{\mathrm{BER}}(\mu,\mu')=\sup_{\lambda\in\mathbb R}\{\lambda\mu-\phi_{\mu'}(\lambda)\}\quad\text{and}\quad\mathrm{KL}(\nu,\nu')\ge\sup_{\lambda\in\mathbb R}\{\lambda\,\mathrm E(\nu)-\mathcal L_{\nu'}(\lambda)\};$$
  see Massart [(2007), pages 21 and 28]; see also Dembo and Zeitouni (1998). Because of Lemma 1, it
  thus holds that for all distributions $\nu,\nu'\in\mathfrak M_1([0,1])$,
  $$d_{\mathrm{BER}}(\mathrm E(\nu),\mathrm E(\nu'))\le\mathrm{KL}(\nu,\nu'),$$
  and it follows that in the model $\mathcal D=\mathfrak M_1([0,1])$ one has
  $$\mathcal K_{\inf}(\nu_a,\mu^\star)\ge d_{\mathrm{BER}}(\mu_a,\mu^\star)."$$
  (Our reading, not in the source: as printed, neither "standard result" has a logarithm. With
  $\phi_{\mu'}=1-\mu'+\mu'\exp(\cdot)$, $\sup_\lambda\{\lambda\mu-\phi_{\mu'}(\lambda)\}=\mu\log\frac{\mu}{\mu'}-\mu+\mu'-1$, not
  $d_{\mathrm{BER}}(\mu,\mu')$. The standard facts are those with $\log\phi_{\mu'}$ and $\log\mathcal L_{\nu'}$:
  $d_{\mathrm{BER}}(\mu,\mu')=\sup_\lambda\{\lambda\mu-\log\phi_{\mu'}(\lambda)\}$ and the Donsker–Varadhan bound
  $\mathrm{KL}(\nu,\nu')\ge\sup_\lambda\{\lambda\mathrm E(\nu)-\log\mathcal L_{\nu'}(\lambda)\}$; with them and Lemma 1 the conclusion
  $d_{\mathrm{BER}}(\mathrm E(\nu),\mathrm E(\nu'))\le\mathrm{KL}(\nu,\nu')$ follows. The step to $\mathcal K_{\inf}$ is not written out: for
  $\nu'$ with $\mathrm E(\nu')>\mu^\star\ge\mu_a$ it uses that $d_{\mathrm{BER}}(\mu_a,\cdot)$ is nondecreasing on
  $[\mu_a,1]$, which the source does not state.)
- **UCB1 as a special case (p. 18).** "It is readily checked that the latter [the UCB algorithm]
  exactly corresponds to the choice of $d_{\mathrm{QUAD}}(\mu,\mu')=2(\mu-\mu')^2$ in Algorithm 2 together with
  some nondecreasing function $f$. For instance, the original algorithm UCB1 of Auer, Cesa-Bianchi
  and Fischer [(2002), Theorem 1], relies on $f(t)=4\log(t)$."
- **Corollary 2 (p. 18).** kl-UCB with $d_{\mathrm{QUAD}}$ and $f$ of Theorem 1, "or equivalently, the UCB
  algorithm tuned as follows: at step $t+1>K$, an arm maximizing the upper-confidence bounds
  $\widehat\mu_a(t)+\sqrt{(\log(t)+3\log\log(t))/(2N_a(t))}$ is chosen. Then the number of draws of a
  suboptimal arm $a$ is upper bounded as
  $\mathbb E[N_a(T)]\le\frac{\log(T)}{2(\mu^\star-\mu_a)^2}+\frac{2\sqrt\pi}{(\mu^\star-\mu_a)^2}\sqrt{\log(T)+3\log(\log(T))}+\Bigl(4e+\frac{3}{2(\mu^\star-\mu_a)^2}\Bigr)\log(\log(T))+\frac{8}{(\mu^\star-\mu_a)^2}+6.$"

### Other statements seen

- **Theorem 1 (§4.2, p. 14).** "Assume that all arms belong to a canonical, regular, exponential
  family $\mathcal D=\{\nu_\theta:\theta\in\Theta\}$ of probability distributions indexed by its natural parameter
  space $\Theta\subseteq\mathbb R$. Then, using Algorithm 2 with the divergence $d$ given in (11) and with the
  choice $f(t)=\log(t)+3\log\log(t)$ for $t\ge3$ and $f(1)=f(2)=f(3)$, the number of draws of any
  suboptimal arm $a$ is upper bounded for any horizon $T\ge3$ as
  $$\mathbb E[N_a(T)]\le\frac{\log(T)}{d(\mu_a,\mu^\star)}+2\sqrt{\frac{2\pi\sigma^2_{a,\star}(d'(\mu_a,\mu^\star))^2}{(d(\mu_a,\mu^\star))^3}}\sqrt{\log(T)+3\log(\log(T))}+\Bigl(4e+\frac{3}{d(\mu_a,\mu^\star)}\Bigr)\log(\log(T))+8\sigma^2_{a,\star}\Bigl(\frac{d'(\mu_a,\mu^\star)}{d(\mu_a,\mu^\star)}\Bigr)^2+6,$$
  where $\sigma^2_{a,\star}=\max\{\mathrm{Var}(\nu_\theta):\mu_a\le\mathrm E(\nu_\theta)\le\mu^\star\}$ and where
  $d'(\cdot,\mu^\star)$ denotes the derivative of $d(\cdot,\mu^\star)$." ((11) and Algorithm 2 not read.)
- Theorem 2 (§5, p. 15), Proposition 1 (§6.2, p. 20): statements seen, not used here.

## Techniques

- Domination of moment-generating functions (Lemma 1, credited to Hoeffding 1963) plus the
  variational (Donsker–Varadhan type) lower bound on KL, credited to Massart (2007, pp. 21 and 28)
  and Dembo–Zeitouni (1998), giving $d_{\mathrm{BER}}(\mathrm E(\nu),\mathrm E(\nu'))\le\mathrm{KL}(\nu,\nu')$ on
  $\mathfrak M_1([0,1])$ and hence $\mathcal K_{\inf}\ge d_{\mathrm{BER}}$ there.
- The introduction (p. 2) credits Agrawal (1995) with formally introducing UCB-type index policies
  and Auer, Cesa-Bianchi and Fischer (2002) with "a finite time analysis for a particular variant of
  UCB based on Hoeffding's inequality"; the lower bounds (1) are attributed to Lai–Robbins (1985)
  and Burnetas–Katehakis (1996).

## Where Incognita uses it

`papers/P007-stochastic-setting/` (models, KL-UCB, [CGMMS13, Theorem 1]; requested by its referee
for §6.1: $\mathcal K_{\inf}\ge d_{\mathrm{BER}}$ on laws on $[0,1]$), `papers/P005-bounded-kurtosis/`,
`papers/P000-hy-unknown-imposed-grid/`, `roadmaps/StochasticBandits/KNOWN.md` (KL-UCB entries, K59).
