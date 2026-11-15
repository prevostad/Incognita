# GMS19: Explore first, exploit next

| | |
|---|---|
| Work | A. Garivier, P. Ménard, G. Stoltz, *Explore First, Exploit Next: The True Shape of Regret in Bandit Problems*, Mathematics of Operations Research 44(2), 2019 |
| Identifiers | DOI 10.1287/moor.2017.0928, arXiv 1602.07182 (v1 23 Feb 2016, v2 17 Jun 2016, v3 13 Oct 2018, from the arXiv abs page) |
| Read | abstract and introduction (arXiv v3); inequalities (6) and (11); arXiv v3 §2.1: (8), Remark 2, Lemma 1; Appendix A, Lemma 5. LaTeX source of arXiv:1602.07182v3 (the e-print, file `Bandit-lower-bounds-MOR-v3.tex`, in the INFORMS class with equations, theorems and definitions numbered through the paper): §1.1 (setting, strategies, $I_t$, $N_{\psi,a}(T)$, (1)); §1.2 ($\mathcal K_{\inf}$, (2)); §2 opening, (5)–(7), Remark 1; §2.1 (8), Remark 2, the proofs of the equality and of the inequality in (8), Lemma 1 and its proof; §2.2 Definition 1, Theorem 1 and its proof, (10)–(11); Appendix A, Lemma 5 and (the classical) Pinsker's inequality; the `.bbl` entries of the works credited in §1.2 and §2.1. Not read: §3–§4 in full, conclusion, the published MOR version |
| By, date | an agent for the owner (inequalities (6), (11)), 2026-10-31; Claude (abstract, introduction), 2026-11-13; Claude Opus 5.5 (role revise, P000: arXiv v3, (8), Lemma 1, Remark 2, Lemma 5 of Appendix A), 2026-11-14; Claude Opus 5.5 (role bibliographer: the v3 LaTeX source, exact statements of (5), (6), (10), (11), Definition 1, Theorem 1), 2026-11-15 |

## Results

Statements below copied from the LaTeX source of arXiv:1602.07182v3, with the authors' macros
expanded (`\unu` is $\underline\nu$, `\E` is $\mathbb E$, `\ind` is $\mathbb I$, `\Kinf` is
$\mathcal K_{\inf}$; `\geq` is printed $\geqslant$). The numbering is that of v3, whose source file
name says it is the MOR version; the numbering of the published article was not checked (the
INFORMS page refused access, 403). The page images were not viewed: no page numbers below.

### Setting (§1.1)

- **Bandit problem.** "Each of these arms is associated with an unknown probability distribution
  $\nu_a$ over $\mathbb R$. We assume that each $\nu_a$ has a well-defined expectation and call
  $\underline\nu=(\nu_a)_{a=1,\ldots,K}$ a bandit problem." Rewards: at round $t\ge1$ the player
  pulls $A_t$ and gets $Y_t$ drawn independently according to $\nu_{A_t}$.
- **Strategies.** Auxiliary randomisation by i.i.d. uniform $U_0,U_1,\ldots$ on $[0,1]$. "Formally, a
  strategy is a sequence $\psi=(\psi_t)_{t\geq0}$ of measurable functions, each of which associates
  with the said past information, namely,
  $I_t=\bigl(U_0,\,Y_1,U_1,\,\ldots,\,Y_t,U_t\bigr)$,
  an arm $\psi_t(I_t)=A_{t+1}\in\{1,\ldots,K\}$, where $t\geq0$. The initial information reduces to
  $I_0=U_0$ and the first arm is $A_1=\psi_0(U_0)$." The randomisation $U_t$ is independent of
  $I_{t-1}$ and $Y_t$.
- **Counts.** "$N_{\psi,a}(T)=\sum_{t=1}^T\mathbb I_{\{A_t=a\}}=\sum_{t=1}^T\mathbb I_{\{\psi_{t-1}(I_{t-1})=a\}}$."
  Regret (1): $R_{\psi,\underline\nu,T}=T\mu^\star-\mathbb E_{\underline\nu}\bigl[\sum_{t=1}^TY_t\bigr]=\sum_{a=1}^K\Delta_a\,\mathbb E_{\underline\nu}\bigl[N_{\psi,a}(T)\bigr]$.
- **$\mathcal K_{\inf}$ (§1.2).** "For any given $\nu_a\in\mathcal D$ and any real number $x$,
  $\mathcal K_{\inf}(\nu_a,x,\mathcal D)=\inf\bigl\{\mathrm{KL}(\nu_a,\nu'_a):\ \nu'_a\in\mathcal D\ \text{and}\ E(\nu'_a)>x\bigr\}$;
  by convention, the infimum of the empty set equals $+\infty$." Here $\mathcal D$ is a model, "a
  subset of the set of all possible distributions over $\mathbb R$ with an expectation", and
  $\mathrm{KL}$ is "the Kullback-Leibler divergence between two probability distributions".

### §2: the fundamental inequality

- **(5).** "$\forall p,q\in[0,1]^2,\qquad\mathrm{kl}(p,q)=p\ln\frac pq+(1-p)\ln\frac{1-p}{1-q}$."
- **(6), the fundamental inequality.** "We show in this section that for all strategies $\psi$, for
  all bandit problems $\underline\nu$ and $\underline\nu'$, for all $\sigma(I_T)$–measurable random
  variables $Z$ with values in $[0,1]$,
  $$\sum_{a=1}^K\mathbb E_{\underline\nu}\bigl[N_{\psi,a}(T)\bigr]\,\mathrm{KL}(\nu_a,\nu'_a)\geq\mathrm{kl}\bigl(\mathbb E_{\underline\nu}[Z],\,\mathbb E_{\underline\nu'}[Z]\bigr)\,.\qquad(6)$$"
  The source states no further hypothesis ($T$ is a fixed horizon; infinite divergences are not
  discussed). $\mathbb P_{\underline\nu}$ and $\mathbb P_{\underline\nu'}$ are the laws of the
  interaction of the same strategy $\psi$ with $\underline\nu$ and $\underline\nu'$, built by (7).
- **(7).** On $\Omega=[0,1]\times(\mathbb R\times[0,1])^{\mathbb N}$, "for all $t\geq0$, for all Borel
  sets $B\subseteq\mathbb R$ and $B'\subseteq[0,1]$,
  $\mathbb P_{\underline\nu}\bigl(Y_{t+1}\in B,\,U_{t+1}\in B'\,\big|\,I_t\bigr)=\nu_{\psi_t(I_t)}(B)\,\lambda(B')$,
  where $\lambda$ denotes the Lebesgue measure on $[0,1]$." Remark 1: the measures depend on $\psi$
  too, dropped from the notation.
- **(8), §2.1.** "$\sum_{a=1}^K\mathbb E_{\underline\nu}\bigl[N_{\psi,a}(T)\bigr]\,\mathrm{KL}(\nu_a,\nu'_a)=\mathrm{KL}\bigl(\mathbb P_{\underline\nu}^{I_T},\,\mathbb P_{\underline\nu'}^{I_T}\bigr)\geq\mathrm{kl}\bigl(\mathbb E_{\underline\nu}[Z],\,\mathbb E_{\underline\nu'}[Z]\bigr)$",
  where $\mathbb P_{\underline\nu}^{I_T}$, $\mathbb P_{\underline\nu'}^{I_T}$ are the laws of $I_T$.
- **Remark 2, §2.1.** Credits [KCG16, Lemma 1] for the fact that (8) "actually holds not only for
  deterministic values of $T$ but also for any stopping time with respect to the filtration
  generated by $(I_t)_{t\geq1}$". KCG16's Lemma 1 is the form with events
  ($\sup_{\mathcal E\in\mathcal F_\sigma}d(\mathbb P_\nu(\mathcal E),\mathbb P_{\nu'}(\mathcal E))$), not
  with a $[0,1]$-valued $Z$.
- **Lemma 1, §2.1.** "Consider a measurable space $(\Gamma,\mathcal G)$ equipped with two distributions
  $\mathbb P_1$ and $\mathbb P_2$, and any $\mathcal G$–measurable random variable $Z:\Omega\to[0,1]$. We denote
  respectively by $\mathbb E_1$ and $\mathbb E_2$ the expectations under $\mathbb P_1$ and $\mathbb P_2$. Then,
  $\mathrm{KL}(\mathbb P_1,\mathbb P_2)\geq\mathrm{kl}\bigl(\mathbb E_1[Z],\mathbb E_2[Z]\bigr)$." (The domain "$\Omega$" is as
  printed, in the source too; $\Gamma$ is meant.) Proof: on $\Gamma\times[0,1]$ with the Lebesgue measure on the second
  factor, the event $E=\{(\gamma,x):x\le Z(\gamma)\}$ and Lemma 5.

### §2.2: re-derivation of the asymptotic bound

- **Definition 1.** "A strategy $\psi$ is uniformly fast convergent on a model $\mathcal D$ if for all
  bandit problems $\underline\nu$ in $\mathcal D$, for all suboptimal arms $a$, i.e., for all arms $a$
  such that $\Delta_a>0$, for all $0<\alpha\leq1$, it satisfies $\mathbb E_{\underline\nu}\bigl[N_{\psi,a}(T)\bigr]=o(T^\alpha)$."
- **Theorem 1.** "For all models $\mathcal D$, for all uniformly fast convergent strategies $\psi$ on
  $\mathcal D$, for all bandit problems $\underline\nu$, for all suboptimal arms $a$,
  $\liminf_{T\to\infty}\frac{\mathbb E_{\underline\nu}[N_{\psi,a}(T)]}{\ln T}\geq\frac1{\mathcal K_{\inf}(\nu_a,\mu^\star,\mathcal D)}$."
- **(10), in the proof of Theorem 1.** With $\nu'_k=\nu_k$ for $k\ne a$, $E(\nu'_a)>\mu^\star$, and
  $Z=N_{\psi,a}(T)/T$ in (6):
  "$\mathbb E_{\underline\nu}\bigl[N_{\psi,a}(T)\bigr]\,\mathrm{KL}(\nu_a,\nu'_a)\geq\mathrm{kl}\Bigl(\frac{\mathbb E_{\underline\nu}[N_{\psi,a}(T)]}{T},\,\frac{\mathbb E_{\underline\nu'}[N_{\psi,a}(T)]}{T}\Bigr)\geq\Bigl(1-\frac{\mathbb E_{\underline\nu}[N_{\psi,a}(T)]}{T}\Bigr)\ln\frac{T}{T-\mathbb E_{\underline\nu'}[N_{\psi,a}(T)]}-\ln2\,,$"
  (only the second inequality is numbered (10)).
- **(11).** Introduced by "where we used for the second inequality that for all $(p,q)\in[0,1]^2$,"
  $$\mathrm{kl}(p,q)=\underbrace{p\ln\frac1q}_{\geq0}+(1-p)\ln\frac1{1-q}+\bigl(\underbrace{p\ln p+(1-p)\ln(1-p)}_{\geq-\ln2}\bigr)\,.\qquad(11)$$
  **(11) is an identity, not an inequality.** The source draws from it, in (10),
  $\mathrm{kl}(p,q)\ge(1-p)\ln\frac1{1-q}-\ln2$ (dropping the term marked $\geq0$). The form
  "$\mathrm{kl}(p,q)\ge p\log(1/q)-\log2$" recorded in this note before 2026-11-15 is not printed
  in the source: it follows from (11) by dropping $(1-p)\ln\frac1{1-q}$ instead, which is also
  nonnegative for $q\in[0,1]$ but is not marked so in (11). It is (10)'s inequality with $(p,q)$
  replaced by $(1-p,1-q)$ (kl is invariant under this swap).
- Rest of the proof of Theorem 1: uniform fast convergence on $\underline\nu'$ gives
  $T-\mathbb E_{\underline\nu'}[N_{\psi,a}(T)]\le T^\alpha$ for $T$ large, hence the liminf of
  $\frac1{\ln T}\ln\frac{T}{T-\mathbb E_{\underline\nu'}[N_{\psi,a}(T)]}$ is at least $1-\alpha$; on
  $\underline\nu$, $\mathbb E_{\underline\nu}[N_{\psi,a}(T)]/T\to0$; then the supremum over $\nu'_a$.
  The empty case gives $\mathcal K_{\inf}=+\infty$.

### Appendix A and later sections

- **Lemma 5, Appendix A (data processing).** "Consider a measurable space $(\Gamma,\mathcal G)$
  equipped with two distributions $\mathbb P_1$ and $\mathbb P_2$, any other $(\Gamma',\mathcal G')$ measurable
  space, and any random variable $X:(\Gamma,\mathcal G)\to(\Gamma',\mathcal G')$. Then,
  $\mathrm{KL}\bigl(\mathbb P_1^X,\mathbb P_2^X\bigr)\leq\mathrm{KL}(\mathbb P_1,\mathbb P_2)$, where $\mathbb P_1^X$ and $\mathbb P_2^X$ denote the
  respective distributions of $X$ under $\mathbb P_1$ and $\mathbb P_2$."
- Section 3 (not read in full): lower bounds for small horizons, almost linear regret, under mild
  symmetry assumptions on the strategies.
- Section 4 (not read in full): a non-asymptotic lower bound for large horizons for uniformly
  super-fast convergent strategies, with a second-order term of order $-\log\log T$. The exact
  constants and numbers must be read in the paper before any use.

## Techniques

- Change of measure written as a single inequality (6): the chain rule for KL along the history
  (the equality in (8)), credited by the authors to the proofs of the distribution-free lower bound
  (Auer, Cesa-Bianchi, Freund, Schapire 2002, SIAM J. Comput. 32(1); Cesa-Bianchi, Lugosi 2006,
  *Prediction, Learning, and Games*; see also Combes, Proutière 2014, "Unimodal bandits without
  smoothness", arXiv:1406.7447, which is not the entry CP14 of `bibliography.json`), then data processing applied to a $[0,1]$-valued $Z$ (Lemma 1), which the authors call
  their "key contribution". It replaces the explicit change of measure and the Markov–Chernoff
  bounding of well-chosen events in Lai–Robbins, Burnetas–Katehakis and KCG16, App. B.
- The asymptotic bound (Theorem 1) by (6) with $Z=N_{\psi,a}(T)/T$, the lower bound on kl from (11),
  and uniform fast convergence on both instances. The authors attribute $\mathcal K_{\inf}$ to
  Burnetas–Katehakis 1996 (quantity (3)-(b), p. 125) and the non-parametric statement to
  Cowan–Katehakis 2015 (arXiv:1510.02041). (Titles and years from the `.bbl` of the v3 source.)
- The same inequality gives the distribution-free $\sqrt{KT}$ bound and the Bubeck–Perchet–Rigollet
  bounds (Appendix B, not read).

## Where Incognita uses it

Roadmaps StochasticBandits (F1–F3; KNOWN K2, K4, K5; directions D1, D3; it absorbed the draft
RegretShape) and BatchedBandits (known result 1). Paper `papers/P000-hy-unknown-imposed-grid/`:
node `cite:garivier2019explore-dataprocessing` (Lemma 1), Lemma `lem:onebatch`. Paper
`papers/P002-transfer-drift-between-laws/`: nodes `cite:GMS19-6` ((6)) and `cite:GMS19-11` ((11)),
used in the proof of `prop:lower`; its node `cite:GMS19-11` states the inequality
$\mathrm{kl}(p,q)\ge p\log(1/q)-\log2$, which is a consequence of (11), not its statement (see
(11) above).
