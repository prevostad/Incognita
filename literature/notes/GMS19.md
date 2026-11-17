# GMS19: Explore first, exploit next

| | |
|---|---|
| Work | A. Garivier, P. Ménard, G. Stoltz, *Explore First, Exploit Next: The True Shape of Regret in Bandit Problems*, Mathematics of Operations Research 44(2), 2019 |
| Identifiers | DOI 10.1287/moor.2017.0928, arXiv 1602.07182 (v1 23 Feb 2016, v2 17 Jun 2016, v3 13 Oct 2018, from the arXiv abs page) |
| Read | abstract and introduction (arXiv v3); inequalities (6) and (11); arXiv v3 §2.1: (8), Remark 2, Lemma 1; Appendix A, Lemma 5. LaTeX source of arXiv:1602.07182v3 (the e-print, file `Bandit-lower-bounds-MOR-v3.tex`, in the INFORMS class with equations, theorems and definitions numbered through the paper): §1.1 (setting, strategies, $I_t$, $N_{\psi,a}(T)$, (1)); §1.2 ($\mathcal K_{\inf}$, (2)); §2 opening, (5)–(7), Remark 1; §2.1 (8), Remark 2, the proofs of the equality and of the inequality in (8), Lemma 1 and its proof; §2.2 Definition 1, Theorem 1 and its proof, (10)–(11); Appendix A, Lemma 5 and (the classical) Pinsker's inequality; the `.bbl` entries of the works credited in §1.2 and §2.1; Appendix B.1 (theorem, proof, and the paragraph after it) in the ar5iv rendering of arXiv:1602.07182 (labelled "Theorem B.1" there; that it is Theorem 6 in the PDF of v3 is not checked). Not read: §3–§4 in full, conclusion, the published MOR version |
| By, date | an agent for the owner (inequalities (6), (11)), 2026-10-31; Claude (abstract, introduction), 2026-11-13; Claude Opus 5.5 (role revise, P000: arXiv v3, (8), Lemma 1, Remark 2, Lemma 5 of Appendix A), 2026-11-14; Claude Opus 5.5 (role bibliographer: the v3 LaTeX source, exact statements of (5), (6), (10), (11), Definition 1, Theorem 1), 2026-11-15; Claude Opus 5.5 (revise, P001: Appendix B.1), 2026-11-15 |

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
- **Theorem of Appendix B.1 "Distribution-free lower bound" (Appendix B "Re-derivation of other
  earlier lower bounds"; "Theorem B.1" in the ar5iv rendering, reportedly Theorem 6 in the v3 PDF,
  not checked).** "Consider the bandit model $\mathcal D=\mathcal M([0,1])$ of all probability
  distributions over $[0,1]$. For all $\varepsilon\in(0,1/2)$, for all strategies $\psi$, there exists a
  bandit problem $\underline\nu'$ in $\mathcal M([0,1])$ such that
  $R_{\psi,\underline\nu',T}\ge T\varepsilon\bigl(1-\frac1K-\frac12\sqrt{\frac TK\ln\frac1{1-4\varepsilon^2}}\bigr)$.
  This problem $\underline\nu'$ can be given by Bernoulli distributions, with parameters $1/2$ for all
  arms but one, for which the parameter is $1/2+\varepsilon$." Proof: $\underline\nu$ all Bernoulli$(1/2)$;
  "There exists an arm $k$ such that $\mathbb E_{\underline\nu}[N_{\psi,k}(T)]\le T/K$, as these $K$ numbers
  of pulls sum up to $T$" (pigeonhole, a single arm, no prior); $\underline\nu'$ raises arm $k$ to
  $1/2+\varepsilon$; (6) with $Z=N_{\psi,k}(T)/T$ and $\mathrm{kl}(1/2,1/2+\varepsilon)=\frac12\ln\frac1{1-4\varepsilon^2}$, then
  "Pinsker's inequality (in its classical form, see Appendix A)"; no convexity of kl, no (11). The
  paragraph after it takes $\varepsilon=\min\{\sqrt{K/T},1\}/4$ to get $\ge\frac1{20}\min\{\sqrt{KT},T\}$ and
  says "The constant $1/20$ can actually be improved into $1/8$, see Cesa-Bianchi and Lugosi 2006,
  Theorem 6.11". The text says the re-derivation "follows the very same proof scheme as in the
  original proof" (Auer et al.).

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
`papers/P001-minimax-constant/`: thm:bounds, Main result, Closest known, Attribution (fundamental
inequality; Appendix B.1 as the closest known proof). Paper
`papers/P002-transfer-drift-between-laws/`: nodes `cite:GMS19-6` ((6)) and `cite:GMS19-11` ((11)),
used in the proof of `prop:lower`; its node `cite:GMS19-11` states the inequality
$\mathrm{kl}(p,q)\ge p\log(1/q)-\log2$, which is a consequence of (11), not its statement (see
(11) above). Paper `papers/P007-stochastic-setting/` (the setting paper of StochasticBandits): nodes
`cite:GMS19-lem1` (Lemma 1, used for $\mathcal K_{\inf}\ge\mathrm{kl}$ on laws on $[0,1]$) and
`cite:GMS19-thm1` (Theorem 1, restricted to instances of $\mathcal D^\alpha$, used in `cor:lower`);
Definitions 1, 2 and 6 restated as `def:ufc` and `def:smarter` (on arbitrary sets of instances).

## Definitions 2–4, 6 and 7, verbatim (arXiv v3 PDF)

Added by Claude Opus 5.5 (revise, P007), 2026-11-17. Read: the PDF of arXiv:1602.07182v3
(stamp "arXiv:1602.07182v3 [math.ST] 13 Oct 2018", INFORMS layout, header "Mathematics of
Operations Research DOI: 10.1287/moor.2017.0928"), page images of pp. 1–4, 8–17 and 22–26: §3
opening (p. 10), §3.1 Definition 2 and Theorem 2 (pp. 10–11), §3.2 Definition 3, Theorem 3 and its
proof (pp. 11–12), §3.3 Definition 4, Theorem 4 and its proof, Lemma 2 (pp. 13–14), §3.4 (p. 14),
§4 opening, Definition 5, Definition 6 and the paragraphs after it, §4.1, Theorem 5, Remark 3
(pp. 15–17), Appendix B.2 with Definition 7 and Theorems 7–8 (pp. 22–25), Appendix C and Theorem 9
(pp. 25–26). The LaTeX source could not be unpacked in this session (no archive tool), so the
displays below are retyped from the page images, in the notation of the PDF ($\underline\nu$ is the
underlined $\nu$, $\geqslant$/$\leqslant$ as printed); words are as printed, including typos. The
ar5iv rendering numbers these definitions differently (section-based numbers): cite the PDF numbers.

### Notation they rely on (from §1.1, p. 3, and §3.3, p. 13)

- Arms $a\in\{1,\ldots,K\}$; rounds $t\geqslant1$; $N_{\psi,a}(T)=\sum_{t=1}^T\mathbb I_{\{A_t=a\}}$ (see
  "Setting (§1.1)" above). "we denote by $E(\nu_a)=\mu_a$ the expected payoff of arm $a$ and by
  $\Delta_a$ its gap to an optimal arm: $\mu^\star=\max_{a=1,\ldots,K}\mu_a$ and $\Delta_a=\mu^\star-\mu_a$."
  Suboptimal arms are "all arms $a$ such that $\Delta_a>0$" (Definition 1). Optimal arms are not
  defined further; §3.3 writes $\mathcal A^\star(\underline\nu)$ for "the set of its optimal arms".
- Model (§1.2, p. 3): "We consider a bandit model $\mathcal D$, i.e., a collection of possible
  distributions $\nu_a$ associated with the arms. (That is, $\mathcal D$ is a subset of the set of all
  possible distributions over $\mathbb R$ with an expectation.)" "Bandit problems $\underline\nu$ in
  $\mathcal D$" are those whose arm distributions all lie in $\mathcal D$ (same $\mathcal D$ for every arm).
- No permutation of a bandit problem is used by Definitions 2–4. Permutations appear only in
  Definition 7 (Appendix B.2), quoted below, which the sentence introducing Definition 3 refers to.

### §3 opening (p. 10), paragraph "Minimal restrictions on the considered strategies"

"We prove these lower bounds under minimal assumptions on the considered strategies: either some
mild symmetry (much milder than asking for symmetry under permutation of the arms, see
Definition 3); or the fact that for suboptimal arms $a$, the number of pulls
$\mathbb E_{\underline\nu}\big[N_{\psi,a}(T)\big]$ should decrease as $\mu_a$ decreases, all other
distributions of arms being fixed (see Definitions 2 and 4). These assumptions are satisfied by all
well-performing strategies we could think of: the UCB strategy of Auer et al. [2], the KL-UCB
strategy of Cappé et al. [11], Thompson [24] Sampling, EXP3 of Auer et al. [3], etc."

"Note that the assumption of uniform fast convergence (Definition 1), though classical and well
accepted, is quite strong. Note that it is necessary for a strategy to satisfy some symmetry and to
be smarter than the uniform strategy in the limit (not for all $T$, see Definition 2) to be uniformly
fast convergent. Hence, the class of strategies we consider is essentially much larger than the
subset of uniformly fast convergent strategies."

(This paraphrase of monotonicity, one suboptimal arm whose mean decreases, is not what Definition 4
says: see below.)

### Definition 2, §3.1 "Absolute lower bound for a suboptimal arm" (p. 10)

"The uniform strategy is the one that pulls an arm uniformly at random at each round.

**Definition 2.** A strategy $\psi$ is smarter than the uniform strategy on a model $\mathcal D$ if for all
bandit problems $\underline\nu$ in $\mathcal D$, for all optimal arms $a^\star$, for all $T\geqslant1$,
$$\mathbb E_{\underline\nu}\big[N_{\psi,a^\star}(T)\big]\geqslant\frac TK\,."$$

### Definition 3, §3.2 "Relative lower bound" (p. 11)

"Our proof will be based on an assumption of symmetry (milder than requiring that if the arms are
permuted in a bandit problem, the algorithm behaves the same way, as in Definition 7).

**Definition 3.** A strategy $\psi$ is pairwise symmetric for optimal arms on $\mathcal D$ if for all bandit
problems $\underline\nu$ in $\mathcal D$, for each pair of optimal arms $a^\star$ and $a_\star$, the equality
$\nu_{a^\star}=\nu_{a_\star}$ entails that, for all $T\geqslant1$,
$$\big(N_{\psi,a^\star}(T),\,N_{\psi,a_\star}(T)\big)\qquad\text{and}\qquad\big(N_{\psi,a_\star}(T),\,N_{\psi,a^\star}(T)\big)$$
have the same distribution.

Note that the required symmetry is extremely mild as only pairs of *optimal* arms with the *same*
distribution are to be considered. What the equality of distributions means is that the strategy
should be based only on payoffs and not on the values of the indexes of the arms."

The definition compares two laws under the same $\mathbb P_{\underline\nu}$; no permuted problem is
involved, and it does not say that $a^\star\ne a_\star$ (the case $a^\star=a_\star$ is trivial).

### Definition 4, §3.3 "Collective lower bound" (p. 13)

"In this section, for any given bandit problem $\underline\nu$, we denote by $\mathcal A^\star(\underline\nu)$ the set
of its optimal arms and by $\mathcal W(\underline\nu)$ the set of its worst arms, i.e., the ones associated with
the distributions with the smallest expectation among all distributions for the arms. We also let
$A^\star_{\underline\nu}$ be the cardinality of $\mathcal A^\star(\underline\nu)$.

We define the following partial order $\preccurlyeq$ on bandit problems: $\underline\nu'\preccurlyeq\underline\nu$ if
$$\forall a\in\mathcal A^\star(\underline\nu),\quad\nu_a=\nu'_a\qquad\text{and}\qquad\forall a\notin\mathcal A^\star(\underline\nu),\quad E(\nu'_a)\leqslant E(\nu_a)\,.$$
In particular, $\mathcal A^\star(\underline\nu)=\mathcal A^\star(\underline\nu')$ in this case. The definition models the fact
that the bandit problem $\underline\nu'$ should be easier than $\underline\nu$, as non-optimal arms in $\underline\nu'$ are
farther away from the optimal arms (in expectation) that in $\underline\nu$. Any reasonable strategy should
perform better on $\underline\nu'$ than on $\underline\nu$, which leads to the following definition, where we
measure performance in the expected number of times optimal arms are pulled. (Recall that the sets
of optimal arms are identical for $\underline\nu$ and $\underline\nu'$.)

**Definition 4.** A strategy $\psi$ is monotonic on a model $\mathcal D$ if for all bandit problems
$\underline\nu'\preccurlyeq\underline\nu$ in $\mathcal D$,
$$\sum_{a^\star\in\mathcal A^\star(\underline\nu')}\mathbb E_{\underline\nu'}\big[N_{\psi,a^\star}(T)\big]\geqslant\sum_{a^\star\in\mathcal A^\star(\underline\nu)}\mathbb E_{\underline\nu}\big[N_{\psi,a^\star}(T)\big]\,."$$

Remarks. (i) Definition 4 has **no quantifier on $T$** (nor does Theorem 4, which uses it: "for all
bandit problems $\underline\nu$ in $\mathcal D$, suboptimal arms are collectively sampled at least
$T\big(1-\ldots\big)$"); reading it "for all $T\geqslant1$" is an interpretation. (ii) The laws of the
non-optimal arms of $\underline\nu'$ are arbitrary in $\mathcal D$ (only their means are constrained), several
of them may change at once, and the inequality is on the total expected count of the optimal arms,
not on each suboptimal arm. (iii) The proof of Theorem 4 (p. 13) applies monotonicity to
$\underline{\underline\nu}\preccurlyeq\underline\nu$, where $\underline{\underline\nu}$ replaces every suboptimal arm by
$\nu_{\widetilde w}$, a worst arm of $\underline\nu$; and uses pairwise symmetry on the problem
$\underset{\sim}{\nu}$ whose arms are all $\nu_{\widetilde w}$ (all optimal), to get
$\mathbb E[N_{\psi,a}(T)]=T/K$ for all $a$.

### Definition 6, §4 "Non-asymptotic bounds for large T" (p. 16)

§4 opens (p. 15): "We restrict our attention to well-behaved models and uniformly super-fast
convergent strategies."

"**Definition 6.** A strategy $\psi$ is uniformly super-fast convergent on a model $\mathcal D$ if there exists
a constant $C_{\psi,\mathcal D}$ such that for all bandit problems $\underline\nu$ in $\mathcal D$, for all suboptimal arms
$a$, for all $T\geqslant2$,
$$\mathbb E_{\underline\nu}\big[N_{\psi,a}(T)\big]\leqslant C_{\psi,\mathcal D}\frac{\ln T}{\Delta_a^2}\,.$$
Uniform super-fast convergence is a refinement of the notion of uniform fast convergence based on
two considerations. First, that there exist such strategies, for instance, the UCB strategy of
Auer et al. [2] on any bounded model $\mathcal D$, i.e., a model with distributions all supported within
a common bounded interval $[m,M]$."

### Definition 7, Appendix B.2 (p. 24), the permutation invariance referred to by §3.2

"These properties of symmetry and invariance by translation are most natural requirements. To
define them, for all $c\in\mathbb R$ and all distributions $\nu$, we denote by $\tau_c(\nu)$ the distribution of
$Y+c$ when $Y\sim\nu$.

**Definition 7.** A strategy $\psi$ for $K$–armed bandits is symmetric and invariant by translation of
the payoffs if for all permutations $\sigma$ of $\{1,\ldots,K\}$, all $c\in\mathbb R$, and all $T\geqslant1$, the
distribution of $\big(N_{\psi,1}(T),\ldots,N_{\psi,K}(T)\big)$ in the bandit problem $(\nu_1,\ldots,\nu_K)$ is equal to
the one of $\big(N_{\psi,\sigma^{-1}(1)}(T),\ldots,N_{\psi,\sigma^{-1}(K)}(T)\big)$ in the bandit problem
$\big(\tau_c(\nu_{\sigma(1)}),\ldots,\tau_c(\nu_{\sigma(K)})\big)$."
