# VPG24: Optimal learning for structured bandits

| | |
|---|---|
| Work | B. Van Parys, N. Golrezaei, *Optimal Learning for Structured Bandits*, arXiv:2007.07302 (2020); published in Management Science 70(6), 3951–3998, 2024 (from Crossref, not checked against the publisher page: INFORMS returned 403) |
| Identifiers | DOI 10.1287/mnsc.2020.02108 (Management Science, from Crossref); arXiv 2007.07302 (v1 14 Jul 2020, v2 29 Sep 2021, v3 10 Jul 2023, from the arXiv abs page); also SSRN, DOI 10.2139/ssrn.3651397 (Crossref, not opened) |
| Read | The PDF of arXiv:2007.07302v3 (watermark "arXiv:2007.07302v3 [cs.LG] 10 Jul 2023"; running head "Article submitted to *Management Science*"), page images: abstract and §1 (pp. 1–4); §3 Setup, (1), (2), footnote 4, Definition 1 (pp. 6–8); §3.1 Example 1 (pp. 8–9), Example 2 skimmed (pp. 9–10); §4 in full: (4), (5), footnote 6, Proposition 1 with (6)–(7) and the two paragraphs after it, Theorem 1 (informal) (pp. 10–13); §4.1 in full: (8), non-deceitful and deceitful arms, the example (9), Proposition 2 with (10) and the paragraph after it, Example 3 items 1–3 with (11) (pp. 13–16); §5 opening, §5.1 with Assumption 1, Proposition 3 and the example $C(P_\lambda)$ (pp. 16–21); §5.2 (13)–(15), Lemma 1, Theorem 2 (pp. 21–23); Theorem 3 and Remark 1 (pp. 28–29); §8 Concluding remarks and the references (pp. 36–38); Appendix B, Lemma 2 and its proof (p. 40); Appendix H.1, proof of Proposition 2 (pp. 73–74). The arXiv HTML of v3 was consulted only through summaries (not used for any quotation below). Not read: §6–§7 except as listed, the rest of Appendices C–J, Appendix D (proof of Theorem 3), the published Management Science version (its numbering and wording are not checked against v3) |
| By, date | Claude Opus 5.5 (interactive session, P007-stochastic-setting revision), 2026-11-17 |

## Results

Statements below are transcribed from the page images of the v3 PDF (no LaTeX source was read). The
operators printed in small capitals in the PDF are written $\mathrm{Rew}$, $\mathrm{Deceit}$,
$\mathrm{Dist}$, $\mathrm{Reg}$; $\mathfrak R$ is the reward set. Italics of theorem bodies are not
reproduced. Page numbers are those of the v3 PDF.

### Setting (§3, pp. 6–8) — summary

- Arms: a finite set $X$. Pulling $x$ gives a nonnegative reward $R_t(x)=r\in\mathfrak R$ with
  probability $P(r,x)$, independent across arms and rounds. Footnote 4: "To ease the exposition, we
  assume that the set of all potential rewards $\mathfrak R$ is common to all arms and is
  discrete." (arm-dependent sets are said to be a trivial extension). The proofs use a **finite**
  reward set: (1) and Appendix B work in $\mathbb R_+^{|\mathfrak R|}$, Appendix E.2 takes
  $\mathfrak R=\{1,\ldots,k\}$, and §8 says "in our setting, we assume that the set of realized
  rewards for each arm is finite" (p. 36), with infinite reward sets left as a direction.
- The class: $P=(P(r,x))_{r\in\mathfrak R,x\in X}\in\mathcal P$, "where $\mathcal P$ is a closed
  convex subset with non-empty interior" (p. 7); the next sentence, the abstract and §1 call it
  compact ("convex compact set"). (1): $\mathcal P_\Omega:=\{Q\in\mathbb R_+^{|\mathfrak R|\times|X|}:\sum_{r\in\mathfrak R}Q(r,x)=1\ \forall x\in X\}$.
- Optimal arms: "$x^\star(P)\in\arg\max_{x\in X}\sum_{r\in\mathfrak R}rP(r,x)$ denote the set of
  optimal arms" (set-valued: ties allowed in all definitions of §3–§4);
  $\mathrm{Rew}^\star(P):=\max_{x\in X}\sum_{r}rP(r,x)$; $\tilde X(P):=X\setminus x^\star(P)$;
  $\Delta(x,P):=\mathrm{Rew}^\star(P)-\sum_rrP(r,x)$. Regret (2):
  $\mathrm{Reg}_\pi(T,P):=T\max_{x}\sum_rrP(r,x)-\sum_{t=1}^T\mathbb E[\sum_rrP(r,x_t^\pi)]$.
- Definition 1 (Uniformly Good Policies), p. 8: for all $\alpha>0$ and all $P\in\mathcal P$,
  $\limsup_{T\to\infty}\mathrm{Reg}_\pi(T,P)/T^\alpha=0$ (credited to Lai and Robbins 1985).
- Unique optimal arm and $P$ in the interior are **not** standing assumptions: they are items 1 and
  3 of Assumption 1 (§5.1, p. 19), which also asks $\mathrm{Rew}_{\max}(x,P)\ne\mathrm{Rew}^\star(P)$
  for every $x$; it is used for continuity of $C$ (Proposition 3) and for the upper bound
  (Theorem 3), not in Propositions 1–2 or Example 3. Proposition 1 asks $0<P$ (every atom
  positive); Proposition 2 asks only $P\in\mathcal P$.

### Example 1 (§3.1, pp. 8–9), items 1–2, verbatim

"**Example 1 (Representing well-known structural information in our framework)**

1. Generic bandits. Assume that the reward of any arm $x$ is drawn from an arbitrary distribution
   with the discrete support of $\mathfrak R$. In this case, the set $\mathcal P$ coincides with
   $\mathcal P_\Omega$, defined in Equation (1).
2. Separable bandits. Assume that the reward of arm $x$ can be any distribution in $\mathcal P_x$
   where $\mathcal P_x$, $x\in X$, is a closed feasible set for the reward distribution of arm $x$.
   Then, the set $\mathcal P$ coincides with $\prod_{x\in X}\mathcal P_x$. For example, if
   $\mathcal P_x$ is $\{Q\in\mathbb R_+^{|\mathfrak R|}:\sum_{r\in\mathfrak R}Q(r)=1\}$ for all arms
   $x$, we have $\mathcal P=\mathcal P_\Omega$."

Items 3 (Bernoulli Lipschitz bandits) and 4 (parametric bandits, $\mathcal P_{\rm param}(\delta)$;
footnote 5: $\delta>0$ is needed for $\mathcal P_{\rm param}(\delta)$ to have an interior) are not
used here. Convexity of each $\mathcal P_x$ is not written in item 2; it follows from the standing
convexity of $\mathcal P$ when the $\mathcal P_x$ are nonempty.

### §4: deceitful distributions, information distance, Proposition 1 (pp. 11–12), verbatim

- (4): "$\mathrm{Deceit}(x',P):=\{Q\in\mathcal P:\ Q(x^\star(P))=P(x^\star(P)),\ \sum_{r\in\mathfrak R}rQ(r,x')>\sum_{r\in\mathfrak R}rQ(r,x^\star(P))\}$"
  "as sets of deceitful reward distributions relative to the actual but unknown reward
  distribution $P$."
- (5): "$I(M',M):=\sum_{r\in\mathfrak R}M'(r)\log(M'(r)/M(r))-M'(r)+M(r)]$" [unbalanced bracket as
  printed] "if $M'\ll M$, and $+\infty$ otherwise. Here, $M'\ll M$ denotes the implication
  $M(r)=0\implies M'(r)=0$ for all $r\in\mathfrak R$. Finally, we use the shorthand $M>0$ for the
  implication $M(r)>0$ for all $r\in\mathfrak R$." On probability vectors, $I$ is the
  Kullback–Leibler divergence; in (7) it is applied as $I(P(x),Q(x))$, i.e.
  $\mathrm{KL}(\text{true},\text{alternative})$.
- **Proposition 1 (Regret Lower Bound)** "Let $\pi$ be any uniformly good policy. For any reward
  distribution $0<P\in\mathcal P$, we have that
  $\liminf_{T\to\infty}\ \mathrm{Reg}_\pi(T,P)/\log(T)\ge C(P)$, where the regret lower bound
  function is characterized as
  $$C(P):=\inf_{\eta\ge0}\ \sum_{x\in\tilde X(P)}\eta(x)\Delta(x,P)\quad\text{s.t. } 1\le\mathrm{Dist}(\eta,x,P)\quad\forall x\in\tilde X(P)\,.\qquad(6)$$
  Here, if the set $\mathrm{Deceit}(x',P)$ is non-empty, the distance function $\mathrm{Dist}$ is
  defined as follows
  $$\mathrm{Dist}(\eta,x',P):=\inf\ \sum_{x\in\tilde X(P)}\eta(x)I(P(x),Q(x))\quad\text{s.t. } Q\in\mathrm{Deceit}(x',P)\,.\qquad(7)$$
  Otherwise, we take $\mathrm{Dist}(\eta,x',P)=\infty$."
- **The paragraph right after it** (p. 12), first two and last three sentences, verbatim:
  "Proposition 1 is a straightforward corollary (Combes et al. 2017, Theorem 1) of a much more
  general result proven by Graves and Lai (1997, Theorem 1) in a Markovian setting. Thus, we do not
  provide its proof here. A special case of Proposition 1 for discrete bandit model sets
  $\mathcal P$ was proven much earlier by Agrawal et al. (1989). As indicated in Proposition 1 by the
  infima, we make no assumptions whether or not either minimization problems (6) or (7) are
  attained. This will be a source of technical difficulty which we address."
  The reference list gives "Agrawal R, Teneketzis D, Anantharam V (1989) Asymptotically efficient
  adaptive allocation schemes for controlled iid processes: Finite parameter space. *IEEE
  Transactions on Automatic Control* 34(3)." and Graves, Lai (1997), SIAM J. Control Optim.
  35(3):715–743. No proof of Proposition 1 is given in the paper.
- The next two paragraphs (pp. 12–13) interpret $\eta(x)$ as the rate $N_{T+1}(x)\approx\eta(x)\log T$
  and the constraint as an optimal hypothesis-testing condition, credited to Graves and Lai.
- Footnote 6 (p. 11): in "rare instances" the lower bound does not scale with $T$: the set of
  deceitful distributions is empty and suboptimal arms "can be simply ruled out".

### §4.1: partition of the suboptimal arms (pp. 13–15), verbatim

- (8): "$\mathrm{Rew}_{\max}(x,P):=\max\ \sum_{r\in\mathfrak R}rQ(r,x)$ s.t.
  $Q\in\mathcal P,\ Q(x^\star(P))=P(x^\star(P))$".
- **Non-deceitful arms**: "Non-deceitful arms $\tilde X_n(P)$. A suboptimal arm $x$ is
  non-deceitful, i.e., $x\in\tilde X_n(P)$, if $\mathrm{Rew}_{\max}(x,P)\le\mathrm{Rew}^\star(P)$. For
  any non-deceitful arm $x\in\tilde X_n(P)$, the set of associated deceitful distributions
  $\mathrm{Deceit}(x,P)$ is empty. Consequently, non-deceitful arms do not impose any conditions on
  the rates with which suboptimal arms need to be played in the regret lower bound (6); we have
  indeed $\mathrm{Dist}(\eta,x,P)=+\infty$ for any logarithmic exploration rate $\eta$."
- **Deceitful arms** (the definition): "Deceitful arms $\tilde X_d(P)$. Suboptimal arm
  $x\in\tilde X_d(P)$ if $\mathrm{Rew}_{\max}(x,P)>\mathrm{Rew}^\star(P)$. For these arms, the set of
  associated deceitful distributions $\mathrm{Deceit}(x,P)$ is non-empty and the distance
  $\mathrm{Dist}(\eta,x,P)$ between reward distribution $P$ and these deceitful distributions is
  finite."
- **The example (9)** (summary, p. 14): a separable Bernoulli bandit, $\mathfrak R=\{0,1\}$,
  $X=\{a,b\}$,
  $\mathcal P=\mathcal P_1\times\mathcal P_2:=\{Q\in\mathbb R_+^2:\sum_{r\in\{0,1\}}Q(r)=1,\ Q(0)\ge\frac25\}\times\{Q\in\mathbb R_+^2:\sum_{r\in\{0,1\}}Q(r)=1\}$ (9).
  Then $\mathrm{Rew}_{\max}(a,P)=\frac35$, $\mathrm{Rew}_{\max}(b,P)=1$ for every $P$. With
  $P(a)=[1/2,1/2]$, $P(b)=[1/5,4/5]$: $x^\star(P)=b$, $\mathrm{Rew}^\star(P)=4/5>3/5$, so $a$ is not
  deceitful; playing $b$ alone eventually rules $a$ out, and the text concludes "the lower bound,
  $C(P)$, presented in Proposition 1, is zero."
- **Proposition 2 (Distance Function for Deceitful Arms)** (p. 15) "Consider any reward distribution
  $P\in\mathcal P$, deceitful arm $x'\in\tilde X_d(P)$, and positive exploration rate $\eta\ge0$.
  Then,
  $$\mathrm{Dist}(\eta,x',P)=\min_{Q\in\mathcal P}\ \sum_{x\in\tilde X(P)}\eta(x)I(P(x),Q(x))\quad\text{s.t. } Q(x^\star(P))=P(x^\star(P)),\ \sum_{r\in\mathfrak R}rQ(r,x')\ge\mathrm{Rew}^\star(P).\qquad(10)$$"
  ("positive" and "$\eta\ge0$" as printed.) The paragraph after it: the proof is in Appendix H
  (H.1); for a deceitful arm "(i) the infimum in the previous optimization problem is achieved and
  is finite, and (ii)" the constraint $Q\in\mathrm{Deceit}(x',P)$ can be replaced by the two
  constraints of (10); "the partitioning of arms into two types alleviates the technical
  difficulty caused by potential non-attainment of the infimum (7)."
- **Example 3 (Regret Lower Bound)**, opening and items 1–2 (pp. 15–16), verbatim:
  "Using Proposition 2, we characterize the lower bound and distance functions ($C$ and
  $\mathrm{Dist}$) for generic, separable, and Lipschitz Bernoulli bandits.
  1–2. Generic and separable bandits. For generic, and more generally separable bandits, the lower
  bound presented in Proposition 1 coincides precisely with the results first proven in the seminal
  work of Lai and Robbins (1985). Recall that for separable bandits, the set $\mathcal P$ decomposes
  as the Cartesian product $\prod_{x\in X}\mathcal P_x$. This implies that for any reward
  distribution $P\in\mathcal P$ and suboptimal arm $x'\in\tilde X(P)$, we get
  $\mathrm{Rew}_{\max}(x',P)=\max\{\sum_{r\in\mathfrak R}rQ(r):Q\in\mathcal P_{x'}\}$. For any
  deceitful arm $x'$, we define a distribution $Q^\star_{x'}(x)=P(x)$ for all $x\in X\setminus\{x'\}$
  and let
  $$Q^\star_{x'}(x')\in\arg\min_Q\{I(P(x'),Q):\ Q\in\mathcal P_{x'},\ \textstyle\sum_{r\in\mathfrak R}rQ(r)\ge\mathrm{Rew}^\star(P)\}.$$
  The constructed reward distribution $Q^\star_{x'}$ can be interpreted as the worst deceitful
  reward distribution for deceitful arm $x'$. That is, it can be verified that $Q^\star_{x'}$ is the
  optimal solution to problem (10). Also note that the constraint $\mathrm{Dist}(\eta,x',P)\ge1$ in
  the regret lower bound problem demands that $\eta(x')\ge1/I(P(x'),Q^\star_{x'}(x'))$ for each
  deceitful arm. This leads to $\eta^\star(x',P)=1/I(P(x'),Q^\star_{x'}(x'))$ for
  $x'\in\tilde X_d(P)$ and $\eta^\star(x',P)=0$ for $x'\in\tilde X_n(P)$, which is the minimizer in
  problem (6) defining the lower regret bound for all suboptimal arms $x'\in\tilde X(P)$."
  The value $C(P)=\sum_{x'\in\tilde X_d(P)}\Delta(x',P)/I(P(x'),Q^\star_{x'}(x'))$ is **not
  displayed**; it is what the stated minimiser gives in (6). No separate proof ("it can be
  verified"). Item 3 (Bernoulli Lipschitz, credited to Magureanu et al. 2014) gives the linear
  program (11) and $C(P)=0$ when $\mathrm{Rew}^\star(P)=\max(\mathfrak R)$.

### Other results read — summary

- §5.1 (pp. 20–21), the separable example (9) with $P_\lambda(a)=[\frac12,\frac12]$,
  $P_\lambda(b)=[1-\lambda,\lambda]$, $\lambda\in[0,1]$: printed
  $C(P_\lambda)=0$ on $[\frac35,1]\cup\{\frac12\}$ (at $\lambda=\frac12$ both arms are optimal, so
  $\tilde X(P)=\varnothing$), $C(P_\lambda)=\frac{\lambda-\frac12}{\frac12\log(\frac{1/2}{\lambda})+\frac12\log(\frac{1/2}{1-\lambda})}$
  on $(\frac12,\frac35)$ and $\frac{1/2-\lambda}{\lambda\log(\frac{\lambda}{1/2})+(1-\lambda)\log(\frac{1-\lambda}{1/2})}$
  on $[0,\frac12)$; discontinuous at $\frac12$ and $\frac35$ (motivating Assumption 1). At
  $\lambda=\frac35$, $\mathrm{Rew}_{\max}(a)=\mathrm{Rew}^\star$: $a$ is non-deceitful and contributes 0.
- Proposition 3 (continuity of $C$ and of an $\epsilon$-suboptimal rate selection on
  $\mathcal P'$, the set of $P$ satisfying Assumption 1); Lemma 1 and Theorem 2 (dual formulation of
  $\mathrm{Dist}$ and of $C$); Theorem 3 (for $P\in\mathcal P'$, $0<\epsilon<1/|X|$, DUSA has
  $\limsup_T\mathrm{Reg}/\log T\le(1+\epsilon)(C(P)+\epsilon(1+\sum_x\Delta(x,P)))$); Remark 1
  (p. 29): for $P\in\mathcal P'$ with $\tilde X_d(P)=\varnothing$, "the regret lower bound function
  $C(P)=0$ vanishes", with bounded regret for DUSA.
- Appendix B, Lemma 2 (p. 40), on the finite simplex: $I\ge0$ with equality iff equal; joint
  convexity; continuity of $I(P,P')$ in $P'$ on $\{P\ll P'\}$; lower semicontinuity (closed bounded
  sublevel sets).

## Techniques

- Proof of Proposition 2 (Appendix H.1, pp. 73–74). First part: $\mathrm{Dist}$ is finite iff
  $\mathrm{Rew}^\star(P)<\mathrm{Rew}_{\max}(x',P)$, by mixing a maximiser $\hat Q$ of (8) with $P$,
  $\bar Q=(1-\theta)\hat Q+\theta P$ (convexity of $\mathcal P$; the text writes $\bar Q\ll P$,
  while what the mixture gives and what finiteness of $I(P(x),\bar Q(x))$ needs in the convention
  of (5) is $P(x)\ll\bar Q(x)$). Second part: (10) has a minimiser (lower semicontinuity of $I$,
  compact feasible set, Bertsekas 2009 Prop. 3.2.1); the segment
  $Q'_\theta=\theta\bar Q+(1-\theta)Q^\star$ lies in $\mathrm{Deceit}(x',P)$ for $\theta\in(0,1]$, and
  convexity of $I$ in its second argument with $\theta\downarrow0$ gives equality of (7) and (10).
  Uses: finite reward set, $\mathcal P$ closed and convex; not $P>0$, not uniqueness of the optimal
  arm, not the interior.
- Proposition 1 is not proved; credited to Combes et al. 2017, Theorem 1 and Graves–Lai 1997,
  Theorem 1, with the special case of "discrete bandit model sets" to Agrawal et al. 1989.
- Duality: $\mathrm{Dist}$ and $C$ are rewritten as finite convex programs over the dual cone of
  $\mathrm{cone}(\mathcal P)$ (§5.2, Appendix C), the basis of the algorithm DUSA.

## Where Incognita uses it

Not cited yet (2026-11-17). Intended for `papers/P007-stochastic-setting/` (the setting paper of
StochasticBandits) as the nearest published statement of `thm:main`, at a referee's request:
Example 3, items 1–2, with Proposition 2, is the case "finite common reward set, closed convex
$\mathcal P_x$, $\mathcal P$ with nonempty interior" of the formula
$C(\nu)=\sum_{a}\Delta_a/\mathcal K_{\inf}(\nu_a,m^\star;\mathcal D_a)$.
