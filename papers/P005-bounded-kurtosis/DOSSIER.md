# Dossier of P005-bounded-kurtosis, version 1

Refereed and versioned with `paper.tex`, never compiled into the PDF: what the referees and the
owner need and the reader does not. It changes only with a new version of `paper.tex` after
acceptance. Private KNOWN entries are cited by id only, never quoted (this roadmap has none).

The paper was written on 2026-11-16 from a research report and its independent check (working
notes outside the repository); the check's defects V1.1–V1.10 and what was done with each are in the
last section.

## Roadmap correspondence

- Items served (`directions` of META.toml): **D8, part (a)**. The roadmap asks: "Kurtosis: for
  instances in $\mathcal H_\kappa^\alpha$ (kurtosis at most a known $\kappa$, positive variances), an
  algorithm with $\limsup_T R_T/\log T\le\sum_a\Delta_a/\mathcal K_{\inf}(\nu_a,m^\star;\mathcal H_\kappa)$, matching
  K1; or a proof that no consistent algorithm attains it (known: only up to a universal constant,
  K19; open problem of [L17, Section 4], K62)." Correspondence: `thm:main`(ii) is exactly this
  inequality for the anytime algorithm `KL-UCB-Kurt` (Definition `def:algorithm`), on every
  $\nu\in\mathcal H_\kappa^\alpha$, with $\mathcal H_\kappa$ = laws with finite fourth moment, positive variance and
  kurtosis $\le\kappa$ (`def:class`; the finite fourth moment is implicit in "kurtosis"); `cor:exact`
  pairs it with K1 ([LS, Theorem 16.2], node `cite:LS-16.2`) in the class of algorithms consistent
  over $\mathcal H_\kappa^\alpha$. Part (b) of D8 (heavy tails, $o(T)$ recomputations) is not addressed.
- **D7 material for the kurtosis class** (not declared in `directions`, since the main result serves
  D8 and D7 asks for one class per paper "used by an item of C"; the referee may judge whether D7
  should be added): D7 asks, for the class with kurtosis at most $\kappa$, "a dual or variational formula
  for $\mathcal K_{\inf}(P,\mu;\mathcal D)$, its continuity in $(P,\mu)$ where it holds, and a deviation inequality
  $\mathbb P(n\mathcal K_{\inf}(\hat P_n,m(P);\mathcal D)\ge x)\le f(n)e^{-x}$ with explicit $f$". Given: the dual formula
  for every law (`prop:dual`(v)); lower semicontinuity in $(P,\mu)$ at every non-Dirac law with a finite
  fourth moment, continuity in $\mu$ (`prop:regularity`), not continuity in $P$ (not proved; it fails at
  Dirac masses, remark "Failure at Dirac masses"); the deviation inequality with $f(n)=e(n+1)^2$,
  even anytime (`thm:deviation`(i)). These results are used by D8(a) here.
- What the items ask that the paper does not give: nothing for D8(a) at first order. The roadmap's
  list of important results mentions "a simple algorithm (stated by its formula, with a stated cost
  per round)": the algorithm is stated by its formula, but its index has no certified computation, so
  no cost per round is claimed (paragraph "Computation" of Section 5, `oq:computation`). The Scope
  paragraph of Section 6 says this in words.
- Acceptance criteria of the roadmap, one by one:
  1. model, class of algorithms, criterion: `thm:main` (class $\mathcal H_\kappa^\alpha$, anytime algorithm, first
     order and a finite-time bound with an existential constant), `cor:exact` (consistent algorithms,
     first order). Met.
  2. Closest known: below (K1, K17, K19, K43, K50, K62, K63; PA26, A22, AKJ21, BSH23 since revision
     round 1; empirical likelihood and Cat12 for the techniques and the confidence sequence). Met.
  3. Instance and $K=2$ Gaussian/Bernoulli checks: Section 9 (`N(1,1)` vs `N(0,1)`, $\kappa=3$; Bernoulli
     and Gaussian bullets), and below. Met.
  4. Algorithm defined completely: threshold (eq:threshold), initialisation, tie rule (any), anytime,
     `sup ∅ := −∞`, Dirac empirical laws (Lemma `lem:index`). D8(a) does not mention computation; the
     paper says that no certified computation is given. Met.
  5. Constants: existential $C_a(\varepsilon)$, dependence on $(\nu_a,m^\star,\varepsilon,\kappa)$ stated; everything else
     explicit from $T\ge3$. Met.
  6. Optimality only as a corollary pairing two bounds in one class (`cor:exact`). Met.
  7. Not routine: see "Closest known" (the lower deviation needs `lem:escape` and the value
     $\mathcal K_\infty$; the independent check judged that a scope referee could not write the proof in half
     a page). Met, to be judged by the referee.
  8. Not a lemma paper. Not applicable.
  9. Previous best value and new one: for the by-product $\mathcal K_{\inf}\le\mathcal K_\infty(\kappa)$, the previous
     bound [L17, Theorem 9] (large-gap branch $\log\frac{\kappa}{\kappa-1}$) is stated and compared (paragraph
     after `prop:kinfty`, node `cite:L17-thm9`); the main result gives the exact constant where only
     constant factors were known (K19). Met.
  10. Not a "not important on their own" result: it is an exact first-order constant where only
      constant factors were known, listed as important by the roadmap. Met.
- Conventions of the roadmap: $\mathcal K_{\inf}$ strict (`def:kinfD`), with the non-strict version shown equal
  (`lem:strict`); rounds numbered from 1, $N_a(t)$ = pulls in rounds $1,\dots,t$ (the same quantity as
  LML's `pullCount` at $t$); consistency as [LS, Definition 16.1]. The threshold uses $t\vee3$ (so that it
  is defined and non-negative from the first index round $t=K\ge2$); this is a choice of the algorithm,
  not a change of convention. No convention changed.

## Closest known

- **K1** ([LS, Theorem 16.2]; Lean: LMLExplore `eventually_mul_log_le_integral_regret_of_isConsistent`):
  the lower bound. Used as is (`cite:LS-16.2`) in `cor:exact`(i), with $\mathcal M_i=\mathcal H_\kappa$ (finite means)
  and $d_{\inf}=\mathcal K$ (strict). The paper's contribution is the matching upper bound and the structure
  of $\mathcal K$.
- **K19** ([L17, Theorem 2], node `cite:L17-thm2`): $\limsup R_n/\log n\le C\sum\Delta_i(\kappa-1+\sigma_i^2/\Delta_i^2)$ with a
  universal $C$. Difference: constant factor. Derivation attempt: none possible; the median-of-means
  index loses constant factors by construction, and the bound does not involve $\mathcal K_{\inf}$. The paper
  compares the two numerically (Table `tab:curves`: ratio 1.4–2.1 on two laws).
- **K62** ([L17, Section 4]) and **K63** ([LS, Section 16.4]): the open problem (optimal constants for
  bounded kurtosis); answered at first order by `cor:exact`. The second open problem of K62
  (non-parametric Thompson sampling) is `oq:randomised`.
- **K43** ([L17, Theorem 7]): $\kappa$ must be known. Consistent with the paper ($\kappa$ is an input; Scope
  paragraph).
- **K17, K50** ([AJK21, Theorem 1, Corollary 2], node `cite:AJK21-cor2`): KLinf-UCB optimal on
  $\mathcal L_B=\{\mathbb E|X|^{1+\varepsilon}\le B\}$. Same algorithmic template and threshold. Derivation attempt: run the
  proof of [AJK21] with $\mathcal L=\mathcal H_\kappa$. It fails at two places: (1) the dual formula [AJK21, Lemma 7]
  comes from Lagrangian duality for the convex class $\mathcal L_B$ with a compact dual region $R(x,B)$ at
  the level $x$; $\mathcal H_\kappa$ is not convex (a mixture of two laws of small kurtosis can have a large
  kurtosis), so a convexification is needed (`lem:G`, `lem:repr`); (2) the lower deviation [AJK21,
  Lemma 6] rests on continuity properties of $\mathrm{KL}_{\inf}$ on a class that is tight (bounded
  $(1+\varepsilon)$-moment); $\mathcal H_\kappa$ is scale free, hence not tight, and near-optimal alternatives can
  escape along the affine group (`lem:escape`, with the value $\mathcal K_\infty$ from `lem:atom`).
- **[PA26, Theorem 3.1]** (node `cite:PA26-thm3.1`): KLinf-UCB is optimal on any class satisfying
  Assumptions 2.3 and 2.4. Derivation attempt: show that $\mathcal H_\kappa$ satisfies both and apply it.
  Assumption 2.3 holds with $g(n)=2\log(1+n)+1$: it is `thm:deviation`(i), whose proof needs the
  convexification and the finite-support duality (about a page once `lem:G`, `lem:repr`, `lem:finite`
  are known; the independent check called this part routine for an expert of AJK21 and of the thesis
  A22). Assumption 2.4 asks, for each $\nu$ and $\delta>0$, a rate $e^{-nc_\nu d^2}$ for **all** $d<d_0$ at the fixed
  level $m(\nu)+\delta$; it is **not proved here**: `thm:deviation`(ii) gives, for each $\varepsilon$, an existential
  rate $2Je^{-2n\eta^2}$ at the shifted level $\mu-\delta$, which suffices for the first order but is not of the
  form of 2.4. So [PA26, Theorem 3.1] cannot be applied as such; the paper gives a self-contained
  regret proof (Appendix F). Moreover even the weaker lower deviation needs `lem:escape` and
  `prop:kinfty`: this is where the difficulty lies, so the result is not a routine corollary of PA26.
  Note (independent check, V1.9): in PA26 App. A.2 the lower-deviation term is bounded by
  $\sum_te^{-tc_{\nu_a}d^2}$ with the round $t$ in place of the sample count; Appendix F counts over the sample
  sizes $s=N_a(t)$ with the fundamental inequality (eq:fundamental). The paper does not comment on
  PA26's proof.
- **[A22, Section 6.10; Chapter 6; App. 6.D.1] and [AKJ21, Theorem 3.4]**: the device "outer scalar
  minimisation + convex inner problem + duality + mixture martingale with the outer variable fixed at
  its true value". For CVaR the outer variable ranges over a **compact** interval (range lemma, A22
  Lemma 6.1); for the centred-moment class A22 §6.10 writes the reduction over the location $y\ge x$,
  states that a concentration result "can be proven", and leaves "the continuity of these new
  projection functions" and "the extreme distributions" to separate research. Difference: two outer
  parameters (location and scale) for a ratio of moments, through the quartic $\varphi$; a non-compact
  outer domain, whose boundary value $\mathcal K_\infty(\kappa)$ is computed from the largest atom; the
  kurtosis theorem. Derivation attempt: none of these works treats the kurtosis or a scale parameter
  (text search of A22 for "kurtosis" and "scale": only the related-work sentence of §3.1). The paper
  credits the device in the Introduction, in Related work, after `lem:repr`, and in Appendix H.
- **[BSH23, §4.4.2, Lemma 9, Corollary 6, App. D.5]** (arXiv:2303.06058v3; `literature/notes/BSH23.md`,
  added in revision round 1 after the scope referee's SC1.1): for the non-convex centred class
  $\{F:\mathbb E_Fh(|X-\mu_F|)<B,\ \mathbb E_Fh(|X|)^{2+\varepsilon_F}<\infty,\ \mu_F\ge\mu^-\}$ ($h$ convex, $B$ and a lower bound
  $\mu^-$ on the means known, the latter "in order use arguments based on compactness"), they write
  $\mathcal K_{\inf}$ as an infimum over the location $\mu\ge\mu_1$ of a convex fixed-location problem with a
  two-dimensional dual, reduce it by a translation to the uncentred problem, state that the infimum is
  attained at $\mu_1$, and prove that MED is asymptotically optimal (Corollary 6). Difference: a fixed level
  $B$ and one outer parameter (the location), on a half-line where the infimum is attained at the end,
  with a known lower bound on the means; here a ratio of moments, invariant under scale changes, with two
  outer parameters, a non-compact outer domain on which the infimum need not be attained, no bound on
  the means or scales, and the boundary value $\mathcal K_\infty(\kappa)$. Derivation attempt: write
  $\mathcal H_\kappa$ in their form. The constraint $\mathbb E(X-m)^4\le\kappa\sigma^4$ is not $\mathbb Eh(|X-m|)<B$ for a fixed $B$,
  and fixing the location alone leaves the non-convex constraint $\int(x-c)^4dQ\le\kappa(\int(x-c)^2dQ)^2$; with the
  scale fixed too (our $\mathcal G_\kappa$) the problem is convex, but the translation argument that puts their
  infimum at $\mu_1$ has no analogue for the scale, and near-optimal scales can go to $0$ or $\infty$
  (`lem:escape`). So the main result is not a corollary. The paper says this in Related work (Table 1,
  "Non-convex information functions", "Closest related work", "Gap with the literature"), after `lem:G`
  and `lem:repr`, in `oq:profiled` and in Appendix H.
- **Empirical likelihood** ([O01], table of contents only; the scope referee's SC1.2): profiling the mean
  and the variance as nuisance parameters of estimating equations to make inference on skewness and
  kurtosis is classical there (Owen 2001, §1.1 and §3.5, by their titles), with the dual
  $\max\sum\log(1+\lambda\cdot g)$. Difference: there the constraints are equalities of estimating equations
  at the sample; here the inequality $\mathrm{kurt}\le\kappa$ is made linear by the quartic $\varphi$ with a free
  scale, inside $\mathcal K_{\inf}$ for arbitrary laws, and the outer problem's escape is analysed. The paper
  cites [O01] as "see also" (its text was not read): Related work, after `lem:G`, Appendix H.
- **Scale-free confidence intervals under a kurtosis bound** ([Cat12, Corollary 4.3, Proposition 4.5];
  also arXiv:0909.5366 §5, Proposition 5.2, no entry; the scope referee's SC1.10): fixed sample size and
  level, width $\simeq\sqrt{2v\log(1/\epsilon)/n}$, condition $\log(1/\epsilon)\le n/(36(\kappa-1))-1/8$ for $\kappa\ge3$.
  `cor:confseq` is anytime and has no closed-form width; compared in the paragraph after it.
- **K14, K15** (Gaussian laws with unknown variance, [HT14], [CHK18]): a parametric subclass of
  $\mathcal H_\kappa$ for $\kappa\ge3$; their constant $\Delta/(\frac12\log(1+\Delta^2/\sigma^2))$ is smaller than ours (larger class,
  smaller $\mathcal K_{\inf}$). Used in the example of Section 9.
- **K11, K16, K46, K49**: other classes (semi-bounded, $[0,1]$); not applicable.
- Library papers: no paper of the library is on this roadmap's direction; `depends_on` is empty.

## Sanity checks

- **$\kappa$.** $\kappa\le1$: the class is empty for $\kappa<1$ and contains only symmetric two-point laws for
  $\kappa=1$ (excluded by $\kappa>1$; there $\mathcal K=+\infty$ above the mean). $\kappa\downarrow1$: $q_\kappa\to1/2$,
  $\mathcal K_\infty\to\log2$. $\kappa\to\infty$: $\mathcal K_\infty\sim1/\kappa\to0$; consistent with K43 (no logarithmic regret
  uniformly over the classes).
- **$K=2$, Gaussian arms** ($\kappa=3$, $\mathcal N(1,1)$ and $\mathcal N(0,1)$, Section 9): hypotheses hold (kurtosis 3);
  the constant $1/\mathcal K(\mathcal N(0,1),1)$ is at least $1/\mathcal K_\infty(3)=4.21$ (rigorous, `prop:kinfty`(ii)) and at
  least the Gaussian-model constant $2.885$ (K14), as it must be for a larger class; numerics suggest
  about $5.2$.
- **Bernoulli arms.** Bernoulli($\theta$) $\in\mathcal H_\kappa$ iff $\theta\in[1-q_\kappa,q_\kappa]$; the extreme laws are the
  largest-atom laws of `prop:kinfty`(i). Against K1: for a Bernoulli arm,
  $\mathcal K(\mathrm{Ber}(\theta),m^\star)\le\inf\{\mathrm{kl}(\theta,\theta'):\theta'>m^\star,\ \theta'\in[1-q_\kappa,q_\kappa]\}$ (Bernoulli alternatives inside
  $\mathcal H_\kappa$), so the constant over $\mathcal H_\kappa$ is at least the one of the Bernoulli model restricted to
  $[1-q_\kappa,q_\kappa]$, as it must be for a larger class. Dirac empirical laws (all samples equal, probability $\le q_\kappa^{n-1}$): the index is
  $\pm\infty$ (`lem:index`(iii)), covered by `thm:deviation`(i) for the optimal arm; on that event
  $n\mathcal K=n\mathcal K_\infty$ and $q_\kappa^{n-1}\le e(n+1)^2e^{-n\mathcal K_\infty}$, consistent with (i).
- **Ties, several optimal arms:** any tie rule; the decomposition uses one optimal arm $a^\star$.
- **Infinite divergences:** $\mathcal K\le\mathcal K_\infty<1$ for every law with a finite fourth moment (in particular
  every empirical law), so the index is $+\infty$ only through $n\mathcal K_\infty\le g$; laws with
  $\mathbb E\log(1+|X|)=\infty$ have $\mathcal K_{\mathcal G}=\infty$ at every $(c,s)$ but are never empirical laws.
- **Boundary laws** ($\mathrm{kurt}=\kappa$: Gaussian with $\kappa=3$, extreme Bernoulli): covered (only
  $\mathbb E\varphi(Y)\le0$ and non-Diracness are used); numerics of Table `tab:duality` (right) show continuity
  at the mean and the limit $\mathcal K_\infty$.
- **Heavy-tailed empirical laws** (kurtosis of $\hat P_n$ above $\kappa$): then $\mathcal K(\hat P_n,\mu)>0$ even below the
  empirical mean; harmless, only the two deviation events enter the proof.
- **Consistency with KNOWN:** K1 (strict $d_{\inf}$, as LMLExplore's `dInf`); K19 (our constant is
  $>\kappa\Delta$ per arm, consistent with the $\kappa-1$ term); K43 ($\kappa$ known). KNOWN.md has no entry with the
  status `[Lean]`; K1's Lean declarations are the lower bound we pair with.
- **Numerics:** Tables 2–4 of the paper (Table 1 is the comparison table) reproduce the report and the independent check to the printed
  digits (scripts and outputs in `notebook/`).

## Weak points

The three steps the authors are least sure of, most doubtful first:

1. **`lem:finite`, Steps 2–5 (strong duality for finitely supported laws).** The research report
   proved it by Slater's condition for a program over the non-closed cone generated by the moment
   curve (checked by the independent verification, with Rockafellar's Theorem 28.2, which was not read
   for this paper). The paper replaces it by a direct construction (first-order condition at a
   maximiser $\lambda^\star$, separation from the cone of the $\gamma(u)$ at the zeros of $h_{\lambda^\star}$, feasibility of
   $\lambda^\star+td_\epsilon$ near the zeros and at infinity, then an explicit optimal law). This proof is new
   relative to the checked report. A second independent check of the paper (2026-11-16, verdict
   accept, last section) went through Steps 1–5 line by line, including the bound $c_F>0$ on the closed
   set $F$, the perturbation $d_\epsilon=d-\epsilon\lambda^\star$, a maximiser at a vertex of $\Lambda$ and the mass computation
   of Step 5, and found no gap; it also rebuilt the optimal law of Step 5 numerically on seven laws. A
   referee should still check the feasibility argument of Step 4. Numerical agreement of dual and
   primal on four random laws (interpretation of Table `tab:duality`, `notebook/table2_out.txt`) supports the statement.
2. **`lem:escape`, the case analysis.** The lower semicontinuity holds only at non-Dirac laws with a
   finite fourth moment; it fails at Dirac masses. Case 2 uses $P(\{c\})<1$, case 4 the largest atom; the
   exhaustiveness argument is short. If a case were missing, `thm:deviation`(ii), hence `thm:main`,
   would fail. The independent check found no gap.
3. **Novelty and the existential rate.** (a) The convexification device is in [AKJ21; A22 Ch. 6] for
   CVaR, in [A22 §6.10] and, with a regret theorem for MED under a known lower bound on the means, in
   [BSH23, App. D.5, Corollary 6] for centred moments; profiling location and scale as nuisance
   parameters is classical in empirical likelihood ([O01], whose text was not read: cited as "see
   also"). Since revision round 1 the paper claims as new only the inequality $\mathrm{kurt}\le\kappa$ made
   linear by $\varphi$ with a free scale inside $\mathcal K_{\inf}$, the escape analysis without bounds on the means or
   scales, with $\mathcal K_\infty$, and the kurtosis theorem. An empirical-likelihood text with an inequality
   moment-ratio constraint may still exist (not found: El Barmi-type inequality constraints have no ratios,
   per the scope referee's searches). (b) `thm:deviation`(ii) has an existential rate, so no explicit
   second-order term (`oq:finite`).

Lesser points: `lem:alllaws` (Skorokhod applied at a fixed outcome of Varadarajan's theorem and the
SLLN); measurability (`lem:index`, corrected as asked by V1.4); the comparison with [L17, Theorem 9],
whose printed statement has the class of the alternatives with the wrong subscript (see
`literature/notes/L17.md`; the paper restates the weaker reading).

## Searches

From the research report (2026-11-15/16, WebSearch and the Semantic Scholar API):

- "asymptotically optimal bandit bounded kurtosis K_inf": L17; AJK21; Honda–Takemura 2010; Baudry et
  al. "Dirichlet sampling" (arXiv:2111.09724); Baudry–Suzuki–Honda "general recipe" (arXiv:2303.06058).
  No $\mathcal K_{\inf}$ for kurtosis.
- "Lattimore 'bounded kurtosis' bandit open problem optimal constant solved": only L17 and AJK21.
- "kurtosis bandits asymptotically optimal K_inf/KL_inf moment ratio class 2023–2025": AJK21;
  arXiv:2303.06058 ($h$-moment classes $\mathbb Eh(|X|)\le B$, not ratios); an LIL for KL_inf (arXiv:2602.05259).
- "bandit 'known kurtosis' OR 'bounded kurtosis' regret lower bound exact constant 2022–2024": nothing
  beyond L17.
- "Shubhada Agrawal thesis … moment constraints KL_inf duality": Agrawal–Juneja–Glynn 2020,
  Agrawal–Koolen–Juneja 2021, a 2022 talk; the thesis not found then.
- "kurtosis multi-armed bandit Thompson sampling / median of means / Catoni scale-free 2019–2026": L17,
  arXiv:2006.03378, AJK21.
- Semantic Scholar, papers citing arXiv:1703.08937 (25 titles) and arXiv:2102.03734 (48 titles):
  none claims the optimal constant on bounded kurtosis; abstracts read: Gupta–Sethi–Agrawal 2026
  (arXiv:2610.18055, empirical likelihood, forcing, no known class), Do–Nguyen 2026 (arXiv:2611.12140),
  Shekhar–Agrawal 2026 (arXiv:2603.21027), Panda–Agrawal 2026 (PA26), Clerico 2026 (arXiv:2606.06769).

From the independent check (2026-11-16, WebSearch): "asymptotically optimal bandit algorithm bounded
kurtosis KL_inf Lattimore open problem"; "\"kurtosis\" bandit \"Burnetas\" \"Katehakis\" optimal constant
scale-free 2024 OR 2025 OR 2026"; "Shubhada Agrawal PhD thesis TIFR \"heavy tails\" bandits algorithms
analysis optimality kurtosis" (led to the publications page and the thesis); "\"empirical likelihood\"
bandit kurtosis scale-free \"2610.18055\""; "bandit \"bounded kurtosis\" asymptotically optimal regret
\"KL\" index 2025 2026 arXiv"; "minimum KL divergence moment ratio constraint \"kurtosis\" empirical
likelihood profile location scale dual formula"; "\"KLinf\" OR \"K_inf\" kurtosis \"scale-invariant\" OR
\"location-scale\" class bandit optimal Lattimore 2017 open question solved". None found the main result
or a $\mathcal K_{\inf}$ formula over $\mathcal H_\kappa$; Broniatowski–Keziou (divergence duality, linear constraints
only).

For this paper (2026-11-16): "Shubhada Agrawal PhD thesis \"Bandits with Heavy Tails\" TIFR pdf"
(publications page, thesis link, NeurIPS 2021 CVaR paper, PA26 listed as ISIT 2026); the thesis PDF
(Google Drive link of that page) and the NeurIPS 2021 paper PDF were fetched and read in the parts
listed in `literature/index.md`.

From revision round 1 (2026-11-17, three search agents of the revise session, WebFetch on the
pages below and WebSearch for the PDFs): arXiv abstract page and v3 PDF of arXiv:2303.06058 (BSH23; HTML
version for text search of "kurtosis", "scale", "ratio", "variance": none for kurtosis, scale or ratios);
Project Euclid pages of Owen (1990, Ann. Statist. 18) and Qin–Lawless (1994, Ann. Statist. 22): empty
pages, only the Crossref and OpenAlex records were read (not cited); Owen's empirical-likelihood home page,
the table of contents and the errata of Owen (2001) (O01); Google Books preview of O01 (no text); the
OUP page of Owen (1988, Biometrika), abstract only (not cited); arXiv:0909.5366 (Catoni 2009, §5) and
arXiv:1009.2048 with the journal PDF of Cat12 on numdam.org; arXiv:2008.07606v3 (AKJ21, Lemma E.1);
arXiv:2102.03734v1 (AJK21, Lemma 17 and its reference); the JMLR page and PDF of CHK18 (Theorems 4–6).

## Reading notes

- [L17]: arXiv v1 text and ar5iv: Assumption 1, Theorems 2, 7, 9, (6), §4, App. A
  (`literature/notes/L17.md`). Theorem 9's class of alternatives is printed with the subscript of the
  kurtosis of $\nu$; the paper restates the weaker reading.
- [AJK21]: PMLR text: Theorem 1, Corollary 2, Proposition 5, Lemmas 6, 7, 11, Remark 12, §3.5, §5
  (`literature/notes/AJK21.md`).
- [PA26]: arXiv v1: Definition 2.1, Assumptions 2.3–2.4, Theorem 3.1, App. A.1–A.2
  (`literature/notes/PA26.md`).
- [A22]: thesis PDF: TOC, §1.4, §3.1, §6.1, §6.3.2 (Theorem 6.5, Proposition 6.6 and after), §6.10,
  App. 6.D.1 to (6.55) (`literature/notes/A22.md`).
- [AKJ21]: NeurIPS 2021 PDF: abstract, §1, Theorem 3.4, after Proposition 3.5, Proposition 4.2 and after.
- [LS]: Theorem 3.9, Definition 16.1, Theorem 16.2, §16.3, §16.4 (`literature/notes/LS.md`).
- Revision round 1 (2026-11-17): [BSH23] §4.4, §4.4.2, Lemma 9, Corollary 6, App. D.5 (note
  `BSH23.md`); [Cat12] §4.1, Corollary 4.3, §4.2, Proposition 4.5 (and arXiv:0909.5366 §5); [AKJ21]
  arXiv:2008.07606v3 Theorem 3.4 and Lemma E.1 with the sentence crediting Blum–Kalai and
  Hazan–Agarwal–Kale; [AJK21] arXiv v1 Lemma 17 ("borrowed from Agrawal et al. (2020b)" = AKJ21);
  [CHK18] JMLR PDF, Theorems 4–6 (the asymptotic statement is Theorem 5 there, Theorem 4 in arXiv v2);
  [O01] table of contents only. Parts read are in `literature/index.md`.

## Material left out of the paper

- **Centred-moment class** (the report's "Theorem E", proved there in condensed form, checked bullet
  by bullet by the independent check): for $\mathcal L^c=\{Q:\int|x-m(Q)|^p\,dQ\le B\}$, $p>1$, KL-UCB with
  $\mathcal K_{\inf}(\cdot,\cdot;\mathcal L^c)$ and the same threshold has $\limsup\mathbb EN_a(T)/\log T\le1/\mathcal K_{\inf}(\nu_a,m^\star;\mathcal L^c)$.
  Sketch: $Q\in\mathcal L^c$ with mean $c$ iff its translate by $-c$ lies in the convex weakly compact
  $\mathcal G'=\{\int y\,dQ=0,\int|y|^pdQ\le B\}$; dual set $\Lambda'=\{1+\lambda_1y+\lambda_2(|y|^p-B)\ge0\}$ with $\lambda_2\le1/B$; Slater
  points $u\in\{-a,0,a\}$; upper deviation verbatim; strict = non-strict by mixing with $\delta_\mu$; finiteness
  by a far atom; lower semicontinuity at **every** law, since escaping translations cost $+\infty$ by the
  tail bound. Not in the paper because (V1.1, V1.6) its reduction and its upper deviation are sketched
  in A22 §6.10, so it would be an extension needing a full written proof, and it is a different class;
  it is the first test case of `oq:profiled`.
- **A quantitative lower bound on $\mathcal K$ through [L17, Theorem 2]** (report, Remark 2): applying K1 to
  Lattimore's consistent algorithm on two-armed instances gives
  $\mathcal K(P,m(P)+\Delta)\ge(C(\kappa-1+\sigma^2(P)/\Delta^2))^{-1}\ge(2C)^{-1}\min\{\Delta^2/\sigma^2,1/\kappa\}$. Conditional on
  [L17, Theorem 2], whose proof was not read. Since revision round 1 (SC1.9) it is stated, with this
  derivation, in `oq:smallgap`, which keeps open only the small-gap equivalence and the upper half for
  $\Delta<\sigma/\sqrt\kappa$; it is not a node.
- **Martingale version of the confidence sequence** (report, Remark 3: only conditional moments needed,
  as in [AJK21, Remark 12]): not proved in the paper, left out.

## Defects of the independent check and what was done

| ID | Class | What was asked | What was done |
|---|---|---|---|
| V1.1 | G | Credit Agrawal's thesis (§6.10, Ch. 6) and AKJ21; do not claim the centred-moment theorem settles an open problem; say precisely what is new | Thesis fetched and read (parts in `literature/index.md`, note `A22.md`); AKJ21 read (Theorem 3.4 and the text around it). Credited in the Introduction, in Related work (paragraphs "Non-convex information functions", "Closest related work", "Gap with the literature", Table 1), after `lem:G` and `lem:repr`, and in Appendix H (rows "outer minimisation" and "fixing the outer parameter at its true value", the latter from App. 6.D.1, (6.55)). The centred-moment theorem is not in the paper: it is a test case of `oq:profiled` and is described above. What is claimed new is stated in "Gap with the literature": two-parameter profiling of a moment ratio, the escape analysis with the exact boundary value, the kurtosis theorem |
| V1.2 | L | Compare with [L17, Theorem 9] | Node `cite:L17-thm9` (weaker reading of its class); paragraph "Comparison with the bound of Lattimore" after `prop:kinfty`: the large-gap branch $\log\frac\kappa{\kappa-1}$ is improved to $\mathcal K_\infty(\kappa)<1/\kappa<\log\frac\kappa{\kappa-1}$, for every $\kappa>1$, exact in the limit (`cor:largegap`); Table `tab:kinfty` gives both |
| V1.3 | L | Remove the cost claims; the theorem assumes exact computation; computation to Open questions | No cost claim anywhere; paragraph "Computation" of Section 5 says that no certified procedure is given and that `thm:main` assumes the exact index; `oq:computation`; the numerics are called heuristic |
| V1.4 | P | Measurability wording | `lem:index`(i) and Appendix E: usc as a max over the compact $\Lambda$ of jointly usc functions, lsc as a sup over $\mathrm{int}\,\Lambda$ of continuous functions (equal by the segment argument) |
| V1.5 | P | $\infty-\infty$ conventions | `prop:dual`(iv) and `lem:alllaws` state the sup over $\mathrm{int}\,\Lambda$ and well-definedness when $\mathbb E\log(1+|Y|)<\infty$; `lem:weak` proves the integrability of the positive part |
| V1.6 | P | Theorem E in full or split | Left out (see above and V1.1) |
| V1.7 | P | Interpretive phrasing of the $\kappa-1$ term | "in the regime $\Delta_a/\sigma_a\to\infty$ … the exact form of the term $(\kappa-1)\Delta_a$" (Introduction, Section 6) |
| V1.8 | P | Dirac index remark | `lem:index`(iii) and the paragraph "Arms with a Dirac empirical law" (what the algorithm does: index $+\infty$ while $n\mathcal K_\infty\le g$, then $-\infty$ until the threshold grows); Bernoulli bullet of Section 9 |
| V1.9 | P | PA26 sentence | Paragraph "Comparison with KL$_{\inf}$-UCB and with the generic theorem" (Section 6) and "Closest related work"; the remark on PA26's App. A.2 is kept here only |
| V1.10 | P | Largest atom: "elementary; source not known" | After `lem:atom` and in Appendix H |

## Second independent check of the paper and what was done

A second independent check (2026-11-16, working notes outside the repository) read version 1 of
`paper.tex`, concentrating on the new proof of `lem:finite` and on the statements changed since the
report. Verdict: accept, no F, G or L defect. It checked numerically the construction of Step 5
(seven laws, including a maximiser at $\lambda^\star=0$ and at a vertex of $\Lambda$) and the dual formula
`eq:dual` against a direct primal search (nine cases, agreement to $3\cdot10^{-9}$). Its five
presentation points and what was done:

| ID | Class | What was asked | What was done |
|---|---|---|---|
| P1 | P | The remark after `lem:finite` said that the new proof "avoids a constraint qualification in infinite dimension", but the replaced Slater argument was finite-dimensional; Appendix H said "source not known" for the construction | Remark after `lem:finite`: the proof is the standard first-order (Karush–Kuhn–Tucker) argument for a concave maximisation over a convex set, the optimal law being read off from a maximiser and the multipliers of its active constraints; it does not invoke Slater's condition. Appendix H row "Direct construction …": credited to that standard argument, "as in empirical likelihood", instead of "source not known" |
| P2 | P | The conclusion of `lem:finite` holds for every maximiser | Statement: "for any maximiser $\lambda^\star$ of $\Phi$"; Step 1 of the proof: "Let $\lambda^\star$ be any maximiser" |
| P3 | P | Step 2 of `lem:finite`: $\mathcal K_G(R)=0$ follows from $R\in G_\kappa$, not from `lem:weak` | "So $R\in G_\kappa$, hence $\mathcal K_G(R)=\mathrm{KL}(R,R)=0=\Phi(0)=\Phi(\lambda^\star)$" (`lem:weak` is still used in Step 5) |
| P4 | P | $\mathcal K_\infty(\kappa)$ is the supremum of $\mathcal K$ only over laws with a finite fourth moment | Abstract: "its largest value over laws with a finite fourth moment"; Section 8, after `lem:escape`: "the supremum of $\mathcal K$ over laws with a finite fourth moment"; the same precision in the Conclusion |
| P5 | P | Proof of `prop:regularity`(ii): `lem:escape` gives (a) or (b) only along a subsequence | The limit $\mu\to\infty$ now passes first to a subsequence realising $\ell:=\liminf_n\mathcal K(P,\mu_n)$, as in (i), then to a further subsequence along which case (b) holds |

At the same time the citations were put in the author–year style of `docs/writing.md` §2a (natbib,
`plainnat`, `\citet`/`\citep` with loci; titles of cited nodes "From Lattimore (2017, Theorem 9)");
`refs.bib` unchanged (every entry has its authors and year). No statement changed, except the
slightly stronger "any maximiser" of P2.

## Referee reports of round 1 and what was done

Reports on head `42709c9` (2026-11-16): `referee-scope` (verdict major, SC1.1–SC1.12) and
`referee-proofs` (verdict accept, PF1.1–PF1.5). Revision of 2026-11-17 (version still 1).

| ID | Class | What was done |
|---|---|---|
| SC1.1 | G | BSH23 read and added (`bibliography.json`, `index.md`, note). Table 1: the centred row is now BSH23 Corollary 6 (MED, exact, under a known lower bound on the means). "Non-convex information functions": a paragraph on BSH23 §4.4.2/App. D.5. "Closest related work": five works, with why BSH23 does not give the result. "Gap with the literature" rewritten. Remarks after `lem:G` and `lem:repr`, Appendix H row, `oq:profiled` (now a precise question for KL-UCB with no lower bound on the means), "Closest known" above |
| SC1.2 | L | Novelty claim restricted (Gap with the literature, remark after `lem:G`, Appendix H): the inequality $\mathrm{kurt}\le\kappa$ as a linear constraint with a free scale inside $\mathcal K_{\inf}$. Empirical likelihood credited for profiling location and scale and for the dual and the multipliers, as "see also [O01, §1.1, §3.5, §3.14]": the texts of Owen (1988, 1990, 2001) and Qin–Lawless (1994) could not be read in this session (Project Euclid returned empty pages; OUP and the book are paywalled), so they are not cited as read |
| SC1.3 | L | Remark after `lem:alllaws` and Appendix H: the scheme is credited to the proof of [HT10, Theorem 8] (finite supports, then approximation); only the Fatou variant on an unbounded support is claimed as the paper's. "new in this form" removed. Shekhar–Agrawal (arXiv:2603.21027) not read, not cited |
| SC1.4 | L | Remark after `lem:mixbound` and Appendix H: the bound is [AKJ21, Lemma E.1 of arXiv:2008.07606], restated as [AJK21, Lemma 11]; AKJ21 credit Blum–Kalai and Hazan–Agarwal–Kale (named, not cited: not read) |
| SC1.5 | L | "Theorem 4" of CHK18 replaced by Theorem 5 (JMLR numbering, checked on the JMLR PDF), in Related work and Table 1 |
| SC1.6 | P | Disputed in part: `thm:main` stays in Section 6 (p. 11). Its statement needs $\mathcal K$, the algorithm and its threshold (Sections 3–5) and a compact copy earlier would repeat the main result (W14); the informal statement with its constant is on p. 2, and the introduction now points to `thm:main` and `cor:exact` at that statement. As P000 did |
| SC1.7 | P | Section 9: a paragraph "Why no simulation of the algorithm" (no certified computation of the index: the outer problem is non-convex, non-compact, approached at infinity; a simulation would test a heuristic; a first-order constant is a limit), and a "Reproduction" sentence naming the scripts, their tables, their run times |
| SC1.8 | P | Tables 1–4 use `\Kinf`, `\Kc`, `\Kinfty`, `\qk` (captions with a short plain optional argument) |
| SC1.9 | P | `oq:smallgap`: the lower half $(2C)^{-1}\min\{\Delta^2/\sigma^2,1/\kappa\}\le\mathcal K$, from `cite:L17-thm2` and `cite:LS-16.2` on the two-armed instance, is stated with its derivation; the upper half for $\Delta\ge\sigma/\sqrt\kappa$ follows from `prop:kinfty`; open: the small-gap equivalence and $\mathcal K\le C'\Delta^2/\sigma^2$ for $\Delta<\sigma/\sqrt\kappa$ |
| SC1.10 | P | Paragraph after `cor:confseq`: comparison with [Cat12, Corollary 4.3, Proposition 4.5] (fixed $n$ and level, width $\simeq\sqrt{2v\log(1/\epsilon)/n}$, condition on $n$; ours anytime, no closed-form width). L17 §2 (median of means) not compared: not read |
| SC1.11 | P | After `lem:atom` and in Appendix H: an instance of the maximal mass at a point under moment constraints (Chebyshev–Markov–Krein), named without a citation (not read) |
| SC1.12 | P | Renaming line before `cite:AJK21-cor2`: the alternative is $Q'$ |
| PF1.1 | P | `thm:deviation` added to the `\uses` of the proof of `thm:main`; the proof now says that the dependence of $C_a(\varepsilon)$ is read from the statement of `thm:deviation`(ii) |
| PF1.2 | P | `lem:decomp` and `lem:termB` stated "for every $\delta>0$" (with $B$, $C$ depending on $\delta$); `lem:termC` stated for the $(\delta,J,\eta)$ of `thm:deviation`(ii); the preamble of Appendix F and the proof of `thm:main` say which $\delta$ is used. Mathematical content unchanged |
| PF1.3 | P | New node `lem:mixkl` (the inequality `eq:mixkl`, with its proof), used in the `\uses` of the proofs of `lem:strict` and `lem:mixture` |
| PF1.4 | P | Introduction: "for a fixed standardised law" |
| PF1.5 | P | Proof of `thm:deviation`, Step 3: the normalisation of the $f_j$ and the single $\eta=\min_j\eta/(\sup f_j-\inf f_j)$ |

## Changes

None (version 1).
