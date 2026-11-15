Not refereed: working notes of the authors of P002.

## 2026-11-14, write-paper (claude-opus-5-5, owner's interactive session)

**Origin.** Direction D8 of TransferBandits was explored by an agent in the owner's session
(research report, not in the repository), then written up here. Sources read for the paper: the
roadmap and KNOWN.md, the posted source of arXiv:2610.21582 (PMRM26: problem formulation, lower
bound, KL-UCB-Transfer, the lemma on the exponential moment of the source of the optimal arm),
arXiv:2509.19098v1 (PMM25: Section 3, Definition 2, Theorem 3, Corollary 4, Theorem 6),
arXiv:1210.1136v4 (CGMMS13: Sections 1-6, Theorem 2), arXiv:2405.02594v2 (CL24: Sections 1-4.2,
the bias bound (4)) and the abstract of arXiv:2602.20503 (KT26).

**What changed from the research report.**
- The lower bound is not claimed: PMM25, Theorem 3, already states it for an arbitrary
  pseudo-distance and deterministic sizes. KNOWN K1 does not say so (it was "not re-read"); this is
  for the owner to update.
- Pinsker's inequality is not used: the proofs use the compactness constant
  kappa_q(theta) = inf{KL(r,q) : TV(r,q) >= theta} > 0 (Lemma lem:types), so that no textbook
  result outside Mathlib is needed. The constants lose their explicit form (Pinsker would give
  kappa >= 2 theta^2).
- The KL projection (Lemma lem:projection) is proved without KKT: an explicit candidate (the tilt,
  plus an atom at x_max when the tilt saturates) and the inequality log u <= u - 1 give optimality
  and uniqueness at once.
- The Kolmogorov / Wasserstein ordering (Lemma lem:ipm-order) is proved by Abel summation on S,
  from the IPM definitions only (no Kantorovich-Rubinstein).
- The lower bound uses GMS19 (6) and (11), the cited nodes of the library, through an embedding of
  the source as forced pulls of K extra arms.
- Only weak duality is kept (Lemma lem:weak-duality), for the numerical certificates; strong
  duality was only sketched in the report.
- Part (i) of the theorem uses the lower semicontinuity of l -> K_S(nu_a, l) (not its continuity),
  which also covers mu* = x_max.

**Dead ends and limits (from the report).**
- Nonparametric P([0,1]): the method of types gives the (n+1)^|S| prefactor; for continuous laws
  KL(empirical, q) is infinite, and a dual statistic has a functional multiplier (bounded for TV,
  Lipschitz for W1) whose union bounds cost e^{O(s)}, which destroys the e^{-s theta kappa} gain.
- Without the margin eta on the optimal arm, E exp(n' KL(empirical source, source)) grows like
  n'^{(|S|-1)/2}: the proof gives nothing at d(nu_1, nu'_1) = L_1.
- Random source sizes: Lemma lem:source extends (sum over sizes), Lemma lem:sub-constant does not.

**Numerical experiments** (`calculs/`, Python 3 with numpy and scipy; each script runs in seconds
to minutes on a laptop; see `calculs/README.txt`). J is computed as a convex programme (SLSQP,
slack variables for absolute values), D by bisection; brackets are certified by a primal feasible
point (J < 1) and a dual point of the weak duality lemma (J >= 1). The mean pseudo-distance
reproduces (1 - c K'_0)_+ / K_0 exactly. Examples 1 (Bernoulli) and 4 of the report were computed
with the primal bisection only. Once, SLSQP failed on a near-degenerate law; the dual detected it,
and better starting points fixed it. Numbers are in double precision, without interval arithmetic.

**Independent check of the research report** (an agent that did not write it, 2026-11-14): verdict
major, no fatal defect. It redid every step of the lemmas and of the upper and lower bounds, compared
the margin argument with the published lemma, tested the structure results on random instances
(20,000 for the W1 no-gain claim, 7,761 with K'_0 > 0 for the TV/KS bound), and recomputed the
examples with an independent implementation (brackets of width 1e-5 matching). Its defects and
what the paper does with them:
- V1 (L), V6 (P): the strict TV gain needs K'_0 > 0 (counterexample otherwise: S = {0,1/2,1},
  nu = nu' = (1/4,1/2,1/4), L = 0.12). The paper states prop:tv with K'_0 > 0, and the abstract now
  says so.
- V2 (G): a strict gain for KS was claimed in the report without proof. The paper does not claim it
  (the verifier's proof sketch: L <= W1 <= (x_max - x_min) KS when K'_0 > 0, with equality only if
  the distribution functions differ by a constant on the interior; not written up).
- V3 (G): strong duality only sketched. The paper keeps weak duality only (lem:weak-duality), which
  is all the numerical certificates use.
- V4 (L): "recovers K2-K4" was overstated. The paper now says: first-order constants only, laws
  carried by S with 1 in S, deterministic sizes.
- V5 (P): run6.py leaves an uncertified bracket [3.0143, 3.3911] at c = 10 in Example 2; the value
  3.1692 is certified by run7.py (better dual starting points). Said in the paper.
- V11 (P): the lower bound is K1's Theorem 3 (closed constraint d <= L, deterministic sizes): the
  paper cites it and does not claim it.
- V13 (P): arXiv:2605.10289 (mean shift only, no lower bound) is now cited (LFCK26).
The verifier rated the interest about 2/5 and expects a scope referee to raise the finite support,
the restriction to integral probability metrics (D8 also names Hellinger and KL), and the standard
techniques.

## 2026-11-15, revise round 1 (claude-opus-5-5)

Reports: referee-scope (SC1.1-SC1.8) and referee-proofs (PF1.1-PF1.8) on head 0feaea1, both
`major`, no G defect. No rebase (the branch does not conflict with main; main only changed scripts).

Sources read for this round: arXiv:2610.21582v1 HTML (outline, §4.2, Lemma 17 in App. B.4, proved
in B.6); arXiv:2509.19098v1 HTML §5, §5.2, index (4); arXiv:1405.4758v1 HTML §4.1 (OSLB/CKL-UCB
index) and its abs page; PMLR v22 page of Shivaswamy-Joachims (abstract); arXiv abs page of
2605.10289 (names); arXiv:1811.12852 HTML §4.3 (credits the known-support index to BK96, "as in
Burnetas and Katehakis (1996)"); Crossref records of BK96, Csiszar-Korner (2nd ed.), Shaked-
Shanthikumar, Owen 1988. BK96 itself: ScienceDirect refused access (403); only the abstract, through
a search result.

- SC1.1 (L) fixed: Closest known, new paragraph "KL-UCB on a known finite support [BK96, CGMMS13]";
  Attribution row "Index". BK96 is cited with "(to be checked)": only its abstract was read.
- SC1.2 (L) fixed: PMM25 §5.2 (4) credited in Closest known (PMM25 paragraph) and Attribution;
  MCP14 added to literature/ and credited; new paragraph "Structured bandits [MCP14, CMP17]" on why
  forced source samples are not covered.
- SC1.3 (L) fixed: def:class remark cites PMRM26 §4.2; the remark after def:algo cites §5.2; the
  Attribution cites Lemma 17 and "proof of Theorem 2". The PMRM26 row of literature/index.md is
  corrected.
- SC1.4 (L) fixed: new paragraph "The drift on one optimal arm only: KNOWN K5" in Closest known
  (cites PMRM26 §7 "to be checked": only the section title was read); Roadmap items paragraph.
- SC1.5 (L) fixed: new paragraph "Historical data without drift [SJ12]"; SJ12 added to literature/;
  Attribution row.
- SC1.6 (P) fixed: prop:lower title and the remark after it ("a variant", same proof, PMM25 App. A,
  larger class); Closest known PMM25 paragraph.
- SC1.7 (P) fixed: Attribution rows for the method of types [CK11], lem:lr [SS07, Thm 1.C.1],
  lem:ipm-order (standard, reference to be checked), Berge (reference to be checked), the
  empirical-likelihood weights [O88]; all "(to be checked)", none read. CK11, SS07, O88 added to
  literature/ with metadata from Crossref (Crossref lists Shaked and Shanthikumar as editors).
- SC1.8 (P) fixed: LFCK26 given names from the arXiv page (bibliography.json, refs.bib, index.md).
- PF1.1 (L) fixed: the structure statements no longer assume "(nu,nu') in Theta" (ambiguous: which
  d?). prop:order (first claim), prop:criteria (a), the mean clause of (b), and prop:bernoulli now
  assume m(nu'_a) <= mu* + L_a; prop:w1 and prop:tv get it for free (their proofs say so). New
  remark after prop:order: the hypothesis cannot be dropped, since m(nu'_a) > mu* + L_a gives
  K'_0 = 0 and D^mean_a(c) < 1/K_0 for every c > 0 by prop:criteria(b) (mean gap: d(Q*, nu') =
  |mu* - m(nu')| > L). The referee's example (S = {0,1/2,1}, F = {1_{0}}, nu = (0.1,0.8,0.1),
  nu' = (0.1,0,0.9), L = 0.1, mu* = 0.6) is such a case. Changed nodes: prop:order, prop:criteria,
  prop:bernoulli (statements and proofs), proofs of prop:w1 and prop:tv, the text before the
  propositions and the intro of the proofs subsection, the sanity bullet "Mean gap".
- PF1.2 (P) fixed: remark after def:algo: equality with K8 for the one-sided condition; with the
  two-sided mean gap, equality when m(hat nu'_k) <= U^K8_k(t) + L_k (argument: at a maximiser of
  K8 with m(q) = U^K8, replace q' by the KL projection of hat nu' at level U^K8 - L, whose mean is
  max(U^K8 - L, m(hat nu')) <= U^K8 + L).
- PF1.3 (P) fixed: \uses of lem:lr (proof: lem:ipm-order), lem:delta (def:algo), lem:deviation
  (lem:ipm, lem:lsc, with the attainment of the min stated); lem:sub-reduction proves the
  existence of the min from the compactness of Gamma_a(mu* - eps) and lem:lsc(a), not lem:J(a).
- PF1.4 (P) fixed: hypotheses repeated in the statements of prop:order to prop:tv and
  lem:criterion-point; for the proof of thm:main, the notation (a, Delta_a, eta, admissible eps,
  theta, A_T, B_T, the hypotheses of thm:main) is a new node def:proof-notation, used by
  lem:decomposition, lem:optimal-arm, lem:sub-reduction, lem:sub-kl, lem:sub-constant and the proof
  of thm:main. The mathematics of these lemmas is unchanged.
- PF1.5 (P) fixed: paragraph "Constants": C_2 depends on eps through theta.
- PF1.6 (P) fixed: lem:ipm(b) proof, the particular case is the identity with (q,q',r,t) <-
  (r,q,q,1-t).
- PF1.7 (P) fixed: ex:no-drift, omega_TV = alpha_0 + min(beta_0, L - alpha_0)/2, both cases
  checked: (1 + gamma_0 + L)/2 >= 0.6 iff gamma_0 >= 0.09, else the sum is 1 and gamma_0 > 0.89.
  Values unchanged.
- PF1.8 (P) fixed: prop:lower Step 2, horizon T + sum_k N'_k(T) of the 2K-armed game.

Not done: the Ask-owner line of the scope report (D8 and the [0,1] case) is for the owner. KNOWN K1
and K8 ("Section 4") still cite PMRM26/PMM25 loosely; KNOWN.md is not this role's to edit.
