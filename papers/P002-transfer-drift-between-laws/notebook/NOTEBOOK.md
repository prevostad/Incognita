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
