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

## 2026-11-15, presentation revision, version 2 (claude-opus-5-5, owner's interactive session)

Task: rewrite `paper.tex` for presentation under the writing rules v1 (one source, reader and
blueprint builds, `DOSSIER.md`), without changing any statement or proof in substance.

- **Structure.** Introduction (motivation, why a distance between laws, the supremum form of the
  constant and its meaning, the main result, the no-drift example as the hook with a figure,
  comparison table with the published results, contributions, techniques), Setting (with the
  algorithm in words and pseudo-code), Main results (theorem, lower bound, corollary, meaning of the
  constant, structure results, relation with published bounds), Proof overview (the proof of
  thm:main is there), Examples, Open questions, appendices (cited results, tools, $J_a$/$D_a$, upper
  bound, lower bound, structure, weak duality, sources, notation). Theorem 3.1 starts on page 5;
  the main text is 14 pages, the reader PDF 31.
- **Moved to DOSSIER.md:** roadmap items and conventions, KNOWN ids, Closest known with the
  derivation attempts, weak points, searches, reading admissions and "(to be checked)", the process
  sanity checks. DOSSIER.md also holds the statement correspondence v1 -> v2.
- **GMS19 (11).** The cited node now states the identity (11) as printed (bibliographer's finding);
  the inequality used by the lower bound is the new Lemma lem:kl-lower, proved from it.
- **Renamings** (list in DOSSIER.md, section 7): randomisation $V_t$ (not $W_t$: $W_1$ is the
  Wasserstein distance), $\mathcal A_T,\mathcal B_T$, $\mathcal K_0,\mathcal K'_0,\mathcal K_\varepsilon$,
  $H_\varrho$, $\tilde\nu$ in the cited node, Dirac mass $\mathbf 1_{\{x_{\max}\}}$ ($\delta_t$ kept for
  the exploration rate, as in PMRM26), and the local abbreviations $\nu,\nu',L$ written out.
- **Checks run.** A script compared the two sources node by node: same labels, same `\uses` (except
  prop:lower's proof: lem:kl-lower in place of cite:GMS19-11), statements printed side by side and
  read. A second script lists the `\ref`s inside proofs missing from their `\uses`: only the pointer
  of prop:w1's proof to prop:bernoulli's case analysis, as in version 1.
- **Figure.** `calculs/fig_dtv.py` (new) computes $c\mapsto D^{\rm TV}_a(c)$ for the no-drift example
  by primal bisection (d8.Dc) at 26 values of $c$, about a minute on the PC; output `calculs/fig_dtv.txt`.
  It checks the five certified values (agreement to $10^{-4}$) and that the values are nonincreasing
  and convex (they must be: each ratio of the supremum form is a nonincreasing convex function of $c$).
  PDFs under `papers/` are git-ignored, so the paper draws the curve with TikZ from these coordinates.
- **Reading.** The HTML of arXiv:2610.21582v1 (PMRM26) was read by a fetch agent for Theorems 2, 3, 5
  and Proposition 4 (recorded in literature/index.md), so that the paper cites PMRM26 Theorem 5 for
  misspecification instead of "Section 7, to be checked", and Theorem 3 for the second-order term
  $O((\log T)^{4/5}(\log\log T)^{1/5})$. Only a restatement of the statements was available (quotes
  capped); the numbering and hypotheses match KNOWN K2-K5.
- **Uncertain.** (1) The abstract and the introduction say "the source never hurts" and that $D_a$ is
  convex in $c$: both follow in one line from the supremum form (written in Section 3.3), but they are
  new sentences, not nodes. (2) The two-armed instance now says "every learner consistent for the
  mean-drift model" where version 1 said "every learner that uses the source only through a mean
  bound"; the new wording is the one Proposition prop:lower (with the mean gap) actually proves.
  (3) BK96 is now only a "see also" (abstract read); SS07, CK11 and O88 are cited as classics without
  a theorem number.

## 2026-11-16, presentation revision, version 2, second pass (claude-opus-5-5, owner's interactive session)

Goal: the owner's house style (docs/writing.md §2, §2a, W15; model arXiv:2610.21582; approved
example P005), without changing the mathematics. Same pull request, version still 2.

- **How.** The paper was rewritten section by section from the first-pass text, then a script
  replaced every plain use of a defined symbol, from "Problem formulation" on, by its link macro
  (`\sy`), skipping headings, comments, key arguments and a marked region (the notation
  correspondence of GMS19, where $U_t$, $N_{\psi,a}$, $\psi$ are the source's symbols). Symbols
  preceded by a letter (`nH_\varrho`, `sH_{...}`, `\max_kU_k`) escaped the pass and were fixed by
  hand. The scripts lived in the session's scratchpad (tooling, not experiments; not committed).
- **Checks.** A comparison script (macros of each version expanded, spaces, braces and display
  delimiters removed) against the previous head ac41a8a: same 39 nodes and 30 proofs, same labels,
  environments and `\uses`; the 21 statements that differ were read one by one (layout or wording
  only; table in DOSSIER.md §9). Every `\sy` link has an anchor and every anchor is used. No
  undefined reference, no duplicate label, no "Uses:" in the reader PDF, `certify.py check` clean.
- **Dead ends.** (1) `sed` in Git Bash dropped the backslash of `\I`/`\H` in replacements; use
  PowerShell string replacement. (2) Anchor names such as `s:K0`, `s:C1` are read by CI as KNOWN or
  roadmap ids; renamed `s:Kzero`, `s:Cone`, … (3) Switching to natbib needs the old `alpha` `.bbl`
  removed (latexmk -C), otherwise natbib stops with "Bibliography not compatible with author-year
  citations".
- **Owner's rule relayed during the session:** author-year citations (natbib, round, plainnat);
  `\citet` in running text, `\citep` in parentheses, cited-node titles "From \citet{GMS19}, …".
- **One wording corrected on the way.** The first draft of the opening of Section 6 attributed to
  [CGMMS13, Theorem 2] a bound "with the divergence computed on the known support"; that theorem is
  for empirical KL-UCB with $\mathcal K_{\inf}$ over finitely supported laws of $[0,1]$. The text now
  says so, with the equality $\mathcal K_{\inf}=\mathcal K_S$ when $1\in S$ of Section 6.1.
- **Uncertain / for the owner.** (1) Main text 19 pages, Theorem 6.1 on page 10 (rule: about 15
  pages, theorem within 5 when possible). (2) `natbib` is outside the package list of AGENTS.md §5.2
  (added at the owner's request; CI compiles it). (3) The classical lower bound of Section 4.1 cites
  [BK96], of which only the abstract was read (a classic cited for a standard fact).

## 2026-11-16, Claude Opus 5.5 (revise, repair of #36): rebase on main

Repair round (no referee report on this head): the branch conflicted with `main`.

- **Rebase.** `git rebase origin/main` (main at 006a8bb). One conflict, outside `papers/P002-…/`:
  the PMRM26 row of `literature/index.md`, extended on both sides (on main by the P003 sessions:
  §3–4 through a fetch tool, Appendix E and Lemma 22 from the LaTeX source; here by the reading of
  Theorems 2, 3, 5 and Proposition 4 for this version). Resolved by keeping main's row and appending
  this branch's reading and its line in the "who" column; the branch's "appendices not read" was
  dropped, since main now records a reading of Appendix E.
- **Rules changed on main meanwhile.** natbib and plainnat are now in the template and in the
  package list of AGENTS.md §5.2 (point (2) of "Uncertain / for the owner" above is settled; the
  paper already used them). New criterion W16 (numerical experiments, or a paragraph saying why
  not, P): Section 9 (Examples and special cases) gives certified values of the constant on explicit instances, not simulations
  of the algorithm, and has no paragraph on simulations. Left as is in this repair round (no change
  of `paper.tex`); a likely P point for the scope referee.
- **Checks after the rebase.** `paper.tex` unchanged by the rebase; `certify.py bib` and
  `certify.py check --base origin/main` clean; both builds compile (41 and 43 pages) with no error,
  no `undefined`, no `multiply defined`; no "Uses:" in the reader PDF.

## 2026-11-16, Claude Opus 5.5 (revise, repair of #36): failed build (directions.md)

Repair round (no referee report on this head): check "Build and check" failed at
`certify.py check --base origin/main` with "roadmaps/TransferBandits/directions.md: entries were
removed or reordered" and "C4 was edited". Cause: `main` added the entry C4 (from P003v1
oq:deterministic, ec5e8ec) after this branch was rebased; the branch never touches `directions.md`,
but its tree lacked C4, which the check reads as a removal.

- **Fix.** `git rebase origin/main` (main at ec5e8ec), no conflict. `paper.tex` unchanged.
- **Checks.** `certify.py bib` and `certify.py check --base origin/main` clean; both builds compile
  (reader 41 pages, blueprint 43) with no error, no `undefined`, no `multiply defined`; no "Uses:"
  and no "??" in the reader PDF.
- W16 (no simulations, no paragraph on why) still left for the scope referee, as in the previous
  repair.

## 2026-11-16, Claude Opus 5.5 (revise, revision round 1 of #36): scope referee, SC1.1–SC1.8

Presentation revision: no statement and no proof changed in substance.

- **Rebase.** `git rebase origin/main` (main at 9d368a2: P000 v2 and the bibliographer's #30). One
  conflict, outside the paper, in the PMM25 and PMRM26 rows of `literature/index.md`: kept main's
  status and notes columns (checked by the bibliographer), and for PMRM26 this branch's longer "parts
  read" and "who" columns (Theorems 2, 3, 5 and Proposition 4).
- **SC1.1 (G): fixed** (degenerate cases, now Appendix H, "Mean gap" item). Checked in the arXiv
  HTML v1 of PMRM26 (2026-11-16): Theorem 3(i) is for $\mu'_a<\mu_1-L_a$ and (ii) for
  $\mu'_a\ge\mu_1-L_a$; Proposition 4 says the bounds match "except possibly when
  $\mu'_a=\mu_1-L_a$"; $\mathcal K_{\inf}$ of §4.1 is an infimum over $\tilde\mu_k>\mu_1$. At the
  boundary, Theorem 2(i) applies (hypothesis $\le$) with
  $\mathcal K_{\inf}(\nu'_a,\mu'_a)=0$ (mixtures $(1-\epsilon)\nu'_a+\epsilon\delta_1$, as $\mu'_a<1$),
  so it gives $1/\mathcal K_{\inf}(\nu_a,\mu_1)$, the constant of Theorem 3(ii). The paper now cites
  Theorems 2(i) and 3(ii) for the boundary and says that Proposition 4 leaves it out. (The same
  argument seems to work for random sizes too, since $\mathcal K_{\inf}(\nu'_a,\mu'_a)=0$ kills the
  source term whatever $\mathbb E N'_a$; not claimed in the paper, which only needs deterministic
  sizes.)
- **SC1.5: fixed** (Section 2 and Section 6.1: "except possibly at the boundary").
- **SC1.4: fixed** (introduction: $\mathcal K_0,\mathcal K'_0$ in words; the superscript of $D^d_a$).
- **SC1.6: fixed.** Ratio $R(q,q')\to\Upsilon_c(q,q')$ (not $\rho_c$: $\rho$ is a generic law in
  $\mathcal K_S(\rho,\ell)$ and Lemma lem:projection); simplex $\Delta_S\to\mathcal P_S$. Two plain
  $R$ for the ratio were left in lem:D and in Step 6 of its proof; now macros.
- **SC1.7: fixed** ("In short", first bullet). **SC1.8: fixed** (proof of lem:optimal-arm).
- **SC1.2 (W16): fixed** by a simulation (Section 9.3, scripts `calculs/sim.py`, `run_sim.py`,
  `test_sim.py`, output `calculs/sim.txt`).
  - Dead end: SLSQP on the whole index programme (maximise $m(q)$ under the budget) stops short of
    the maximum on random inputs (budget at the returned point several units below $\delta$), and
    fails outright on some feasible cases; the logarithms near the boundary of the simplex make it
    ill-conditioned.
  - What works: bisection on the mean $\mu$ of $q$, the smallest budget at mean exactly $\mu$ being
    convex in $\mu$; on $\{0,\frac12,1\}$ the laws of mean $\mu$ form a segment (grid refined three
    times); for TV, the KL projection of $\hat\nu'$ on the TV ball around $q$ in closed form from KKT:
    $q'=\min(\max(q,s_-\hat\nu'),s_+\hat\nu')$ on $\mathrm{supp}\,\hat\nu'$, mass outside the support
    removed first, $s_\pm$ from two piecewise-linear equations. For KL-UCB-Transfer, the source term
    is $N'\mathcal K_S(\hat\nu',\mu-L)$ at mean exactly $\mu$: a check that used the one-sided
    $\mathcal K_S(\hat\nu,\mu)$ for the target term was wrong below $m(\hat\nu)$ (the index can be below
    the empirical mean when the source pulls it down), not the script.
  - Checks (`test_sim.py`): closed-form TV projection never above a grid minimum over the TV ball
    (200 cases, gap at most $7.5\cdot10^{-3}$, the grid's resolution); indices against `d8.py`
    (SLSQP with several starts for TV, dual $\mathcal K_S$ otherwise): relative error of the budget at
    the index at most $1.7\cdot10^{-5}$, and the budget exceeds $\delta$ at index $+10^{-3}$ (60 random
    inputs per learner).
  - Results ($T=10^4$, 40 runs, `run_sim.py`, about 62 minutes on 4 cores; per run about 35 s
    for KL-UCB, 45 s for KL-UCB-Transfer, 125 s for TV): mean $N_2(T)$ ± s.e. — KL-UCB
    $56.4\pm2.1$ (first order $55.5$); KL-UCB-Transfer $56.7\pm2.6$ ($c=5$) and $59.2\pm2.4$
    ($c=25$) (first order $55.5$ for both); KL-UCB-TV-Transfer $37.4\pm2.2$ ($c=5$, first order
    $42.0$) and $3.2\pm0.7$ ($c=25$, first order $0$; 23 runs of 40 pull arm 2 only at the
    initialisation, the largest value is 24). The TV learner at $c=5$ is below its first-order value
    and the ratio of means ($0.66$) is not the ratio of constants ($0.76$): second-order effects at
    $\log T\approx9$; the paper says that the table illustrates and does not measure the constants.
- **SC1.3: partly done.** Main text shortened by moves to the appendices (degenerate cases, two
  examples, precision, the class of PMRM26, Sections 8.3–8.4 merged); Theorem 6.1 on page 10, main
  text pages 1–19 including the new Section 9.3. Not reduced to about 15: that would move main
  statements or the proof overview out (DOSSIER §10, "Length").
- Checks: both builds, no error, no undefined, no multiply defined (reader 43 pages, blueprint 44);
  no "??" and no "Uses:" in the reader text; `certify.py check --base origin/main` clean.
