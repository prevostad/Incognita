Not refereed: working notes of the authors of P000.

# P000: HY on an unknown imposed grid (a paper of the owner)

## 2026-11-14, submission (Claude Opus 5.5, for the owner)

**Provenance.** `paper.tex` is the owner's readable version of 4 November 2026 ("lower bound and
optimality of HY with the default parameters"), converted to the format of the library. The
statements and the proofs are unchanged. What changed is the form only:

- sections in the order of AGENTS.md 5.2: Main result (the former Corollary, now `thm:main`),
  Setting (its paragraphs became definition nodes `def:grid`, `def:ass-x`, `def:model`,
  `def:kinf`, `def:learner`, `def:M0`, `def:stacks`, then `def:hy` and `def:hy-vocab`), Closest
  known, Proofs (the former appendices), Sanity checks, Weak points, Open questions, Attribution
  (these five written for the submission), then the notation;
- blueprint: `\uses` generated from the references and from the hyperlinked symbols of each
  statement and proof, `\proves` for every proof placed away from its statement; the two classical
  tools of the lower bound became cited nodes (`cite:honda2010asymptotically-primal`,
  `cite:garivier2019explore-dataprocessing`);
- packages of the template only: the boxes Setting/Goal became plain paragraphs, the pseudo-code is
  written with `tabbing`, the two dependency maps (TikZ) became lists, the notation tables became
  paragraphs, natbib citations became `\cite`;
- the status lines and the Lean boxes of the author's version are removed (AGENTS.md 5.2: the
  library's audit alone prints them).

**Checks before this version.** The source was checked by independent AI agents: the working
notes behind each part (case x > 1 and case x = 1 by two different agents), then the readable
rewriting (verdict accept, no error, no important gap; its remarks were applied). The author
verified Theorems lower and upper and the main theorem in a private Lean 4 project
(`Bandits/Batch/PaperHY/`, no sorry, remainders existential), on LeanMachineLearning and Lean
4.35, not on this library's dependencies.

**Left for later.**

- Literature notes for the two cited nodes: `honda2010asymptotically` (Lemma 2 and Theorem 8:
  the primal formula of K_inf) and `garivier2019explore` (Lemma 1: data processing) are not in
  `literature/notes/` yet (the library's GMS19 note records inequality (6), not Lemma 1).
- Formalisation: the author's private Lean project is the natural guide for
  `formalize-statements` and `prove` (port to the library's dependencies). Ask the owner for it.
- Two clarifications the author asked for on the first (long) version of the lower bound may help
  the referees: in Lemma `lem:twobatches`, why the instances with rho+ and rho- are used instead of
  nu (the decision on batch l+1 is taken under Q, where the M rewards of a in batch l follow G;
  moving Q to P_nu would cost M KL(G, nu_a), which is not controlled); and that D_G bounds the
  log-likelihood ratios, not the rewards (the readable version already says the second).
- Item 3 of the roadmap's Appendix A (all rounds) is not in this paper.

## 2026-11-14, revision round 1 (role revise, Claude Opus 5.5)

Answer to the report of `referee-scope` on `c1d368dbcb35` (SC1.1–SC1.12). Branch rebased on
`origin/main` (5602eb3, the roadmap change that lifts the hold on F4); no conflict. Statements of the
theorems unchanged; the nodes changed are the two cited nodes (SC1.7, SC1.8) and the remark of
`def:kinf` (citation part only). Everything else is in non-node text (Main result, Closest known,
Attribution) and in the bibliography.

- **SC1.1 (G), fixed** (`sec:closest`). JTXHXG21 read in full (PMLR paper and supplement). Theorem 4:
  one-parameter exponential families, unique best arm, static grid, "no anytime algorithm can achieve
  the asymptotically optimal regret in (1) within c log log T batches", optimality meaning
  lim_T R_T/log T over all rounds. Its proof (Appendix C) is the one-batch change of measure (Lemma 7,
  divergence decomposition on the observations up to t_j; Bretagnolle–Huber on the event
  T_i(N_{n+1}) ≥ N_{n+1}/2; N_{n+1} = N_n^{x'} with x' = e^{1/(4c)}). It states no quantitative factor,
  and the mechanism cannot give more than log t_{j+1}/log t_j → x (our `lem:onebatch`). New bullet in
  "Why Theorem 1.1 does not follow": a qualitative special case of thm:lower(ii) in that class; why x²,
  𝒫/K_inf and thm:upper do not follow. BK18 read in full: the conjecture is unnumbered (Section 6,
  p. 11) and is about the restart doubling trick with an exponential sequence; Remark 8 gives the
  factor b²/(b−1) for that trick. JTXHXG21's paraphrase of the conjecture is broader than BK18's text,
  so the paper says "presented by its authors as a confirmation", not more.
- **SC1.2 (L), fixed** (Attribution, Related work): [H60] (abstract only: E_0(N) at a third point θ_0
  between θ_1 and θ_2), [L83, Theorem 3 and its proof], [GHRZ19, §3.2, Lemmas 4–5, App. B.4–B.5]
  credited; what is new is stated (two-sided consistency at batch ends, boundary tilt with atoms at 0
  and 1, tightness of the pulls in batch ℓ). L83 itself was not reopened (Project Euclid unreachable);
  its Theorem 3 was checked against Bartroff–Tartakovsky, arXiv:2403.18782, §2.5.2 (their Theorem 5).
- **SC1.3 (L), fixed**: [CMP17, §5, Algorithm 1] credited for paced targets (1+ω)c log t; LS17 "(to be
  checked)" (its algorithm section is not among the parts marked read). "Source not known" kept for
  the queue lemma and for planning from statistics frozen at t_ℓ towards the test two batches later.
- **SC1.4 (L), fixed, with a correction**: PRCS16 read (arXiv v3, the IMS reprint): the lower bound is
  **Theorem 4**, and the sentence "P_i^t is a product distribution of at most t_{J(t)−1} marginals" is
  in **Appendix A** (between Lemma A.1 and Proposition A.1). GHRZ19 read (arXiv v3): it has no product
  sentence; it has the laws P_i^t "of observations available at time t" and KL = 2Δ² E T_i(t) (§3.1),
  so it is credited with §3.1, not with "Lemmas 2–3" (Lemma 2 is a minimax bound, Lemma 3 a tree
  version of Le Cam's inequality). KCG16 Lemma 1 read: it is the **event** form at a stopping time, not
  the form with a [0,1]-valued Z; it is credited for the event form, GMS19 Lemma 1 for the Z form.
- **SC1.5 (L), fixed**: the Searches paragraph lists the sources read in this revision and reuses the
  referee's queries (which the report allows).
- **SC1.6 (L), fixed**: every key is now a key of `literature/bibliography.json`; new entries
  (unchecked) BK18, EKMM21, H60, H63, JGS13, JXXG21, KMS21, P26; `refs.bib` regenerated from the
  bibliography (same keys, same metadata); index.md updated with what was read this session (HT10,
  GMS19, KCG16, JTXHXG21, BK18, GHRZ19, PRCS16, KO21b, JGS13, H60). Citations of entries with no read
  part carry "(to be checked)": LR85, BK96, EKMM21, JXXG21, KMS21, H63, P26, LS17, [LS, §4.6].
  kalkanli2023asymptotic (IEEE TIT 2023) replaced by KO21b (arXiv:2110.00158, the ISIT 2021 version),
  which was read; the TIT metadata is recorded in index.md.
- **SC1.7 (L), fixed** (`cite:honda2010asymptotically-primal`, label kept). Note
  `literature/notes/HT10.md` written from the COLT PDF. The part "Lemma 2 and Theorem 8" is right for
  the COLT version: Theorem 8 is D_min = D'_min (the dual (5)), Lemma 2 is D_min = D_inf. HT15's
  "Theorem 5" is the numbering of the MED preprint arXiv:0905.2776v3, a different paper. The node now
  copies the two statements verbatim (HT10's notation); a remark after it translates to K_inf. **Two
  points found**: (i) Lemma 2 is printed "for all F ∈ A and µ < 0" (also "For µ < 0" at the start of
  §4.1), evidently a remnant of the [−1,0] convention of the preprint; its printed proof gives µ < 1
  through Theorems 7(i) and 8, and the remark says so. (ii) D'_min is a max over the closed interval
  [0, 1/(1−µ)], def:kinf a sup over [0, 1/(1−µ)); they agree by concavity (the value at the end is at
  most the limit from the left), also in the remark.
- **SC1.8 (L), partly disputed, node fixed** (`cite:garivier2019explore-dataprocessing`, label
  kept). In the PDF of arXiv:1602.07182v3, **Lemma 1 (§2.1, p. 8) is exactly the statement**
  KL(P_1,P_2) ≥ kl(E_1 Z, E_2 Z) for a [0,1]-valued Z (proved with Lemma 5 of Appendix A, data
  processing). So the part "Lemma 1" was right in the arXiv v3 numbering; the ar5iv rendering numbers
  it differently ("Lemma 2.3" per the report). Lemma 1 is added verbatim to `notes/GMS19.md`, with (8),
  Remark 2 and Lemma 5; the node now copies it verbatim, with the version, and a sentence on how it is
  applied (Γ the space of O).
- **SC1.9 (L), fixed** (`sec:main`, "Roadmap items"): items 1–2 of Appendix A quoted verbatim, then
  item by item what is proved; it says plainly that the x > 1 non-asymptotic bound with a constant
  margin ω, and item 3, are not proved (prop:dyA bounds the limsup over all rounds for x > 1 only).
- **SC1.10 (P), partly fixed**: `\DeclareRobustCommand` replaced by `\newcommand` (`\sy`, `\HY`,
  `\term`); `\renewcommand{\P}` replaced by `\newcommand{\PP}` (93 uses renamed); two `\protect` in
  `\paragraph` titles (a fragile `\hyperlink` in a moving argument). The 10pt / 2.3cm format is kept:
  with the template's 11pt / 2.5cm the paper has 73 pages and 17 overfull displays (up to 58pt), and
  the owner declared this deviation. Left to the owner (the referee's Ask-owner).
- **SC1.11 (P), fixed** (`sec:main`, "Constants"): the remainders are existential (ranks defined as
  "smallest rank such that", e.g. ℓ₅(ε), ℓ_W).
- **SC1.12 (P), fixed** (`sec:closest`): AJK21 (batches of max(1, ε̃N) rounds chosen by the algorithm,
  factor 1+ε̃; described from the parts marked read and from StochasticBandits KNOWN K17/K50) and KO21b
  (adversarial ends chosen at the previous end, §II.A; points to oq:random).

Dead ends: no PDF tool on this machine (no poppler, no pypdf); the HT10 text layer was read by
decompressing its content streams with zlib (a throwaway script, not committed). AJK21's PDF text
could not be extracted this way, and ar5iv has no rendering of it.

## 2026-11-14, revision round 2 (role revise, Claude Opus 5.5)

Answer to `referee-scope` round 2 (SC2.1–SC2.3, SC1.10) and `referee-proofs` round 1 (PF1.1–PF1.7)
on `7dea39589181`. Branch rebased on `origin/main` (4a982a5) without conflict. No theorem changed; the
statements changed are those of `cite:honda2010asymptotically-primal`, `lem:distinct`, `lem:countsA`
and `lem:goodA` (an explicit hypothesis or quantifier), plus eight new definition nodes that only
wrap existing paragraphs.

- **PF1.2 (L), fixed** by the referee's shorter route. `cite:honda2010asymptotically-primal` (label
  kept) now copies only [HT10, Theorem 8] verbatim (Lemma 2, printed for μ<0, is dropped). The remark
  after it gives K_inf(G,μ) = inf{KL(G,H): E_H ≥ μ} for μ ∈ [0,1) (concavity at the closed end, as
  before). `lem:onebatch`, Step 1, now derives the strict form: ε ∈ (0,1−m*) with
  ε/(1−m*−ε) ≤ ξ/2, μ' = m*+ε; lem:kinf(v) at level μ' with shift ε gives K_inf(ν_a,μ') ≤ d_a+ξ/2;
  Theorem 8 at μ' gives H with E_H ≥ μ' > m* and KL(ν_a,H) ≤ d_a+ξ. `lem:kinf` added to the proof's
  `\uses`. `def:kinf`: citation part only ("[HT10, Theorem 8] and the remark after it").
  `notes/HT10.md`, "Where Incognita uses it", updated.
- **PF1.1 (L), fixed** (`lem:distinct`(i), its proof, and Step 4 of the proof of `lem:decompC`):
  hypothesis N_a(t_1) ≥ 1 added to (i); the proof says the counts lie in [N_a(t_1), t_L]; decompC
  says the hypothesis holds for HY (def:hy-vocab, "every arm is observed"). The referee's
  counterexample (a first pulled in batch 2, g = 1_{0}) is excluded.
- **PF1.3 (P), fixed**: `lem:structA` added to the proofs' `\uses` of thrA, leaderA, countsA, goodA,
  decompA.
- **PF1.4 (P), fixed**: `lem:tilts` added to `lem:typ` (statement: D_G; proof: also `def:tilt`), and
  `def:Q` (PF1.5).
- **PF1.5 (P), fixed**: new definition nodes, text unchanged except the wrapper (anchors kept):
  `def:empkinf` (s:tilt, s:gridl), `def:Q` (s:Q), `def:backlog` (C_ℓ and Q_ℓ(t)), `def:water`
  (s:water, (W1)–(W2), the rank ℓ_W), `def:ranksA` (s:ranksA: ℓ_A, (R1)–(R3), u_ℓ, ℓ_1, (T1)–(T4)),
  `def:H` (s:H), `def:ranksC` (s:ranksC), `def:high` (t:high). `\uses` were added mechanically:
  every node whose statement or proof contains a macro hyperlinked to one of these anchors, or
  (W1)/(W2), (R·)/(T·), Q_ℓ(, C_ℓ, "-high"/"high batch" (script not committed); lem:levelC's own
  rank ℓ_L shares the macro of s:ranksC and was excluded by hand (no cycle with def:ranksC).
- **PF1.6 (P), fixed**: prop:fixedC's statement `\uses` gains lem:decompC (ℓ_5), lem:sumC (C_π),
  lem:amb (C_4). lem:countsA and lem:goodA: "for some ε' ∈ (0, ε̄]"; lem:countsA also states
  D_ε > 0, which the definition of ℓ_1 presupposes (its only use, in lem:goodA, has it).
- **PF1.7 (P), fixed**: def:grid "(ℓ ≥ 2)". lem:optW: a sentence after the statement says the last
  hypothesis t_{j−1} ≥ K U_{j−1} is unused in its proof and is there so that def:amb(a) provides it
  to lem:amb (Case (i), W_{ℓ−1} ≠ ∅); lem:amb's proof says so at that point. lem:fewC removed from
  the `\uses` of the proof of lem:optW (it is only compared with, not used). The hypothesis was kept
  in lem:optW rather than moved, so that def:amb(a) and its users are unchanged.
- **SC2.1 (L), fixed** (Attribution): [GHMS22, Appendix B.1] credited for the mixing step (read on
  ar5iv: ν'_α = (1−α)ν' + αδ_x, x > μ arbitrarily close to 1, α = ε/(ε+(x−μ)); "a variation on the
  proofs that can be found in Honda and Takemura 2015"), and the atom of HT10's boundary case. New
  here: both mixtures (δ_0 and δ_1). App. B.1 added to GHMS22's read list in index.md.
- **SC2.2 (L), fixed** (Attribution): [GK16, Appendix B.1, Lemma 15] (read on ar5iv: rule
  I_{k+1} ∈ argmax_i [P_i(k+1) − N_i(k)], max_i |N_i(n) − P_i(n)| ≤ K−1) and its use in Lemma 7
  credited as the closest form; what lem:service adds (fixed order, capped integer targets growing
  like log t, initial burst). "Source not known" kept only for the plan two batches ahead. GK16 added
  to bibliography.json (unchecked; metadata from the PMLR page), index.md and refs.bib.
- **SC2.3 (P), fixed**: stale "not read" removed from the JTXHXG21 row of index.md.
- **SC1.10 (P)**: unchanged (10pt, 2.3cm margins); the owner's decision, still asked.

Build: 66 pages, no error, no undefined reference, no duplicate label.

## 2026-11-15, presentation revision, version 2 (role revise, Claude Opus 5.5)

Rewrite of `paper.tex` for presentation under the writing rules of 2026-11-15 (one source, two builds;
the paper's skeleton; `DOSSIER.md`), without changing the mathematics. Sources: version 1 (accepted)
for every label, node, `\uses` and statement; the author's readable version of 4 November 2026 for
the frame, the prose, the pseudo-code, the TikZ graphs and the Setting/Goal boxes. Details and the
correspondence of every label: `DOSSIER.md`, sections 8 and 9.

- **How it was done.** The appendices (version 1, lines 712–3755) were kept as they are and transformed
  by a script (not committed): the 48 lines `\par\smallskip` that the conversion had written for
  `\begin{setgoal}`/`\end{setgoal}` became the boxes again (they pair exactly with the 48 setgoal lines
  of the readable version); the two lists "B ← A₁; A₂" became the author's TikZ graphs; "section"
  became "appendix" in the plans; the two cited nodes moved to Appendix A. The front (introduction to
  open questions), Appendix A, the attribution table and the notation tables were written by hand,
  from the readable version's text where the content is the same.
- **Self-check.** A script compared the two sources node by node (statement text normalised for
  whitespace, `\uses`, anchors and list-label syntax; proofs matched by `\proves`): 173 labels of
  version 1, all present except `sec:weak`; no node changed kind; 71 statements identical (`thm:main` included), 10
  changed in wording only (listed in DOSSIER.md, section 9); 8 proofs changed in form only (boxes,
  headings, "(to be checked)", the reference to `lem:primal`, the names (Q1), (Q2) in `lem:service`). One node added: `lem:primal` (the remark "How it
  is used" after the HT10 node, now a lemma, rule D5).
- **Dead ends.** A `\paragraph` right after `\begin{proof}` stops compiling with the new macros (the
  reader build prints nothing for `\uses`, so the heading starts inside the proof's list item:
  "Improper \prevdepth"); fixed by bold run-in headings. A `setgoal` box right after
  `\begin{proof}` sits next to "Proof." and overflows by 31pt; the box of `thm:upper` went before the
  proof, as in the readable version. `longtable` (used by the readable version for the notation) is
  not in the allowed packages: two `tabular`s. `\raggedright` in `p` columns without the `array`
  package: one `\raggedright` per cell and `\tabularnewline`.
- **The `\author` line** is unchanged (rule), so its footnote still names item F4 and the private Lean
  project; `sec:lean` is kept for its reference. Left to the owner (DOSSIER.md, section 7).
- **`thm:main` is on page 8**, not within the first 5 pages: the author's order (setting, algorithm,
  results) puts it after the algorithm, which its statement uses. The informal statement with the
  constant is on page 2.
- **Build.** Reader PDF 63 pages (main text pp. 1–12 with the references), blueprint PDF 66 pages; no
  error, no undefined reference or citation, no duplicate label; two overfull displays of about 7pt,
  already in version 1.
## 2026-11-16, version 2, revision round 1 (role revise, Claude Opus 5.5)

Answer to `referee-scope` (verdict major: SC1.1 L, SC1.2–SC1.9 P) and `referee-proofs` (accept: PF1.1–PF1.3 P)
on `4c717f69a164`. Branch rebased on `origin/main` (ec5e8ec) without conflict. Presentation only: no
statement, hypothesis or conclusion changed; no node added or removed. Details: DOSSIER.md, section 8,
"Revision of 2026-11-16".

- **SC1.1 (L), fixed**: the sequential lower bound is [BK96, Proposition 1] "as recalled by [HT10, (2)]",
  with [HT10, Theorem 8] for the dual formula, in Section 2, Table 1, the Examples ("Batches of size one")
  and the new paragraph "The classical sequential result" of Section 5. BK96 is a listed classic; only its
  abstract is recorded as read, and the attribution of (2) to it is HT10's own (§2).
- **SC1.2 (P), fixed**: natbib (round) + plainnat; every `\cite` converted by hand-checked rules
  (`\citet` where the authors were named in the text or in the table columns, `\citealp` inside
  existing parentheses, `\citep` elsewhere). Every refs.bib entry has authors and year.
- **SC1.3 (P), fixed**: Section 2 "Related work and context" (`sec:related`), the existing paragraphs moved,
  ending with "Closest related work" (label `sec:closest` there) and a new "Gap with the literature";
  "Our contributions."
- **SC1.4 (P), fixed** with the paragraph option: "Why no numerical experiments" (Section 7). Checked that the
  geometric grid t_l = 2^(l+1) has no activated batch: s_l = floor(t^(1+theta)) >= 2t = t_(l+1), since t^2 >= 2t
  for t >= 2 (theta = 1 when t < e^e) and t^(1+1/loglog t) >= e t when t >= e^e. A run there would only show
  batched IMED. Doubly exponential grid: ends below 10^9 are 4, 16, 256, 65536.
- **SC1.5 (P), fixed**: opening sentences for Setting, Results, Examples; "Conclusion and open questions" with
  the result and the limitations (pointer to the scope remark, Subsection 5.4); "Plan." capitalised in
  Appendices B, D, E, F.
- **SC1.6 (P), fixed**: water level Lambda_j -> \mathcal W_j (macro `\Lam`); activation round tau_l -> \bar t_l
  (macro `\tauA`); the local scaling factor tau (Lemma B.1(vi), proof of B.5, Lemma B.10, proofs of B.9 and
  B.10) -> \varpi (27 occurrences, all the raw `\tau` of the file). tau_n (Def. B.4) keeps its name.
- **SC1.7 (P), fixed** for Subsection 5.5 (what the green box certifies). The `\author` footnote is the
  owner's line and is unchanged; the referee's Ask-owner stands.
- **SC1.8 (P), fixed**: classical result recalled as a displayed statement in a run-in paragraph (not a new
  node: HT10.md does not hold (2) verbatim, and BK96 was not read beyond its abstract, so a cited node would
  need a reading first); Algorithm 1 typed with the link macros.
- **SC1.9 (P), not done**: Qiao–Wu (arXiv:2611.17500) recorded in DOSSIER.md section 5; citing it waits for
  the owner's answer to the referee's Ask-owner.
- **PF1.2 (P), fixed** (`def:kinf`: "for mu in [0,1)"). **PF1.3 (P), fixed** (`\Require` line). **PF1.1**: no
  change needed.

Build: reader and blueprint, no error, no undefined reference or citation, no duplicate label; two overfull
displays of about 7pt, as before.

## 2026-11-17, presentation revision, version 3: numerical experiments (role revise, Claude Opus 5.5)

At the owner's request (criterion W16): `experiments.py` simulates HY with its default parameters
($w_0=1$, $\beta=2$; $\omega_\ell=1$ and $\gamma_\ell=1/2$ at these horizons) and four published
algorithms (IMED and kl-UCB with frozen statistics and current counts, batched Thompson sampling of
KO21b, BaSE of GHRZ19 with $\gamma=1$ given the grid and $T$), on 10 pairs (instance, grid),
$T=2\cdot10^4$, 64 runs, 218 s in all. Outputs: `results/*.csv` (mean, 95% band, median at 160
log-spaced rounds and at every batch end), `results/log.txt`, figures `fig1`–`fig5` (PDF).

What was learned.

- Every ingredient of HY is computable; the only cost is $K_{\inf}$ at each end (bisection on the dual
  variable). Rewards with finitely many values keep it exact: the multinomial counts of a batch are
  drawn at its end (same law as round by round, since every policy only reads the rewards at the
  ends). A Beta law would need all samples at every end (too slow for the constant grid with 199
  ends); the second law is therefore $\mathrm{Bin}(10,p)/10$.
- Activation is rare at $T=2\cdot10^4$: only after $t_1=4$ on $t_\ell=4\ell^3$, after $16$ and $256$ on
  $2^{2^\ell}$ (paced from $6519$), after $200$ on the irregular grid. Elsewhere HY is IMED with frozen
  statistics, the weight $x_\ell^2$ and the pseudo-count, and its curves follow frozen IMED.
- On $2^{2^\ell}$ (instance A) the means are dominated by rare wrong leaders at $256$ (medians 53 IMED,
  134 HY; means 757 IMED, 476 HY, bands overlapping). On instance C (low variance), the weight
  $y_\ell=4$ makes HY explore more than needed at this horizon (38 versus 18 for IMED).
- BaSE with $\gamma=12$ (its theorem) would eliminate nothing before $T$ on these instances, hence
  $\gamma=1$ (its experiments). kl-UCB with $c=3$ is slow (bisection at every round: 20 s per pair).
- Dead end: a first version plotted Figure 3 with a logarithmic regret axis and all batch ends of the
  irregular grid; unreadable, replaced by a linear axis, a median row and the three ends around the
  long batches.

### Same day: BABA on its own grid (owner's follow-up)

- BABA (JTXHXG21, Algorithms 1-6), $\alpha=3$, $I_1=2000$ (their §6). Its grid is static and does
  not depend on $T$: ends 16, 74, 306, 538, 2000, 2020, 2166, 2750, 3334, then $(3334, I_2=171650]$.
  All algorithms run on it (A, B, C), BABA too: `fig6_baba_grid.pdf`.
- Readings of the pseudo-code (listed in DOSSIER §10): $\lceil\log^2I_r\rceil$, $I_0=0$, $c_0$ = label 1,
  loops stop at the target, $\mathrm{kl}_+$ in (7), clipping, test (8) at the end of Step III's batch.
- Since $c_0$ = label 1 would be the optimal arm in our instances, every run now relabels the arms by a
  uniform permutation; this also removed the advantage of the "smallest label" tie rules, and every
  number of the section was recomputed (292 s in all).
- At $T=2\cdot10^4$ the test (8) of epoch 2 has threshold $\approx0.117>\mathrm{kl}(0.4,0.5)$: Step IV
  explores uniformly (146 pulls per arm), the step 2750-3334 of BABA's curve; then it commits until
  $I_2$. Means at $T$, instance A: HY 56, IMED 57, KL-UCB 111, BABA 203, TS 203, BaSE 304.
- No batch of HY is activated on this grid before $T$ ($s_9=160660$).

## 2026-11-17, version 3, revision round 1 (role revise, Claude Opus 5.5)

Reports on head 196eae3: `referee-scope` major (SC1.1-SC1.10, one L, nine P), `referee-proofs`
accept (PF1.1, PF1.2, both P). Branch rebased on `origin/main` (no conflict). Presentation only.

- SC1.1 (L) fixed: `sec:experiments`, end of "Algorithms": PRCS16 (read) for "chooses its own grid",
  EKMM21 and KMS21 as "see also" (not read; not fetched this session).
- SC1.2 fixed: BaSE item. Rerun of BaSE alone with $\gamma=1$ and $\gamma=12$, same seeds
  (`.agents/scratch/base12.py`, not committed). Mean number of eliminated arms and mean regret at $T$:
  A-const 3 / 208 vs 2 / 1880; A-poly 3 / 260 vs 2 / 1981; A-geom 3 / 328 vs 2 / 2048; A-irr 2.98 / 910
  vs 0.98 / 1112; A-dexp2 0.09 / 347 vs 0 / 347; A-dexp15 1.47 / 168 vs 0 / 168; B-geom 0.95 / 476 vs
  0 / 496; B-dexp2 0 / 396 both; C-geom 3 / 314 vs 2 / 2048; C-dexp2 0 / 38 both; A-baba 2.56 / 304 vs
  0 / 500; B-baba 0.02 / 178 vs 0 / 157; C-baba 2.73 / 304 vs 0 / 500. The $\gamma=1$ numbers equal
  `results/log.txt`. The line of the section above, "BaSE with $\gamma=12$ would eliminate nothing
  before $T$", was wrong: it holds only on the doubly exponential grids and BABA's grid. The
  referee's arithmetic agrees: $\sqrt{12\log(8\cdot10^4)/4096}\approx0.18<0.2$.
- SC1.3 fixed: interpretation of Fig. 2. $\mathfrak R(t_\ell)/\log t_\ell$ from the CSVs: geometric, HY
  2.39, 3.29, 4.44, 5.30, 5.81, 6.04, 6.02, 6.16 for $\ell=6..13$, IMED 2.28 ... 5.35; polynomial, both in
  $[5.0,5.9]$ from $\ell=6$.
- SC1.4 fixed (`-{}-figures`). SC1.5: no change needed; AGENTS.md §5.3 (0c5a3ee, on `main` since this
  morning) allows exactly this sentence.
- SC1.6 fixed (contributions item 4), SC1.7 fixed (abstract about 210 words; ingredients sentence
  removed, the introduction has them).
- SC1.8 fixed: Figures 4-6 and their interpretations moved to a new last Appendix
  `sec:app-experiments`, with a two-sentence summary in `sec:experiments`; the main text now ends on
  p. 15 (was 17). Moving §7.2 instead was rejected: it holds the explicit instance and the special
  cases, the sanity checks of the theorems, which belong in the main text.
- SC1.9 fixed: `\Reg`, `\tl` in captions need `\protect` (first build failed: "Argument of
  \Hy@tempa has an extra }", the `\hyperlink` inside `\sy`). Legends: `shown()` maps "kl-UCB" to
  "KL-UCB" at drawing time, so the CSV keys and saved results stay as they are; figures redrawn
  with `--figures` (the PDFs are 30-67 kB).
- SC1.10 fixed: `lem:amb` Step 6, a `\why` on each line of the `align` (first version 38 pt too wide;
  shortened).
- PF1.1 fixed in the interpretation of Fig. 6 and in "Grids": batch 10 of BABA's grid is activated
  ($171650>s_9=160660$), only its paced phase is after $T$. The last line of the section "BABA on its
  own grid" above ("No batch of HY is activated on this grid") was wrong in the same way.
- PF1.2 fixed: interpretation of Fig. 1, the values of $y_\ell$ in the first batches.

## 2026-11-17, version 3, revision round 2 (role revise, Claude Opus 5.5)

Reports on head 4f6778a: `referee-scope` major (SC2.1 G, SC2.2 P), `referee-proofs` accept (PF2.1
P). Branch rebased on `origin/main` (a56b2e9, no conflict). Presentation only.

- SC2.1 (G, on prose, no node) fixed: `sec:experiments`, last sentence of "Algorithms". The referee
  is right; I checked arXiv:1505.00369v3: §2.2 "We employ a two-armed bandit framework", §3.3 "The
  generic etc policy uses a deterministic grid T that is fixed beforehand", Figure 1 "Generic
  explore-then-commit policy with grid T" (input: the grid), Proposition 1 "run with a given set of
  times". So PRCS16's ETC could be run on an imposed grid, given $T$, like BaSE; what excludes it
  is $K=2$. Round 1's sentence ("chooses its own grid") came from reading "the learner chooses the
  grid" (true of §4, the optimised grids) as a property of the policy itself.
- SC2.2 (P) fixed: `lem:decompA` Step (b), `\why` on the last line. First attempt as a third
  column: 399 pt, then 110 pt too wide (the second line of the `align` is long); put on its own row.
- PF2.1 (P) fixed: "about eight to ten times" (7.7 to 10.3).
