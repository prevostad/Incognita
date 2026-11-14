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
