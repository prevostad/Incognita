Not refereed: working notes of the authors of P008-transfer-lower-bound.

## 2026-11-17, write-paper, claude-opus-5-5

### Choice of the item

Items of TransferBandits (`.agents/items.md`): F0 covered by P003, F1 open (first open item in the
order F0, F1, ...). F1 asks for the lower bound and the upper bound of KL-UCB-Transfer of
arXiv:2610.21582 (PMRM26), with the reduction from two-sided to one-sided drift, "starting with the
elementary lemmas". One session cannot do both bounds well: the upper bound (Theorem 3 of PMRM26,
second-order terms $(\ln T)^{4/5}(\ln\ln T)^{1/5}$, Appendix B-D of the source) is a paper by itself.
This paper takes the **lower-bound part of F1** (Theorem 2 of PMRM26, its Appendix E: Lemmas 22-24)
and the reduction from two-sided to one-sided drift for the lower bound. The upper bound part of F1
is left for a next paper.

### What the library gives

- P003 (setting, accepted, v1): size rules, source data, transfer learners, law of the game, drift
  sets ($\mathcal P_L$ closed two-sided, the two-sided strict condition, $\mathrm{Drift}_L$), the
  class $\mathcal C_L$ (Definition 3.9), the divergence decomposition (Theorem 4.1) and the
  fundamental inequality with a source (Corollary 4.2), prior bandit games (Definition 5.1) and that
  their counts are size rules bounded by $T'$ (Lemma 5.3(b)). Lemma 22 of PMRM26 is replaced by
  Corollary 4.2 of P003.
- P006 (BatchedBandits setting, accepted, v1): Proposition 4.2, values of $\mathcal K_{\inf}$ on laws
  on $[0,1]$: $=\infty$ for $\mu\ge1$, $=0$ for $\mu<m(P)$, and
  $2(\mu-p)^2\le\mathcal K_{\inf}(P,\mu)\le\log\frac{1-p}{1-\mu}$ for $p\le\mu<1$. Used for
  finiteness and positivity, and for $\mathcal K_{\inf}(P,m(P))=0$ (the boundary case).

### Reading of the source proof (Appendix E of PMRM26, from the PDF text layer)

- The source defines $G_a$: alternatives changing arm $a$ only, $\tilde\mu_a>\mu_1$, $|\tilde\mu_a-\tilde\mu'_a|\le L_a$.
- Lemma 22 (divergence decomposition), Lemma 23 (a mixture $(1-t)\lambda^{(n)}+t\nu$ to bring the
  mean of a near-optimal alternative down into a window $(\mu,\mu+\varepsilon_n)$; convexity of KL),
  Lemma 24 (data processing, Maillard 2019, Lemma 3.3).
- Case 1 ($\mu'_a>\mu_1-L_a$): $\tilde\nu'_a:=\nu'_a$, $\tilde\mu_a\in(\mu_1,\mu'_a+L_a)$.
- Case 2 ($\mu'_a\le\mu_1-L_a$, $C:=\limsup\mathbb E N'_a/\ln T<\infty$): bound with
  $(1-C\,\mathrm{KL}(\nu'_a,\tilde\nu'_a))_+$, then sequences from Lemma 23, then "continuity of
  $\mathcal K_{\inf}$ in its second argument (Honda and Takemura 2015)" to let $\varepsilon_n\to0$ in
  $\mathcal K_{\inf}(\nu'_a,\mu_1+\varepsilon_n-L_a)$. Last line uses $(1-CK)_+=\liminf(1-x_TK)_+$.

### Observations (what this paper changes)

1. **No continuity of $\mathcal K_{\inf}$ needed.** Choose the source alternative $Q'$ first (window
   lemma at the level $\mu^\star-L_a$, mean in $(\mu^\star-L_a,\mu^\star)$), then the target
   alternative $Q$ with mean in $(\mu^\star,m(Q')+L_a)$. Both divergences are then within
   $\varepsilon$ of $\mathcal K_{\inf}(\nu_a,\mu^\star)$ and $\mathcal K_{\inf}(\nu'_a,\mu^\star-L_a)$
   directly. This removes the appeal to Honda-Takemura continuity (which, for the strict-inequality
   $\mathcal K_{\inf}$, is right-continuity, automatic, but the source's chain needed it at
   $\mu_1-L_a+\varepsilon_n$ from the right: fine, but avoidable).
2. **The hypothesis $\limsup\mathbb E N'_a/\ln T<\infty$ is redundant when $\mu'_a<\mu^\star-L_a$.**
   If $c:=\liminf_T(1-K'x_T)_+>0$ with $K'>0$, then $x_T\le 1/K'$ for all large $T$; if $c=0$ the
   bound is trivial. It is **not** redundant at the boundary $\mu'_a=\mu^\star-L_a$: there $K'=0$, the
   source term $\mathbb E[N'_a]\mathrm{KL}(\nu'_a,Q')$ with $\mathrm{KL}\le\varepsilon$ can be large
   when $x_T\to\infty$, and the fixed alternative cannot be tuned with $T$ (consistency is not
   uniform over alternatives). This is exactly direction D2 (boundary, $\mathbb E N'_a/\log T\to\infty$):
   open question `oq:boundary`.
3. **Arm 1 unique optimal not needed**: only $\mu_a<\mu^\star$; the alternative makes $a$ the unique
   optimal arm.
4. **Four drift sets.** The alternative changes arm $a$ only and its two constraints are
   $m(Q)-m(Q')<L_a$ (strict, from the window choice) and $m(Q')-m(Q)<L_a$ (strict: case 1 from
   $\mu'_a-\mu_a\le L_a$ and $m(Q)>\mu^\star>\mu_a$; case 2 from $m(Q')<\mu^\star<m(Q)$). So the
   alternative is in each of the four sets (closed/strict, two-sided/one-sided) as soon as the
   original pair is. Lower bound identical for the four classes: this is the reduction from
   two-sided to one-sided drift for the lower bound (the constant depends only on $\mu'_a+L_a$).
5. **Size rules**: P003 Corollary 4.2 holds for every size rule with finite expected sizes under
   $\nu'$; the source's restriction to bandit-game priors is only used through Lemma 22.

### Dead ends / things not pursued

- Trying to state the bound with $\mathbb E[(1-K'N'_a/\ln T)_+]$ (Jensen gap, D1). The change of
  measure sees only $\mathbb E N'_a$. **Idea for a D1 paper (not in P008):** for a size rule whose
  sizes depend on the randomisation $U'$ only through ... more precisely, conditioning on $U'=u$:
  the section $N'(u,\cdot)$ is again a size rule (sections of $\mathcal G_n$-sets are measurable for
  the box $\sigma$-algebra), the online game depends on $(U',X')$ only through $D$, so
  $\mathbb E N_a(T)=\int\mathbb E_{N'(u,\cdot)}N_a(T)\,du$; Fatou then gives
  $\liminf\mathbb E N_a/\ln T\ge\int\liminf_T(1-K'\mathbb E[N'_a\mid U'=u]/\ln T)_+du/K$ for
  $\pi\in\mathcal C_L$ (consistency for each section strategy, pointwise in $u$). For the example of
  K7(a) ($N'_a=T$ w.p. $\varepsilon$ through $U'$) this gives $(1-\varepsilon)/K$. Fluctuations that
  come from the source values are not handled: that is the real D1 question. Not written in P008
  (out of F1; and the hypotheses (boundary, finiteness for each $u$) need care).
- Uniform-in-$T$ alternatives at the boundary: needs a uniform consistency (e.g. $\mathbb E N_k\le
  C_\nu T^\alpha$ with $C$ locally bounded in the instance), not given by $\mathcal C_L$.

### Plan of the paper

- Section 3: setting recalled from P003 (definitions restated as nodes with a pointer), $\mathcal K_{\inf}$,
  the four drift sets, classes $\mathcal C(\mathcal S)$.
- Section 4: Proposition (non-asymptotic change of measure for one alternative), Theorem (main),
  Corollary (Theorem 2 of PMRM26), Corollary (two-sided vs one-sided: same constant).
- Appendix: cited nodes (P003 Cor 4.2, P003 Lemma 5.3, P006 Prop 4.2, GMS19 (11) proved as a lemma
  instead), proofs: window lemma, alternative lemma, kl lemma, rate lemma, the theorem.

### Later in the session

- The "redundancy of the limsup hypothesis" (observation 2 above) is **cosmetic**:
  $\liminf_T(1-K'x_T)_+=(1-K'\limsup_Tx_T)_+$, so when the hypothesis fails and $K'>0$ the
  conclusion is $0$. The paper says so (paragraph Constants) and does not count it as a difference
  with the source.
- The proof of the theorem was over a page: split into `lem:constants` and `lem:one-horizon`.
- Added `cor:concentration` (lower-bound half of PMRM26 Proposition 4) with `lem:positive-part`
  ($(a_+-b_+)\le(a-b)_+$, the Lipschitz bound of PMRM26 Appendix D), the elementary lemma that F1
  names. The matching itself needs Theorem 3 of PMRM26 (upper bound), not proved here.
- Checked the node numbers of P003 (Definitions 3.1-3.9, Theorem 4.1, Corollary 4.2, Definition
  5.1, Lemma 5.3, Propositions 5.7-5.9) and P006 (Definition 3.2, Proposition 4.2) from their
  compiled `.aux` files.

### Numerical part

`constants.py` computes, for Bernoulli instances, $\mathcal K_{\inf}=\mathrm{kl}$ and the constant
$(1-cK')_+/K$ for deterministic sizes $N'_a=\lceil c\ln T\rceil$, and checks the alternative of
Lemma `lem:alternative` numerically (means in the right windows). No simulation: a lower bound for a
class of learners cannot be simulated.

## 2026-11-17, revise (round 1), claude-opus-5-5

Rebased on `origin/main` (no conflict). Since this morning `main` makes W16 an R criterion (a
figure comparing the bound with at least two published algorithms, even for a lower bound), so
the optional SC1.10 is done in full.

### Defects of referee-scope (SC1.*)

- **SC1.1** (R) fixed: abstract and introduction now state the exception at the boundary
  ($\mu'_a=\mu^\star-L_a$ with $\mathbb E N'_a/\ln T$ unbounded); "When $\mu'_a>\mu^\star-L_a$, or
  $\mu'_a=\mu^\star-L_a$ with $\mathbb E[N'_a]=O(\ln T)$, ...". No node changed.
- **SC1.2** (R) fixed: CL24 read (§4 Algorithm 1, Theorems 2–3, Definitions 1–3; App. D.2.1), note
  `literature/notes/CL24.md` created, index updated. Table 1 row and a bullet of Closest related work;
  DOSSIER Closest known. Check of the Gaussian translation: (50) of CL24 with online KL
  $(1+\epsilon)^2\Delta^2/2$ and offline KL $\max\{(1+\epsilon)\Delta-\omega,0\}^2/2$, divided by the
  online KL, gives $((1-p)\ln T-T_S\mathcal K'_{a,\epsilon})/((1+\epsilon)^2\mathcal K_a)$ plus a constant,
  with $\mathcal K'_{a,\epsilon}=(\mu_a+(1+\epsilon)\Delta-V-\mu'_a)_+^2/2$. YTC25 (BAI analogue) cited.
- **SC1.3** (L) fixed: the continuity of $\mathcal K_{\inf}$ in its level is HT10 Lemma 2 +
  Theorems 7(i), 8 (Lemma 2 is printed for $\mu<0$, a remnant of the authors' $[-1,0]$ convention, see
  the note). Abstract, contributions (the 4th item removed, replaced by the simulations), Gap
  paragraph, overview Step 2, remark after `lem:alternative`, App. E, DOSSIER: now "a simplification
  that makes the proof self-contained".
- **SC1.4** (P) fixed: `thm:main` on page 5. Moves without change of content: `lem:classes` to the
  start of `sec:reduction`, `def:prior-game` just before `cor:source`, `prop:fixed` after the
  discussion of the theorem, Table 1 after the Constants paragraph (a float); two remarks of
  Section 3 shortened. Numbers: the theorem is now Theorem 4.1.
- **SC1.5** (P) fixed: "Step 5" -> "Step 3" in App. E and DOSSIER weak point 3.
- **SC1.6** (P) fixed: the sentence on the notebook removed; the new section has one sentence naming
  `notebook/simulate.py`, which AGENTS.md §5.3 allows since today.
- **SC1.7** (P) fixed: Table 1 uses $x_a(T)$, $\mu^\star$ (with "$\mu_1=\mu^\star$, unique optimal arm" in
  the PMRM26 row); the constants are $\mathcal K_a$, $\mathcal K'_a$ (macros `\Ka`, `\Kp`).
- **SC1.8** (P) fixed: (a) GMS19 (10)–(11), and GMS20 (10), §7 (folklore; our lemma is their (10) at
  $(1-p,1-q)$); (b) KCG16 Lemma 1 for the event form; (c) UCB credited to ACF02 in the cited node, LML
  sentence removed, a remark that $c_0=1$ is UCB1 up to $\log t$ vs $\log(t-1)$; (d) Constants
  paragraph and App. E: Pinsker + data processing as in GHMS22 (7), mixing with a Dirac mass GHMS22
  App. B.1, history of Pinsker in Rio23.
- **SC1.9** (P) fixed: HZT26 read (setting, Definitions 1–3, Lemma 11, Theorem 12), note created,
  "see also" sentence in Related work (counts chosen by the learner itself, same laws, no drift).
- **SC1.10** (P, and W16 now R) fixed: `notebook/simulate.py` (see below).

### Defects of referee-proofs (PF1.*)

- **PF1.1** fixed: `\proves{...}` on the 10 detached proofs, `\uses{}` on the proof of
  `lem:positive-part`.
- **PF1.2** fixed: the sets of pairs are now $\mathcal I$ (def:class, lem:classes, thm:main,
  lem:alternative, lem:rate and their proofs, sec:reduction, notation table); $\mathcal S$ is only the
  space of source data, as in P003 (which uses $\mathcal S$ for it).
- **PF1.3** fixed: product $\sigma$-algebra on $\Omega'$, sum $\sigma$-algebra on $\mathcal S$
  (def:size-rule), as in P003 Definitions 3.3 and 3.5.
- **PF1.4** fixed: $\mathbb E_{\sigma,\nu}$ defined in def:game; lem:classes and the cited
  prop:witness now write consistency on $\mathcal P^K$ with it.
- **PF1.5** fixed: $T_0:=\max(T_0',2)$ in Step 2 of the proof of `lem:one-horizon`.

No statement changed (all edits are of presentation, credits, metadata, or the renaming of a symbol).

### Simulations

- Algorithms from their papers: UCB1 (ACF02 Figure 1), kl-UCB (CGMMS13 Algorithm 1 with $d_{BER}$ and
  $f(t)=\ln t+3\ln\ln t$, their Corollary 1), KL-UCB-Transfer (PMRM26 Algorithm 1, $\delta_t=\ln t+\ln\ln t$,
  read in the PDF §5.2 today), MIN-UCB (CL24 Algorithm 1 with $V=L$, $\delta_t=1/(2Kt^2)$, Theorem 2).
  On Bernoulli data the empirical laws are Bernoulli, so $\mathcal K_{\inf}=\mathrm{kl}$ exactly (P006
  Prop. 4.2(iv)); indices by bisection, 40 steps.
- First timing: KL-UCB-Transfer, $T=10^4$, 100 runs vectorised: 18 s.
- Dead end avoided: a single run up to $T_{\max}$ does not give the curve in $T$, since the source size
  $\lfloor c\ln T\rfloor$ depends on the horizon; every horizon is a separate experiment.
- Campaign (`python3 simulate.py`, 4 learners x c in {0,5,10,25} x T in {1e2,...,1e5} x 100 runs):
  about 7 minutes on 4 cores; output `simulate.txt` (summary, then raw $N_2(T)$ per run),
  `fig_counts.pdf` (log-log; MIN-UCB dominates a linear axis). At $T=10^5$, $\mathbb E N_2/\ln T$:
  UCB1 about 44, kl-UCB about 17.3 (no dependence on $c$); KL-UCB-Transfer 13.2, 8.9, 7.2, 1.2
  against the bound 11.47, 8.77, 6.06, 0; MIN-UCB 110–124. KL-UCB-Transfer is below the asymptotic
  bound at moderate $T$ for $c=5,10$ (no contradiction: liminf statement). MIN-UCB is very
  conservative with the parameters of its Theorem 2 ($\log(4Kt^3)$, 1-sub-Gaussian constant).
- Not done: Thompson sampling or IMED as further baselines (not needed: four published algorithms).

## 2026-11-17, revise (round 2), claude-opus-5-5

Rebased on `origin/main` (no conflict). Referee-proofs: accept (P defects only); referee-scope:
major (one R, three P). No statement changed in substance; no G or L defect.

### Defects of referee-scope (SC2.*)

- **SC2.1** (R) fixed: every chain of the appendix proofs now has its justification on its line,
  one step per line. Proof of `thm:main`: Step 2 (the bound on $R_T$, then its limit), Step 3 (the
  chain on $R_T$ split into five lines: definition, $\kappa'\le\mathcal K'_a+\varepsilon$, expanding
  $(1-p_T)(1-\alpha)$, $x_a(T)<1/\mathcal K'_a$, positivity of $1-\mathcal K'_ax_a(T)$; then the
  $\liminf$ in two lines). Proof of `lem:one-horizon`, Step 3: Proposition `prop:fixed` named on
  its line, the move of the (finite) source term and the identity $=R_T\ln T$ as an `align`, and the
  running-text chain $y\ge(R_T)_+/\kappa\ge(R_T)_+/(\mathcal K_a+\varepsilon)\ge R_T/(\mathcal K_a+\varepsilon)$
  as an `align` with its reasons. Proof of `lem:window`, Step 3: the chain
  $\mathrm{KL}(P,Q)\le t\int\ln f\,dP=t\,\mathrm{KL}(P,Q_0)\le\mathrm{KL}(P,Q_0)\le\mathcal K_{\inf}+\varepsilon$
  as an `align`. Proof of `lem:kl`: reasons added on the two lines. No step changed.
- **SC2.2** (P) fixed: the interpretation of Figure 1 re-read against `simulate.txt`, horizon by
  horizon. Facts used (mean/ln T): UCB1 at $T=10^2$ is 6.54, 5.97, 6.37, 6.35 for $c=0,5,10,25$
  (below 11.47), at $3\cdot10^2$ 10.94 for $c=0$ (below) and 11.7 otherwise, from $10^3$ above 18;
  kl-UCB below 11.47 up to $T=10^3$ (11.25 at $c=0$), above from $3\cdot10^3$ (12.5–13.2);
  KL-UCB-Transfer below its bound up to $10^4$ for $c=0$ (10.60 < 11.47) and $c=5$ (8.11 < 8.77),
  above at $3\cdot10^4$ (12.99, 9.00), and for $c=10$ below up to $3\cdot10^4$ (5.11 < 6.06), above at
  $10^5$ (7.24). The referee's suggested sentence "all four learners are below the bound at
  $T\le10^3$" is not exact (UCB1 is at 18.4 at $10^3$, and at $T=10^2$, $c=10$, UCB1 is 6.37 > 6.06),
  so the text says "for $c\in\{0,5\}$ all four learners are below it at $T=10^2$" and gives the
  horizons above. The legend now says kl-UCB (`NAMES` in `simulate.py`; figure redrawn with
  `python3 simulate.py --plot` from the committed `simulate.txt`, numbers unchanged).
- **SC2.3** (P) fixed: PMRM26 §5.1–§5.2 (KL-UCB, the KL-UCB-Transfer index, $\delta_t$, Algorithm 1),
  §6 (Theorem 3 hypotheses) and §9 re-read in the arXiv v1 PDF (text layer) and added to
  `literature/notes/PMRM26.md` and its index row.
- **SC2.4** (P) fixed: the abstract went from about 260 to about 175 words plus the display: the
  sentence on the non-asymptotic inequality is dropped, and the generality is in one sentence.

### Defects of referee-proofs (PF2.*)

- **PF2.1** fixed: `def:drift` added to the `\uses` of `cite:INC-P003-prop:witness`.
- **PF2.2** fixed: `lem:constants` defines $\mathcal K_a$, $\mathcal K'_a$ in its statement, and
  `lem:one-horizon` states its hypotheses in full (the four drift sets, $\pi$, the pair with
  $\mu^\star<1$, the source strategy with finite expected sizes, the arm) and defines
  $\mathcal K_a$, $\mathcal K'_a$, $x_a(T)$; neither refers to Theorem `thm:main` any more. Same
  content. The proof of `thm:main` (Step 0) says that the lemma's constants are the theorem's.
  A separate definition node was not chosen: it would move the definitions out of the statement of
  the main theorem, which the reader should be able to read alone.
- **PF2.3** fixed: "when $\mu^\star<1$" added to the sentence of the Constants paragraph, with
  "when $\mu^\star=1$, both are 0".

Nodes changed: `lem:constants`, `lem:one-horizon` (statements, same content), `cite:INC-P003-prop:witness`
(`\uses` only), the proofs of `thm:main`, `lem:one-horizon`, `lem:window`, `lem:kl` (layout of the
chains). Prose: abstract, Constants paragraph, Interpretation of Figure 1.

## 2026-11-17, revise (round 3), claude-opus-5-5

Rebased on `origin/main` (no conflict). Referee-proofs: accept (one P defect); referee-scope: major
(one L, one P). No statement changed; no proof changed in substance.

- **SC3.1** (L) fixed. I read AJSS23 (arXiv:2306.09048v1 HTML) §2, Theorem 2.1 and App. B.1, (10):
  the offline data come from an unknown adaptive policy on the online laws, (10) is
  $\mathbb E\log(L_\mu/L_{\tilde\nu})=\sum_a(\mathbb E N^o_a+\mathbb E N_a(\tau_\delta))\mathrm{KL}(\mu_a,\tilde\nu_a)$,
  and the lower bound of Theorem 2.1 sees the offline counts only through $\mathbb E N^o_a$. So the
  referee is right: this is the earliest source found for the source phase of the change of measure
  (without drift). App. E, row "Change of measure", now credits AJSS23 (online laws) before PMRM26
  (drift); Related work gains a "see also" sentence on AJSS23. `refs.bib` gains AJSS23 (metadata of
  `bibliography.json`, as in P003); its row of `literature/index.md` records my reading.
- **SC3.2** (P) fixed: in the proof of `lem:positive-part` (b), the chain is an `align` with one
  reason per line ($|\mathbb E X|\le\mathbb E|X|$; the Lipschitz bound above).
- **PF3.1** (P) fixed: the Constants paragraph now says "and, if $\mathcal K'_a>0$, it is 0 when
  $\limsup_T x_a(T)\ge1/\mathcal K'_a$".

Nodes changed: the proof of `lem:positive-part` (layout of one chain). Prose: Related work, the
Constants paragraph, App. E. No new dead end.
