Not refereed: working notes of the authors of P004.

## 2026-11-16, write-paper (claude-opus-5-5, owner's interactive session)

**Origin.** Direction D9 of StochasticBandits (the conjecture of [HT15, Section 9], KNOWN K60) was
explored by a research agent in the owner's session (report `pistes_claude2/D9_moments/rapport.md`,
outside the repository), then checked by an independent referee agent
(`pistes_claude2/D9_moments/verification.md`, verdict accept, defects V1–V11 all of class P). This
paper writes up the proved part of the report; the sketched and conjectured items went to the open
questions of the paper or to `DOSSIER.md`.

**The research, in short.**
- Where the MGF enters [HT15]: only in Lemma 14 (via Proposition 11), for the rounds at which the
  largest empirical mean is low. Proposition 10 (suboptimal arm) needs no moment beyond the mean,
  once Lemma 6 is read as "$\mathbb E[1/(1-\nu^\star(X-\mu))]\le1$".
- [HT15, (26)] bounds those rounds by a *sum* over the sample size $t$ of the optimal arm. Its
  expectation is infinite as soon as the optimal arm has no third moment (Remark in Section 4.2 of
  the paper; the necessity half of a one-sided Baum–Katz theorem). So the natural outcome of their
  route is three moments, not $2+p$.
- The new step: apply [HT15, Lemma 13] once, at the random level
  $M=\sup_s\{sD_{\inf}(\hat F_{j,s},\mu)+\log s:\hat\mu_{j,s}\le\mu\}$: the count is then a *supremum*
  (Lemma 4.2(b)).
- The expectation of that supremum is finite under a finite variance (Proposition 4.3): big jumps
  vs good part; one big jump costs $2Y/\delta$ (linear, because of the dual product), which sums to
  $\mathbb EY^2/\beta$; several jumps by independence; many jumps by Chebyshev + Hölder with an
  exponent $\gamma>1$; small good part by Bennett.
- Counterexample: the reference level of IMED is the empirical mean. One negative outlier $-y$ of the
  optimal arm makes the deterministic arm the leader while the optimal arm's index stays frozen at
  $\ge\log(y/e)$ (Lemma 4.4; the report had $\log y-3/2$, the verification noticed that the constant
  is $1$ since $(s-1)(1/s+1/s^2)=1-1/s^2<1$, checked again here).

**Dead ends and why.**
- Keeping the sum of [HT15, (26)] and replacing Cramér by a polynomial bound: the sum itself has
  infinite expectation without a third moment (see above). This is why the supremum is needed.
- Citing [HT15, Lemma 6] as a node: its dichotomy is imprecise in the boundary case
  $\mathbb E_F[(1-\mu)/(1-X)]=1$ (verification V2); the paper proves what it needs (Lemma B.2).
- Citing [HT15, Lemma 13] and the $G^\star$ construction as nodes: Lemma 13's indexing is loose about
  the initialisation rounds, and $G^\star$ lives in a proof, not a statement. Both are reproved in the
  paper (Lemma 4.2(a), Lemma B.5) and credited in Appendix E.
- A first attempt at Lemma B.5 without $G^\star$ (move the tail mass of an arbitrary $G$ onto the
  shape of $P$'s tail) controls the divergence by the log-sum inequality but not the mean of the new
  law for irregular tails; abandoned for the $G^\star$ route, whose density is at most 1 below $\mu$.

**Things noticed while writing.**
- The index of [HT15, Algorithm 1] is $+\infty$ for *every* arm when $\hat\mu^*=1$ (an arm has seen
  only rewards equal to 1): no law of $\mathcal A$ has a mean above 1. The proof of [HT15, Theorem 3]
  uses that a leader's index is at most $\log n$, so it needs a tie rule that pulls a leader in that
  case; with two arms and an optimal arm with an atom at 1, a rule pulling the other arm forever
  breaks the bound with positive probability. The paper fixes the convention $D_a(t)=0$ for an
  empirical leader (Definition 2.5 and the remark after it); it coincides with [HT15] whenever
  $\hat m^\star<1$.
- The range of $\delta$ in Theorem 3.3 is $(0,(1-m^\star)\mathcal K_i/2)$, per arm; it implies
  $\delta<\Delta_i/2$ because $(1-m^\star)\mathcal K_i\le\Delta_i$ (level shift from $m_i$).
- Lemma B.5 holds for every $r\ge1$, so Corollary 3.7 covers the literal class of the conjecture
  ($r=2+p$) and Open question 2 has the same target constant on $\mathcal S\setminus\{\delta_1\}$.

**Numerical experiments (this session).** `imed_sim.py` (copied from the research session; it
implements IMED with ties to arm 1 and jumps over runs of arm-2 pulls while arm 1's index is frozen;
read and validated by the verification agent) was run on 2026-11-16 with the commands recorded in
`sim_output.txt` (seeds 1–6; 3000 runs up to $T=10^4$, 200 runs up to $T=10^5$; a few minutes in
all on the owner's PC, one campaign, sequential). Table 2 of the paper copies these numbers. They agree with the report's own
runs (other seeds): $q=1.5$, mean of $N_2$ multiplied by 3.0 from $10^3$ to $10^4$ (the report: 2.9);
$q=2$, excess over $\log T/\mathcal K_{\inf}$ of about 2 pulls; $q=3$, mean slightly below
$\log T/\mathcal K_{\inf}$ for $T\ge10^4$. The verification's own short run at $q=2.2$ (finite
variance) also agreed with Theorem 3.3. `check_bounds.py` and the verification's
`indep_checks.py` (pathwise checks of Lemma 3, $(\ast)$, Lemma 1(c), Lemma 8 of the report) were not
copied: the verification reports 0 violations out of 6000–8093 samples for each.

**Not done.** The second-order rate (the report sketches $O((\log n)^{12/13})$), the sufficiency
below the variance (tails $1/(y^2\log y)$), the exact excess at $q=2$ (conjectured
$2\kappa/(e\,m^2)$), the converse of Proposition 4.3, and KL-UCB with finite means only: see the
open questions of the paper and `DOSSIER.md`.

## 2026-11-16, house-style rewrite (claude-opus-5-5, owner's interactive session)

**Task.** Rewrite the presentation of version 1 in the owner's house style (`docs/writing.md`
sections 2, 2a, W15; model arXiv:2610.21582; finished example: P005), without changing the
mathematics; same pull request, still version 1.

**What was done.**
- New order of sections (see `DOSSIER.md`, "Presentation"): related work is its own section;
  the classical results are recalled first (`cite:HT15-thm3` before `thm:main`, which needed
  `def:rate` to move before it, since that theorem uses $\lambda^\star$ and $\mathcal K_i$;
  `cite:GMS19-thm1` before `cor:optimal`); "How the proofs work" carries the decomposition with
  named terms; the simulations are a setup paragraph, the table and an interpretation paragraph.
- Proof of `thm:main` split along the decomposition: `lem:decomp`, `lem:termA`, `lem:termB`,
  `lem:termC` (new labels, restating Steps 2–5 of the former proof). Two quantities that the former
  proof defined inline got their own displays and anchors: $u_i$ (eq:ui) and $M_T$ (eq:MT). The
  fundamental inequality of index policies is displayed as (eq:fundamental).
- Navigation: an anchor `\dt{s:...}` at each definition and a link macro per symbol, applied by a
  script to every use after the definition (abstract, introduction and related work keep raw
  symbols, as in P005); defined words (instance, learner, optimal, suboptimal, consistent,
  uniformly fast convergent, empirical leader, tie rule, anytime) link to their definitions; the
  algorithm name links to its pseudo-code. Captions and section titles keep raw symbols (links
  there break the build).
- Citations in author–year style (natbib, `plainnat`): `\citet` in running text, `\citep` and
  `\citealp` for parenthetical ones; cited-node titles "From \citet[...]{KEY}".

**Pitfalls met.** The substitution of `\lambda^\star(` by the macro of $\lambda^\star(P,\mu)$ also
caught products $\lambda^\star(X-\mu)$ in `lem:optimizer`, `lem:subopt` and `lem:class`; reverted
(only the uses with arguments $(P,\mu)$ and $(\nu_i,m^\star)$ are links). Patterns after a subscript
letter (`\max_am_a`, `\min_aI_a`, `\liminf_TR_T`, `sD_j`) were missed by the first pass and fixed
by hand. A stale `paper.aux` with alpha labels makes natbib fail: clean before rebuilding.

**Check.** A script compared every node statement with the previous commit after normalising the
macros and citation commands: 24 identical, `def:kinf` and `def:run` identical up to sentence
splitting, `def:model` and `def:imed` identical up to sentence splitting and prose words naming the
defined object ("The mean of arm $a$ is"); no formula changed.

## 2026-11-16, Claude Opus 5.5 (revise, repair): rebase on main

Repair round, no referee report. The branch conflicted with `main` (P001 and its literature entries merged meanwhile). `git rebase origin/main`: two additive conflicts outside this paper, `literature/index.md` (rows B62/Adu25 and HT15/Hal69) and `literature/bibliography.json` (entries B62/Adu25); resolved by keeping both sides, with the extended HT15 row of this paper (it adds the parts read on 2026-11-16 to the row of `main`). Nothing of `papers/P004-imed-finite-variance/` changed. The rules merged on `main` meanwhile (author-year citations, criterion W16) were already met: natbib with `plainnat`, Section "Examples and simulations" with the committed simulations. Both builds compile (reader 33 pages, blueprint 34; no error, no undefined or multiply defined reference); `certify.py check --base origin/main` passes.

## 2026-11-16, Claude Opus 5.5 (revise, round 1): scope report SC1.1–SC1.8

Rebase on `main` first (P000 v2, P003 merged): one conflict in `literature/index.md` (row BK65 of
this paper next to the row BK96 updated on `main`); kept both, with `main`'s BK96 row.

- **SC1.3 (L), fixed.** Read [PA26] §2.2, Theorem 3.1 and the outline of its proof (A.2), and
  [BSH23] §4.4 (notes `literature/notes/PA26.md`, `BSH23.md`). Finding: both assumptions of
  [PA26, Theorem 3.1] hold on $\mathcal M_1$ with a finite mean only, at the levels below 1. (a)
  Assumption 2.3: with $\lambda=\theta/(1-m)$, $1-\lambda(X-m)=(1-\theta)+\theta R$, $R=(1-X)/(1-m)$,
  $\mathbb ER=1$; the uniform mixture over $\theta$ of the products is a nonnegative martingale, and
  it is at least the maximum over $\theta$ divided by $n+1$ (universal portfolio, two assets:
  $W(\theta)\ge(1-\alpha)^nW(\theta^\star)$ along the two segments from $\theta^\star$ to $0$ and
  $1$). Doob/Ville gives $g(n)=\log(n+1)$. (b) Assumption 2.4: the Chernoff bound of `lem:subopt`;
  $\psi(\eta)\le\eta K+\eta^2C/2$ on $[-1/2,0]$ with $C=\mathbb E[V^2e^{V^-/2}]$, finite since
  $\mathbb Ee^{-V}\le1$ and $V^+\le\log(1+\lambda^\star|X-\mu|)$; rate $\ge d^2/(2C)$. (c) Their
  $\mathrm{KL}_{\inf}$ ($\ge$, over $\mathcal M_1$) equals $\mathcal K_{\inf}$ (mixing with
  $\delta_1$ or $\delta_0$). Written as the new node `lem:pa-assumptions` and the paragraph "Another
  algorithm" of `sec:counter`, as a reduction (their proof was read in outline only, through a
  fetch tool). `oq:finite-mean` restated for an IMED-type index with a robust level (`IMED`-$\rho$);
  "Gap with the literature", `sec:related`, Table 1 and the conclusion updated.
- **SC1.1 (L), fixed.** [CL75] and [Jan86] added (Crossref metadata; the AMS page refused access, so
  read in their abstracts only): "see also" after `lem:three-moments` (the former remark) and in
  Appendix G. New paragraph "Relation with the last exit time" after `prop:key`:
  $\sup_sw_s\ge L$ (because $\mathcal K_{\inf}\ge0$), $\mathbb EL<\infty$ under a second moment of
  $X^-$ (see also CL75, Jan86), and why `prop:key` is not a corollary (the factor
  $\exp(s\mathcal K_{\inf})$, linear in one big jump).
- **SC1.2 (L), fixed.** [Nag79] and [FN71] added (Crossref metadata, abstracts only), credited as
  "see also" for the split into large summands and a truncated rest, in `sec:related`, after the
  paragraph "Why the variance enters" and in Appendix G; "new" kept for its use inside the dual
  product.
- **SC1.4 (P), fixed in part.** `def:rate`, `def:dev` and `thm:main` now come before the recall of
  `cite:HT15-thm3` (new subsection `sec:upper-ht15`, with the notation of HT15 and the remark on the
  convention for leaders, moved from `sec:algorithm`). `thm:main` is on p. 7 of the reader build
  (was p. 8); Table 1 grew by two rows (SC1.3) and Algorithm 1 does not fit on p. 6. Not on p. 5:
  the informal statement on p. 2 stays the first statement.
- **SC1.5 (P), fixed.** Abstract cut to about 200 words (the mechanism sentences removed).
- **SC1.6 (P), fixed.** The weight of $P_{q,\pi}$ renamed $\varpi$ (statement of `cor:pareto`, its
  proof, Example, Table 2 interpretation, notation). On $\gamma$: $\gamma_{a,\mu}$ of
  `cite:HT15-thm3` is the supremum of the exponents $\gamma$ with $\phi(\gamma)\le1$ of
  `lem:moments`, so one meaning ("an exponent with $\phi(\gamma)\le1$"); said in the renaming line.
  The exponent of the remainder in `oq:second-order`, a third use, renamed $\omega$.
- **SC1.7 (P), fixed.** The remark became the node `lem:three-moments`, its proof in the new appendix
  `sec:proof-three`; a renaming line of HT15's notation before `cite:HT15-thm2`.
- **SC1.8 (P), fixed.** One section "Conclusion and open questions" (`sec:open`).

Dead ends: moving Algorithm 1 to `[!ht]` did not bring `thm:main` to p. 6 (reverted).

## 2026-11-16, Claude Opus 5.5 (revise, round 2): SC2.1–SC2.4, SC1.4, PF1.1–PF1.5

Rebase on `main` (P002 v2 merged): no conflict. Still version 1.

- **PF1.1 (L), fixed in `lem:optimizer`.** Step 2 now proves continuity at $\lambda=0$ separately:
  $|\log(1-\lambda z)|\le2\lambda|z|$ for $\lambda\le\bar\lambda/2$, $z\le1/\bar\lambda$, so
  $|L(\lambda)|\le2\lambda\mathbb E|Z|\to0$; concavity is used only on the open interval. Step 3 reuses
  the bound. The referee's counterexample ($f(0)=-1$, $f=0$ on $(0,1)$) is right: concave and finite
  does not give continuity at an endpoint.
- **PF1.4 (P), fixed.** New part (c) of `lem:optimizer` (same node, statement extended): $V$ satisfies
  $\mathbb Ee^{-V}\le1$, is integrable, $\mathbb EV=\mathcal K_{\inf}(P,\mu)$ (new Step 6, the former
  Step 3 of `lem:subopt`). `lem:subopt` Step 3 and `lem:pa-assumptions` Step 5 cite it.
- **PF1.2 (P), fixed.** `prop:key` Step 0 deleted; a line notes $v\ge\delta^2>0$.
- **PF1.3 (P), fixed.** `thm:counter` (i), (ii): $y_0>0$. Formally a stronger hypothesis, but
  equivalent (replace $y_0$ by $\max\{y_0,1\}$); the proof uses only large $y$; `cor:pareto` uses $y_0=1$.
- **PF1.5 (P), fixed.** `lem:pa-assumptions` Step 8: $\varepsilon\in(0,\min\{1,1-\mu\})$.
- **SC2.1 (L), fixed.** Read AJK21 (arXiv:2102.03734v1 PDF: Proposition 5, App. B.4 Lemma 17,
  B.4.1) and re-read PA26 App. A.1. The referee is right: (a) of `lem:pa-assumptions` is their
  method (mixture of the dual products, a universal-coding factor, Ville). Credited in the Idea of
  `lem:pa-assumptions`, in "Gap with the literature" and in the last row of the appendix of sources.
  What is ours: semi-bounded laws with a finite mean only, one dual variable, and the exact factor
  $n+1$ (no additive constant). Rows AJK21 and BSH23 of `literature/index.md` extended.
- **SC2.2 (P), fixed.** "(no source read; proved in the lemma)" removed from the appendix of sources.
- **SC2.3 (P), fixed.** The referee is right: the former $\rho_a$ was an inversion of
  $\mathcal K_{\inf}$. `oq:finite-mean` now uses the lower-truncated mean
  $\frac1n\sum_{l\le n}\max\{X_{a,l},-\sqrt n\}$ (no inversion; an outlier moves it by at most
  $(1+\sqrt n)/n$), says that an inversion-based level costs as much as KLinf-UCB, and cites
  [BSH23, Remark 1, App. B.4] as the precedent (two-sided truncation, known moment bound). Where the
  method stops: the expectation of the supremum of `lem:sup`(b) on the event that the truncated mean
  is low (the empirical law can still contain outliers). Side remark, not in the paper: for
  $u=\sqrt s$, Bernstein on $\max\{X,-u\}$ (variance $\le u\,\mathbb E|X|$, range $u+1$) gives
  $\Pr(\text{truncated mean}\le m-\delta)\le\exp(-c\sqrt s)$ with a finite mean only; this does not
  bound the expectation of $s\exp(s\mathcal K_{\inf})$ on that event, which is the real difficulty.
- **SC2.4 (P), fixed.** The setup of the simulations says how to reproduce Table 2. Optional part
  done: new script `klinf_ucb_sim.py` (KLinf-UCB of PA26 with $f(t)=\log t+2\log\log t+\log(1+N)+1$;
  on two arms with $\nu_2=\delta_0$, arm 1 is pulled iff $N_1\mathcal K_{\inf}(\hat\nu_1,U_2)\le f$, one
  dual evaluation per round). Its $\mathcal K_{\inf}$ routine was checked against a brute-force grid
  on 2000 random empirical laws (max relative difference $2\cdot10^{-7}$; script in
  `.agents/scratch`, not committed). Run `python klinf_ucb_sim.py 1.5 500 10000 7` (about 17 min,
  recorded in `sim_output.txt`): mean $N_2$ 8.42 and 14.14 at $T=10^3,10^4$ (max 11 and 16, no run
  with $N_2>T/10$), against IMED's max 901 and 7360. Added as two rows of Table 2 with one
  interpretation item.
- **SC1.4 (P, optional), not done.** The attribution sentence of SC2.1 in §2 pushed `thm:main` back to
  the top of p. 8 (a few lines); the sentence was shortened, not enough. Moving Table 1 out of §2
  would break the order of `docs/writing.md` §2a; left as is.
