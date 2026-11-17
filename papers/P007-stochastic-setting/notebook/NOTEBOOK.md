Not refereed: working notes of the authors of P007-stochastic-setting.

## 2026-11-16, write-paper (owner session), claude-opus-5-5

**Scope decided.** F0 of StochasticBandits asks for the Definitions table, the product-class
identity and witnesses/exclusions. Read P004 and P005 (open pull requests) to fix what they use:
$\mathcal S$, $\mathcal H_\kappa$, $\mathcal K_{\inf}$ with the strict inequality, consistency and
uniform fast convergence on $\mathcal D^\alpha$, counts with rounds from 0 (P004) or 1 (P005), and the
stack model of rewards. Deferred: GMS19 Definitions 3–4, SA11 tails, family versions of the
convergence classes, the algorithms of later papers (reasons in DOSSIER.md).

**Main result.** $C(\nu;\prod_a\mathcal D_a)=\sum_{a\ne a^\star}\Delta_a/\mathcal K_{\inf}(\nu_a,m^\star;\mathcal D_a)$.
The proof goes through the reduction `lem:gl-reduction` (weight $\infty$ on the optimal arm, free since
$\Delta_{a^\star}=0$, kills every alternative that moves the optimal law). Without infinite weights the
identity would need an approximation argument (weights $M$ large on $a^\star$ and alternatives with
$\mathrm{KL}(\nu_{a^\star},\nu'_{a^\star})$ arbitrarily small): the roadmap's choice $w\in[0,\infty]^\alpha$
avoids it. **Dead end avoided:** a first draft of Step 1 of `thm:main` concluded $w_a\mathcal K_a\ge1$;
false when no $Q$ has a mean above $m^\star$ ($\mathcal K_a=\infty$, $w_a=0$, $0\cdot\infty=0$). The
statement is $w_a\ge1/\mathcal K_a$.

**Witness of consistency.** The roadmap names KL-UCB; proving KL-UCB in the paper would need a
transcription of [CGMMS13, Theorem 1] (no note; the HTML tool refused verbatim copies). UCB with a
Hoeffding bonus is proved instead, with constants: $\mathbb EN_a(T)\le8\log T/\Delta^2+2/\Delta^2+5/4$,
hence $13\log T/\Delta^2$ for $T\ge2$. Lean route for KL-UCB: LMLExplore `klucb_regret_eventually_le`
+ `isConsistent_of_eventually_le_mul_log` (DOSSIER.md).

**Rewards by count.** The paper defines runs by conditional laws (LML's `IsAlgEnvSeq`), while P004/P005
and the UCB proof use the stack model. `lem:stack` bridges them by truncation in time, as LML's
`RewardByCountMeasure.lean` does (`rewardByCountUntil`).

**Numbers.** `constants.py` (output `constants.txt`): the constants of Section `sec:examples`, and two
checks of `prop:ucb` ($13/4\le5\log2$, $\zeta(3)-1\le1/4$).

**Not checked by a second agent.** All proofs written once; the weak points are listed in DOSSIER.md.

## 2026-11-17, revise (round 1), claude-opus-5-5

Answers to the reports of referee-scope (SC1.*) and referee-proofs (PF1.*) on `37e0e215e697`.
The branch was rebased on `origin/main` first (no conflict). Sources were read by three helper
agents, which wrote the notes `literature/notes/VPG24.md`, `SA11.md`, `ACF02.md`, `BK96.md`,
`CGMMS13.md` and a section of `GMS19.md` (verbatim statements read on page images).

- **SC1.1 (G), fixed.** VPG24 (Van Parys–Golrezaei, Management Science 2024, arXiv:2007.07302v3)
  read: §3–§4.1, Example 3, Propositions 1–2, example (9). `sec:related` ("Structured classes",
  "Closest related work", "Gap with the literature") and DOSSIER (Closest known, Searches) now say
  what it gives (finite set of rewards, closed convex models, $\mathcal K_{\inf}$ positive and
  attained, rates stated without a written proof) and what `thm:main` adds. No node changed.
- **SC1.2 (G), fixed** by new nodes rather than by asking the owner: `def:pairwise`,
  `def:monotonic` (with the order $\preccurlyeq$ in the text), `def:tails`, `def:family`, and the
  witnesses/exclusions `lem:gms-classes`, `lem:tails`, `prop:ucb-tails`, `lem:family`, in a new
  subsection of `sec:learners` (not of `sec:setting`, to keep `thm:main` from moving later; the
  main result uses none of them). Choices: monotonic for every $T\ge1$ (GMS19 Def. 4 has no
  quantifier on $T$); tails of the **pseudo-regret** (SA11's regret is the realised regret against the
  optimal arm's reward sequence, not a function of the counts; the roadmap pins the pseudo-regret),
  declared in the paper. **Dead end:** $\pi^b$ is not an exclusion for monotonicity (both sums are
  $T$ or $0$, since $\nu'\preccurlyeq\nu$ keeps the optimal set); the switching learner $\pi^{\rm sw}$
  (stay on $b$ after a low first reward) is. **Dead end:** a tail bound for UCB from Markov's
  inequality on `prop:ucb` gives only a constant tail; the decomposition summed over all rounds
  (term A of `lem:ucb-terms`) also gives a constant. The fix is to look at the single count
  $s=\lceil10\log T/\Delta^2\rceil-1$ and at the rounds $t\ge s$ only, where
  $\sum_{t\ge s}(t+1)^{-3}\le1/(2s^2)$: tail $1/\log^2T$, uniform in the instance.
- **SC1.3 (L), fixed.** ATA89 and GL97 credited as "see also" (not read; VPG24's account) after
  `lem:gl-reduction`, in `sec:related` and in `sec:attribution`; one-arm alternatives credited to
  LR85 and the proof of BK96 Theorem 1.
- **SC1.4 (L), fixed.** BK96 §4.4 read (authors' PDF p. 140): remark after `lem:kinf-gauss` and
  `sec:attribution` credit it, HT14 as a restatement.
- **SC1.5 (L), fixed.** CGMMS13 §6.1 read: remark after `lem:kinf-unit` and `sec:attribution`.
- **SC1.6 (L), fixed.** Remark after `lem:stack`, `sec:related` and `sec:attribution`: the LML
  formalisation (new entry `LML`), Doob 1936 (`D36`, "see also") and LS §4.6.
- **SC1.7 (L), fixed.** ACF02 Theorem 1 read; remark after `prop:ucb` compares the constants
  ($8\ln n/\Delta^2+1+\pi^2/3$ against ours).
- **SC1.8 (R), fixed.** The exponent of consistency is $\gamma$ everywhere (`def:consistent`,
  `lem:classes`, `lem:constant`, their proofs, Table 1, the notation), with a sentence that it is the
  $\alpha$-consistency of SAE13.
- **SC1.9 (P), fixed.** Mixing weight $\eta$ (`lem:mix`, proofs of `lem:kinf-unit`, `lem:kinf-p1`,
  `lem:semi`); Gaussian variance $v$ (`def:models`, `lem:kinf-gauss`, `lem:kurt`(iii)); scale $b$ in
  `lem:kurt`(ii). Not changed: the moment bound $B$ of $\mathcal L_{\varepsilon,B}$, which is the
  roadmap's pinned notation; $\mathcal B$ (calligraphic) is a different glyph.
- **SC1.10 (P), partly.** `sec:main` now comes right after `sec:setting` (and its appendix first):
  `thm:main` moved from p. 11 to p. 8. Page 5 would need the definitions of learners and of their
  classes after the main section, against the house order.
- **SC1.11 (P), fixed.** Abstract shortened (about 190 words), last sentence dropped, the
  evaluative claim reworded.
- **SC1.12 (P), fixed.** "library", "later paper", "a paper that allows them…", the notebook
  script: reworded for a reader of the paper alone.
- **SC1.13 (P), fixed.** One section `sec:open`, "Conclusion and open questions".
- **SC1.14 (P), fixed.** CGMMS13 §6 for general laws on [0,1] (§5 for finitely supported ones);
  BCL13 assumes the same raw-moment bound.
- **SC1.15 (P), fixed.** "See also" LS Exercise 16.4 (after `lem:kinf-p1`) and the HT10 dual by
  Jensen (after `lem:kinf-unit`); both in `sec:attribution`.
- **PF1.1 (L), fixed.** `def:product`: every class is a structured class, the unstructured ones the
  special case (roadmap convention); $\mathcal E_2$ "is not unstructured"; Scope and "Changes to the
  sources" reworded.
- **PF1.2 (P), fixed.** Models $\subseteq\mathcal P_1$ declared after `def:kinf`, under "Changes to
  the sources" and in DOSSIER.
- **PF1.3, PF1.4 (P), fixed.** `lem:kurt`(ii) and `lem:semi`(iv) restated with their quantifiers.

## 2026-11-17, revise (repair: conflict with `main`), claude-opus-5-5

- The branch conflicted with `main` after P006 (#42) was merged: both added readings of ACF02 and
  CGMMS13. Rebased on `origin/main`; `literature/index.md` (rows ACF02, CGMMS13) and
  `literature/notes/ACF02.md` merged by keeping both readings (P006's and P007's) and both uses.
  Nothing of `papers/P007-stochastic-setting/` changed; `paper.tex` untouched, so no node changed.
- Both builds compile (reader 29 pages, blueprint 30), no error, no undefined, no multiply defined;
  `certify.py check --base origin/main` passes.

## 2026-11-17, revise (round 2), claude-opus-5-5

Answers to referee-scope (SC2.1–SC2.5) and referee-proofs (PF2.1) on `742ab09f7c0a`; referee-proofs
accepted. No rebase needed (`origin/main` = 326680c is the base).

- **SC2.1 (L), fixed.** New cited node `cite:INC-P006-prop:kinf` (P006 v1, Proposition 4.2, items
  (i)–(v), in our notation, with a renaming paragraph: $\mathcal M=\mathcal P[0,1]$,
  $\mathcal K_{\inf}(P,\mu)=\mathcal K_{\inf}(P,\mu;\mathcal P[0,1])$, $\mathcal P$ = instances of
  $\mathcal P[0,1]^\alpha$ with $m^\star<1$; P006's kl conventions at the endpoints agree with ours).
  `depends_on = ["P006v1:def:instance", "P006v1:def:kinf", "P006v1:prop:kinf"]`. `lem:kinf-unit` keeps
  only what P006 lacks: (i) the two consequences ($0<\mathcal K_{\inf}<\infty$ for $m(P)<\mu<1$;
  $0$ at the mean) and (ii) the Bernoulli model $\mathcal B$ (with P006 (iv) for $\mathcal P[0,1]$).
  **Renumbered items**: old (iii) is now (ii); old (i) and the bounds of old (ii) are now the cited
  node (i), (iii). References updated: Degenerate values after `thm:main`, the example after
  `prop:gl-zero`, `sec:examples`, the proof of `lem:semi` (no longer refers to `lem:kinf-unit`; same
  mixing argument written out, `\uses` without `lem:kinf-unit`). Node `cite:GMS19-lem1` removed (no
  user left; label not to be reused). Abstract and contributions reworded (the bounds on $[0,1]$
  are recalled, not proved). DOSSIER: reuse of `Incognita.BatchedBandits.unitLaws`, the wrong
  "BatchedBandits reuses it" corrected.
- **SC2.2 (L), fixed.** AMS09 read (authors' version, §3.2 Theorem 2 (10)–(12), §5.1 in full;
  new note `literature/notes/AMS09.md`, index row extended). Credited as the source of the argument
  of `prop:ucb-tails` (remark after it, `sec:related` "Gap with the literature", contributions,
  `sec:attribution` new row), with the comparison: $b=1$, $\rho=2$ is our index (their round $t+1$
  is our round $t$), $x=1$ gives $\mathbb P(N_a(n)>1+8\log n/\Delta^2)\le n^{-3}+\frac13(1+8\log n/\Delta^2)^{-3}$,
  a $(\log n)^{-3}$ tail; SA11 §2 "log³-T and log³-R". `prop:ucb-tails` is called a weaker,
  self-contained form. Check (DOSSIER, K32): AMS09's bound implies ours, since
  $10\log T/\Delta^2>1+8\log T/\Delta^2$ ($2\log2>1$) and $T^{-3}+\frac13\Delta^6(8\log T)^{-3}\le(\log T)^{-2}$
  for $T\ge2$. Statement and proof of `prop:ucb-tails` unchanged in substance.
- **SC2.3 (P), partly fixed, partly disputed.** Fixed: "see also" [SA11, Proposition 2.1] after
  `lem:tails` and in `sec:attribution`; DOSSIER "Users" rewritten (P004, P005, P006 accepted),
  with the node-by-node comparison with P004 `lem:dualfacts`(a)–(b), P005 `lem:mixkl`,
  `cor:largegap`. **Disputed** (the "see also" to P004 and P005 in `paper.tex`): any `\cite{INC-P…}`
  requires a `depends_on` entry (AGENTS.md §5.6, CI), which records a result *used* and makes this
  paper conditional on P004 and P005 and subject to their dependency checks; nothing of them is used
  (one-line facts, proved here in two lines), and they are users of these definitions. So the
  comparison is in DOSSIER only.
- **SC2.4 (P), fixed.** "Idea." paragraph in the proof of `prop:ucb-tails`.
- **SC2.5 (P), fixed.** refs.bib: `note` on VPG24 (numbering of arXiv:2007.07302v3); in passing the
  same for SA11 (arXiv:1107.4506v2, whose Proposition 2.1 is Proposition 3 in the ALT version, per
  referee-scope's query) and for the new AMS09 entry (authors' version).
- **PF2.1 (P), fixed.** New node `lem:ucb-basic` (statement self-contained: a run of UCB on
  $\mathcal P[0,1]^\alpha$, an optimal arm $a^\star$, $E_t$ defined for $t\ge1$): (a) $A_t\in M_t(H_t)$
  for every $t$ a.s.; (b) $\mathbb P(E_t)\le(t+1)^{-3}$, with its proof (moved from the proof of
  `lem:ucb-terms`, Term A, with the union bound over $j=N_{a^\star}(t)$). Used (`\uses`) by
  `lem:ucb-decomp` (statement and proof), `lem:ucb-terms` (statement and proof; Term A now one line;
  \eqref{eq:hoeffding} keeps only the upper tail for arm $a$, the lower tail being in
  `lem:ucb-basic`) and the proof of `prop:ucb-tails` (Setting, Step 2, Step 3). E_t added to the
  notation table.
- **SC1.10 (P)** stays as in round 1 (`thm:main` on p. 8; reason in the round-1 entry).
- Nodes to re-check: `lem:kinf-unit` (statement and proof), `cite:INC-P006-prop:kinf` (new),
  `lem:semi` (proof wording, item (i)), `lem:ucb-basic` (new), `lem:ucb-decomp`, `lem:ucb-terms`
  (statements' `\uses` and proofs), `prop:ucb-tails` (proof: Setting, Idea, Steps 2–3); removed:
  `cite:GMS19-lem1`. Remarks changed (not nodes): after `lem:tails`, after `prop:ucb-tails`, before
  and after `lem:kinf-unit`, `sec:related`, `sec:overview`, `sec:attribution`, `sec:cited` intro.
- **Dead end avoided:** writing the AMS09 index as "ours up to $\log(t+1)$ instead of $\log t$": with
  rounds from 0, our $\log(t+1)$ at round $t$ is exactly their $\log t$ at their round $t$; the
  indices coincide.
