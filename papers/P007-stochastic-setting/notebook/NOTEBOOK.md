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
