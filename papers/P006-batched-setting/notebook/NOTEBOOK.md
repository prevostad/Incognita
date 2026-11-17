Not refereed: working notes of the authors of P006-batched-setting.

# 2026-11-16, write-paper (interactive session with the owner's assistant), claude-opus-5-5

## What was done

First version of the setting paper (item F0 of BatchedBandits). Nodes: `def:instance`,
`def:kinf`, `def:learner`, `def:counts`, `lem:counts`, `def:seqcons`, `def:grid`, `def:logratio`,
`lem:grid`, `def:exgrids`, `def:batched`, `lem:mask`, `def:infomodel`, `def:consistent`,
`lem:consist-regret`, `thm:main`, `prop:kinf`, `def:exlearners`, `prop:witnesses`,
`cite:GMS19-lem1`, `lem:kl`.

`thm:main` gathers the "basic relations" the roadmap asks for (nesting of the information models,
refinement, the sequential grid). A definitions paper has no theorem in the usual sense; the
choice was to make the relations the main node and keep the $\mathcal K_{\inf}$ bounds and the
witnesses as propositions.

## Choices and why

- **Batched = pointwise invariance of the kernels** (`def:batched`), with the masked kernel form
  as a lemma (`lem:mask`). The pointwise form is easier to state for LML's `Algorithm` (policy on
  `Hist n × Unit`); the masked form is what a change of measure uses.
- **$M_k$ as a property of a family indexed by grids** (`def:infomodel`), comparing two grids only
  at rounds that lie in batch $\ell+1$ of both. With $k=\infty$ written as "agree on every $j$",
  condition (b) is void uniformly, so no separate case.
- **Strictness of the chain** by the parity learner `Par^{(k)}` (reads $t_{\ell+k+1}$). A first
  idea was "pull arm 1 at the last round of the batch" (reads $t_{\ell+1}$), which separates only
  $M_0$ from $M_1$; the parity of $t_{\ell+k+1}$ works for every $k$ with the same pair of grids
  ($\mathsf S_r$ and its shift by one from index $k+1$ on).
- **$\mathcal K_{\inf}$ bounds without the dual formula.** Lower bound: GMS19's Lemma 1 with
  $Z=$ the reward (clipped) gives $\mathrm{KL}(P,Q)\ge\mathrm{kl}(m(P),m(Q))$, then monotonicity of
  $\mathrm{kl}(p,\cdot)$ and Pinsker for Bernoulli. An alternative, self-contained route was
  written first in these notes: the Gibbs variational inequality
  $\mathrm{KL}(P,Q)\ge\mathbb E_P f-\log\mathbb E_Q e^f$ (Jensen), with $f=-\lambda x$ and the convexity
  bound $e^{-\lambda x}\le1-x+xe^{-\lambda}$ on $[0,1]$, which gives the same $\mathrm{kl}(p,q)$ after
  optimising $\lambda$. Dropped in favour of the cited lemma (shorter, already a cited node of
  P000). Upper bound: mixture $(1-u)P+u\delta_1$, density $\le 1/(1-u)$.
- **Consistency witness.** A non-degenerate consistent learner on all of $\mathcal P$ needs a
  regret analysis (forced exploration + frozen greedy works on grids with
  $\log t_{\ell+1}=o((\log t_\ell)^2)$, by Hoeffding, but this is a result, not a definition). Kept
  the degenerate witness `Const_c` on $\mathcal P_c$, which shows the definition is not empty and
  depends on the class; its exclusions (`Const_c`, `RR` on $\mathcal P$) show it is not trivially
  true.

## Dead ends

- Citing LS Theorem 16.2 or GMS19 Theorem 1 for "LMLExplore's lower bounds apply on
  $\mathsf S_s$": both need consistency on a product class $\{\nu:\nu_a\in M_a\}$, and $\mathcal P$
  is not one ($m^\star<1$). The one-alternative version (LMLExplore's
  `eventually_mul_log_le_integral_pullCount_of_klDiv`) is what applies; the paper says so in
  words only and leaves the bound to F1.
- Citing the library paper P000 for motivation: it would need a `depends_on` entry for a result
  that is not used. Not cited; the correspondence with P000's Setting is in DOSSIER.md.

## Numerical experiments

`constants.py` (no randomness): $\mathrm{kl}(0.5,0.7)=0.0872$ between $2\Delta^2=0.08$ and
$\log(0.5/0.3)=0.5108$; ratios of $\mathsf S_2$, $\mathsf G_2$, $\mathsf D_2$. Output in
`constants.txt`. No simulation: there is no algorithm to analyse.

## Not checked

- No Lean was written or compiled (the server runs the loop tonight; Lean is never compiled on the
  PC). The Lean shapes in DOSSIER.md were read from the sources on GitHub, not type-checked.

# 2026-11-17, revise (revision round 1), claude-opus-5-5

Rebased on `origin/main` (no conflict). Answers to the reports of `referee-scope` (major) and
`referee-proofs` (accept, P only) on head `516d2d2`.

## Defects

- **SC1.1 (G), fixed.** Read Qiao–Wu (arXiv:2611.17500: setting, Definition 1, Theorems 1–4) and
  added it to `literature/` (QW26). Changed: sec:related ("Imposed batches and delays", "Closest
  related work", "Gap with the literature": the gap is now the intermediate $\mathcal M_k$,
  consistency at the batch ends and the relations), `tab:comparison` (rows QW26, PGPK21),
  sec:attribution (aware/oblivious credited to QW26), DOSSIER (Closest known with a derivation
  attempt, Searches with this session's queries and the referee's). No statement changed.
- **SC1.2 (L), fixed.** Read CGMMS13 §6.1 (the display $d_{\mathrm{BER}}(E\nu,E\nu')\le
  \mathrm{KL}(\nu,\nu')$) and GHMS22 (7). Credited in sec:related, sec:overview ("The divergence")
  and sec:attribution (CGMMS13 §6.1 earliest found, GMS19 Lemma 1 as the form used, GHMS22 (7) for
  the chain).
- **SC1.3 (L), fixed.** sec:related: empirical KL-UCB, finitely supported laws, $\mu_a>0$,
  $\mu^\star<1$ [CGMMS13, Theorem 2]; the claim for all laws on $[0,1]$ dropped.
- **SC1.4 (R), fixed.** Level of $\mathcal K_{\inf}$ renamed $\mu$ (`def:kinf`, `prop:kinf`
  statement and proof, Table 2, notation table); masking index renamed $r$ (`def:batched`,
  `lem:mask` and its proof, proofs of `thm:main`(i) and `prop:witnesses`(c), vocabulary); the
  $\sigma$-algebra of `cite:GMS19-lem1` renamed $\mathcal S$ (with the renaming line). $m$ is now
  only the mean map ($m(Q)$, $m_c$, $m^\star$). In the proof of `prop:witnesses`(d) the local
  $r:=\max(2,K)$ is replaced by the $s$ of the statement.
- **SC1.5 (P), fixed** by a new witness rather than by dropping "not degenerate": new learner
  `UCB` in `def:exlearners`, new cited node `cite:ACF02-thm1` (ACF02 Theorem 1, read, verbatim in
  `literature/notes/ACF02.md`), new node `cor:ucb` (UCB is batched on $\mathsf S_K$ and consistent
  at its batch ends on $\mathcal P$), proved in a new subsection of Appendix E; Table 2 updated.
  The corollary is placed after `prop:witnesses` and uses `thm:main`, so there is no cycle with
  `thm:main`, which uses `prop:witnesses`.
- **SC1.6 (P), fixed.** (a) PGPK21 (read: §2, Theorem 3.1) and PGPK22 ("see also") in "Imposed
  batches and delays". (b) "BK96, in general" replaced by "for more general models", and the
  lower bound for all laws on $[0,1]$ is cited as [GMS19, Theorem 1].
- **SC1.7 (P), fixed.** Pinsker: Rio23 (read: §2–§4 opening) for the history (Csiszár 1967,
  Kullback 1967, Kemperman 1969, Schützenberger 1953) and for Csiszár's one-line proof (16), which is
  the proof of `lem:kl`. Upper bound: "this form: source not known; the uniform bound: HT10,
  Lemma 14".
- **SC1.8 (P), fixed.** "Idea." paragraphs in the proofs of `thm:main`, `prop:kinf`,
  `prop:witnesses`, `cor:ucb`; Setting/Goal block in the proof of `thm:main`.
- **SC1.9 (P), fixed.** Section 7 renamed "Conclusion and open questions"; abstract: "except in
  the first batch, where they must ignore the rewards"; "Rounds numbered from zero" names the
  formalisation in Lean.
- **SC1.10 (P), fixed.** `def:grid` defines $b_g(t)$; the proof of `thm:main`(ii) recalls it.
- **PF1.1 (P), fixed.** `def:kinf` defines KL on any measurable space.
- **PF1.2 (P), fixed.** Convention $0\log\frac0q:=0$ for every $q\in[0,1]$, so $\mathrm{kl}(p,p)=0$.
- **PF1.3 (P), fixed.** `\uses`: `def:grid` in `lem:mask` (statement and proof); `def:grid`,
  `def:learner` in `lem:consist-regret` (statement and proof); `def:counts` in the proofs of
  `thm:main` and `prop:witnesses`.
- **PF1.4 (P), fixed.** Proof of `lem:kl`: the derivative for $p=0$ stated.
- **PF1.5 (P), fixed.** `prop:witnesses`(d): the constant family $(\mathrm{Const}_c)_g$ is in
  $\mathcal M_0$, with its proof; the example paragraph of sec:examples cites it.

Changed nodes: `def:kinf`, `def:grid`, `def:batched`, `lem:mask`, `lem:consist-regret`,
`def:exlearners`, `prop:kinf` (renaming only), `prop:witnesses` (item (d) extended),
`cite:GMS19-lem1` (renaming only), `lem:kl` (proof), `thm:main` (proof); new: `cite:ACF02-thm1`,
`cor:ucb`. No statement was weakened or strengthened except `prop:witnesses`(d), which gains a
claim.

## Choices

- `cite:ACF02-thm1` is stated in the reward-stack model of ACF02, not in the paper's kernel model:
  the identification of the two laws is a step of the proof of `cor:ucb` (Step 1), since ACF02
  does not print it. The argument: replace the stack of arm $c$ by zeros from index $j$ on; the
  run up to round $t-1$ is unchanged on $\{N_c(t-1)=j-1\}$, so $X_{c,j}$ is independent of the
  history and of the event there. Written for deterministic learners only.
- UCB1 leaves the initial order and ties open; `UCB` fixes them (order $c_1,\dots,c_K$, first
  maximiser). ACF02's Theorem 1 does not use them.

## Dead ends

- Proving `cor:ucb` inside `prop:witnesses` (as item (f)): it needs `thm:main`(iii), and
  `thm:main` uses `prop:witnesses`(d), which would make a cycle in the blueprint. Hence a separate
  corollary.
- Citing Csiszár (1967), Kullback (1967) and Kemperman (1969) directly: not read (only through
  Rio23), so they are named with their years through Rio23, without bibliography entries.

## Not checked

- The second half of the HTML of QW26 (proofs, appendices) was not read; the paper uses only its
  setting and the statements of Theorems 1 and 4.

# 2026-11-17, revise (revision round 2), claude-opus-5-5

Rebased on `origin/main` (P005 merged): one conflict in `literature/index.md` (rows CGMMS13,
CHK18, PA26, PGPK21, PGPK22), resolved by keeping `main`'s rows and adding this branch's (its
CGMMS13 row only extends `main`'s with the parts read in round 1). Answers to the report of
`referee-scope` (major) on head `863af74`; `referee-proofs` has no newer report than its round-1
acceptance.

## Defects

- **SC2.1 (L), fixed.** Read LS §4.6 in full and Exercises 4.1–4.4 (free online edition, text
  layer). §4.6 (p. 65): the law of $A_1,X_1,\dots,A_n,X_n$ "is the same for all choices
  (Exercise 4.4)", the choices being the canonical, random-table and reward-stack models.
  Exercise 4.4 (p. 69) asks to check condition (b) for the two alternative models, with Doob's
  optional stopping as a hint; Proposition 4.8 (Exercise 4.2) gives uniqueness of the law under
  (a)–(b). Recorded in `literature/notes/LS.md` and `literature/index.md`. Changed: the proof of
  `cor:ucb` (Step 1 opens with "This identification is standard: [LS, §4.6] state it, and its
  proof is their Exercise 4.4. We write it out for a deterministic learner."), the paragraph before
  `cite:ACF02-thm1` (LS state the equivalence), and a new row of `sec:attribution`. The argument
  itself is unchanged.
- **SC2.2 (P), fixed** by the referee's third option: one clause in the renaming paragraph before
  `cite:ACF02-thm1` ("$\pi$ is the number $3.14159\ldots$, not a learner"), and the same words in
  Step 2 of the proof of `cor:ucb`. The display of the cited theorem keeps ACF02's $1+\pi^2/3$, so
  that it can still be compared with the note word for word.

Changed nodes: `cor:ucb` (proof only: Step 1, first sentence; Step 2, one clause). No statement
changed. Text outside nodes: the paragraph before `cite:ACF02-thm1`, `sec:attribution`.

## Choices

- The zeroing argument of Step 1 is kept rather than replaced by a citation alone: LS give no
  printed proof, and the paper's model (`def:learner`, infinite horizon, kernels on histories) is
  not literally LS's finite-horizon one. Zeroing the stack from index $j$ also avoids optional
  stopping at the random index $N_c(t-1)+1$, the route of LS's hint.

## Dead ends

- None new.

# 2026-11-17, revise (repair), claude-opus-5-5

The check "Build and check" failed on `e3a33dc` because the branch was behind `main`: `main`
gained entries C7–C11 in `roadmaps/StochasticBandits/directions.md` (commit `43b0a12`), and
`certify.py check` saw them as removed. Rebased on `origin/main` without conflict;
`certify.py check --base origin/main` passes; both builds compile with no error, no undefined
reference and no duplicate label. No node changed.
