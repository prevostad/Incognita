# DOSSIER of P000 (Batched bandits on an unknown imposed grid: the optimal constant $x^2/\mathcal K_{\inf}$ for every $x \ge 1$)

Refereed and versioned with `paper.tex`, never compiled into the PDF (writing rules of 2026-11-15, D3).
It holds what serves the referees and the owner but not the reader. Version 2 (2026-11-15) moved
here, from the paper of version 1, the roadmap quote and correspondence, the comparison with
KNOWN.md, the derivation attempts ("Why Theorem 1.1 does not follow from these works"), the
consistency checks, the weak points, the web searches and the remarks on what was read of each
source. Numbers "Theorem 1.1", "Section 3", … below are those of the version-1 PDF when quoted from
it; the paper's labels are given everywhere, and the last section maps every label of version 1 to
its place in version 2.

## 1. Roadmap correspondence

`META.toml`: roadmap BatchedBandits, `directions = ["F4", "F1"]`.

### Item F4: the roadmap statement, verbatim

From `roadmaps/BatchedBandits/ROADMAP.md`, Appendix A, "Statements" (as quoted in version 1, items
1–2, completed here with item 3). There $L_\ell = \log t_\ell$, $d_a = K_{\inf}(\nu_a, m^\star)$, and
$y_k$, $\omega$, $\varepsilon_0$ are the objects of HY and of its proof.

> On every grid with $x_\ell \to x \in [1, \infty)$, every $\nu$ with rewards in $[0,1]$ and
> $m^\star < 1$, every suboptimal arm $a$:
>
> 1. **Lower bound, "explore two batches ahead".** Every batched learner that is consistent at batch
>    ends, even one that knows the grid, has
>    - if $x = 1$: $\liminf_\ell \mathbb E N_a(t_\ell)/L_\ell \ge 1/d_a$ (this holds on every grid);
>    - if $x > 1$: $\limsup_\ell \mathbb E N_a(t_\ell)/L_\ell \ge x^2/d_a$, and the same with
>      $\liminf$ if $\mathbb E N_a(t_\ell) = O(L_\ell)$;
>    - for the regret: $\liminf_\ell \mathrm{Reg}(t_\ell)/L_\ell \ge x^2 \sum_{c:\Delta_c>0} \Delta_c / K_{\inf}(\nu_c, m^\star)$
>      when $x = 1$, or when $x > 1$ and every suboptimal count is $O(L_\ell)$.
> 2. **Upper bound.** HY with its default parameters (below) is a deterministic learner of $M_0$,
>    consistent, with $\lim_\ell \mathbb E N_a(t_\ell)/L_\ell = x^2/d_a$ and the matching regret limit.
>    Non-asymptotic forms: for $x = 1$,
>    $\mathbb E N_a(t_L) \le L_L/d_a + (2/d_a + 4c^\star/d_a^2)\,\varepsilon L_L + R_1(\varepsilon)$
>    for every $\varepsilon \in (0, \varepsilon_0]$ and every $L$, with $c^\star := (2-m^\star)/(1-m^\star)$;
>    for $x > 1$, with a constant margin $\omega$,
>    $\mathbb E N_a(t_\ell) \le (1+\omega)(1/d_a + 3c^\star\varepsilon/d_a^2)\,H_\ell + R_x(\varepsilon)$
>    where $H_\ell := \max_{k \le \ell} y_{k-1} L_k$ and $H_\ell/L_\ell \to x^2$. The remainders do
>    not depend on $L$ or $\ell$ and are astronomically large.
> 3. **All rounds.** HY also has $\lim_t \mathbb E N_a(t)/\log t = x^2/d_a$ over all rounds.

### What the paper proves, item by item

- Item 1 is `thm:lower`, (i), (ii) and (iii) respectively; `thm:main`(a) and its regret part restate
  it.
- Item 2, first sentence: `thm:upper` (HY is deterministic and in $\mathcal M_0$ by `def:hy` and
  Properties (i) of Section `sec:algo`); `thm:main`(b) restates it.
- Item 2, the non-asymptotic form for $x = 1$: `prop:fixedC`, with $C_1 = 2/d_a + 4c_\star/d_a^2$
  (`def:constC`); the roadmap's $R_1(\varepsilon)$ is the paper's remainder $\mathcal R^1(\varepsilon)$
  (macro `\RHo`).
- Item 2, the non-asymptotic form for $x > 1$ with a constant margin $\omega$: **not proved in this
  paper**. For $x > 1$ the paper proves only `prop:dyA`, a bound on the $\limsup$ for HY with the
  default (dyadic) margins $\omega^{\mathrm{dy}}_\ell \to 0$, which is what `thm:upper` needs.
- Item 3 (the limit over all rounds): **not proved in this paper**. `prop:dyA` bounds the $\limsup$
  over all rounds when $x > 1$, but neither the matching $\liminf$ over all rounds nor the case
  $x = 1$ over all rounds is proved here.

The PDF states the two gaps in plain words in the Remark "scope: what is not proved here" after
`thm:main` (Section 4.4 of version 2), without item ids.

### Item F1

The one-batch lower bound on every grid ($x = 1$): `lem:onebatch`, with the remark in parentheses of
`thm:lower`(i) (proved in the "Every grid" paragraph of the proof of `thm:lower`).

### Open questions and the items they extend

The `\extends{…}` macro (printed only in the blueprint build) records:

- `oq:remainders` extends D1 and D2 (candidate direction C1 of `directions.md`);
- `oq:liminf` extends F4, item 1 of Appendix A (candidate direction C2);
- `oq:random` extends the setting of the roadmap (random batch ends): a new direction, no item id,
  so no `\extends`.

The statements of the three open questions are unchanged from version 1 (C1 and C2 quote them).

## 2. Closest known (KNOWN.md)

`roadmaps/BatchedBandits/KNOWN.md` has no entry ("None yet" in every section; first line
"Reviewed by owner: no"). There is therefore no KNOWN id to compare with, and no private entry. Version
1 said: "The roadmap states the result of this paper in its Appendix A, from the author's manuscript,
and its known-result item F1 (the one-batch lower bound, $x=1$) is Lemma `lem:onebatch`."

### Honest attempts to derive the main result from the literature

Moved verbatim (up to LaTeX markup) from the paragraph "Why Theorem 1.1 does not follow from these
works" of version 1, section "Closest known". The PDF of version 2 keeps one sentence per work in the
related work of the introduction and in Table 1.

- *The classical change of measure* [LR85], [GMS19, (6)], applied at the ends of the batches, gives
  `lem:onebatch`: the count at $t_\ell$ must already pay for the horizon $t_{\ell+1}$, hence the
  constant $x/\mathcal K_{\inf}(\nu_a,\mathbf m^\star)$ when $x>1$, not $x^2/\mathcal K_{\inf}$. The
  attempt to reach $x^2$ this way fails because this change of measure tilts every reward of $a$; it
  does not use that the allocation of batch $\ell+1$ is decided without the rewards of batch $\ell$.
  `lem:twobatches` tilts only those rewards, towards a distribution of mean exactly $\mathbf m^\star$.
- *Sequential index algorithms* (IMED [HT15], KL-UCB [CGMMS13, GHMS22]) attain $1/\mathcal K_{\inf}$
  when the feedback is immediate. On imposed batches their statistics are frozen at $t_\ell$; when
  $x>1$ a batch lasts about $t_\ell^{\,x}$ rounds, so a wrong decision taken at $t_\ell$ (for instance
  an optimal arm judged sub-optimal) costs a power of $t_\ell$. The test of HY makes such mistakes
  summable after multiplication by the batch size, thanks to a strict gain in the deviation
  inequalities (`lem:single`, `lem:pair`); its paced plan aims at the test that will be made two
  batches later; its IMED phase and its consistency threshold keep the leader and the test reliable
  when $x=1$.
- *Batched bandits with a chosen grid* [PRCS16, GHRZ19], [EKMM21] design the batch ends. Their
  algorithms do not apply when the ends are imposed and revealed only when they happen, and their
  lower bounds ([PRCS16, Theorem 4], [GHRZ19, Section 3]) are minimax bounds in terms of the number of
  batches; they do not give the instance-dependent constant at imposed batch ends.
- *Static grids and anytime learners* [JTXHXG21, Theorem 4]: for one-parameter exponential families
  (a unique best arm, bounded variance), for every static grid and every $c>0$, no anytime
  algorithm attains the asymptotically optimal regret with at most $c\log\log T$ batches (paraphrase;
  version 1 quoted the theorem), asymptotic optimality meaning there that $\lim_T R_T/\log T$ equals the constant
  $\sum_i\Delta_i/\mathrm{kl}(\mu_i,\mu_1)$ along all rounds $T$. A grid with $x_\ell\to x>1$ has about
  $\log\log T/\log x$ batch ends below $T$, so Theorem 4 implies, for these families, that the
  sequential constant is not attained on such a grid: this is a qualitative special case of
  `thm:lower`(ii). It is presented by its authors as a confirmation of a conjecture of Besson and
  Kaufmann [BK18, Section 6] (stated there for the exponential doubling trick). Its proof
  [JTXHXG21, Appendix C] is the one-batch change of measure: inside a gap between two batch ends
  $t_j<t_{j+1}$ it takes two times $N_n<N_{n+1}=N_n^{x'}$ with $x'=e^{1/(4c)}$, changes the mean of one
  arm only, on the observations up to $t_j$, and applies the Bretagnolle–Huber inequality; this gives
  a count at $t_j$ at least $x'(1-\epsilon')/(\mathrm{kl}(\mu_i,\mu_1)+\epsilon')$ times $\log t_j$
  along a subsequence of ends, and no quantitative factor is stated. With $N_{n+1}$ just below
  $t_{j+1}$, the same argument gives at most the factor $\log t_{j+1}/\log t_j\to x$, that is the bound
  of `lem:onebatch`, not the factor $x^2$. `thm:lower`(ii) does not follow, for three reasons: the
  factor $x^2$ needs the change of measure of `lem:twobatches`, which tilts only the rewards of $a$ in
  one batch towards a law of mean exactly $\mathbf m^\star$, whereas moving the mean of every reward of
  $a$ cannot give more than $x$; Theorem 4 is about exponential families and kl, not about all
  distributions on $[0,1]$ and $\mathcal K_{\inf}$ (with any number of optimal arms); and it does not
  give the constant $x^2/\mathcal K_{\inf}$, which is the content of `thm:lower`(ii). It is a lower bound
  only, so `thm:upper` does not follow from it either.
- *Imposed batches with Thompson sampling* [KO21b, Theorem 1]: only grids with $x=1$, and the constant
  $2/\Delta_a$ of Gaussian rewards of unit variance, which is not the optimal constant for rewards in
  $[0,1]$.
- *Delayed feedback* [JGS13, Theorem 6]: the reduction preserves optimality only for batches of size
  $o(\log t)$, so not when $x>1$.
- *The companion manuscript* [P26] (unpublished; imposed batch sizes, a batched IMED and a plan
  computed from a known grid): every result used from it is proved again here.

## 3. Sanity checks

- Degenerate cases and an explicit instance: in the paper, Section `sec:examples` (batches of size
  one, where HY is IMED; the Bernoulli instance $\mathrm{Ber}(1/2)$, $\mathrm{Ber}(3/10)$ with
  $\approx48.6\log t_\ell$ on $t_\ell=2^{2^\ell}$ and $\approx12.2\log t_\ell$ on $t_\ell=2^{\ell+1}$;
  the constant finite and positive; the boundary $\mathbf m^\star=1$; several optimal arms and ties;
  every arm observed). Version 2 adds one worked number there: on $t_\ell=2^{2^\ell}$ the one-batch
  bound `lem:onebatch` alone forces $2\log t_\ell/d_a\approx24.3\log t_\ell$ (an instance of
  `lem:onebatch` with $\log t_{\ell+1}=2\log t_\ell$, not a new result).
  Arithmetic: $d_a=\mathrm{kl}(0.3,0.5)=0.3\log0.6+0.7\log1.4\approx0.08228$, $4/d_a\approx48.61$,
  $2/d_a\approx24.31$, $1/d_a\approx12.15$.
- Consistency with the `[Lean]` entries of KNOWN.md: KNOWN.md of BatchedBandits has no entry, hence
  no `[Lean]` entry.
- Consistency with the roadmap: the statements agree with Appendix A, items 1–2, of the roadmap
  (section 1 above), and with the author's own Lean statements (section 7 below).

## 4. Weak points

Moved verbatim from the section "Weak points" of version 1 (label `sec:weak`, removed from the
paper; its content is summarised for the reader in "Where the difficulty lies", Section
`sec:overview`).

The independent verifications (by AI agents) found no error; these are the steps where an error would
be the hardest to see.

1. `lem:twobatches`, Steps 3–4: the order of the limits ($\ell\to\infty$, then $b\to\infty$, then
   $C\to\infty$), with constants that depend on $C$ through the tilt, and the reason why the two
   instances $\nu^{\rho^-_s}$ and $\nu^{\rho^+_s}$ are used instead of $\nu$ itself. This is also where
   the logarithmic counts of `thm:lower`(ii) enter.
2. `lem:amb` (a sub-optimal arm passes the consistency test): the bound on the probability that $a$
   is ambiguous at the start of an activated batch, of order $e^{-c\sqrt{L_\ell}/\log^2L_\ell}$, and
   its summability through `lem:sparse`; the constants of its Steps 5–7.
3. `lem:W` (the IMED phase lifts the water level) and the chain argument of the case $x=1$
   (`lem:levelC`, `lem:fewC` and `lem:optW`), which must hold from some rank on for every grid with
   $x_\ell\to1$, including short batches alternating with long ones.

## 5. Searches

The revision of version 2 of 2026-11-16 ran no web search. The scope report of 2026-11-16 found, with
its own queries (listed in that report), one concurrent work: Qiao and Wu, *Adversarially Batched
Online Learning*, arXiv:2611.17500 (12 November 2026), stochastic bandits whose batch ends are imposed
by an adversary, with hardness $\alpha=\max_jb_j/t_{j-1}$; its bounds are orders of magnitude in
$\alpha$ (Theorem 1, $O(\min\{T,\alpha\log(NT)\sum_i1/\Delta_i\})$; Theorem 4, a lower bound
$\Omega(\alpha^{3/2}\sum_i1/\Delta_i)$), with no first-order constant, and $\alpha$ is unbounded when
$x>1$. It neither implies nor is implied by the theorems of P000 (the referee's reading of §1.2.1).
It is not cited in the paper: the referee asked the owner whether to cite it (Ask-owner), and the
revision waits for the answer (no note in `literature/notes/` yet).

Version 2 (presentation revision, 2026-11-15) ran no web search. Moved verbatim from the paragraph
"Searches" of the section "Attribution" of version 1:

The conversion of 2026-11-14 ran no web search. The revision of 2026-11-14 read the sources above on
the web (the PDFs of HT10, GMS19 arXiv v3, KCG16, JTXHXG21 and its supplement, BK18, GHRZ19 arXiv v3,
PRCS16 arXiv v3, KO21b, JGS13 arXiv v2; the abstract of H60; the account of L83, Theorem 3, in Bartroff
and Tartakovsky, arXiv:2403.18782, Section 2.5), and reuses the queries of the scope report of
2026-11-14, all run on that date, with what they found:

- "batched bandits imposed batch sizes fixed grid asymptotic lower bound Lai Robbins constant"
  (PRCS16, GHRZ19, no constant on imposed grids);
- "stochastic bandit feedback revealed at exogenous batch ends unknown in advance asymptotically
  optimal regret log t" (EKMM21, nothing on unknown imposed ends);
- "Kalkanli Ozgur asymptotic performance Thompson sampling batched multi-armed bandits batch size
  condition" (KO21b);
- "bandits delayed feedback asymptotic lower bound regret constant depends on delay growth
  polynomial delays Lai Robbins" and "bandit with delayed feedback delay proportional to time
  t^beta regret lower bound increases factor" (constant or i.i.d. delays only);
- "multi-armed bandit unknown horizon doubly exponential checkpoints regret constant factor lower
  bound anytime doubling trick" (BK18; JTXHXG21, Theorem 4);
- "batched bandit exponential time grid regret constant b^2 lower bound K_inf IMED batched" (no $b^2$
  constant found);
- "explore two batches ahead bandit lower bound grid" (no hit);
- "Prevost batched bandits imposed grid IMED K_inf 2026 arXiv" (no public version);
- "Lorden 1983 asymptotic efficiency three-stage hypothesis tests last stage negligible" (L83, and
  its account in arXiv:2403.18782);
- "Hoeffding 1960 lower bounds for the expected sample size and the average risk of a sequential
  procedure intermediate distribution" (H60);
- "lower bound batched bandit change of measure only rewards of last batch intermediate
  distribution" (GHRZ19, Lemmas 2–5);
- "Honda Takemura 2010 COLT bounded support models K_inf dual Theorem 8 Lemma 2" (HT10; the numbering
  of HT15 and of arXiv:2111.09724);
- "OSSB Combes Magureanu Proutiere exploration rule (1+gamma) log t tracking" (CMP17, Algorithm 1);
- "adaptive treatment allocation grouped responses group sequential multi-armed bandit asymptotic
  regret" (nothing with a sharp constant);
- "non-asymptotic regret bound batched bandit unknown grid second order term explicit K_inf" (AJK21;
  nothing on unknown grids);
- "batched bandits random batch sizes revealed online" and "bandits feedback at random times
  renewal process batch ends" (only KO21b);
- "lower bound liminf expected number of pulls consistent policy without assumption logarithmic
  regret batched or delayed" (nothing on the batched $\liminf$).

The second revision (2026-11-14) reuses two queries of the second scope report, with what they found:
"K_inf regularity proof mixture Dirac mass point x close to 1 increase mean continuity Honda Takemura"
(GHMS22, Appendix B.1, read on ar5iv) and "round-robin scheduling lemma deficits of several arms
C-tracking lemma Garivier Kaufmann" (GK16, Lemmas 7 and 15, read on ar5iv); it read the PMLR page of
GK16 for its metadata.

## 6. Reading notes on the citations

What was read of each source is recorded in `literature/index.md` (column "Read"). Version 1 marked
"(to be checked)" every citation of an entry with no part recorded as read (14 occurrences in the
PDF). Version 2 removed every "(to be checked)", as follows.

| Key | Read (literature/index.md) | Version 2 |
|---|---|---|
| LR85 | nothing recorded | classic (Lai–Robbins), cited as is for the change of measure |
| H63 | nothing recorded | classic (Hoeffding's inequality), cited as is (`lem:hoeffding` and Appendix A) |
| LS | §9.2, §15.1 Lemma 15.1, §16, §25, §36 notes; not §4.6 | classic (Lattimore–Szepesvári), cited as is for reward stacks (§4.6, `def:stacks`, proof of `lem:stacks`) and the chain rule (Lemma 15.1) |
| BK96 | abstract only | classic (Burnetas–Katehakis, listed in AGENTS.md §5.2), cited as is for the sequential lower bound: "[BK96, Proposition 1], as recalled by [HT10, (2)]" in Section 2 ("Sequential bandits on [0,1]"), Table 1, the paragraph "The classical sequential result" of Section 5 and the Examples ("Batches of size one"); [HT10, Theorem 8] for the identification of the divergence with the dual formula. HT10 §2 introduces (2) as "Proposition 1 (Proposition 1 of Burnetas and Katehakis (1996))" (read by the scope referee on 2026-11-16 and recorded in index.md as read: "§2 definition of $D_{\inf}$, (2)"). The first submission of v2 had weakened BK96 to "see also" (SC1.1 of the scope report of 2026-11-16) |
| EKMM21 | not read | "see also" (Motivation; chosen-grid paragraph) |
| JXXG21 | not read | "see also" (chosen-grid paragraph) |
| KMS21 | not read | "see also … for Thompson sampling" (the title says so) |
| P26 | not read (the author's own unpublished manuscript) | "see also" in three places: everything used from it is proved again here; the water-level technique comes from it (the author's statement, as in his readable version); the attribution row |
| LS17 | §1–4, Theorem 10 statement, §8–9 (not the algorithm sections) | dropped (it was "also [LS17] (to be checked)" in the attribution row of the paced targets) |
| H60 | abstract | kept: "evaluating the expected sample size at a parameter between the two hypotheses goes back to Hoeffding [H60]" rests on the abstract |
| L83 | proof of Theorem 3 and inequality (23), pp. 134–137 (agent for the owner, 2026-11-11); in revision 1, checked against Bartroff–Tartakovsky, arXiv:2403.18782, §2.5 | kept, as in version 1 |

Other remarks on the cited results:

- [HT10, Theorem 8] is restated in `cite:honda2010asymptotically-primal` in the paper's notation, with
  the renaming line before it and the verbatim text in a LaTeX comment inside the node (the verbatim
  statement stays in `literature/notes/HT10.md`). Its consequence for $\mathcal K_{\inf}$ (sup over the
  half-open interval $\Lambda(\mu)$ instead of max over the closed one), which version 1 derived in the
  remark "How it is used" after the node, is now `lem:primal`, proved from the cited node by the same
  argument (concavity at the closed end): rule D5 ("a consequence of a cited result that the source
  does not print is a lemma of the paper"), and D8 allows a node for a step that was inline. The proof
  of `lem:onebatch` now uses `lem:primal` (its `\uses` lists `lem:primal` instead of the cited node).
- The parenthesis "Lemma 2 of [HT10] states the strict form, but as printed only for $\mu<0$; it is
  not used here" is kept in the paper (Appendix A), since it explains why the strict form is derived.
- [GMS19, Lemma 1] is restated with $Z:\Gamma\to[0,1]$; the source prints $Z:\Omega\to[0,1]$, a
  misprint ($\Gamma$ is meant), recorded in `literature/notes/GMS19.md`.
- Table 1 of the paper (comparison of constants) only uses parts recorded as read, and the classic BK96: [BK96, Proposition 1], [HT15], [CGMMS13],
  [GHMS22], [HT10, (2)], [GMS19, (6)], [JTXHXG21, Theorem 4], [BK18, Remark 8], [KO21b, Theorem 1],
  [JGS13, Theorem 6]. The theorem of [JTXHXG21] is paraphrased in the paper and in section 2.

## 7. Formal verification (moved from the paper) and the author line

Version 1 said, in its Subsection "Formal verification" (label `sec:lean`), in its Contributions and
in its Discussion:

> The author verified Theorems `thm:lower`, `thm:upper` and `thm:main` in a private Lean 4 project
> (Mathlib and LeanMachineLearning, no `sorry`, axioms `propext`, `Classical.choice`, `Quot.sound`),
> for HY with any fixed tie rules, the remainders being existential. Those Lean statements write
> $\liminf\ge L$ as "for every $c<L$, eventually $c\le u_\ell$", $\limsup\ge L$ as "for every $c<L$,
> $c<u_\ell$ for infinitely many $\ell$", and limits as convergences. The Lean proof follows the
> architecture of the proofs below, but many lemmas are formalized in a different form, so the proofs
> are not claimed verified as written. That project is not part of this library: formalising this
> paper here (frozen statements, then proofs) is the next step, and only the library's audit can mark
> a node as verified.

Version 1 also said, in Properties (ii) of the algorithm, that "the Lean theorems hold for any rules
satisfying their specification, with any order of batch 1 in which every arm is pulled"; version 2
keeps only the paper's own claim ("the proofs do not use these rules").

Version 2 removes these claims from the text (rule: no Lean claim that the reader cannot check). The
subsection `sec:lean` now says, for a reader who does not know the library (revision of 2026-11-16,
SC1.7): the statements are written to be translated into Lean 4, a second build lists the uses of
every proof, a green box LEAN APPROVED marks a statement whose Lean translation (compared with the
printed statement by a referee) is proved in Lean, the box certifies the statement and not the printed
proof, and no claim rests on a formal proof the reader cannot check. No statement of P000 is
formalised in the library yet (no file under `Statements/`).

**Open point for the owner: the `\author` line.** The `\author` line of version 1 is kept byte for
byte (rule: `human_authors` and the `\author` line never change). Its `\thanks` footnote still reads
"Submitted by its author to the Incognita library (roadmap BatchedBandits, item F4) on 2026-11-14. …
The author verified the main statements in a private Lean 4 project (Subsection `sec:lean`)." It
therefore keeps, in the PDF, a roadmap id (F4) and the private-Lean claim that the rest of the
revision removes, and it points to `sec:lean`, which is why that label is kept. Only the owner can
decide whether the footnote may be shortened (for instance to "Refereed by AI agents (accepted on
2026-11-15); not yet formalised in this library.").

## 8. Presentation revision v2: what changed

Done on 2026-11-15 (role revise, Claude Opus 5.5), from version 1 and the author's readable version
of 4 November 2026 (the frame and the prose).

- **Frame of the author's readable version restored.** 1 Introduction (Motivation; Setting in a
  nutshell; Contributions; The algorithm in a nutshell; Related work; Techniques; Outline),
  2 Setting, 3 The algorithm HY, 4 Results (lower bound, upper bound, optimality, discussion, formal
  verification), 5 How the proofs work, 6 Examples and special cases, 7 Open questions, references,
  then `\appendix`: A Results from the literature, B Tools, C Lower bound, D Deterministic
  properties of HY, E Upper bound $x>1$, F Upper bound $x=1$, G End of the proof of `thm:upper`,
  H Sources of the techniques, I Notation. The proof appendices B–G are the author's appendices
  A–F, in his order and with his text (version 1 had them as body sections 5–10).
- **Results in the author's order**: `thm:lower` (4.1), `thm:upper` (4.2), then `thm:main` (4.3),
  which is the author's Corollary 4 (it was Theorem 1.1 on page 1 of version 1); it stays a
  `theorem` environment with the label `thm:main`, and its proof follows it. The introduction points
  to the three of them. `thm:main` is on page 8 of the reader PDF, after the setting and the
  algorithm, which its statement uses; the informal statement with the constant is on page 2
  (Contributions).
- **Prose**: the author's prose verbatim wherever the content is the same (abstract, introduction
  paragraphs, setting, algorithm, comments, properties, results, discussion, how the proofs work,
  appendix plans). New prose: the related work (from version 1's "Closest known", rewritten as a
  comparison with one sentence per work on why it does not give the result, and Table 1), the
  "Techniques" paragraph, the Remarks "constants" and "scope", "Structure" and "Where the difficulty
  lies" in Section 5, the Examples section (from version 1's "Sanity checks").
- **Restored from the readable version**: the `algorithm`/`algpseudocode` pseudo-code (Algorithm 1,
  label `alg:hy`; version 1 had a `tabbing` box), the two TikZ dependency graphs of Appendices E and F
  (version 1 had lists "B ← A₁; A₂"), the boxed Setting/Goal/Plan blocks (`tcolorbox` environment
  `setgoal`, 24 boxes, at exactly the places of the readable version; version 1 had unboxed
  paragraphs), "appendix" instead of "section" in the appendix plans, the notation tables
  (`booktabs`, split in two tabulars; no `longtable`, which is not in the allowed packages).
- **Assumption on the grid**: `def:ass-x` keeps its label and its kind (definition). To stop a
  hypothesis from being typeset as a definition, it now defines a *convergent grid with limit
  $x\in[1,\infty)$* ($x_\ell\to x$), and `thm:lower`, `thm:upper`, `lem:H` say "let the grid be
  convergent with limit $x$ (Definition 2.2)". The `assumption` environment is not used: changing the
  environment would change the node kind.
- **Cited results** (Appendix A): restated in the paper's notation with a renaming line (rule D5);
  new `lem:primal` (see section 6).
- **Moved to this dossier**: the roadmap quote and correspondence, "What is proved here, item by
  item", the KNOWN comparison, the derivation attempts, the Lean statements, "Consistency with the
  roadmap", Weak points, Searches.
- **Small edits**: no "(to be checked)" (section 6); headings `\paragraph{(i)…}` inside the proofs of
  `thm:lower` and `thm:upper` became bold run-in headings (a `\paragraph` right after
  `\begin{proof}` no longer compiles now that the reader build prints nothing for `\uses`), and the
  duplicate end-of-proof square of `thm:lower` was removed; the two facts of the proof of
  `lem:service` are named (Q1), (Q2) instead of (F1), (F2), so that no string of the paper reads like
  a roadmap item; the Setting/Goal box of the proof of `thm:upper` is placed before "Proof." as in the
  readable version.
- **Not changed**: every statement and proof of the appendices (except the edits above), every
  `\uses` (except the proof of `lem:onebatch`), the 10pt font and 2.3 cm margins, the hyperlinked
  symbols.
- Builds: reader PDF 63 pages (main text pp. 1–12 including the references), blueprint PDF 66 pages;
  no error, no undefined reference, no duplicate label. Version 1: 66 pages.

### Revision of 2026-11-16 (answer to the reports of round 1)

Presentation only; no statement, hypothesis or conclusion changed, no node added or removed.

- **Attribution of the sequential lower bound (SC1.1)**: [BK96, Proposition 1], "as recalled by
  [HT10, (2)]", and [HT10, Theorem 8] for the dual formula, in Section 2, Table 1 and the Examples;
  section 6 above.
- **Citations (SC1.2)**: `natbib` (`round`) and `plainnat`, `\citet`/`\citep`/`\citealp` with the
  same keys and loci; the titles of the two cited nodes read "From [author (year), part], …" as in
  the template.
- **Related work (SC1.3)**: the related work and the techniques are now Section 2, "Related work and
  context" (`sec:related`), with run-in paragraphs (sequential bandits on [0,1], chosen grids, imposed
  batches, delayed feedback, multi-stage tests, techniques), then "Closest related work" (label
  `sec:closest` moved there: the one-batch change of measure, and Jin et al. with Besson–Kaufmann),
  Table 1, and a new paragraph "Gap with the literature". The paragraphs are the text of the first
  submission of v2, moved; the paragraph on the classical change of measure was split between
  "Sequential bandits" and "Closest related work". "Contributions." became "Our contributions."; the
  Outline names Section 2.
- **Numerical experiments (SC1.4)**: a paragraph "Why no numerical experiments" ends Section 7
  (existential and astronomical remainders; four batch ends below 10^9 on the doubly exponential grid;
  no activated batch on the geometric grid, so a run would show a batched IMED; the lower bound cannot
  be simulated).
- **Opening sentences (SC1.5)**: Sections 3 (Setting), 5 (Results), 7 (Examples); Section 8 is now
  "Conclusion and open questions" and opens with the result and its limitations (pointer to the scope
  remark, Subsection 5.4, new label `sec:discussion`); "Plan." of Appendices B, D, E, F capitalised.
- **Symbols (SC1.6)**: the water level of Definition D.4 is $\mathcal W_j$ (macro `\Lam`, formerly
  $\Lambda_j$); the activation round of Definition 4.1 is $\bar t_\ell$ (macro `\tauA`, formerly
  $\tau_\ell$); the local scaling factor of Lemma B.1(vi), of the proof of Lemma B.5, of Lemma B.10 and
  of the proofs of Lemmas B.9 and B.10 is $\varpi$ (formerly $\tau$). $\tau_n$ (grid of
  Definition B.4) and $\Lambda(\mu)$, $\widehat\Lambda_\ell$ keep their names, each with one meaning.
- **Formal verification (SC1.7)**: Subsection 5.5 reworded for an outside reader (section 7 above).
  The `\author` footnote is unchanged (the owner's line): see the open point in section 7.
- **Classical result and pseudo-code (SC1.8)**: a paragraph "The classical sequential result" opens
  Section 5 (the lower bound $1/\mathcal K_{\inf}$ of [BK96, Proposition 1] with the display, attained
  by IMED and KL-UCB); Algorithm 1 uses the link macros of the symbols.
- **SC1.9** (concurrent work Qiao–Wu): not added, pending the owner's answer (section 5 above).
- **PF1.2**: the remark of `def:kinf` says "for $\mu\in[0,1)$". **PF1.3**: the `\Require` line of
  Algorithm 1 states the conditions of Definition 4.1 on $\omega,\vartheta,\gamma$ and points to it.
  **PF1.1**: no change (the section label `sec:weak` was removed with its section in the first
  submission of v2; it is never reused).

Nodes whose text changed in this revision (wording or notation only): `def:kinf` (PF1.2),
`def:hy` (the symbol $\bar t_\ell$), `lem:kinf`(vi) and its proof, `lem:grid` (proof),
`lem:lowerdev` (proof), `lem:upperdev` (statement and proof) (the symbol $\varpi$); the symbol $\mathcal W$ of the water
level, through its macro, in the statements of `def:water`, `def:high`, `lem:W`, `lem:lowmass`,
`lem:highC` and in the proofs of `lem:W`, `lem:lowmass`, `lem:highC`, `lem:levelC`, `lem:goodhigh`,
`lem:logcountC`; `lem:sparse` (proof, $\bar t_\ell$); and the titles of
`cite:honda2010asymptotically-primal` and `cite:garivier2019explore-dataprocessing`.

## 9. Presentation revision v2: statement correspondence

Numbers of version 2 as revised on 2026-11-16: the new Section 2 (Related work and context) moved the
main-text sections 2–7 to 3–8; the appendix numbers did not change. The column "v2 number" gives the
revised numbers; the status texts quote the numbers of the first submission of version 2.

Every label of version 1 (`git show origin/main:papers/P000-hy-unknown-imposed-grid/paper.tex`, 173
labels, 81 environments of which 78 nodes and 3 open questions), in the order of version 1, with its
number in the version-1 PDF and in the version-2 reader PDF. "Statement identical" means identical up
to whitespace, `\uses`, `\label`/`\dt` anchors and the syntax of list labels (`\item[(i)]` versus
`enumitem` labels, which print the same). Kinds: no node changed environment, no node was removed.
The proofs are unchanged except those listed in section 8 (`lem:hoeffding`, `lem:stacks`: "(to be
checked)" removed; `lem:onebatch`: `lem:primal` and Lemma A.3 named; `lem:tilts`, `lem:fewC`:
boxes; `thm:lower`, `thm:upper`: headings and box placement; `lem:service`: its two facts named (Q1),
(Q2) instead of (F1), (F2)).

| v1 label | kind | v1 number | v2 number | status |
|---|---|---|---|---|
| `sec:main` | section | 1 | 5 | kept: v1 "Main result", v2 "Results" |
| `sec:intro` | section | 1 | 1 | kept: v1 "Main result", v2 "Introduction" |
| `thm:main` | Theorem | 1.1 | 5.3 | unchanged; now placed after thm:lower and thm:upper (the author's order), still a theorem environment, proof right after it |
| `sec:lean` | section | 1.1 | 5.5 | kept: v1 "Formal verification", v2 "Formal verification" |
| `sec:setting` | section | 2 | 3 | kept: v1 "Setting", v2 "Setting" |
| `def:grid` | Definition | 2.1 | 3.1 | statement identical |
| `def:ass-x` | Definition | 2.2 | 3.2 | reworded as a definition ("the grid is convergent, with limit x in [1,oo), if x_l -> x"); the theorems say "let the grid be convergent with limit x" instead of "satisfy Assumption 2.2 with x": same hypothesis |
| `def:model` | Definition | 2.3 | 3.3 | statement identical |
| `def:kinf` | Definition | 2.4 | 3.4 | definition unchanged; only the citation remark points to Lemma A.2 (lem:primal) and Step 1 of the proof of lem:onebatch |
| `def:learner` | Definition | 2.5 | 3.5 | statement identical |
| `def:M0` | Definition | 2.6 | 3.6 | only the cross-reference sec:results -> sec:main (same section) |
| `def:stacks` | Definition | 2.7 | 3.7 | "(to be checked)" removed after the classic [LS, Section 4.6] |
| `sec:algo` | section | 2.1 | 4 | kept: v1 "The algorithm HY", v2 "The algorithm HY" |
| `def:hy` | Definition | 2.8 | 4.1 | "Theorem 4.2 and Theorem 1.1(b)" -> "Theorems 4.2 and 4.3(b)" in the parenthesis on the defaults; enumerate labels by enumitem (same (1)-(7)) |
| `def:hy-vocab` | Definition | 2.9 | 4.2 | statement identical |
| `sec:closest` | section | 3 | 2 (paragraph "Closest related work") | kept: v1 "Closest known", v2 "Related work" |
| `sec:proofs` | section | 4 | 6 | kept: v1 "Proofs", v2 "How the proofs work" |
| `sec:results` | section | 4 | 5 | kept: v1 "Proofs", v2 "Results" |
| `thm:lower` | Theorem | 4.1 | 5.1 | "satisfy Assumption 2.2 with x" -> "be convergent with limit x (Definition 2.2)" |
| `thm:upper` | Theorem | 4.2 | 5.2 | same rewording as thm:lower |
| `sec:how` | section | 4.3 | 6 | kept: v1 "How the proofs work", v2 "How the proofs work" |
| `sec:app-tools` | section | 5 | B | kept: v1 "Tools", v2 "Tools" |
| `lem:kinf` | Lemma | 5.1 | B.1 | statement identical |
| `lem:pseudo` | Lemma | 5.2 | B.2 | statement identical |
| `lem:hoeffding` | Lemma | 5.3 | B.3 | statement identical |
| `def:empkinf` | Definition | 5.4 | B.4 | statement identical |
| `lem:grid` | Lemma | 5.5 | B.5 | statement identical |
| `lem:single` | Lemma | 5.6 | B.6 | statement identical |
| `lem:pair` | Lemma | 5.7 | B.7 | statement identical |
| `lem:theta` | Lemma | 5.8 | B.8 | statement identical |
| `lem:lowerdev` | Lemma | 5.9 | B.9 | statement identical |
| `lem:upperdev` | Lemma | 5.10 | B.10 | statement identical |
| `lem:stacks` | Lemma | 5.11 | B.11 | statement identical |
| `sec:app-sums` | section | 5.4 | B.4 | kept: v1 "Elementary sums and sequences", v2 "Elementary sums and sequences" |
| `lem:sums` | Lemma | 5.12 | B.12 | statement identical |
| `lem:diag` | Lemma | 5.13 | B.13 | statement identical |
| `lem:distinct` | Lemma | 5.14 | B.14 | statement identical |
| `lem:chain` | Lemma | 5.15 | B.15 | statement identical |
| `sec:pf-lem:kinf` | section | 5.5 | B.5 | kept: v1 "Proof of Lemma~\ref {lem:kinf}", v2 "Proof of Lemma~\ref {lem:kinf}" |
| `sec:pf-lem:pseudo` | section | 5.6 | B.6 | kept: v1 "Proof of Lemma~\ref {lem:pseudo}", v2 "Proof of Lemma~\ref {lem:pseudo}" |
| `sec:pf-lem:hoeffding` | section | 5.7 | B.7 | kept: v1 "Proof of Lemma~\ref {lem:hoeffding}", v2 "Proof of Lemma~\ref {lem:hoeffding}" |
| `sec:pf-lem:grid` | section | 5.8 | B.8 | kept: v1 "Proof of Lemma~\ref {lem:grid}", v2 "Proof of Lemma~\ref {lem:grid}" |
| `sec:pf-lem:single` | section | 5.9 | B.9 | kept: v1 "Proof of Lemma~\ref {lem:single}", v2 "Proof of Lemma~\ref {lem:single}" |
| `sec:pf-lem:pair` | section | 5.10 | B.10 | kept: v1 "Proof of Lemma~\ref {lem:pair}", v2 "Proof of Lemma~\ref {lem:pair}" |
| `sec:pf-lem:theta` | section | 5.11 | B.11 | kept: v1 "Proof of Lemma~\ref {lem:theta}", v2 "Proof of Lemma~\ref {lem:theta}" |
| `sec:pf-lem:lowerdev` | section | 5.12 | B.12 | kept: v1 "Proof of Lemma~\ref {lem:lowerdev}", v2 "Proof of Lemma~\ref {lem:lowerdev}" |
| `sec:pf-lem:upperdev` | section | 5.13 | B.13 | kept: v1 "Proof of Lemma~\ref {lem:upperdev}", v2 "Proof of Lemma~\ref {lem:upperdev}" |
| `sec:pf-lem:stacks` | section | 5.14 | B.14 | kept: v1 "Proof of Lemma~\ref {lem:stacks}", v2 "Proof of Lemma~\ref {lem:stacks}" |
| `sec:pf-lem:sums` | section | 5.15 | B.15 | kept: v1 "Proof of Lemma~\ref {lem:sums}", v2 "Proof of Lemma~\ref {lem:sums}" |
| `sec:pf-lem:diag` | section | 5.16 | B.16 | kept: v1 "Proof of Lemma~\ref {lem:diag}", v2 "Proof of Lemma~\ref {lem:diag}" |
| `sec:pf-lem:distinct` | section | 5.17 | B.17 | kept: v1 "Proof of Lemma~\ref {lem:distinct}", v2 "Proof of Lemma~\ref {lem:distinct}" |
| `sec:pf-lem:chain` | section | 5.18 | B.18 | kept: v1 "Proof of Lemma~\ref {lem:chain}", v2 "Proof of Lemma~\ref {lem:chain}" |
| `sec:app-lower` | section | 6 | C | kept: v1 "Proof of the lower bound (Theorem~\ref {thm:lower})", v2 "Proof of the lower bound (Theorem~\ref {thm:lower})" |
| `cite:honda2010asymptotically-primal` | Lemma | 6.1 | A.1 | restated in the paper's notation (KL, E, lambda for the dual variable), preceded by the renaming line; verbatim text in a comment and in literature/notes/HT10.md; equivalent (same range mu < 1, same max over the closed interval) |
| `cite:garivier2019explore-dataprocessing` | Lemma | 6.2 | A.3 | restated: P, E, KL, kl macros; domain of Z written Gamma (the source prints Omega, a misprint recorded in notes/GMS19.md); equivalent |
| `sec:app-lb-one` | section | 6.1 | C.1 | kept: v1 "One batch ahead", v2 "One batch ahead" |
| `lem:onebatch` | Lemma | 6.3 | C.1 | statement identical |
| `sec:app-lb-two` | section | 6.2 | C.2 | kept: v1 "Two batches ahead", v2 "Two batches ahead" |
| `def:tilt` | Definition | 6.4 | C.2 | statement identical |
| `lem:tilts` | Lemma | 6.5 | C.3 | statement identical |
| `def:Q` | Definition | 6.6 | C.4 | statement identical |
| `lem:com` | Lemma | 6.7 | C.5 | statement identical |
| `lem:typ` | Lemma | 6.8 | C.6 | statement identical |
| `lem:twobatches` | Lemma | 6.9 | C.7 | statement identical |
| `sec:app-lb-assembly` | section | 6.3 | C.3 | kept: v1 "Proof of Theorem~\ref {thm:lower}", v2 "Proof of Theorem~\ref {thm:lower}" |
| `sec:pf-lem:onebatch` | section | 6.4 | C.4 | kept: v1 "Proof of Lemma~\ref {lem:onebatch}", v2 "Proof of Lemma~\ref {lem:onebatch}" |
| `sec:pf-lem:tilts` | section | 6.5 | C.5 | kept: v1 "Proof of Lemma~\ref {lem:tilts}", v2 "Proof of Lemma~\ref {lem:tilts}" |
| `sec:pf-lem:com` | section | 6.6 | C.6 | kept: v1 "Proof of Lemma~\ref {lem:com}", v2 "Proof of Lemma~\ref {lem:com}" |
| `sec:pf-lem:typ` | section | 6.7 | C.7 | kept: v1 "Proof of Lemma~\ref {lem:typ}", v2 "Proof of Lemma~\ref {lem:typ}" |
| `sec:pf-lem:twobatches` | section | 6.8 | C.8 | kept: v1 "Proof of Lemma~\ref {lem:twobatches}", v2 "Proof of Lemma~\ref {lem:twobatches}" |
| `sec:app-det` | section | 7 | D | kept: v1 "Deterministic properties of HY", v2 "Deterministic properties of HY" |
| `lem:imedround` | Lemma | 7.1 | D.1 | statement identical |
| `def:backlog` | Definition | 7.2 | D.2 | statement identical |
| `lem:service` | Lemma | 7.3 | D.3 | statement identical |
| `sec:app-water-det` | section | 7.2 | D.2 | kept: v1 "The IMED prelude lifts the water level", v2 "The IMED prelude lifts the water level" |
| `def:water` | Definition | 7.4 | D.4 | statement identical |
| `lem:W` | Lemma | 7.5 | D.5 | statement identical |
| `lem:sparse` | Lemma | 7.6 | D.6 | statement identical |
| `sec:pf-lem:imedround` | section | 7.3 | D.3 | kept: v1 "Proof of Lemma~\ref {lem:imedround}", v2 "Proof of Lemma~\ref {lem:imedround}" |
| `sec:pf-lem:service` | section | 7.4 | D.4 | kept: v1 "Proof of Lemma~\ref {lem:service}", v2 "Proof of Lemma~\ref {lem:service}" |
| `sec:pf-lem:W` | section | 7.5 | D.5 | kept: v1 "Proof of Lemma~\ref {lem:W}", v2 "Proof of Lemma~\ref {lem:W}" |
| `sec:pf-lem:sparse` | section | 7.6 | D.6 | kept: v1 "Proof of Lemma~\ref {lem:sparse}", v2 "Proof of Lemma~\ref {lem:sparse}" |
| `sec:app-xsup` | section | 8 | E | kept: v1 "Upper bound when \texorpdfstring {$x>1$}{x>1}", v2 "Upper bound when \texorpdfstring {$x>1$}{x>1}" |
| `sec:app-constA` | section | 8.1 | E.1 | kept: v1 "Constants, ranks and levels", v2 "Constants, ranks and levels" |
| `def:constA` | Definition | 8.1 | E.1 | statement identical |
| `lem:constA` | Lemma | 8.2 | E.2 | statement identical |
| `def:ranksA` | Definition | 8.3 | E.3 | statement identical |
| `lem:ranksA` | Lemma | 8.4 | E.4 | statement identical |
| `def:H` | Definition | 8.5 | E.5 | statement identical |
| `lem:H` | Lemma | 8.6 | E.6 | "Under Assumption 2.2 (any x >= 1)" -> "If the grid is convergent with limit x in [1,oo) (Definition 2.2), then" |
| `sec:app-skelA` | section | 8.2 | E.2 | kept: v1 "The skeleton: proposition, events, decomposition and sums", v2 "The skeleton: proposition, events, decomposition and sums" |
| `prop:dyA` | Proposition | 8.7 | E.7 | statement identical |
| `def:evA` | Definition | 8.8 | E.8 | statement identical |
| `lem:decompA` | Lemma | 8.9 | E.9 | statement identical |
| `eq:DA` | other | 1 | 1 | kept: v1 "decomposition, $x>1$", v2 "decomposition, $x>1$" |
| `lem:probasA` | Lemma | 8.10 | E.10 | statement identical |
| `lem:sumsA` | Lemma | 8.11 | E.11 | statement identical |
| `sec:app-structA` | section | 8.3 | E.3 | kept: v1 "Why is the threshold deterministic?", v2 "Why is the threshold deterministic?" |
| `lem:structA` | Lemma | 8.12 | E.12 | statement identical |
| `lem:thrA` | Lemma | 8.13 | E.13 | statement identical |
| `sec:app-leaderA` | section | 8.4 | E.4 | kept: v1 "Why is the leader optimal?", v2 "Why is the leader optimal?" |
| `lem:leaderA` | Lemma | 8.14 | E.14 | statement identical |
| `lem:countsA` | Lemma | 8.15 | E.15 | statement identical |
| `sec:app-goodA` | section | 8.5 | E.5 | kept: v1 "What happens in a good batch?", v2 "What happens in a good batch?" |
| `lem:goodA` | Lemma | 8.16 | E.16 | statement identical |
| `sec:pf-lem:constA` | section | 8.6 | E.6 | kept: v1 "Proof of Lemma~\ref {lem:constA}", v2 "Proof of Lemma~\ref {lem:constA}" |
| `sec:pf-lem:ranksA` | section | 8.7 | E.7 | kept: v1 "Proof of Lemma~\ref {lem:ranksA}", v2 "Proof of Lemma~\ref {lem:ranksA}" |
| `sec:pf-lem:H` | section | 8.8 | E.8 | kept: v1 "Proof of Lemma~\ref {lem:H}", v2 "Proof of Lemma~\ref {lem:H}" |
| `sec:pf-prop:dyA` | section | 8.9 | E.9 | kept: v1 "Proof of Proposition~\ref {prop:dyA}", v2 "Proof of Proposition~\ref {prop:dyA}" |
| `eq:main2A` | other | 2 | 2 | kept: v1 "Proof of Proposition~\ref {prop:dyA}", v2 "Proof of Proposition~\ref {prop:dyA}" |
| `sec:pf-lem:decompA` | section | 8.10 | E.10 | kept: v1 "Proof of Lemma~\ref {lem:decompA}", v2 "Proof of Lemma~\ref {lem:decompA}" |
| `sec:pf-lem:probasA` | section | 8.11 | E.11 | kept: v1 "Proof of Lemma~\ref {lem:probasA}", v2 "Proof of Lemma~\ref {lem:probasA}" |
| `sec:pf-lem:sumsA` | section | 8.12 | E.12 | kept: v1 "Proof of Lemma~\ref {lem:sumsA}", v2 "Proof of Lemma~\ref {lem:sumsA}" |
| `sec:pf-lem:structA` | section | 8.13 | E.13 | kept: v1 "Proof of Lemma~\ref {lem:structA}", v2 "Proof of Lemma~\ref {lem:structA}" |
| `sec:pf-lem:thrA` | section | 8.14 | E.14 | kept: v1 "Proof of Lemma~\ref {lem:thrA}", v2 "Proof of Lemma~\ref {lem:thrA}" |
| `sec:pf-lem:leaderA` | section | 8.15 | E.15 | kept: v1 "Proof of Lemma~\ref {lem:leaderA}", v2 "Proof of Lemma~\ref {lem:leaderA}" |
| `eq:rejA` | other | 3 | 3 | kept: v1 "Proof of Lemma~\ref {lem:leaderA}", v2 "Proof of Lemma~\ref {lem:leaderA}" |
| `sec:pf-lem:countsA` | section | 8.16 | E.16 | kept: v1 "Proof of Lemma~\ref {lem:countsA}", v2 "Proof of Lemma~\ref {lem:countsA}" |
| `sec:pf-lem:goodA` | section | 8.17 | E.17 | kept: v1 "Proof of Lemma~\ref {lem:goodA}", v2 "Proof of Lemma~\ref {lem:goodA}" |
| `sec:app-xone` | section | 9 | F | kept: v1 "Upper bound when \texorpdfstring {$x=1$}{x=1}", v2 "Upper bound when \texorpdfstring {$x=1$}{x=1}" |
| `sec:app-constC` | section | 9.1 | F.1 | kept: v1 "Constants and ranks", v2 "Constants and ranks" |
| `def:constC` | Definition | 9.1 | F.1 | statement identical |
| `lem:constC` | Lemma | 9.2 | F.2 | statement identical |
| `def:ranksC` | Definition | 9.3 | F.3 | statement identical |
| `sec:app-skelC` | section | 9.2 | F.2 | kept: v1 "The skeleton: events, decomposition and proof of the proposition", v2 "The skeleton: events, decomposition and proof of the proposition" |
| `def:evC` | Definition | 9.4 | F.4 | statement identical |
| `def:amb` | Definition | 9.5 | F.5 | statement identical |
| `lem:decompC` | Lemma | 9.6 | F.6 | statement identical |
| `lem:controlC` | Lemma | 9.7 | F.7 | statement identical |
| `lem:sumC` | Lemma | 9.8 | F.8 | statement identical |
| `prop:fixedC` | Proposition | 9.9 | F.9 | statement identical |
| `sec:app-water` | section | 9.3 | F.3 | kept: v1 "Why are many batches high?", v2 "Why are many batches high?" |
| `def:high` | Definition | 9.10 | F.10 | statement identical |
| `lem:lowmass` | Lemma | 9.11 | F.11 | statement identical |
| `lem:growth` | Lemma | 9.12 | F.12 | statement identical |
| `lem:levelC` | Lemma | 9.13 | F.13 | statement identical |
| `sec:app-pathC` | section | 9.4 | F.4 | kept: v1 "Why are the leaders reliable, and why are wrong means rare?", v2 "Why are the leaders reliable, and why are wrong means rare?" |
| `lem:goodhigh` | Lemma | 9.14 | F.14 | statement identical |
| `lem:highC` | Lemma | 9.15 | F.15 | statement identical |
| `lem:fewC` | Lemma | 9.16 | F.16 | statement identical |
| `lem:logcountC` | Lemma | 9.17 | F.17 | statement identical |
| `sec:app-optW` | section | 9.5 | F.5 | kept: v1 "Why is an optimal arm well sampled, and how many times is \texorpdfstring {$a$}{a} pulled?", v2 "Why is an optimal arm well sampled, and how many times is \texorpdfstring {$a$}{a} pulled?" |
| `lem:optW` | Lemma | 9.18 | F.18 | statement identical |
| `lem:pullsC` | Lemma | 9.19 | F.19 | statement identical |
| `sec:app-amb` | section | 9.6 | F.6 | kept: v1 "Why does \texorpdfstring {$a$}{a} pass the consistency test?", v2 "Why does \texorpdfstring {$a$}{a} pass the consistency test?" |
| `lem:amb` | Lemma | 9.20 | F.20 | statement identical |
| `sec:pf-lem:constC` | section | 9.7 | F.7 | kept: v1 "Proof of Lemma~\ref {lem:constC}", v2 "Proof of Lemma~\ref {lem:constC}" |
| `sec:pf-lem:decompC` | section | 9.8 | F.8 | kept: v1 "Proof of Lemma~\ref {lem:decompC}", v2 "Proof of Lemma~\ref {lem:decompC}" |
| `sec:pf-lem:controlC` | section | 9.9 | F.9 | kept: v1 "Proof of Lemma~\ref {lem:controlC}", v2 "Proof of Lemma~\ref {lem:controlC}" |
| `sec:pf-lem:sumC` | section | 9.10 | F.10 | kept: v1 "Proof of Lemma~\ref {lem:sumC}", v2 "Proof of Lemma~\ref {lem:sumC}" |
| `sec:pf-lem:lowmass` | section | 9.11 | F.11 | kept: v1 "Proof of Lemma~\ref {lem:lowmass}", v2 "Proof of Lemma~\ref {lem:lowmass}" |
| `sec:pf-lem:growth` | section | 9.12 | F.12 | kept: v1 "Proof of Lemma~\ref {lem:growth}", v2 "Proof of Lemma~\ref {lem:growth}" |
| `sec:pf-lem:levelC` | section | 9.13 | F.13 | kept: v1 "Proof of Lemma~\ref {lem:levelC}", v2 "Proof of Lemma~\ref {lem:levelC}" |
| `sec:pf-lem:goodhigh` | section | 9.14 | F.14 | kept: v1 "Proof of Lemma~\ref {lem:goodhigh}", v2 "Proof of Lemma~\ref {lem:goodhigh}" |
| `sec:pf-lem:highC` | section | 9.15 | F.15 | kept: v1 "Proof of Lemma~\ref {lem:highC}", v2 "Proof of Lemma~\ref {lem:highC}" |
| `sec:pf-lem:fewC` | section | 9.16 | F.16 | kept: v1 "Proof of Lemma~\ref {lem:fewC}", v2 "Proof of Lemma~\ref {lem:fewC}" |
| `sec:pf-lem:logcountC` | section | 9.17 | F.17 | kept: v1 "Proof of Lemma~\ref {lem:logcountC}", v2 "Proof of Lemma~\ref {lem:logcountC}" |
| `sec:pf-lem:optW` | section | 9.18 | F.18 | kept: v1 "Proof of Lemma~\ref {lem:optW}", v2 "Proof of Lemma~\ref {lem:optW}" |
| `sec:pf-lem:pullsC` | section | 9.19 | F.19 | kept: v1 "Proof of Lemma~\ref {lem:pullsC}", v2 "Proof of Lemma~\ref {lem:pullsC}" |
| `sec:pf-lem:amb` | section | 9.20 | F.20 | kept: v1 "Proof of Lemma~\ref {lem:amb}", v2 "Proof of Lemma~\ref {lem:amb}" |
| `eq:old` | other | 4 | 4 | kept: v1 "Proof of Lemma~\ref {lem:amb}", v2 "Proof of Lemma~\ref {lem:amb}" |
| `sec:app-end` | section | 10 | G | kept: v1 "End of the proof of Theorem~\ref {thm:upper}", v2 "End of the proof of Theorem~\ref {thm:upper}" |
| `sec:app-proofupper` | section | 10.1 | G.1 | kept: v1 "Proof of Theorem~\ref {thm:upper}", v2 "Proof of Theorem~\ref {thm:upper}" |
| `sec:sanity` | section | 11 | 7 | kept: v1 "Sanity checks", v2 "Examples and special cases" |
| `sec:weak` | section | 12 | - | removed: the section "Weak points" moved to DOSSIER.md, section 4 |
| `sec:open` | section | 13 | 8 | kept: v1 "Open questions", v2 "Open questions" |
| `oq:remainders` | Open question | 1 | 1 | statement identical |
| `oq:liminf` | Open question | 2 | 2 | statement identical |
| `oq:random` | Open question | 3 | 3 | statement identical |
| `sec:attribution` | section | 14 | H | kept: v1 "Attribution", v2 "Sources of the techniques" |
| `sec:notation` | section | 15 | I | kept: v1 "Notation", v2 "Notation" |
| `sec:app-vocab` | section | 15.1 | I.1 | kept: v1 "Vocabulary", v2 "Vocabulary" |
| `sec:app-notation` | section | 15.2 | I.2 | kept: v1 "Notation", v2 "Notation" |

New labels in v2: `alg:hy` (1), `lem:primal` (A.2), `sec:cited` (A), `sec:examples` (7), `sec:overview` (6), `tab:related` (1),
`sec:related` (2) and `sec:discussion` (5.4), the last two added in the revision of 2026-11-16.
