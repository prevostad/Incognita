# DOSSIER of P002 (refereed with the paper, never compiled into the PDF)

Material that serves the referees and the owner but not the reader of `paper.tex` (writing rules
v1, D3). Created for version 2 (presentation revision, 2026-11-15, claude-opus-5-5): everything
below except the last two sections was in the text of version 1 and has been moved here unchanged
(LaTeX turned into Markdown; KNOWN and roadmap ids kept).

## 1. Roadmap correspondence

**Items served** (META.toml `directions`): D8 of the roadmap TransferBandits. Version 1 opened with
"This paper serves direction D8 of the roadmap TransferBandits: the drift between target and source
is measured between laws."

**D8, verbatim** (`roadmaps/TransferBandits/ROADMAP.md`):

> **D8. Drift measured between laws, not between means.** Replace the drift condition by
> $d(\nu_k,\nu'_k) < L_k$ for a pseudo-distance (or a divergence) $d$ between laws on $[0,1]$
> fixed by the paper, for example the Wasserstein distance $W_1$, the total variation, the
> Kolmogorov distance, the Hellinger distance or $\mathrm{KL}(\nu'_k,\nu_k)$. The mean condition is
> the case $d(\nu,\nu') := |m(\nu)-m(\nu')|$ (or its one-sided version). Questions. (a) The lower
> bound: an alternative must now move the target law $\nu_a$ to some $Q$ with $m(Q)>\mu^\star$
> **and** the source law $\nu'_a$ to some $Q'$ with $d(Q,Q')<L_a$, so the cost
> $\mathbb E[N_a(T)]\,\mathrm{KL}(\nu_a,Q)+\mathbb E[N'_a]\,\mathrm{KL}(\nu'_a,Q')$ couples the two
> divergences through $d$. Identify the resulting constant (an infimum over pairs $(Q,Q')$), say
> when it splits into an online term and a source term as in the mean case (K2, K3), and compare it
> with the mean case: for instance $|m(Q)-m(Q')|\le W_1(Q,Q')$, so a $W_1$ condition with bound $L$
> restricts the pairs at least as much as the mean condition with the same $L$. (b) An algorithm
> that attains it, for example a KL-UCB-Transfer (K8) whose index uses the empirical source law
> through $d$, not only its mean, with its cost per round. (c) Which pseudo-distances give an
> improvement over KL-UCB where the mean condition gives none, and what misspecification does
> (as in K5). Answer: matching lower and upper bounds for one pseudo-distance, with a check that
> $d(\nu,\nu')=|m(\nu)-m(\nu')|$ gives back K2–K4.

**Correspondence with the paper** (the "Roadmap items" paragraph of version 1, verbatim; labels as
in the source):

> D8: (a) the constant is identified as the value of a convex programme (Definition def:constant,
> Lemma lem:D); the lower bound itself is known [PMM25, Theorem 3]. (b) An algorithm attains it
> (Theorem thm:main); each index is a convex programme in $2|S|$ variables (plus $O(|S|)$ slack
> variables for TV, KS, $W_1$). (c) The pseudo-distances that give an improvement where the mean
> gives none are characterised (Propositions prop:criteria to prop:tv), and $d=$ mean gap gives back
> the first-order constants of K2–K4, for laws carried by $S$ with $1\in S$ and deterministic sizes
> only (Proposition prop:order, Section sec:sanity). Missing: the nonparametric model
> $\mathcal P([0,1])$ (the method of types is used; Open question oq:nonparametric), random source
> sizes, an explicit second-order term, and misspecification beyond the remark that Theorem thm:main
> needs the drift condition on one optimal arm only, the analogue of the well-specified case of K5
> (Section sec:closest; Open question oq:misspecification).

What D8 asks that the paper does not give: the model of all laws on $[0,1]$; the Hellinger distance
and $\mathrm{KL}(\nu'_k,\nu_k)$ (the paper covers integral probability metrics with $[0,1]$-valued
test functions only); random source sizes (`E[N'_a]` in the roadmap's cost); misspecification.
Version 2 says these limits in plain words in the "Scope" paragraph after Theorem 6.1.

**Conventions** (the opening of the Setting of version 1): "The conventions are those of the roadmap
TransferBandits, with three changes required by D8 or by the method: the drift is measured by a
pseudo-distance between laws (D8); the rewards take values in a known finite set $S$, and the source
sizes are deterministic (the method of types is used; see Section sec:weak); consistency is required
for one sequence of source sizes (Definition def:class), which makes the lower bound stronger."

**Open questions and roadmap items** (version 1 wrote them in the text; version 2 puts them in
`\extends{…}`): oq:nonparametric extends D8; oq:second-order extends D8 and D7; oq:misspecification
extends D8(c) and K5; oq:random extends D1 and D8.

## 2. Closest known, by KNOWN id, with the derivation attempts

The "Closest known" section of version 1, verbatim except for the LaTeX. The published results it
discusses are compared in the paper itself (Section 2 with Table 1, and Section 6.1), cited by
publication.

**The lower bound with a pseudo-distance: [PMM25, Theorem 3] (KNOWN K1).** The ACML paper assumes a
known family of pseudo-distances $d_k$ with $d_k(\nu_k,\nu'_k)\le L_k$ and proves, for every
consistent algorithm and deterministic sizes, that
$\liminf_T\inf\{\mathbb E N_k(T)\mathrm{KL}(\nu_k,\tilde\nu_k)+N'_k\mathrm{KL}(\nu'_k,\tilde\nu'_k)\}/\log T\ge1$,
the infimum running over pairs with mean of $\tilde\nu_k$ larger than $\mu_1$ and
$d_k(\tilde\nu_k,\tilde\nu'_k)\le L_k$. Proposition prop:lower is a variant of it on $\Delta_S$ (see
the remark after it); we do not claim it. Its Section 5.2 introduces the source-penalised index
KL-UCB-Transfer [PMM25, (4)], for Gaussian laws and the mean gap: the first form of the index of
Definition def:algo. Its upper bound (Theorem 6 there) is for Gaussian laws and the mean gap only. We
found no discussion there of total variation, Kolmogorov or Wasserstein distances, nor of the
structure of the constant. *Attempt to derive Theorem thm:main:* the Gaussian upper bound does not
apply to laws on $S$, and for the mean gap it gives the mean constant only.

**The mean model: KNOWN K2–K4 and K8 [PMRM26].** With a mean drift, K2 is the lower bound and K3 the
upper bound of KL-UCB-Transfer (K8) on $\mathcal P([0,1])$, with random source sizes. *Attempt:* if
$d$ has (M), every instance of $\Theta$ has $|\mu_k-\mu'_k|<L_k$, so K3 applies to K8 on $\Theta$ and
gives, for $N'_a/\log T\to c_a$ and $1\in S$ (then $\mathcal K_{\inf}$ on $[0,1]$ equals
$\mathcal K_S$ on laws carried by $S$: the projection on a bounded support adds mass only at $1$,
[HT10, Theorem 8 and its proof]; for finitely supported competitors this is Lemma lem:projection),
$\limsup\mathbb E N_a(T)/\log T\le(1-c_a K'_0)_+/K_0=D^{\rm mean}_a(c_a)$ (Proposition prop:order).
This is Theorem thm:main(ii) exactly when $D^d_a(c_a)=D^{\rm mean}_a(c_a)$, and the attempt fails
exactly when $d(Q^\star,Q'^\star)>L_a$ or $d(Q^\star,\nu'_a)>L_a$ (Proposition prop:criteria): K8 uses
the source only through its mean, and the lower bound shows that no algorithm doing so can be optimal
there. Example ex:no-drift is such a case, with $d=\mathrm{TV}$.

**The drift on one optimal arm only: KNOWN K5.** Theorem thm:main asks for
$d(\nu_{i^\star},\nu'_{i^\star})<L_{i^\star}$ on one optimal arm and for nothing on the other arms.
For the mean gap this is the well-specified regime of K5 ([PMRM26, Section 7], to be checked:
$\mu^\dagger=\mu_1<\mu'_1+L_1$, with no condition on the other arms), which K5 states in the
one-sided form $\mu_1<\mu'_1+L_1$. This part of Theorem thm:main is the analogue of K5's
well-specified case for a distance $d$ between laws, in the two-sided form; it is not new for the mean
gap. *(Version 2: [PMRM26, Theorem 5] has now been read, see Section 6 below; the paper cites it.)*

**KL-UCB on a known finite support [BK96, CGMMS13].** Without a source ($N'=0$), Theorem thm:main is
the first-order bound of KL-UCB with the divergence computed on the known support $S$. The model of
laws on a known finite support is that of Burnetas and Katehakis [BK96] (we read only its abstract,
which says that its assumptions are verified for nonparametric discrete laws with finite support). It
is the earliest source we found for the index "maximum of the mean over the laws on the known support
in a KL ball of the empirical law" and for its asymptotic optimality on that model, so that, for
$N'=0$, the index of Definition def:algo and Theorem thm:main(i) at first order are theirs (to be
checked: the section of [BK96] on discrete laws was not read). [CGMMS13, Theorem 2] (arXiv v4
numbering) proves, with explicit second-order terms, the bound $\log T/\mathcal K_{\inf}(\nu_a,\mu^\star)$
for empirical KL-UCB on finitely supported laws of $[0,1]$ (support not known, $\mu^\star<1$,
$\mathcal K_{\inf}$ over finitely supported laws of $[0,1]$); its constant equals ours when $1\in S$
(for a competitor $q$, apply Lemma lem:projection on $S\cup\mathrm{supp}\,q$: the projection adds
mass only at $1$), and is larger otherwise. The novelty is the source term.

**Historical data without drift [SJ12].** Shivaswamy and Joachims study bandits in which observations
of the arms are available before the game, from the same laws; from their abstract (the only part we
read), a logarithmic amount of historic data can reduce the regret from logarithmic to constant. This
is the phenomenon of Proposition prop:threshold with no drift. What the drift adds is the threshold
$G^d$, which depends on $d$ and on $L_a$ (Proposition prop:threshold), and the constant $D_a(c)$
below it.

**Structured bandits [MCP14, CMP17].** The index of Definition def:algo maximises a mean under one KL
budget shared by several samples tied by a constraint. So does the index of OSLB and CKL-UCB for
Lipschitz bandits [MCP14, Section 4.1], a supremum of $q$ under
$\sum_{k'}t_{k'}(n)I^+(\hat\theta_{k'}(n),\lambda^{q,k}_{k'})\le f(n)$, the sum running over all the
arms. The results on structured bandits ([MCP14], and OSSB [CMP17, Section 5]) do not cover forced
source samples: there every sample comes from an arm of the game, pulled by the learner, and the lower
bound is an allocation problem over these arms. Here the source samples come from laws $\nu'_k$ that
are not arms of the game, their number $N'_k(T)$ is imposed and not chosen, and the structure ties
each target law to its own source law only.

**Biased offline data [CL24].** Cheung and Lyu study online bandits with offline data whose bias is
bounded through the means only, $V(a)\ge|\mu^{(\rm off)}(a)-\mu^{(\rm on)}(a)|$ (their (4)), for
$1$-sub-Gaussian laws. Their algorithms use mean-based confidence radii and cannot use a drift between
laws. Li, Fu, Chen and Kong [LFCK26] (Thompson sampling anchored on the sample mean) also bound the
shift of the means only, $|\mu^{\rm off}_i-\mu^{\rm on}_i|\le V_i$, and give no lower bound.

**Wasserstein ambiguity sets [KT26].** Kimura and Tamano borrow external data in clinical trials with
Wasserstein ambiguity sets; it is a fixed-design test with type I error control (from the abstract),
not a regret problem.

## 3. Sanity checks

The "Sanity checks" section of version 1. The examples are in Section 9 of version 2 and the
degenerate cases in its Appendix H (without the KNOWN ids); the process items are here.

- *No source* ($N'_a=0$, $c_a=0$): $D_a(0)=1/\mathcal K_S(\nu_a,\mu^\star)$, the KL-UCB constant on
  $S$, which is that of [CGMMS13, Theorem 2] when $1\in S$.
- *Mean gap*: $D^{\rm mean}_a(c)=(1-cK'_0)_+/K_0$ (Proposition prop:order), which is the first-order
  constant of K2(i) and K3(i) (not their second-order terms, nor their random sizes) for
  deterministic sizes on $S$ when $1\in S$ (then $\mathcal K_S=\mathcal K_{\inf}$ for laws carried by
  $S$), on instances with $|\mu_a-m(\nu'_a)|<L_a$ (then $m(\nu'_a)\le\mu^\star+L_a$); the condition of
  improvement is $m(\nu'_a)<\mu^\star-L_a$ (Proposition prop:criteria(b)), that of K2; when
  $m(\nu'_a)\ge\mu^\star-L_a$, $K'_0=0$ and $D^{\rm mean}_a=1/K_0$, which is K2(ii) and K3(ii). The
  boundary $m(\nu'_a)=\mu^\star-L_a$ falls in the second case. *(Corrected in revision round 1,
  2026-11-16, scope referee SC1.1: version 1 and the first submission of version 2 added "as in K4
  when the sizes are deterministic", but K4 = [PMRM26, Proposition 4] excludes exactly this boundary
  ("except possibly when $\mu'_a=\mu_1-L_a$"). At the boundary and for deterministic sizes, K2(i)
  applies (hypothesis $\mu'_a\le\mu_1-L_a$) and gives $1/\mathcal K_{\inf}(\nu_a,\mu_1)$, because
  [PMRM26]'s $\mathcal K_{\inf}$ takes laws of mean strictly above the level, so
  $\mathcal K_{\inf}(\nu'_a,\mu'_a)=0$ when $\mu'_a<1$; K3(ii) (hypothesis $\mu'_a\ge\mu_1-L_a$)
  gives the same constant. The paper now says this, in Appendix "Degenerate cases".)*
- *$\mu^\star=x_{\max}$*: $D_a=0$ and $\mathbb E N_a(T)=o(\log T)$ (Lemma lem:D).
- *Infinite divergences*: handled by the conventions of Definition def:laws.
- *Several optimal arms, ties*: Theorem thm:main needs one optimal arm with the margin; ties of
  indices are broken at random and play no role in the proofs.
- *$K=2$, Bernoulli*: Example ex:bernoulli.
- **Consistency with the `[Lean]` entries of KNOWN.md:** KNOWN.md of TransferBandits has no `[Lean]`
  entry.
- *One instance satisfying all hypotheses*: the two-armed instance of Section 9.2 ("A complete
  instance with two arms"); in version 1 it said that KL-UCB-Transfer "(K8)" with mean drift $0.11$
  gains nothing.
- *Numerical values*: Section 9.1 of the paper (the computation and its certificates); the scripts
  are `notebook/calculs/` (run5.py, run6.py, run7.py for the certified values; fig_dtv.py, new in
  version 2, for the curve of Figure 1, checked against the certified values).

## 4. Weak points

The three steps the author is least sure of (version 1, verbatim). Version 2 names the same three
steps, without calling them weak, in Section 8.2 "Where the difficulty lies".

1. Lemma lem:sub-constant, the neighbourhood step: the lower semicontinuity of $\psi$ jointly in
   $(r,r',\beta,\mu)$ (with the constraint set depending on $\mu$ through a closed graph), and the use
   of TV-neighbourhoods for both empirical laws; an error there would break Theorem thm:main(ii)
   only, not (i).
2. Lemma lem:optimal-arm, the event inclusion: it uses a pair $(q,\bar q')$ built from the unknown
   $\nu'_{i^\star}$ (an analysis device, legitimate since it is only shown to be feasible), and the
   independence between the stack of $i^\star$ and its source sample, which holds because the sizes
   are deterministic.
3. Lemmas lem:J-zero and lem:D, the perturbation arguments (mixing with $\delta_{x_{\max}}$ and with a
   common law): short but delicate; they need $\mu^\star<x_{\max}$, and the case $\mu^\star=x_{\max}$
   is treated separately. The numerical values of Section sec:sanity are in double precision only.

## 5. Searches

The "Searches" paragraph of version 1, verbatim.

Web searches on 2026-11-14 (by the author's session): transfer learning in multi-armed bandits with a
Wasserstein or total variation bound between source and target reward laws and a regret lower bound;
bandits with offline data from a shifted distribution (total variation, warm start); "Leveraging
(biased) information" and Cheung–Lyu's discrepancy; KL-UCB with prior samples of a related
distribution, "total variation", transfer, asymptotic optimality; bandits with "distribution shift",
historical data, "Wasserstein ball"; offline-to-online bandits with a Wasserstein or total variation
discrepancy (2025); structured bandits (Graves–Lai) with prior data; bandits with misspecified prior
data and Kolmogorov, Wasserstein or total variation robustness; bandits corrupted by nature (total
variation contamination); multi-task bandits with similar distributions; distributionally robust
bandits with Wasserstein ambiguity sets and KL-UCB; transfer with historical data and "total variation
distance". On 2026-11-15 (revision, after the scope referee's report, which named [BK96], [MCP14],
[SJ12], [PMM25, Section 5.2] and the numbering of [PMRM26]): the posted HTML of [PMRM26] (outline,
Lemma 17), of [PMM25] (Section 5.2) and of [MCP14] (Section 4.1); the PMLR page of [SJ12]; the query
"Burnetas Katehakis 1996 Optimal adaptive policies for sequential allocation problems pdf", which
returned the publisher's page (access refused) and citing papers; Crossref records for the metadata
of [BK96], [CK11], [SS07] and [O88]. The searches of 2026-11-14 returned [PMM25] (whose Theorem 3 is
the lower bound above), [PMRM26], [CL24] (mean bias), [KT26] (Wasserstein sets, testing), works on
Bayesian priors in total variation, on Huber contamination, on multi-task bandits with a mean or
parameter distance, and on dynamic pricing under covariate shift; none gives an algorithm for a
drift between laws, nor the structure of the constant.

Version 2 (2026-11-15): one page read, no search: the HTML of arXiv:2610.21582v1 ([PMRM26]) for the
statements of Theorems 2, 3, 5 and Proposition 4 (recorded in `literature/index.md`).

## 6. Reading notes on the citations

What was read of each source cited by the paper, and how version 2 cites it (writing rules v1, D4: a
citation rests on a part that was read, or is weakened to "see also"; classics may be cited for
standard facts).

| Key | Read | How version 2 cites it |
|---|---|---|
| PMM25 | §3, Def. 2, Thm 3, Cor. 4, §5.2 index (4), Thm 6, App. A | Theorem 3 (lower bound), §5.2 (4), Theorem 6, Appendix A |
| PMRM26 | setting, §4.2 class $\mathcal C_L$ and Theorem 2, §5.2 index, Lemma 17; in version 2 also Theorem 3, Proposition 4, Theorem 5 (HTML v1) | Theorems 2, 3, 5, Proposition 4, §4.2, §5.2, §6, Lemma 17. Version 1 cited §7 with "to be checked" (title only read); version 2 cites Theorem 5, now read |
| GMS19 | (5), (6), (10), (11), Thm 1 (v3 source) | (5), (6), (11) restated in the paper's notation (Appendix A) |
| CGMMS13 | §1–§6, Thm 2 | Theorem 2, §5 |
| HT10 | whole COLT paper | Theorems 5 and 8, proof of Theorem 8 |
| BK96 | abstract only | weakened to "see also" (version 1 credited the known-support index to it, "to be checked") |
| SJ12 | abstract only | the phenomenon stated in its abstract (a logarithmic history can make the regret constant) |
| MCP14 | §4.1 | §4.1 |
| CMP17 | §3–§6 (Thm 2, OSSB) | §5 |
| CL24 | §1–§4.2, (4) | (4); the bias bound, stated in words |
| LFCK26 | abstract and setting | the mean-shift bound, in words |
| KT26 | abstract only | "see also" |
| CK11 | not read | classic, "see" for the method of types (version 1: "(to be checked)") |
| SS07 | not read | classic, "see" for the likelihood-ratio order (version 1 cited Theorem 1.C.1, "(to be checked)"; the theorem number is dropped) |
| O88 | not read | "see also" for the form of the empirical-likelihood weights (version 1: "(to be checked)") |

Version 1's attribution table also said "standard: Berge's maximum theorem (reference to be checked;
not in the bibliography of the library)" for Lemma lem:lsc and "standard (reference to be checked)"
for Lemma lem:ipm-order; version 2 says "classical" without a reference for both (each lemma is
proved in full in the paper).

## 7. Presentation revision v2: what changed (first pass, 2026-11-15)

**Structure** (writing rules v1, D2). Introduction (problem, why a distance between laws, the
constant in supremum form with its meaning, the main result, the no-drift example with Figure 1,
comparison with published results with Table 1, contributions, techniques); Setting (definitions,
the algorithm in words and as pseudo-code); Main results (Theorem, lower bound, corollary, meaning of
the constant, structure results with a summary, relation with published bounds); Proof overview
(decomposition, the two steps, the proof of Theorem thm:main, where the difficulty lies, the lower
bound and the structure results in words, map of the appendices); Examples and special cases; Open
questions; appendices A (cited results), B (tools), C ($J_a$, $D_a$), D (upper bound), E (lower
bound), F (structure results), G (weak duality), H (sources of the techniques), I (notation).

**Moved here from paper.tex:** the "serves direction D8" sentence, the "Roadmap items" paragraph, the
roadmap conventions sentence, the KNOWN ids K1–K8 (39 occurrences), the "Closest known" section
with its derivation attempts and reading admissions, the "Weak points" section, the "Searches"
paragraph, every "(to be checked)", and the process items of "Sanity checks" (the `[Lean]`
consistency line).

**Renamings** (consistent in the whole paper):

| Version 1 | Version 2 | Why |
|---|---|---|
| $U_0,U_1,\dots$ (randomisation) | $V_0,V_1,\dots$ | $U_k(t)$ is the index; $W_t$ was not used because $W_1$ is the Wasserstein distance |
| $A_T$, $B_T$, $B^0_T$ (counts of the proof) | $\mathcal A_T$, $\mathcal B_T$, $\mathcal B^0_T$ | $A_t$ is the arm pulled |
| $K_0$, $K'_0$ | $\mathcal K_0$, $\mathcal K'_0$ | $K$ is the number of arms; calligraphic $\mathcal K$ for divergence values, as $\mathcal K_S$ |
| $k_\varepsilon$ (Lemma lem:sub-kl) | $\mathcal K_\varepsilon$ | $k$ is an arm index; consistent with $\mathcal K_0$ |
| $K_\rho$, $K_{\eta/2}$ (Lemma lem:deviation) | $H_\varrho$, $H_{\eta/2}$ | $K$ |
| radius $\rho$ (lem:deviation), $r_\xi$, $r_0$ | $\varrho$, $\varrho_\xi$, $\varrho_0$ | $\rho$ and $r$ are laws |
| alternative instance $\nu'$ in cite:GMS19-6 | $\tilde\nu$ | $\nu'$ is the source law |
| $(p,q)$ in $\mathrm{kl}$ | $(p,\tilde p)$ | $q$ is a law |
| $Z$ (Lemma lem:source) | $\Lambda$ | $Z$ is the variable of cite:GMS19-6 |
| $G:=F_q-F_{q'}$ (lem:ipm-order), event $G$ (lem:source), $G'$, $E_s$ (lem:sub-constant) | written out / $\Delta F$ in the proof; $\mathcal E$, $\mathcal E'$, $\mathcal E_s$ | $G^d$ is the threshold quantity |
| $\delta_{x_{\max}}$ (Dirac mass) | $\mathbf 1_{\{x_{\max}\}}$ | $\delta_t$ is the exploration rate (kept, as in [PMRM26]) |
| mixing weights $t$ (lem:ipm), $\kappa$ (proofs of lem:J, lem:J-zero, lem:D), $t$ (proof of prop:threshold) | $\tau$ | $t$ is a round, $\kappa_q(\theta)$ a constant |
| multiplier $\kappa$, functions $A$, $B$ (lem:weak-duality) | $\sigma$, $\phi$, $\phi'$ | $\kappa_q$; $A_t$; $\mathcal B_T$ |
| $A:=\mathrm{supp}\,\rho$ (lem:projection), $\mathrm{supp}\,\nu$ (proofs of prop:w1, prop:tv) | $S_\rho$, $S_{\nu_a}$ | $A_t$ |
| $\Xi$, $Z$ (lem:lsc) | $\mathcal X$, $\mathcal Z$ | $Z$ |
| local $\varphi$ (proof of lem:lsc), $\beta$ (proof of lem:D), $\Delta_\pm$ (proof of prop:tv), $r_0$ (proof of prop:w1) | $\chi$, $b$, $\alpha_\pm$, $u_0$ | clashes with $\psi$/$\phi$, the argument $\beta$ of $\psi$, $\Delta_a$, $\varrho_0$ |
| local abbreviations $\nu:=\nu_a$, $\nu':=\nu'_a$, $L:=L_a$ (Appendix "programme", structure proofs) | $\nu_a$, $\nu'_a$, $L_a$ written out | $\nu$, $\nu'$, $L$ are vectors |
| $\mu'_k$ (used in v1 without definition) | $\mu'_k:=m(\nu'_k)$, defined in the notation of Section 2 | |

**The fix of cite:GMS19-11** (known defect found by the bibliographer, see
`literature/notes/GMS19.md`, item "(11)"). Version 1's cited node stated
$\mathrm{kl}(p,q)\ge p\log(1/q)-\log2$, which [GMS19] does not print: (11) is an identity,
$\mathrm{kl}(p,q)=p\ln\frac1q+(1-p)\ln\frac1{1-q}+(p\ln p+(1-p)\ln(1-p))$, with the first term marked
$\ge0$ and the last bracket marked $\ge-\ln2$. Version 2: cite:GMS19-11 states (11) as printed, in
the paper's notation ($\ln\to\log$, $q\to\tilde p$), with the two marked bounds; the inequality is the
new Lemma lem:kl-lower, proved from it (drop the nonnegative term $(1-p)\log\frac1{1-\tilde p}$, bound
the bracket by $-\log2$); the proof of prop:lower `\uses` lem:kl-lower in place of cite:GMS19-11.
The mathematics of the lower bound is unchanged (the same inequality, now proved).

**New text claims outside the nodes** (for the scope referee; each comes with its justification in
the paper):
- Section 3.3: $D_a(c)\le1/\mathcal K_0$ and $D_a(0)=1/\mathcal K_0$ (Lemma lem:D(a) and the case
  $c_a=0$ of the proof of thm:main), and "$D_a$ is nonincreasing and convex in $c$" (each ratio of the
  supremum form is a nonincreasing convex function of $c$; a supremum keeps both properties).
- Section 3.1, "The index": the index programme is convex ($\mathrm{KL}$ convex in its second
  argument, $d$ jointly convex by Lemma lem:ipm(b)); with $N'_k=0$ the index is KL-UCB's on $S$ (the
  pair $(q,q)$ is feasible). The relation with KL-UCB-Transfer is version 1's remark after def:algo.
- Section 5.3, the two-armed instance: version 1 said "every learner that uses the source only
  through a mean bound, and KL-UCB, need $6.0285\log T$"; version 2 states it as "every learner
  consistent for the mean-drift model on the same instances (the class $\mathcal C(N')$ defined with
  the mean gap) pulls arm 2 at least $6.0285\log T(1-o(1))$ times", which is Proposition prop:lower
  with the mean gap and Proposition prop:order(a) ($\mathcal K'_0=0$).
- Figure 1: the curve $c\mapsto D^{\rm TV}_a(c)$ of Example ex:no-drift, computed by
  `notebook/calculs/fig_dtv.py` (primal bisection, 26 values of $c$; it checks the five certified
  values of the table to $2\cdot10^{-3}$ — they agree to $10^{-4}$ — and that the values are
  nonincreasing and convex). PDFs under `papers/` are never committed (`.gitignore`), so the figure is
  drawn by TikZ from the printed coordinates (`notebook/calculs/fig_dtv.txt`).

**Proofs.** No step changed in substance. Added: "Idea." paragraphs and named steps (Lemmas
lem:projection, lem:J-zero, lem:D, lem:deviation, lem:optimal-arm, lem:sub-reduction,
lem:sub-constant, lem:weak-duality, Propositions prop:lower, prop:w1; the structure proofs are split
by the parts (a), (b), (c) of the statements), Setting/Goal blocks (lem:optimal-arm, prop:lower),
justifications on the lines of aligned chains (lem:projection, lem:ipm-order, lem:optimal-arm,
prop:lower, lem:weak-duality), "Role." lines under the appendix lemmas. Moved: the proofs of
lem:decomposition and thm:main to Section 4.1 (main text), the proof of cor:optimal right after the
corollary (Section 3.2). Lemma lem:source's proof now writes $\mathbb E[e^\Lambda\mathbf 1_{\mathcal E}]\le1$
explicitly (version 1: "on $G$, $Z=0$").

## 8. Presentation revision v2: statement correspondence

Every label of version 1 (`git show origin/main:papers/P002-transfer-drift-between-laws/paper.tex`),
with its place in version 2 and the relation between the two statements. "Identical" means the same
LaTeX up to spaces; "reworded" means a different wording or layout of the same hypotheses and
conclusions; "renamed" lists notation changes (Section 7). The `\uses` lists of all statements and
proofs are unchanged, except the proof of prop:lower (cite:GMS19-11 replaced by lem:kl-lower). This
was checked by a script comparing the two sources node by node.

| Label (v1) | Place in v2 (numbering of 2026-11-16) | Statement v1 → v2 (first pass, 2026-11-15) |
|---|---|---|
| sec:main | Section 6, Regret upper bound | section (was §1 "Main result") |
| thm:main | Theorem 6.1 | identical (punctuation: "let $K\ge2$ and $L\in\dots$") |
| prop:lower | Proposition 4.2 | reworded: the conclusion displayed |
| cor:optimal | Corollary 6.2 | reworded: "assume that …", the limit displayed, "Let $\mathcal R:=\dots$. Then …" |
| sec:structure | Section 7, When does the law help? | subsection (was §1.1) |
| prop:order | Proposition 7.1 | reworded: the three claims as items (a), (b), (c) |
| prop:criteria | Proposition 7.2 | reworded: items; the parenthetical "the condition of K2" (a KNOWN id, not mathematics) is dropped from the statement; the text after it cites [PMRM26, §6] |
| prop:threshold | Proposition 7.3 | reworded: $\omega_d$ and $G^d$ defined first, the three claims as items (a), (b), (c) |
| prop:bernoulli | Proposition 7.4 | identical |
| prop:w1 | Proposition 7.5 | identical |
| prop:tv | Proposition 7.6 | reworded: "Assume $\mathcal K'_0>0$. Then (a) …; (b) hence …; (c) this holds in particular …" |
| sec:setting | Section 3, Problem formulation | section |
| def:laws | Definition 3.1 | reworded ("Let … be", the names "Kullback–Leibler divergence", "total variation") |
| def:ipm | Definition 3.2 | reworded ("The four examples are", names of the distances, "mean property" in italics) |
| def:model | Definition 3.3 | renamed $U_t\to V_t$; "uniform" → "uniform on $[0,1]$" (the usual reading); "The empirical laws are …" |
| def:class | Definition 3.4 | reworded ("Let $\Theta:=\dots$") |
| def:constant | Definition 4.1 | reworded (sentences split) |
| def:algo | Definition 5.1 | renamed $U_t\to V_t$ (tie-breaking); "The inputs are …" |
| sec:closest | Section 2, Related work and context | the KNOWN-id comparison moved to this dossier (§2); the comparison with publications is in Section 2 (Related work and context, with Table 1) and §6.1 |
| sec:proofs | Appendix B, Tools on the simplex | the first appendix of proofs |
| lem:ipm | Lemma B.1 | renamed $t\to\tau$; items |
| lem:ipm-order | Lemma B.2 | reworded: $G:=F_q-F_{q'}$ written out in the identity; "$q,q'\in\Delta_S$" made explicit |
| lem:lsc | Lemma B.3 | renamed $\Xi\to\mathcal X$, $Z\to\mathcal Z$; (a) reworded |
| lem:types | Lemma B.4 | items; "laws $r$ with …" |
| lem:projection | Lemma B.5 | renamed $A\to S_\rho$ |
| lem:lr | Lemma B.6 | identical |
| lem:J | Lemma C.1 | $\mathcal K_S(\nu,\mu)\to\mathcal K_S(\nu_a,\mu)$ (v1's local abbreviation $\nu:=\nu_a$ written out); items; the inequality of (c) displayed |
| lem:J-zero | Lemma C.2 | identical |
| lem:D | Lemma C.3 | $\nu,\nu',L\to\nu_a,\nu'_a,L_a$ (v1's local abbreviations written out); in (a) the bound $D_a(c)\le1/\mathcal K_0<\infty$ stated first, the supremum displayed |
| lem:index | Lemma C.4 | identical |
| sec:proof-lower | Appendix E, Proof of Proposition 4.2 | section |
| cite:GMS19-6 | Lemma A.1 | restated in the paper's notation: two bandit problems $\nu$, $\tilde\nu$ (v1: $\nu,\nu'$) with $\bar K$ arms, the same learner, horizon $T$, $Z$ measurable for the history up to $T$; the inequality is [GMS19, (6)], as in v1 (quantifiers made explicit, as in the source) |
| cite:GMS19-11 | Lemma A.2 | **changed, as required**: v1 stated $\mathrm{kl}(p,q)\ge p\log(1/q)-\log2$ (not printed in [GMS19]); v2 states (11) as printed (the identity and its two marked bounds), with $q\to\tilde p$. v1's inequality is the new Lemma lem:kl-lower |
| lem:deviation | Lemma D.7 | renamed $\rho\to\varrho$, $K_\rho\to H_\varrho$; definition of $H_\varrho$ displayed; "Then, for every $u\ge0$" |
| lem:source | Lemma D.8 | renamed $Z\to\Lambda$ |
| lem:delta | Lemma D.9 | identical |
| def:proof-notation | Definition D.1 | renamed $A_T,B_T\to\mathcal A_T,\mathcal B_T$; "let $\Delta_a:=\dots$, and let $\eta:=\dots$" |
| lem:decomposition | Lemma D.2 | renamed $\mathcal A_T,\mathcal B_T$ |
| lem:optimal-arm | Lemma D.3 | renamed $\mathcal A_T$; "and let $C_2:=\dots$. Then, for every …" |
| lem:sub-reduction | Lemma D.4 | renamed $\mathcal B_T$, $\mathcal B^0_T$; $\Phi_s$ displayed |
| lem:sub-kl | Lemma D.5 | renamed $k_\varepsilon\to\mathcal K_\varepsilon$, $r_\xi\to\varrho_\xi$, $\mathcal B^0_T$ |
| lem:sub-constant | Lemma D.6 | renamed $r_0\to\varrho_0$, $\mathcal B_T$ |
| lem:criterion-point | Lemma F.1 | identical up to punctuation ("$c\ge0$ and $x_0>0$") |
| lem:weak-duality | Lemma G.1 | renamed $\kappa\to\sigma$, $A\to\phi$, $B\to\phi'$; "let $g$ be …, and let $\zeta,\zeta'$ be …" |
| sec:sanity | Section 9, Examples and special cases | the process items moved to this dossier (§3) |
| ex:bernoulli | Example 9.1 | reworded ("Let …", "For the mean gap, TV, …"); same numbers |
| ex:no-drift | Example 9.2 | reworded; the table of certified values is Table 2 (same numbers); the threshold computation displayed |
| ex:w1-gain | Example 9.3 | reworded ($\mu^\star$ and $L_a$ given before $W_1(\nu_a,\nu'_a)$); same numbers |
| sec:weak | §8.2 Where the difficulty lies | the three steps named there; the "Weak points" list moved to this dossier (§4) |
| sec:open | Section 11, Open questions | section |
| oq:nonparametric | Open question 1 | "Extends D8" moved to `\extends{D8}`; "$B$ in Lemma lem:weak-duality" → "$\phi'$" (renaming); same question |
| oq:second-order | Open question 2 | "as in K3" → "the order of the second-order term of KL-UCB-Transfer for the mean drift, $O((\log T)^{4/5}(\log\log T)^{1/5})$ [PMRM26, Theorem 3]"; `\extends{D8, D7}`; same question |
| oq:misspecification | Open question 3 | "as in K5" / "of K5" → [PMRM26, Theorem 5]; $\mu'_1:=m(\nu'_1)$ defined; "iff" → "if and only if"; `\extends{D8}` (v1: "D8(c) and K5"); same question |
| oq:random | Open question 4 | "as in the roadmap (…)" → the description in the parentheses; "the analogue of K3(i)" → "of [PMRM26, Theorem 3(i)]"; `\extends{D1, D8}`; same question |
| sec:attribution | Appendix H, Sources of the techniques | the table without "(to be checked)" (see §6); the "Searches" paragraph moved to this dossier (§5) |

**New labels of version 2.** Node: lem:kl-lower (Lemma E.1, a consequence of cite:GMS19-11, as
D5 requires). Not nodes: sec:intro, sec:closest (kept), sec:upper, sec:lower, sec:meaning,
sec:mean-drift, sec:overview, sec:overview-upper, sec:map, sec:examples, sec:degenerate,
sec:numerics, sec:cited, sec:proof-J, sec:proof-upper, sec:concentration, sec:optimal-arm,
sec:suboptimal-arm, sec:proof-structure, sec:proof-duality, sec:notation; eq:sup-form (the
supremum form, Lemma lem:D(a), displayed in the introduction); fig:no-drift; tab:comparison;
tab:no-drift; alg:index (Algorithm 1, the pseudo-code of def:algo). Second pass (2026-11-16), not
nodes: sec:related, sec:algorithm, sec:conclusion; eq:rate, eq:index (the exploration rate and the
index, displayed inside def:algo); one subsection label per appendix proof, sec:proof-lem-<name> and
sec:proof-prop-<name> (sec:optimal-arm and sec:suboptimal-arm now label the proofs of
lem:optimal-arm and lem:sub-reduction). No label was removed or renamed.

## 9. Presentation revision v2, second pass (2026-11-16): the owner's house style

Same pull request (#36), version still 2. The presentation is rewritten in the house style of
docs/writing.md §2 and §2a (criterion W15, merged on main), whose model is the owner's paper
arXiv:2610.21582 [PMRM26], following the approved example P005. No statement and no proof changed
in substance.

**Structure (current numbering).**
1. Introduction, ending with `\paragraph{Our contributions}` (items pointing to Definition 5.1,
   Theorem 6.1, Corollary 6.2, Proposition 4.2, Lemma C.3, Propositions 7.1–7.6, Section 9) and
   `\paragraph{Outline}`.
2. Related work and context (label sec:related, and sec:closest kept on it): run-in themes (transfer
   with a drift between means; KL-UCB and laws on a finite support; historical and offline data;
   structured bandits), Table 1, "Closest related work" (why each does not give thm:main), "Gap with
   the literature", "Techniques".
3. Problem formulation: 3.1 classical setting (def:laws and the classical bandit on $S$), 3.2
   distances (def:ipm), 3.3 transfer setting (def:model, def:class), "Notational convention".
4. Lower bound and the optimal constant: 4.1 the classical lower bound recalled, 4.2 def:constant,
   4.3 prop:lower with "(See the proof in Appendix E)" and the two relation paragraphs, 4.4 what the
   constant means.
5. The algorithm: 5.1 KL-UCB and KL-UCB-Transfer recalled, 5.2 one sentence of intuition, def:algo
   with the rate and the index displayed in numbered equations, a sentence on the shared budget,
   Algorithm 1, then "Computation", "Without source data it is KL-UCB on $S$", "Relation with
   KL-UCB-Transfer".
6. Regret upper bound (sec:main): the classical KL-UCB bound recalled, thm:main with its quantifiers
   first and both bounds displayed, cor:optimal, each followed by "(See the proof in Appendix D)",
   then "Comparison with the lower bound", "Safety", "Nature of the constants", "Scope"; 6.1
   Comparison with published bounds (sec:mean-drift).
7. When does the law help? (sec:structure): the six propositions, each followed by "(See the proof
   in Subsection F.x)", with interpretation paragraphs.
8. How the proofs work (sec:overview): the decomposition displayed, Steps 1–3, where the difficulty
   lies, the lower bound, the structure results, the map of the appendices.
9. Examples and special cases: 9.1 numerical setup, 9.2 the four instances with interpretation
   paragraphs, 9.3 degenerate cases.
10. Conclusion (new). 11. Open questions (title kept for certify.py; the four questions unchanged).

Appendices: A Useful lemmas (cited nodes titled "From Garivier et al. (2019), inequality (6)" and
"(11)"); B Tools on the simplex and C The programme $J_a$ and the constant $D_a$ (the statements with
a "Role." line and "(See the proof in Subsection …)", then one subsection per proof); D Proof of
Theorem 6.1 and Corollary 6.2 (def:proof-notation; the decomposition lem:decomposition with its two
terms written under `\underbrace`; one lemma per term, each followed by "(See the proof in
Subsection …)" and a sentence saying whether it is classical or new; the proof of the theorem as an
aligned chain from the lemmas, with the choice $\varepsilon:=\min(\varrho_0,1,\Delta_a)/2$ and its
reason; the proof of the corollary; the three concentration lemmas; one subsection per lemma); E
Proof of Proposition 4.2 (lem:kl-lower, the proof, then the proof of the lemma); F structure results
(lem:criterion-point, then one subsection per proof); G weak duality; H sources; I notation ("Every
symbol is a link to its definition").

**Moved.** def:proof-notation, lem:decomposition and the proof of thm:main from the main text
(first pass, Section 4.1) to Appendix D; the proof of cor:optimal from after the corollary to
Appendix D. Every proof away from its statement carries `\proves`.

**Navigation.** 58 anchors `\dt{s:…}`; after its definition, every defined symbol is typed with its
link macro (`\sy`) in statements, proofs, displays and tables (a script replaced the plain forms,
and a second one checks that every link has an anchor and every anchor is used); the defined word
"admissible" is a `\term`; the algorithm's name links to Algorithm 1. Anchor names avoid a letter
followed by digits (s:Kzero, s:Cone, s:Wone…) because CI reads such strings as KNOWN or roadmap
ids. A few distant results are cited with their name in italics (A6d). Symbols that are not defined
with `:=` (the given laws $\nu_k,\nu'_k$, the bounds $L_k$, the sizes $N'_k$, the existential radii
$\varrho_\xi,\varrho_0$, local abbreviations inside one proof) are not linked; the local parameters
$\eta$ of lem:source and $\theta$ of lem:deviation and lem:types are deliberately plain, since they
are not the $\eta$, $\theta$ of def:proof-notation.

**Citations.** Author-year (natbib with `round`, `plainnat`): the owner's rule of 2026-11-16,
relayed by the coordinator; `natbib` is not in the package list of AGENTS.md §5.2 and is added at the
owner's request. Keys unchanged; every entry of refs.bib has author and year.

**Statements unchanged.** A script compared every node of this commit with the previous head
(ac41a8a) after expanding the macros of each version and removing spaces, braces and display
delimiters: the same 39 nodes, labels and environments, the same `\uses` of every statement and of
every one of the 30 proofs (the only reference outside `\uses` is, as before, the pointer of
prop:w1's proof to the case analysis of prop:bernoulli's proof). 21 statements differ in layout or
wording only:

| Label | Second-pass change (same hypotheses and conclusions) |
|---|---|
| thm:main | quantifiers first: "For every finite $S$ …, every integral probability metric …, every $K\ge2$ and $L$, every $(\nu,\nu')$ such that …, and with deterministic source sizes …, the learner satisfies"; both bounds displayed |
| cor:optimal | the two regret limits displayed with $\lim_{T\to\infty}$ |
| prop:lower, lem:J, lem:ipm-order, lem:sub-reduction, lem:weak-duality, cite:GMS19-6, cite:GMS19-11 | `\[ \]` replaced by `equation*` (same formula) |
| lem:D | the ratio $R(q,q')$ displayed as a fraction |
| lem:deviation, lem:source | the definition of $H_\varrho$ and the bound on $\mathbb E e^\Lambda$ in `equation*`; the final bound of lem:deviation displayed |
| lem:sub-kl | the bound displayed, "with $C_3:=$" written ", $C_3:=$" inside the display |
| lem:decomposition | the two terms written out under `\underbrace` with their names $\mathcal A_T$, $\mathcal B_T$ (the sums of def:proof-notation) |
| def:laws | one sentence per quantity: "Its largest point is $x_{\max}:=\max S$ …"; the set of probability vectors written $\Delta_S:=\{q\in[0,\infty)^S:\sum_yq(y)=1\}$; mean, support and distribution function in one display; KL, TV and $\mathcal K_S$ each displayed |
| def:ipm | the four examples as a list ("$d=\mathrm{TV}$, with $\mathcal F$ …", "so that …") |
| def:model | "The mean of arm $k$ is $\mu_k:=m(\nu_k)$, and the best mean is $\mu^\star:=\max_k\mu_k$"; the three data families as a list; $N_k(t)$ displayed ("the number of pulls of arm $k$ up to round $t$") |
| def:class | "The class of instances is" $\Theta:=\dots$, displayed |
| def:constant | "the set of alternative pairs is", "the programme is", "The constant is", each displayed |
| def:algo | "The exploration rate is" (equation eq:rate); the index in equation eq:index |
| def:proof-notation | "Its gap is $\Delta_a:=\dots$. The margin of the optimal arm is $\eta:=\dots$" displayed; "and the two counts are" |

**New text outside the nodes (for the scope referee).**
- §4.1: the classical lower bound recalled with [BK96] (a classic cited for a standard fact; only
  its abstract was read, see §6), and its relation with prop:lower without source.
- §5.1: the KL-UCB index on $S$ displayed; KL-UCB-Transfer described in words [PMRM26, §5.2].
- §6, opening: the bound of empirical KL-UCB [CGMMS13, Theorem 2] with $\mathcal K_{\inf}$ over
  finitely supported laws of $[0,1]$, equal to $\mathcal K_S$ when $1\in S$ (as already said in
  §6.1), and thm:main(i) without source as its known-support version.
- §2 "Gap with the literature" (what is new, "as far as we found") and §10 Conclusion: summaries of
  the results, no new claim.
- §7: "Part (a) is new" after prop:criteria (D8's comparison with the mean case, see §2 of this
  dossier); the interpretation after prop:threshold (meaning of $\omega_d$ and $G^d$; total
  variation can lower the threshold: Example 9.2 has $1/G^{\rm TV}=23.505$ while
  $\mathcal K'_0=0$).
- §9.2: "Interpretation of Table 2" (from the certified values: $6.0285-5.7289=0.2996$ for the first
  unit of $c$, and $0.0831/0.505\approx0.16$ per unit on $[23,23.505]$; the decrease slows, as a
  nonincreasing convex function does) and "Interpretation of Example 9.3" ($(17.6085-14.7889)/17.6085
  =0.160$ at $c=10$).
- §8.1 "Step 3: the combination": a summary of the proof of thm:main.
- Appendix A: the textbook facts used by name (Gibbs' inequality, convexity of KL, Abel summation,
  attainment of the infimum of a lower semicontinuous function on a compact set).
- "Role." lines for lem:index, lem:criterion-point, lem:weak-duality, lem:kl-lower; the
  classical/new sentence after each lemma of Appendix D (lem:optimal-arm: the source handled as in
  [PMRM26, Lemma 17]; lem:sub-reduction, lem:sub-kl: classical; lem:sub-constant: new).

**Length.** The reader PDF has 41 pages (first pass: 31): the main text is 19 pages and
Theorem 6.1 is on page 10. This exceeds the "about 15 pages" of docs/writing.md §2: the displays
and the short paragraphs of the house style, the recalled classical results and the separate
sections (related work, algorithm, conclusion) cost about five pages. Shortening would mean moving
Section 7's interpretations or Section 9 to the appendices; left to the owner.

## 10. Revision round 1 (2026-11-16): answers to the scope referee

Report of the scope referee on head 3250af9 (verdict major: one G, seven P). Presentation only: no
statement and no proof changed in substance; no label removed; new labels `sec:experiments`,
`tab:simulation` (not nodes). `sec:degenerate` keeps its label and moves from a subsection of
Section 9 to an appendix.

| ID | What was done |
|---|---|
| SC1.1 (G) | The "Mean gap" item of the degenerate cases (now Appendix H) no longer cites [PMRM26, Proposition 4] for the boundary $m(\nu'_a)=\mu^\star-L_a$. It says that Proposition 4 leaves the boundary out, and that for deterministic sizes [PMRM26, Theorem 2(i)] (hypothesis $\mu'_a\le\mu_1-L_a$; their $\mathcal K_{\inf}$ is over laws of mean $>$ the level, so $\mathcal K_{\inf}(\nu'_a,\mu'_a)=0$) and [PMRM26, Theorem 3(ii)] (hypothesis $\mu'_a\ge\mu_1-L_a$) both give $1/\mathcal K_{\inf}(\nu_a,\mu_1)$. Checked in the arXiv HTML v1 on 2026-11-16: Theorem 3(i) is for $\mu'_a<\mu_1-L_a$, (ii) for $\mu'_a\ge\mu_1-L_a$; Proposition 4 says "except possibly when $\mu'_a=\mu_1-L_a$"; $\mathcal K_{\inf}$ (§4.1) uses $\tilde\mu_k>\mu_1$. Section 3 of this dossier corrected likewise (K4). |
| SC1.2 (P, W16) | New Section 9.3 "Numerical experiments": a simulation of KL-UCB, KL-UCB-Transfer and KL-UCB-TV-Transfer on the two-armed instance of Section 9.2 (see below). |
| SC1.3 (P) | Main text shortened: the degenerate cases moved to a new Appendix H; the "Precision" paragraph of Section 9.1 moved to Appendix G; Sections 8.3 and 8.4 merged into one short subsection (the $2K$-arm construction, the $W_1$ display and the TV sentence are in Appendices E and F); the paragraph "Alternatives" of Section 4.4 (a repetition of the introduction) reduced to one sentence; the paragraph "Comparison with KL-UCB" of Section 6.1 merged into the opening of Section 6. See "Length" below. |
| SC1.4 (P) | The introduction defines $\mathcal K_0$, $\mathcal K'_0$ in words at first use, and says that the superscript of $D^{\rm mean}_a$, $D^{W_1}_a$, $D^{\rm TV}_a$ names the distance. |
| SC1.5 (P) | "except possibly at the boundary $\mu'_a=\mu^\star-L_a$" added in Section 2 (transfer with a drift between means) and in Section 6.1 (with a pointer to Appendix H). |
| SC1.6 (P) | Renamed: the ratio $R(q,q')$ of Lemma lem:D is now $\Upsilon_c(q,q')$ (macro `\Rat`; the two plain $R$ of lem:D and of its proof, Step 6, now use the macro); the simplex $\Delta_S$ is now $\mathcal P_S$ (macro `\Simp`, and its definition in def:laws), so that $\Delta_a$ is only the gap. $\rho_c$, suggested by the referee, was not used: $\rho$ is already a generic law ($\mathcal K_S(\rho,\ell)$, Lemma lem:projection). Statements of def:laws and lem:D change in notation only. |
| SC1.7 (P) | "In short" (Section 7): "$D^{\rm mean}_a=(1-c\mathcal K'_0)_+/\mathcal K_0$ when $m(\nu'_a)\le\mu^\star+L_a$". |
| SC1.8 (P) | Proof of lem:optimal-arm, Setting: "with the parameter $\eta$ of Lemma lem:source equal to the margin $\eta$ of Definition def:proof-notation". |

**The simulation (SC1.2).** Scripts in `notebook/calculs/`: `sim.py` (the three learners, the index
computations), `test_sim.py` (checks of the indices against `d8.py`: the closed-form TV projection
against a grid over the TV ball, 200 random cases; the indices against the independent SLSQP solver
of the programme and the dual $\mathcal K_S$, 60 random inputs per learner, largest relative error
of the budget at the computed index $1.7\cdot10^{-5}$; output below), `run_sim.py` (the driver),
`sim.txt` (the output). Each index is the right end of the interval of means $\mu$ where the
smallest budget over the pairs with $m(q)=\mu$ is at most $\delta_t$ (convex in $\mu$); on
$S=\{0,\frac12,1\}$ the laws of mean $\mu$ form a segment, minimised on a refined grid; for TV the
best $q'$ is the KL projection of $\hat\nu'_k$ on a TV ball, in closed form by the KKT conditions
($q'=\min(\max(q,s_-\hat\nu'),s_+\hat\nu')$ on $\mathrm{supp}\,\hat\nu'$, mass off the support
removed first). A first attempt with SLSQP on the whole index programme stopped short of the
maximum on random inputs (dead end, notebook). The simulation illustrates; it is not evidence for
the constants (docs/writing.md W16), and the paper says so.

Results (`notebook/calculs/sim.txt`, $T=10^4$, 40 runs each; mean of $N_2(T)$ ± standard error,
first-order value in brackets): KL-UCB $56.4\pm2.1$ [55.5]; KL-UCB-Transfer $c=5$: $56.7\pm2.6$
[55.5], $c=25$: $59.2\pm2.4$ [55.5]; KL-UCB-TV-Transfer $c=5$: $37.4\pm2.2$ [42.0], $c=25$:
$3.2\pm0.7$ [0], with 23 of the 40 runs at 1 (the initial pull only).

**Length.** Reader PDF 43 pages (before this round 41). Theorem 6.1 is on page 10 (it had moved to
page 11 with the definitions added to the introduction for SC1.4, and is back on page 10 after the
moves); the main text is pages 1–19, as before this round, but it now contains Section 9.3
(simulations, about one page) and the definitions of SC1.4. Moved out of the main text in this
round: the degenerate cases, Examples ex:bernoulli and ex:w1-gain with the interpretation of the
latter (all three to Appendix H, "Further examples and degenerate cases"); the "Precision"
paragraph (Appendix G); the paragraph on the class $\mathcal C_L$ of [PMRM26] (opening of
Appendix E; one sentence remains after prop:lower); Sections 8.3–8.4 merged and shortened;
"Alternatives" in 4.4 and "Comparison with KL-UCB" in 6.1 folded into neighbouring text. Reaching
about 15 pages would need to move main statements (the six propositions of Section 7) or the proof
overview out of the main text, which docs/writing.md §2 keeps there; the theorem cannot be within 5
pages with the introduction, the related work (with Table 1) and the setting that the house style
puts before it, and the introduction states it, with its constant, on page 2.
