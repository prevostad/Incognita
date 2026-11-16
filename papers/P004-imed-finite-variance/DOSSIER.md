# Dossier of P004-imed-finite-variance, version 1

Refereed and versioned with `paper.tex`, never compiled into the PDF: what the referees and the
owner need and the reader does not. It changes only with a new version of `paper.tex` after
acceptance. Private KNOWN entries are cited by id only, never quoted (none is used here).

Origin: a research report of an agent in the owner's session (2026-11-16, outside the repository,
`pistes_claude2/D9_moments/rapport.md`) and its independent verification by another agent
(`pistes_claude2/D9_moments/verification.md`, **verdict: accept**, eleven defects V1–V11, all of
class P). The paper states only what the report labels **[proved]**; its **[sketched]** and
**[conjectured]** items went to the open questions of the paper or to this dossier (list at the end
of "Roadmap correspondence"). Labels below are those of `paper.tex`.

## Roadmap correspondence

- **Item served:** D9 of StochasticBandits, verbatim: "Prove that IMED (K46) is asymptotically
  optimal on semi-bounded laws when the arms only have a finite moment of order $2+p$ for some
  $p>0$, instead of a finite moment generating function near 0, or give a counterexample
  (conjecture of [HT15, Section 9], K60). Answer: theorem or refutation."
- **How:** `thm:main` and `cor:optimal`(b) with $r=2+p$ prove the conjecture: IMED is consistent
  and uniformly fast convergent on $\mathcal M_{2+p}=\mathcal S_{2+p}\setminus\{\delta_1\}$, and
  $\lim_T\mathbb E N_i(T)/\log T=1/\mathcal K_{\inf}(\nu_i,m^\star;\mathcal M_{2+p})$, the constant
  of the lower bound `cite:GMS19-thm1` on that class (`lem:class` identifies it with the
  semi-bounded $\mathcal K_{\inf}$). The law $\delta_1$ is excluded because an instance with an arm
  $\delta_1$ has $m^\star=1$, which [HT15, Theorem 3] excludes too.
- **More than asked:** (1) $p=0$ suffices, and only for **one optimal arm**: `thm:main` assumes a
  finite variance of one optimal arm and finite means elsewhere, and is a finite-time bound.
  (2) The converse on the scale of power-law tails (`thm:counter`, `cor:pareto`): with a lower
  tail $\ge\kappa y^{-q}$, $1<q<2$, IMED is not consistent; with a tail $\asymp y^{-2}$ its
  $\liminf$ exceeds the lower-bound constant by $\ge\kappa/(4e)$. So, for power tails, the moment
  of order two is the threshold for IMED. (3) Two reusable tools: `lem:sup` (counting by a
  supremum) and `prop:key` ($\Gamma(P,\mu)<\infty$ on $\mathcal S_2$).
- **What D9 asks that the paper does not give:** nothing of "theorem or refutation". Not given (and
  said in words in the paragraph "Scope" after `thm:main` and in the open questions): a rate for the second-order term (the
  report sketches $O((\log n)^{12/13})$, `oq:second-order`); whether the variance is necessary
  beyond power tails (tails $1/(y^2\log y)$, `oq:boundary`(a)); the exact excess at $q=2$
  (`oq:boundary`(b)); whether some algorithm is optimal with finite means only (`oq:finite-mean`).
- **Acceptance criteria of the roadmap, one by one:**
  1. Main result states the class ($\nu\in\mathcal S^\alpha$, $m^\star<1$, one optimal arm in
     $\mathcal S_2$; `cor:optimal`: $\mathcal M_r^\alpha$), the algorithm (IMED, anytime, any tie
     rule) and the criterion (finite time, every $T\ge1$; first order). Met.
  2. Closest known: below (K1, K8, K11, K16, K17, K18, K46, K60, K63; Appendix B of the roadmap:
     only the lower bound of LMLExplore, K1). Met.
  3. Sanity checks: one instance with all hypotheses (the example of `sec:examples`); Bernoulli $K=2$ against K1
     (the degenerate cases of `sec:examples`: $\mathcal K_{\inf}=\mathrm{kl}$). Met.
  4. Upper bound: the algorithm is defined completely (Algorithm 1, Definition `def:imed`:
     initialisation, index, convention for leaders, tie rule, anytime). Lower bounds
     (`thm:counter`) are for IMED only, any tie rule; `cor:pareto`(b) names the class of learners of
     the comparison (uniformly fast convergent on $\mathcal C$). D9 does not mention computation;
     the subsection of `sec:algorithm` on IMED says that each index is a one-dimensional concave
     maximisation.
  5. Constants: explicit, except $\Gamma(\nu_j,m^\star-\delta)$ (explicit bound `eq:gammabound`
     of Appendix D, through an exponent $\gamma$ that exists by continuity) and $T_0$ in
     `thm:counter`(i) (existential, its dependence stated). Met.
  6. "Optimal" never defined; `cor:optimal` pairs the two bounds in the class $\mathcal M_r$; the
     introduction uses "asymptotically optimal" only as a shorthand for this pair. Met.
  7. Not routine: see "Closest known" (the route of [HT15] needs a third moment; the supremum step
     and `prop:key` are new). For the referee to judge.
  8. Not a lemma paper. `lem:sup`, `prop:key` and `lem:class` are general (any instance, any law of
     $\mathcal S_2$, any $r\ge1$) and used by `thm:main` and `cor:optimal`.
  9. D9 asks for a moment condition, not for constants; the paper does not claim improved
     constants.
  10. Not among the "not important on their own" results.
- **Conventions changed:** (1) IMED: the divergence term of an empirical leader is set to 0
  (`def:imed`). It equals [HT15, Algorithm 1] whenever $\hat m^\star(t)<1$; when $\hat m^\star(t)=1$
  every index of [HT15] is $+\infty$ and the paper pulls a leader (one admissible choice of their
  arbitrary tie rule). Declared after `def:imed`, and explained in the remark of `sec:upper-ht15`
  (moved there in revision round 1, next to `cite:HT15-thm3`), with the reason (the proof of
  [HT15, Theorem 3] needs it; without it a tie rule can pull a suboptimal arm forever with positive
  probability when an optimal arm has an atom at 1). (2) Notation: $\mathcal S$ for the
  semi-bounded laws (HT15's $\mathcal A$ clashes with the pinned $\mathcal A^\star(\nu)$), $\lambda$
  for the dual variable (HT15's $\nu$ clashes with the pinned instance $\nu$), rounds from 0 (pinned
  Lean convention). $\mathcal K_{\inf}$ with the strict inequality, as pinned.
- **Where the report's unproved items went:**
  - [sketched] second order $O((\log n)^{12/13})$ (report, Remark 1): `oq:second-order`, as a
    question; not stated.
  - [sketched] optimality below the variance, tails $1/(y^2\log y)$ (Remark 2): `oq:boundary`(a).
  - [conjectured] exact limit $1/D_{\inf}+2\kappa/(e\,m^2)$ at $q=2$ (Remark 3): `oq:boundary`(b).
  - [sketched] converse of Proposition 2, $\Gamma(P,\mu)<\infty\iff P\in\mathcal S_2$, via
    $\sup_sw_s\ge L:=\sup\{s:\hat m_s\le\mu\}$ and the last-exit-time moment theorem of Janson
    (1986, not read): not claimed in the paper; since revision round 1, the paragraph "Relation
    with the last exit time" after `prop:key` states $\sup_sw_s\ge L$ (proved there in one line)
    and cites [CL75, Jan86] as "see also" for $\mathbb EL<\infty$ under a second moment of $X^-$.
  - [sketched] "the summed bound of [HT15] needs three moments" (report §2): now **proved** in the
    paper (`lem:three-moments`, a node since revision round 1, proof in its own appendix;
    one-big-jump and Bonferroni), with Chow–Lai and Baum–Katz cited as "see also" (V7, SC1.1).
  - [conjectured] KL-UCB optimal with finite means only (report): since revision round 1, reduced
    to [PA26, Theorem 3.1] by `lem:pa-assumptions` (the paragraph "Another algorithm" of
    `sec:counter`, stated as a reduction, not as a theorem); a robust-level IMED: `oq:finite-mean`,
    restated for `IMED`-$\rho$.
  - Non-parametric Thompson sampling (report OQ5, roadmap D10a): `oq:thompson`.

## Closest known

- **K11** ([HT15, Theorems 2, 3, 5, Corollary 4]). Theorem 3 assumes an MGF near 0 for one
  optimal arm $j$. *Attempt to derive `thm:main`:* keep [HT15]'s proof and only replace
  Proposition 11. Its third term is
  $6e/((1-1/\lambda_{j})(1-e^{-(1-1/\lambda_j)\Lambda_j^*(m^\star-\delta)})^3)$; without an exponential
  moment of the lower tail, Cramér's rate $\Lambda_j^*(m^\star-\delta)$ is $0$ and the term is
  infinite (for $P_{3,0.1}$ of the example of `sec:examples`, for instance). Replacing Cramér's bound by a polynomial
  one fails at (26): the bound $\sum_t\mathbb 1\{\hat\mu_{j,t}\le\mu\}te^{tD_{\inf}}$ has expectation
  $\ge\sum_tt\,\mathbb P(\hat\mu_{j,t}\le\mu)$, which is infinite when
  $\mathbb E[(X^-)^3]=\infty$ (proved in `lem:three-moments`). So [HT15]'s route gives at best
  three moments, and only with a new polynomial version of Proposition 11. The new step (`lem:sup`(b),
  the supremum) is what brings two moments; `prop:key` is new. Theorem 5 (O(1) remainder) assumes
  MGFs for every arm and is not touched.
- **K46** (IMED, [HT15, Algorithm 1]): the algorithm; the paper's IMED is a special case (convention
  for leaders, above).
- **K60** ([HT15, §9]): the conjecture; answered (`cor:optimal` with $r=2+p$) and sharpened
  (`thm:main`, `thm:counter`). [HT15]'s own suggestion, their condition (30)
  $\sum_tt^p\Pr[|\hat\mu_{i,t}-\mu_i|>\delta]<\infty$, applied to (26), needs $p=1$, hence three
  moments (Baum–Katz; Chow–Lai, whom [HT15, §9] cite), consistent with `lem:three-moments`.
- **K17** ([AJK21, Theorem 1, Corollary 2]): exact first order with KLinf-UCB on
  $\mathcal L_B=\{\mathbb E|X|^{1+\varepsilon}\le B\}$, $B,\varepsilon$ known, $\mathcal K_{\inf}$ over
  $\mathcal L_B$ with $\ge$. *Attempt:* restrict $\mathcal L_B$ to semi-bounded laws. Fails: the class
  depends on a known $B$ (IMED knows none), its $\mathrm{KL}_{\inf}^{\mathcal L}$ is a different
  constant (an infimum over $\mathcal L_B$, not over $\mathcal S$), the algorithm differs, and nothing
  is said about IMED or about the semi-bounded model with an unknown variance.
- **K18** ([BCL13, Theorem 1], Robust-UCB): logarithmic regret with a known moment bound, constant
  polynomial in $u/\Delta$, not $1/\mathcal K_{\inf}$. Cannot give an exact first order.
- **K8** ([BCL13, Theorem 2]): with only $1+\varepsilon$ moments, a $\Delta^{-1/\varepsilon}$
  dependence is necessary in $\mathcal L$. Not a contradiction with `thm:main` (semi-bounded, finite
  variance of one optimal arm), nor a source of `thm:counter`: the instances of `cor:pareto` have a
  finite lower-bound constant $\log\frac1{1-m}$, and `thm:counter` is about IMED only.
- **K1** (lower bound [LS, Theorem 16.2], [GMS19, Theorem 1]; LMLExplore in Lean): used through
  `cite:GMS19-thm1` in `cor:optimal` and `cor:pareto`. Consistent.
- **K16** ([RH20, Theorem 5], NPTS on $[0,1]$): bounded rewards; the semi-bounded analogue is
  `oq:thompson` (roadmap D10a).
- **K63** ([LS, §16.4]: the semi-bounded case is "murky"): context only, not cited in the paper.
- **K5**, **K21** (second order): not used; `oq:second-order` asks the analogue under a variance.
- **Library papers:** P000 (batched, $\mathcal K_{\inf}$ on $[0,1]$ of [HT10]) and P002 (transfer):
  no overlap, no dependence (`depends_on = []`).
- **Published, outside KNOWN** (from the searches, below): Do–Nguyen, arXiv:2611.12140 (Nov 2026,
  "Visible Tails"), the closest recent work: it notes that [HT15]'s theorem needs an MGF for an
  optimal arm and makes no claim on IMED under finite moments (read by the research agent: abstract
  and the first 100k characters of the HTML; not cited in the paper, whose citations rest only on
  parts recorded in `literature/index.md`). None of the works below gives `thm:main` or
  `thm:counter`.
- **[BSH23]** (Baudry–Suzuki–Honda, arXiv:2303.06058v3, §4.4 read in revision round 1,
  `literature/notes/BSH23.md`): MED optimal on $\mathcal F_{h,B}=\{\mathbb E h(|X|)<B,\ \mathbb
  E h(|X|)^{2+\epsilon}<\infty\}$ with $h$ and $B$ **known**. *Attempt to derive `thm:main`:* fails;
  a different algorithm (randomised MED), a known moment bound, laws on $\mathbb R$; nothing on IMED
  or on the semi-bounded model with an unknown variance. Compared in `sec:related` and Table 1.
- **[PA26]** (Panda–Agrawal, arXiv:2604.14876v1, ISIT 2026; §2.2, Theorem 3.1 and the outline of
  its proof read in revision round 1, `literature/notes/PA26.md`): KLinf-UCB with
  $f_a(t)=\log t+2\log\log t+g(N_a(t))$ is optimal on every class satisfying their Assumptions 2.3
  (time-uniform upper deviations at the mean) and 2.4 (quadratic-exponential lower deviations).
  *Attempt to derive `thm:main`:* impossible, it is about KLinf-UCB, not IMED. *Bearing on
  `oq:finite-mean`* (the referee's SC1.3): both assumptions hold on $\mathcal M_1$ with a finite mean
  only, at the levels below 1 (`lem:pa-assumptions`: (a) Ville/Doob for a mixture over the dual
  variable, with the universal-portfolio factor $n+1$; (b) the Chernoff bound of `lem:subopt` with a
  rate $\ge d^2/(2C)$; (c) their $\mathrm{KL}_{\inf}$ with $\ge$ over $\mathcal M_1$ equals
  $\mathcal K_{\inf}$). Assumption 2.4 fails literally at levels $\ge1$ (both sides $+\infty$), as for
  their own bounded-support example above $b$; the outline of their proof (A.2) uses it at $\mu_1$
  only. So KLinf-UCB plausibly answers the former `oq:finite-mean`; the paper states this as a
  reduction (paragraph "Another algorithm" of `sec:counter`), since their proof (through AJK21,
  Lemmas 14 and 18) was not checked line by line, and restates `oq:finite-mean` for an index of the
  IMED type (`IMED`-$\rho$).

## Sanity checks

- **Degenerate cases.**
  - $K=2$, Bernoulli arms $p_2<p_1<1$: the dual gives $\mathcal K_{\inf}(\mathrm{Ber}(p),\mu)=\mathrm{kl}(p,\mu)$
    (maximiser $\lambda=(\mu-p)/(\mu(1-\mu))\le1/(1-\mu)$), so `cor:optimal` gives
    $1/\mathrm{kl}(p_2,p_1)$, the Lai–Robbins constant (K1). `sec:examples`.
  - Bounded supports: all moments finite; `thm:main` applies; first order equal to [HT15, Cor. 4].
  - $m^\star=1$: excluded (an arm $\delta_1$); then every non-leader has an infinite index.
  - A deterministic optimal arm $\delta_{m^\star}$: $\Gamma=0$ (its empirical mean is never below
    $m^\star-\delta$); the bound reduces to the suboptimal-arm terms.
  - Several optimal arms: one with a finite variance suffices since $\hat m^\star\ge\hat m_j$; the
    counterexample needs the optimal arm with the heavy tail to be the only optimal arm.
  - Ties: every result holds for every tie rule (measurable in the seed and the past); the
    all-infinite case $\hat m^\star=1$ is fixed by the convention for leaders.
  - Infinite divergences: $\mathcal K_{\inf}(P,\mu)=+\infty$ for $\mu\ge1$; $0\cdot\infty=0$ in
    $w_s$; $\sup\emptyset$ conventions in `lem:sup`.
  - $\nu_2=\delta_0$: $\mathcal K_{\inf}(\delta_0,\mu)=\log\frac1{1-\mu}$, increasing; `lem:explore`
    gives the $\log T/\log\frac1{1-m}$ pulls, which `thm:counter`(ii) adds to.
- **Internal consistency.** `thm:main` needs $q>2$ for Pareto tails (finite variance); `thm:counter`
  needs $q\le2$: no overlap. At $q=2$, `thm:counter`(ii) exceeds the constant that `thm:main` would
  give, and `thm:main` does not apply (infinite variance). `cor:pareto`(b): the lower-bound constant
  for $\delta_0$ is $\log\frac1{1-m}$ in every class between the laws on $\{0,1\}$ and $\mathcal S$
  (checked in its proof), so the comparison is legitimate.
- **Consistency with KNOWN.** KNOWN.md has no `[Lean]` entry of the owner. With the published
  entries: K1 (the lower bound, used), K11 (IMED under an MGF: `thm:main` contains its first order,
  since an MGF near 0 of a law on $(-\infty,1]$ gives all moments), K8 and K17–K18 (different
  models, no contradiction, above).
- **Explicit example with all hypotheses:** the example of `sec:examples`, $(P_{3,1/10},\delta_0)$: $m_1=0.75$, finite
  variance, no MGF of the lower tail, $\mathcal K_{\inf}(\delta_0,0.75)=\log4$. It is in
  $\mathcal M_r^{\{1,2\}}$ for $r\in[2,3)$.
- **Numerics** (illustration only; notebook): Table 2 of the paper. $q=3$: mean of $N_2(T)$ close to
  and below $\log T/\mathcal K_{\inf}$ for $T\ge10^4$; $q=1.5$: mean $\times3.0$ per decade
  ($\sqrt{10}\approx3.16$ for $T^{1/2}$); $q=2$: excess of about 2 pulls at $10^3$–$10^4$, above the
  proved asymptotic $\frac{\varpi}{4e}\log T\approx0.06$–$0.09$. The verification agent re-derived
  $(\ast)$, the grid lemma, the level shift and Lemma 8 numerically: 0 violations out of 6000–8093
  samples each (exact dual by bisection).

## Weak points

The three steps the authors are least sure of, most doubtful first:

1. **`prop:key`, Steps 2–4** (the partition, `eq:split`, the one-jump bound and the several-jumps
   bound). An error there would be fatal for `thm:main`. Checked: the partition is per $s$ and
   $W_s=0$ on $E5_s$; `lem:goodpart` needs no sign condition on $S_s$; in Step 3,
   $Y_{l^\star}\ge s\delta/2$ follows from $W_s>0$, and $Y_{l^\star}>\beta s\ge\beta l^\star$ gives a bound
   uniform in $s$; in Step 4 the bound $\mathbb 1\{B_s=B\}\le\prod_{l\in B}\mathbb 1\{Y_l>\beta s\}$ and
   independence give $(C_1e_s/s)^k$. The verification checked every line of the report's version
   and $(\ast)$ numerically.
2. **`thm:counter`, Steps 1–2** (independence of $Y_s$ from $\{\tau_s\le u\}$ and the frozen index).
   They rest on the table model and on the tie rule being a function of the seed and the past. At
   $s=1$, $\tau_1\in\{0,1\}$ falls in the initialisation, and the step uses that round 1 pulls arm 2
   when $\tau_1=0$. When $\hat m_{1,s}=0$ exactly, arm 1 is also a leader and its index is $\log s$;
   the paper uses $D_1(t)=\mathcal K_{\inf}(\hat\nu_{1,s},0)$ in both cases (`lem:dualfacts`(b)).
3. **`lem:class`** (the law $G^\star$). It relies on the first-order condition of `lem:optimizer`,
   including the boundary case $\lambda^\star=1/(1-\mu)$ (Fatou), and on the mean identity
   $(1-c)(1-\mu-1/\lambda^\star)=0$. The report used the densities read in the text layer of [HT15];
   the paper reproves everything from the dual formula only, and the page image of [HT15, p. 3735]
   was viewed for this paper (the densities match).

Added in revision round 1: **`lem:pa-assumptions`** (new node, used by no other result, only by
the paragraph "Another algorithm" and `oq:finite-mean`). Most delicate: the universal-portfolio
bound of Step 3 (the two integrals over $[\theta^\star,1]$ and $[0,\theta^\star]$, each of the
length of its interval divided by $n+1$) and the constant $C$ of (b) (integrability of
$V^2e^{V^-/2}$ through $\mathbb E e^{-V}\le1$; Step 5). The claim about [PA26, Theorem 3.1] is a
reduction only: its proof was read in outline, through a fetch tool. The method of (a) is that of
[AJK21, Proposition 5] (credited since round 2); what is ours is the one-dimensional semi-bounded
form and the exact factor $n+1$.

Also worth a referee's look: the convention for leaders in `def:imed` (a reader comparing with
[HT15] may see it as a change of algorithm; it is one admissible tie rule of theirs).

## Searches

From the research report (web search, 2026-11-15/16; queries verbatim):

- "IMED Honda Takemura semi-bounded moment condition conjecture heavy tail asymptotically optimal":
  [HT15], arXiv:1202.2277 (its preprint), Baudry–Saux–Maillard arXiv:2111.09724, arXiv:2606.09802
  (drifting bandits; MED analysed only for sub-Gaussian rewards; not read).
- "bandit "semi-bounded" rewards asymptotically optimal Thompson sampling Dirichlet "unbounded from
  below"": Baudry–Saux–Maillard 2021, Riou–Honda 2020, risk-averse TS arXiv:2606.09191
  (sub-Gaussian), KL-Maillard sampling (bounded).
- ""semi-bounded support" bandit IMED OR DMED OR "KL-UCB" 2018..2026": IMED-RL (NeurIPS 2022),
  KL-UCB-switch; nothing on moments.
- "Honda heavy-tailed bandit "minimum empirical divergence" OR IMED Pareto finite variance
  asymptotic optimality 2023 2024 2025": IMED-UB arXiv:2112.01452, Baudry–Suzuki–Honda
  arXiv:2303.06058, Baudry–Pesquerel–Degenne–Maillard NeurIPS 2023.
- ""Honda and Takemura" IMED "moment generating function" assumption removed OR weakened OR relaxed
  "finite variance" bandit": the technical report METR12-03 (= arXiv:1202.2277) and Do–Nguyen,
  arXiv:2611.12140 (9 and 11 Nov 2026).
- ""IMED" bandit "heavy-tailed" OR "infinite variance" OR "polynomial tail" optimal arm lower tail
  empirical mean failure": nothing on IMED under heavy tails.
- "Janson 1986 moments first-passage last-exit times ...": metadata only.

From the verification (web search, 2026-11-16):

- "IMED Honda Takemura semi-bounded rewards finite variance moment condition asymptotic
  optimality"; ""minimum empirical divergence" heavy-tailed rewards "unbounded from below" bandit
  asymptotically optimal moment assumption"; "IMED Honda Takemura conjecture moment generating
  function weakened finite moments bandit 2024 2025 2026"; "bandit rewards bounded above "unbounded
  below" asymptotically optimal "finite variance" KL-inf IMED OR "KL-UCB" OR "Thompson sampling"
  non-parametric"; "IMED algorithm heavy-tailed rewards inconsistent counterexample empirical mean
  outlier regret polynomial"; ""semi-bounded" bandit "second moment" OR "finite variance"
  asymptotically optimal "Honda" 2023 OR 2024 OR 2025 OR 2026 arXiv"; ""Visible Tails" ...",
  ""Regret Tail Characterization ..."", ""Reliable Scale-Free Bandits via Empirical Likelihood"";
  and the Semantic Scholar list of the 124 papers citing [HT15], by title.
- Findings: nothing proves IMED optimal under finite moments, and nothing shows IMED inconsistent
  under heavy lower tails. Closest recent titles (abstracts only): Do–Nguyen arXiv:2611.12140,
  Panda–Agrawal arXiv:2604.14876, Gupta–Sethi–Agrawal arXiv:2610.18055; none concerns IMED.

The writing session (2026-11-16) ran no new web search. Revision round 1 (2026-11-16) read the
works found by the scope referee (its queries 2–4, 7, 8, in its report) and ran:

- "Chow Lai 1975 "Some one-sided theorems on the tail distribution of sample sums with applications
  to the last time and largest excess of boundary crossings" Transactions AMS 208": the metadata
  (DOI 10.1090/S0002-9947-1975-0380973-6); the AMS page refused access (403); abstract through
  Crossref.
- Crossref queries for Janson (1986), Nagaev (1979) and Fuk–Nagaev (1971): metadata and abstracts
  only; Project Euclid returned no text for Nagaev (1979).
- arXiv pages of arXiv:2604.14876 (Panda–Agrawal) and arXiv:2303.06058 (Baudry–Suzuki–Honda): the
  parts listed in `literature/index.md`.

Revision round 2 (2026-11-16) ran no new search: it fetched the sources named by the scope referee
(its queries 15–20): the PDF and the abstract page of arXiv:2102.03734 (only v1 exists), the HTML of
arXiv:2604.14876v1 (App. A.1), and the PDF of arXiv:2303.06058v3 (Remark 1, App. B.4).

## Reading notes

- [HT15]: `literature/notes/HT15.md` (statements copied from the page images: Algorithm 1, (2),
  Theorem 2, (4)–(6), Theorem 3, Corollary 4, Theorem 5, Lemmas 6–8, the $G^\star$ of the proof of
  Theorem 2(ii), Propositions 10–12, Lemmas 13–14, (25)–(29), §9). The cited nodes
  `cite:HT15-thm2` (Theorem 2(ii), restricted to laws with a finite mean) and `cite:HT15-thm3`
  (Theorem 3, for IMED with the convention for leaders, a special case of their arbitrary tie rule)
  are restated from it. Lemma 6 is not cited (imprecise at the boundary, V2); Lemma 13 and $G^\star$
  are reproved.
- [GMS19, Theorem 1, Definition 1]: from `literature/notes/GMS19.md` (verbatim there).
- [LS, Definition 16.1], [AJK21, Corollary 2], [BCL13, Theorem 1], [RH20, Section 3], [HT10]: parts
  recorded as read in `literature/index.md` (by earlier sessions); not re-read in this session.
- [LR85], [BK96]: classics, cited for the lower bound only. [B62] (Bennett's inequality, proved in
  the paper as `lem:bennett`) and [BK65] (Baum–Katz, "see also") added to `bibliography.json` with
  metadata `unchecked` and not read.
- Revision round 1: [PA26] and [BSH23] read in part (notes written); [CL75], [Jan86], [Nag79],
  [FN71] added with Crossref metadata, read in their abstracts only, and cited as "see also".
- Revision round 2: [AJK21, Proposition 5, Appendix B.4 (Lemma 17) and B.4.1] read in the PDF of
  arXiv:2102.03734v1 (text extracted with pdftotext); [PA26, Appendix A.1] re-read in the HTML
  (bounded supports: "along the same lines" as AJK21, with the dual of [HT10] and a lemma of
  Agrawal–Koolen–Juneja 2021b, $g(n)=\log(1+n)+1$); [BSH23, Remark 1 and Appendix B.4] read in the
  v3 PDF. Agrawal–Koolen–Juneja, arXiv:2008.07606 (the source of AJK21's Lemma 17), not read and
  not cited.

## Verification defects (V1–V11) and how the paper answers them

- V1 (`lem:class`, moment bound): $\mathbb E_{G^\star}|X|^r\le\mathbb E_P|X|^r+\max\{1,|\mu|^r\}$
  (Step 5), stated for every $r\ge1$.
- V2 (`lem:optimizer`): "$\le1$", with equality when $\lambda^\star<1/(1-\mu)$; [HT15, Lemma 6] is not
  cited.
- V3 (`lem:goodpart`, Step 3): the product is a polynomial in $\lambda$, hence continuous at
  $1/c$.
- V4 (`lem:jump`): constant 1 instead of 3/2, verified ($(s-1)(1/s+1/s^2)=1-1/s^2<1$); hence $e^{-1}$
  in `thm:counter`: $\kappa2^q/(64e^q)$ in (i), $\kappa/(4e)$ in (ii).
- V5 (calibration): "on the scale of power-law lower tails, the exponent two is the threshold"
  (abstract, introduction, paragraph "The threshold, and what is not claimed" of `sec:counter`); finite variance sufficient, not necessary
  (paragraphs "Scope" and "The threshold", `oq:boundary`); the moment remark of the example is attached to
  `cor:pareto` and to the sentence after `thm:counter`.
- V6 (liminf and class): `cor:pareto`(b) states the $\liminf$, names the class $\mathcal C$, computes
  $\mathcal K_{\inf}(\delta_0,m;\mathcal C)$ and compares with `cite:GMS19-thm1`; attainability on
  $\bigcap_{r<2}\mathcal S_r$ is `oq:finite-mean`.
- V7 (attribution): the three-moments remark is proved in the paper and credits Baum–Katz ("see
  also"); the converse of `prop:key` (Janson 1986, not read) is not in the paper.
- V8 (numerics): no claim about [HT15, Theorem 5(ii)] (bounded supports) for the $q=3$ runs; the
  script is in `notebook/`.
- V9 (range of $\delta$): paragraph "The range of $\delta$" after `thm:main`.
- V10 (`lem:explore`, $d(\hat m^\star)=\infty$): Step 4 says that $\bar m_T<1$ for large $T$.
- V11 (integer parts): $h=\lfloor T/2\rfloor$, $g=\lfloor T/4\rfloor$ in the proof of `thm:counter`.

Interest scores given by the agents (for the owner; the scope referee gives its own): the report
5/10, the verification 4/10 ("one algorithm in one model; a paper that also settled the
finite-mean question would deserve 5–6").

## Presentation (house style, still version 1)

On 2026-11-16 the presentation of `paper.tex` was rewritten in the owner's house style
(`docs/writing.md`, sections 2, 2a and W15), without changing its mathematics:

- Sections in the order of the model paper: introduction (contributions, outline), related work
  with the comparison table, problem formulation (classical setting, then semi-bounded rewards),
  the algorithm, one section per main result (each recalling the classical result first:
  `cite:HT15-thm3` before `thm:main`, `cite:GMS19-thm1` before `cor:optimal`), how the proofs work,
  examples and simulations, conclusion, open questions; appendices: useful lemmas, properties of
  $\mathcal K_{\inf}$, one appendix per proof, sources, notation.
- The proof of `thm:main` is now a decomposition lemma and one lemma per term: `lem:decomp`
  (the split (eq:decomp), formerly inline), `lem:termA` (formerly Step 2: `lem:sup`(b) and
  `prop:key`), `lem:termB` (formerly Steps 3–4: the pathwise count and the level shift), `lem:termC`
  (formerly Step 5: the Chernoff bound of `lem:subopt`), then the proof of the theorem from them.
  These four labels are new; they restate steps of the former proof, with the same constants.
  `lem:sup` stays in the main text, its proof moved to the appendix (`\proves`); `lem:jump` moved to
  the appendix of `thm:counter`.
- Every defined symbol has an anchor and a link macro; every statement of an existing node is
  unchanged up to these macros, the citation commands (author–year, natbib) and, in `def:model`,
  `def:kinf`, `def:run` and `def:imed`, one definition per sentence with displays (checked by a
  script comparing the normalised statements and their formulas with the previous commit).

## Revision round 1 (scope report SC1.1–SC1.8, 2026-11-16; still version 1)

Nodes for the referees to re-check:

- **New:** `lem:three-moments` (the former unlabelled remark "A summed bound needs three moments"
  of `sec:overview-mgf`, same statement and proof, the proof moved to the appendix
  `sec:proof-three`); `lem:pa-assumptions` (Appendix B, new mathematics: the assumptions of
  [PA26, Theorem 3.1] on $\mathcal M_1$).
- **Changed in notation only:** `cor:pareto` (the weight $\pi$ renamed $\varpi$, SC1.6; its proof
  too); `oq:second-order` (the exponent of the remainder renamed $\omega$); `oq:finite-mean`
  (restated for `IMED`-$\rho$, SC1.3).
- **Unchanged statements, moved:** `def:rate`, `def:dev`, `thm:main` now precede the recall of
  `cite:HT15-thm3` (new subsection `sec:upper-ht15`, SC1.4); the remark on the convention for
  leaders moved from `sec:algorithm` to `sec:upper-ht15`; Conclusion and Open questions merged into
  `sec:open` (SC1.8).
- **Text only:** abstract (SC1.5); `sec:related` and Table 1 (BSH23, PA26; SC1.3); the paragraph
  "Another algorithm" of `sec:counter`; the paragraphs after `lem:three-moments` and `prop:key`
  (Chow–Lai, Janson, Nagaev, Fuk–Nagaev as "see also", SC1.1–SC1.2); a renaming line before
  `cite:HT15-thm2` (SC1.7); Appendix G.

## Revision round 2 (SC2.1–SC2.4, SC1.4, PF1.1–PF1.5, 2026-11-16; still version 1)

Nodes for the referees to re-check:

- **Changed proof and statement:** `lem:optimizer` (Step 2: continuity at $\lambda=0$ proved by
  the bound $|\log(1-\lambda z)|\le2\lambda|z|$, PF1.1; new part (c) and Step 6: $V$ integrable with
  $\mathbb EV=\mathcal K_{\inf}(P,\mu)$ and $\mathbb Ee^{-V}\le1$, formerly inside the proof of
  `lem:subopt`, PF1.4).
- **Changed proofs:** `lem:subopt` (Step 3 cites `lem:optimizer`(c)); `lem:pa-assumptions` (Step 5
  cites `lem:optimizer`(c), PF1.4; Step 8, the range of $\varepsilon$, PF1.5; its Idea credits
  [AJK21, Proposition 5] and [PA26, App. A.1], SC2.1); `prop:key` (Step 0 replaced by the remark
  $v\ge\delta^2>0$, PF1.2).
- **Changed statement:** `thm:counter` (i), (ii): $y_0>0$ instead of $y_0\ge0$ (PF1.3); equivalent
  hypotheses, proof unchanged.
- **Open question:** `oq:finite-mean` uses a lower-truncated empirical mean, which needs no
  inversion of $\mathcal K_{\inf}$ (SC2.3), with [BSH23, Remark 1, App. B.4] as precedent.
- **Text only:** "Gap with the literature" and the last row of the appendix of sources (SC2.1,
  SC2.2); the setup of the simulations and Table 2 (SC2.4: how to reproduce; a KLinf-UCB row).

SC1.4 (optional): `thm:main` is at the top of p. 8 of the reader build (the round-2 attribution
sentence in §2 moved it by a few lines); not changed further.
