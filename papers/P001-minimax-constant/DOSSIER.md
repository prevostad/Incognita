# Dossier of P001-minimax-constant, version 1

Refereed and versioned with `paper.tex`, never compiled into the PDF: what the referees and the
owner need and the reader does not. It changes only with a new version of `paper.tex` after
acceptance. Private KNOWN entries are cited by id only, never quoted.

A paper of the owner (Adrien Prevost), converted to the library's format on 2026-11-14. This dossier
was created in revision round 3 (2026-11-16, Claude Opus 5.5, role `revise`), from the process
sections that the earlier versions printed in `paper.tex` (the paragraph "Roadmap items", Section 3
"Closest known", Sections 11 "Sanity checks" and 12 "Weak points", the paragraph "Searches" of the
attribution section, and the reading admissions of the related work).

## Roadmap correspondence

- Items served (`directions` of META.toml): **D19** of StochasticBandits (the constant of the
  minimax regret, and a policy that attains it).
  - **(a)** "does $R^\star_{K,\mathcal D}(T)/\sqrt T$ converge as $T\to\infty$ for fixed $K$, and to
    which constant": answered by `thm:main`, for every $K\ge2$ and every regular class
    (`def:regular`), which includes the three models of D19 (Bernoulli laws, $\mathcal P[0,1]$,
    Gaussian laws of variance at most 1 with means in a bounded interval; `cor:examples`). The limit
    is $\bar\sigma V_K$, with $V_K$ the value of a Gaussian game (`def:risk`), characterized four
    ways (`prop:four`, `cor:four-c`); it depends on the model only through $\bar\sigma$.
  - **(b)** "is the constant attained by an explicit policy, horizon-dependent or anytime, defined by
    its formula with its cost per round": the horizon-dependent policy Screen-Core (`def:sc`, with
    its cost per round in the paragraph after it) attains $\bar\sigma V_K+\varepsilon$ for every
    $\varepsilon>0$ (`thm:main`(ii), `thm:u-upper`). Its core is a near-optimal batched policy of
    the limit game, which exists for every $K$ (`prop:four`(b)) but is computed only for $K=2$
    (approximately; `def:opt2` is a heuristic without guarantee). No anytime policy (`oq:anytime`).
  - **(c)** "bounds on the constant for every $K$ that improve the known ones, and its order in
    $K$": `thm:bounds`, $\kappa\lambda_K\sqrt{K-1}\le V_K\le2\sqrt2\sqrt K$; the lower bound is
    non-asymptotic for Gaussian rewards and improves the Gaussian constants of [LS, Theorem 15.2]
    and [LS, Exercise 15.2] for every $K$, and the Bernoulli constant $0.2730\sqrt K$ reported in
    [LWKW26, Section 5.2] for [CBL06, Theorem 6.11] for $K\ge3$ only. The upper bound is the
    published $\sqrt{2KT}$ [LS19, Theorem 6.1]. Order $\sqrt K$, up to the factors $0.9025$ and
    $2\sqrt2$. For two arms, `prop:K2` (under (H$_{\rm fp}$)) sharpens slightly Bather's and
    Vogel's asymptotic bounds.
- What the items ask that the paper does not give: an explicit core for $K\ge3$ (the core is
  existential); an anytime policy; the value of $V_K$ for $K\ge3$; certified (interval-arithmetic)
  bounds on $V_2$. The paper says these in words in the Scope paragraphs after `thm:main` and in its
  conclusion.
- Acceptance criteria of the roadmap, one by one:
  1. Model, class of algorithms, criterion: met. Regular classes (`def:regular`); horizon-dependent
     policies with external randomization (`def:regret` and the conventions of `sec:setting`);
     criterion $\lim_T R^\star/\sqrt T$ (`thm:main`), with non-asymptotic or eventual forms
     (`thm:lowEF`, `thm:u-upper`, `thm:bounds`).
  2. Closest known, with a derivation attempt: in this dossier, section Closest known.
  3. Sanity checks, one instance satisfying every hypothesis: section Sanity checks below, and the
     explicit example of `sec:examples` of the paper. The check against K1 (first-order
     problem-dependent constant) does not apply: the paper is about the worst case.
  4. Explicit class; algorithm by its formula, tie rule, cost per round: met (`def:sc` with the
     smallest-index tie rule for $i_0$, the fallback $N=0$, and its cost per round; `def:opt2` with
     its tie rule and cost). The core of Screen-Core is existential for $K\ge3$, declared in the
     paper.
  5. Constants explicit or existential: met (paragraph "Nature of the constants" after `thm:main`;
     remarks after `thm:bounds` and `prop:K2`).
  6. "Optimal" never a definition: met (the title's "optimal constant" is the limit of the minimax
     regret, which is defined; `thm:main` pairs the lower and the upper bound).
  7. Not routine: met (the minimax theorem in the limit and the uniform transfer over all policies
     are each several pages).
  8. Building block: not applicable.
  9. Improvement of constants with previous best values: met, in `sec:related` (comparison table)
     and the remarks after `thm:bounds` and `prop:K2`.
  10. Not "unimportant on its own": met.
- Conventions of the roadmap changed: declared in the conventions paragraph of `sec:setting`
  (arms enumerated; rounds from 1; $\mu_k$, $\Delta_k$; horizon-dependent policies with external
  randomization; the new classes; limits stated with $\lim$ instead of eventual inequalities, with
  the eventual forms given by `thm:lowEF`, `thm:u-upper` and the non-asymptotic half of
  `thm:bounds`).

## Closest known

- **K20–K23** (KL-UCB++, KL-UCB-switch, ADA-UCB, MOTS/MOTS-J): minimax regret $O(\sqrt{KT})$ with
  constants ($76\sqrt{VKT}$, $23\sqrt{KT}$, a universal $C$, an $O(\cdot)$), together with
  asymptotic optimality on fixed instances. Same order as `thm:main`, larger or unspecified
  constants, and no lower bound with a matching constant. Derivation attempt: these give
  $\limsup R^\star/\sqrt T\le c$ for their constants, which are above $2\sqrt2\sqrt K\cdot\bar\sigma$;
  they say nothing about a limit. Fails: no lower bound with the same constant, no identification.
- **K24** (MOSS as tuned is not asymptotically optimal): problem-dependent, unrelated to the
  constant of the worst case.
- **K33** (anytime versus horizon-dependent): related to `oq:anytime`, under another criterion
  (tails), not to the constant.
- **K37** (explore-then-commit loses a factor 2, two Gaussian arms): problem-dependent; unrelated.
- **The published bounds** (direction D19's list, checked): $\frac1{20}\sqrt{KT}$ for rewards in
  $[0,1]$ ([ACFS02, Theorem 5.1], not read; re-proved in [GMS19, Appendix B.1], read, where the
  constant is reported), $\frac1{27}\sqrt{(K-1)T}$ and $\frac18\sqrt{KT}$ for Gaussian rewards
  [LS, Theorem 15.2, Exercise 15.2], $>0.1365\sqrt{KT}$ for Bernoulli rewards ([CBL06, Theorem 6.11]
  through [LWKW26, Section 5.2]), and the upper bounds $49\sqrt{KT}$ [AB09, Theorem 5],
  $\sqrt{2KT}$ [LS19, Theorem 6.1], $\sqrt{2KT}+48K$ [ZL19, Theorem 11]. Derivation attempt: they
  bracket $R^\star/\sqrt{KT}$ between constants that differ by a factor larger than 28 for rewards
  in $[0,1]$; no limit follows. `thm:bounds` is consistent with them (in the normalization of
  [LS, Theorem 15.2], $\kappa\lambda_K\ge\frac1{27}$; for rewards in $[0,1]$ the upper bound
  $\frac12V_K\le\sqrt{2K}$ is the constant of [LS19]).
- **Two arms: Vogel, Fabius–van Zwet, Bather.** The order $\sqrt N$ [Vog60] and the asymptotic
  bounds $0.612\le V_2\le0.752$ (Bather's lower bound and Vogel's upper bound, as quoted in
  [KNS17, Theorem 1] and [Kol17, (3)]; the originals Bat83 and Vog60 were not read), and
  $0.53\le V_2\le0.752$ from [FvZ70, abstract]. No limit; they bracket $V_2$.
- **Two arms: Kolnogorov.** Reading notes (Russian originals through an extraction tool, to be
  checked against the page images; see Reading notes below):
  - [Kol17] proves the batched Bayes recursion in the state $(U,n_1,n_2)$ and its invariant form
    (Theorems 1 and 2), takes "minimax = Bayes" from "the main theorem of the theory of games" (its
    (5)), derives the limiting equation (26)–(27) formally, assuming continuous partial
    derivatives, and states the limit $\lim N^{-1/2}R^M_N=\sup_\varrho r(\varrho;0,0,0)$ (its (21))
    in Theorem 3, which "is given without proof"; numerically $\approx0.637$ at $d\approx1.57$.
  - [Kol12] bounds the normalized minimax risk on both sides (its Theorem 2), with "minimax = Bayes
    on the worst prior" taken from "the results of [8, 9], where the applicability of the main
    theorem of game theory was established", [8] being [Kol11] (see below); it states no limit.
  - [Kol14, Theorem 3] states the limit $\lim N^{-1/2}R^M_N(\Theta_N)=\sup_\varrho r(\varrho;0,0,0)$
    on the close set $\Theta_N=\{|m_1-m_2|\le2cN^{-1/2}\}$ and proves it in an appendix, starting
    from minimax = Bayes for the worst prior.
  - [Kol14a] gives Bayes risks and two lemmas "without proof"; no limit theorem. [Kol15] restates
    [Kol14]'s theorem, calls its values $0.634$, $0.637$ "preliminary", derives the limiting
    equation by "non-rigorous reasoning", and proves the threshold form of the Bayes strategy (its
    Theorem 2). [Kol16] recalls these results and proposes $\approx0.637$ (its (3)). [Kol20] says
    the existence of the limit "is established", takes the minimax theorem from game theory,
    derives the equation by "non-rigorous reasoning", and says a rigorous proof needs smoothness
    estimates that "have not yet been obtained"; its Theorem 6 is about the Bayes risk of a fixed
    prior; its Section 2 (Theorem 2, Corollary 1) reduces the two-arm minimax risk to close
    alternatives by an initial threshold stage.
  - [Kol11, Theorem 1]: the finite-horizon two-armed game on a compact parameter set has a value
    over all randomized strategies; see the section "Kolnogorov 2011" below (SC3.6).
  - Derivation attempt for $K=2$: combine minimax = Bayes at finite $N$ [Kol11, Theorem 1], the
    limit on close alternatives [Kol14, Theorem 3], and the reduction to close alternatives
    [Kol20, Theorem 2 and Corollary 1]. This may give the case $K=2$, unit-variance Gaussian, of
    `thm:main` (see "Kolnogorov 2011" below for the two caveats); it does not give $K\ge3$, other
    classes, the game in continuous time, or a policy for $K\ge3$. For $K\ge3$ nothing in this line gives a limit:
    [Kol25] (abstract read) derives recursions, a limiting equation and a three-armed numerical
    example, with the minimax theorem taken from game theory.
- **Diffusion asymptotics.** [Adu25] (arXiv v16, the Econometrica version) proves lower bounds on
  the minimax risk for the one-armed bandit (Section 5.4, (5.8), whose sharpness is "left for
  future research"; Section 6, (6.2)); its conclusion says that "for minimax risk, the paper only
  proves a lower bound" (Section 7); it works "under a minimax theorem" (Section 2.4), which v1 calls
  "an open question" in bandits (Section 2.3). [HP23, Theorem 2]: asymptotic representations with a
  fixed number of batches, no minimax regret. [KK23, Corollary 3.5]: leading-order minimax regret of
  the symmetric two-armed Bernoulli bandit (means summing to one), through the heat equation.
  Derivation attempt: [Adu25]'s lower bounds with the minimax theorem would give a lower bound for
  $K=2$ in a one-armed reduction; no upper bound, no $K\ge3$, and the minimax theorem is assumed.
  Fails at the minimax theorem in the limit (`prop:four`(a)) and at the uniform transfer over all
  policies (`thm:lowEF`, `thm:u-upper`).
- **Lower-bound technique.** [GMS19, (6)] (fundamental inequality); [GMS19, Appendix B.1] re-proves a
  distribution-free $\Omega(\sqrt{KT})$ bound by a single arm with few pulls and Pinsker, without a
  prior on the position and without convexity of kl. The uniform position of the good arm is that
  of [ACFS02, Theorem 5.1] (not read) and the average over the position is [LS, Exercise 15.2];
  averaging kl by joint convexity is [GMS20, Section 3, (4)–(5), Corollary 3]. No published proof
  found that combines these with an optimized height of the good arm.
- Library papers: P000 (BatchedBandits) and P002 (TransferBandits) do not concern the minimax
  constant; `depends_on = []`.

### Kolnogorov 2011 (SC3.6)

Read on 2026-11-16 (Russian original, Math-Net.ru at1708, through r.jina.ai and an extraction tool
that returns short quotations and paraphrases; note `literature/notes/Kol11.md`). What it proves:

- **Model and class.** Two arms, unit-variance Gaussian rewards, horizon $N$, loss the regret; the
  parameter set is a fixed compact set $\Theta=\{|m_1-m_2|\le2c_1,\ |m_1+m_2|\le2c_2\}$ ("the
  condition $c_2<\infty$ is needed for $\Theta$ to be compact"). The strategies are **all**
  randomized strategies (measurable functions of the history giving the probabilities of the arms);
  mixed strategies reduce to them. No batching, no forced initial stage.
- **Theorem 1** (verbatim in the note): the game has a value and both players have minimax
  strategies: a worst prior $\Lambda_0$ on $\Theta$ and a minimax mixed strategy $\mu_0$ with
  $\inf_\mu\sup_\Lambda L_N=L_N(\mu_0,\Lambda_0)=\sup_\Lambda\inf_\mu L_N$. So minimax = Bayes for the
  worst prior, at every finite $N$, on a compact $\Theta$.
- **Argument.** Compact metrics on the strategies and on $\Theta$ with $L_N$ uniformly continuous,
  then a general theorem on statistical games (Borovkov 1984, p. 129). Our reader's observation
  (not checked against the page images, and not the paper's): the proof says that the space of
  strategies, with a weighted $L^1$ distance, is compact because it is "bounded and complete", which
  does not follow in infinite dimension; the conclusion may still hold by another route (a weak
  topology on the strategies).
- **Other results.** Lemma 1: invariance of the Bayes risk under swapping the arms and shifting both
  means. Lemma 2: the Bayes risk is continuous and concave in the prior. Theorem 2: the worst prior
  may be taken asymptotically uniform in the common mean ($\kappa_a(u)\rho(v)$, $a\to\infty$).
  Theorem 3: the optimal strategy alternates the arms on the first two steps. Theorem 4: a recursion
  for the Bayes risk. No limit as $N\to\infty$ is stated.

**Consequence for the $K=2$ claim (SC3.6).** The earlier versions said that Theorem 1.1 "proves
Kolnogorov's claim" for two arms. With Kol11, the chain Kol11 Theorem 1 (minimax = Bayes at finite
$N$, all strategies, compact $\Theta$) + Kol14 Theorem 3 (the limit on the close alternatives
$\Theta_N=\{|m_1-m_2|\le2cN^{-1/2}\}$, proved in its appendix from minimax = Bayes) + Kol20 Section 2
(Theorem 2, Corollary 1: reduction to close alternatives) may already give the case $K=2$ of
Theorem 1.1 for unit-variance Gaussian rewards. Two caveats we could not resolve: Kol14's $\Theta_N$
does not bound $m_1+m_2$, while Kol11 needs a compact $\Theta$ (Kol11 Theorem 2 treats $a\to\infty$
only asymptotically); and the class of strategies. As the notes read them, $R^M_N(\Theta_N)$ in
Kol12 (Theorem 2) and Kol14 (Theorem 3) is the minimax risk over all strategies on $\Theta_N$; a
restricted class (an initial stage of $\varepsilon_0N$ pulls of each arm, then decisions on a grid
of step $1/N$) enters through the two sides of the sandwich (the lower side "due to the incomplete
control time", the upper side because "at the initial stage the control is not optimal"), and Kol12
invokes minimax = Bayes "including under the restrictions made on the class of strategies".
Whether the lower side applies minimax = Bayes to the restricted class or to all strategies could
not be determined from the pieces read (Kol11 Theorem 1 covers all strategies, but on a compact
$\Theta$).
The paper now says (Section 8, "Two arms") that, as far as we can tell, these papers give the
existence of the limit for $K=2$ and unit-variance Gaussian rewards, that we have not checked their
proofs, and that Theorem 1.1 differs by: every $K$; every regular class (Bernoulli included); the
identification of the limit as the value of a game in continuous time with a minimax theorem and a
lower bound uniform over all policies; and a policy attaining the constant. The claim "Theorem 1.1
proves Kolnogorov's claim" was removed from the introduction.

## Sanity checks

- *Two arms.* `thm:bounds` gives $\kappa\lambda_2\sqrt1\le V_2\le2\sqrt2\sqrt2=4$, with
  $\lambda_2=e^{-2\log2}=\frac14$, so $0.2256\le V_2\le4$; `prop:K2` gives, under (H$_{\rm fp}$),
  $0.6341\le V_2\le0.7478$, inside this range, and the numerical value $0.6373$ agrees with
  Kolnogorov's $0.637$ [Kol20].
- *The constant $\kappa$.* $u^\star\approx1.256431$ solves $e^u=1+2u$ ($e^{1.256431}\approx3.51286$ and
  $1+2\cdot1.256431=3.51286$), $a^\star=\sqrt{2u^\star}\approx1.585201$, and
  $\kappa=2a^\star/(1+a^{\star2})\approx3.170402/3.512862\approx0.902512$.
- *Published constants.* For rewards in $[0,1]$ ($\bar\sigma=\frac12$), the upper bound gives
  $\lim_TR^\star_K(T)/\sqrt T=\frac12V_K\le\sqrt{2K}$, the constant of [LS19, Theorem 6.1]; the lower
  bound $\kappa\lambda_K\sqrt{(K-1)T}$ exceeds $\frac1{27}\sqrt{(K-1)T}$ [LS, Theorem 15.2] and
  $\frac18\sqrt{KT}$ [LS, Exercise 15.2] for every $K\ge2$, since $\kappa\lambda_2\approx0.23>\frac1{27}$,
  $\kappa\lambda_2>\frac18\sqrt2\approx0.177$ and $\lambda_K\sqrt{(K-1)/K}$ increases with $K$. Against
  $0.2730\sqrt K$ (CBL06 through LWKW26): weaker for $K=2$ ($0.2256<0.386$), barely larger for $K=3$
  ($0.491>0.473$), larger for $K\ge4$, with ratio increasing to $\kappa/0.2730\approx3.31$. For two arms
  the asymptotic bounds $0.612\le V_2\le0.752$ of Bather and Vogel contain the interval of `prop:K2`.
- *Scaling.* If every law of the class is scaled by $c>0$, the regret and $\bar\sigma$ are both
  multiplied by $c$: the limit $\bar\sigma V_K$ is consistent with this, and $V_K$ does not depend on
  the class.
- *Unbounded means.* Without the bound on the means, $R^\star=\infty$: this is why the classes
  $\mathcal C(a,b,\bar\sigma,\sigma_{\rm p})$ bound the means.
- *Degenerate cases.* $K=2$: above. Bernoulli rewards: $\bar\sigma=\frac12$ (`cor:examples`); the
  Bernoulli laws of mean at most $\frac12$ have their law of largest variance at the boundary, and
  the constant is unchanged by `prop:four`(d) (translation invariance). $T<K/\delta$: Screen-Core
  falls back to arm 1, which plays no role since `thm:u-upper` takes $T\ge2K/\delta$. Ties: the
  smallest-index rule for $i_0$; the bounds hold for every maximizer.
- Consistency with `[Lean]` entries of KNOWN.md: KNOWN.md of StochasticBandits has no `[Lean]` entry.
  With the roadmap's known values ($\frac1{20}$, $\frac1{27}$, $\sqrt{2KT}$, $49\sqrt{KT}$, and
  $[0.612,0.752]$ for two arms): consistent, as above.
- *The explicit example* (`sec:examples` of the paper): Gaussian rewards of variance 1 with means in
  $[0,1]$, $K=2$, $T=10^4$: the class is regular with $\bar\sigma=1$, $T\ge2u^\star$, and
  `thm:bounds` gives $R^\star_2(10^4)\ge0.2256\cdot100\approx22.6$, while `thm:main` gives
  $R^\star_2(T)/\sqrt T\to V_2$, with $V_2\in[0.6341,0.7478]$ under (H$_{\rm fp}$) and $V_2\in[0.2256,4]$
  unconditionally.

## Weak points

The independent verifications (by AI agents) found no error; these are the steps where an error
would be the hardest to see, most doubtful first.

1. `prop:K2`: the bounds on $V_2$ are computed in double precision, with an a priori analysis of the
   floating-point errors (`rem:K2-fp`) but without interval arithmetic. A referee cannot check them
   by hand, so the proposition is stated under the hypothesis (H$_{\rm fp}$).
2. The identification of the value (appendix "The limit game"): the compactness of $\mathcal W$, the
   continuity of the risk, and the density of batched policies (`lem:g-compact`, `lem:g-cont`,
   `lem:g-dense`, `lem:g-bridge`), which use measurable selections and the Brownian-bridge argument.
   The minimax step (`prop:four`(a)) now uses Sion's theorem as proved in Mathlib
   (`Sion.minimax'`), with the topologies chosen in its proof.
3. The transfer of the lower bound (`thm:lowEF`): the Skorokhod embedding of each arm's rewards and
   the uniformity of the $O(T^{-1/4})$ error over all policies.

## Searches

- Conversion of 2026-11-14: no web search.
- Revision of 2026-11-15 (round 1): the searches of the scope referee of the first round (run on
  2026-11-14, recorded in its report on pull request #22), among them: "minimax regret constant
  two-armed bandit 0.637"; "Kolnogorov Gaussian two-armed bandit limiting description minimax
  risk"; "Kolnogorov Gaussian multi-armed bandit minimax risk limiting description K arms
  worst-case prior"; "Bernoulli two-armed bandit asymptotic minimax regret constant sqrt(N) Vogel
  Fabius van Zwet value"; "Lattimore Szepesvári "Theorem 15.2" minimax lower bound "1/27"
  sqrt((k-1)n) Gaussian"; "Lattimore Szepesvari minimax regret stochastic bandit equals sup over
  priors finitely supported priors"; "continuous-time multi-armed bandit weak formulation martingale
  problem allocation compact convex set of strategies minimax"; "Mandelbaum 1987 continuous
  multi-armed bandits multiparameter processes"; "Kiefer 1957 Invariance, minimax sequential
  estimation, and continuous time processes Hunt-Stein sequential amenable group"; "Stein 1956
  efficient nonparametric testing and estimation least favorable one-dimensional subfamily hardest
  parametric submodel"; "Hall 1969 embedding submartingales in Wiener processes with drift";
  "Skorokhod embedding multi-armed bandit embed rewards in Brownian motion regret lower bound
  diffusion" (no bandit use found); "sequential experiment Brownian motion drift Brownian bridge
  between observation times independent of drift discrete monitoring approximation continuous-time
  policy" (nothing found); "bandit algorithm add independent Gaussian noise to rewards to equalize
  variances" (nothing found for bandits); "two-armed bandit relaxation reveal block outcomes lower
  bound Bayes risk batched recursion semiconcave value function numerical certificate" (no
  block-revealing source); "sharp constant minimax regret lower bound K-armed bandit large K
  sqrt(KT) constant optimized gap uniform random best arm Gaussian" (loose constants only).
  Crossref bibliographic queries for Kie57, Hal69, Man87, EKNJ87, Ste56, and searches by title, on
  arXiv, Crossref, OpenAlex, Math-Net.ru and the publishers' pages, for each work read.
- Revision of 2026-11-15 (round 2): the searches of the scope referee of round 2 (recorded in its
  report); lookups by identifier: Crossref and Math-Net.ru for Kol12, Kol14, Kol15 (Math-Net.ru ids
  at3793, at14162, at14258), the INASE library for Kol14a, Crossref for Sio58 and CBL06; arXiv
  2609.22690 (LWKW26); the COLT 2009 proceedings site for AB09; for Fan53, PNAS, PMC, Europe PMC,
  JSTOR, Unpaywall and Semantic Scholar (no readable copy), and archive.org, which holds Fan's
  report Fan52; web searches for a verbatim statement of [CBL06, Theorem 6.11] (none found).
- Revision of 2026-11-16 (round 3): the searches of the scope referee of round 3 (2026-11-16,
  recorded in its report; among them the full reference of Kol11, the Bernoulli rounding of
  rewards (found: AG12), and "exact constant minimax regret K-armed stochastic bandit limit
  R*/sqrt(T) Gaussian continuous-time game value 2026": nothing new). Added: the Math-Net.ru page of
  Kol11 (at1708) and its full text (see Kolnogorov 2011 above); the PMLR PDF of AG12; the Mathlib
  source `Mathlib/Topology/Sion.lean` (Sion's minimax theorem, `Sion.minimax'`), read in the
  repository's `.lake` at the pinned revision.

## Reading notes

What was read of each cited source is in `literature/index.md` and `literature/notes/`. Caveats
that the earlier versions printed in the paper:

- Kol12, Kol14, Kol15 (Russian originals) and Kol14a (English) were read in part, through r.jina.ai
  and a text-extraction tool that returns short quotations; Kol14 Theorem 3 is verbatim. To be
  checked against the page images. Kol20 was read whole in the Russian original; Kol16 and Kol17
  whole.
- Kol25: abstract only (the full text could not be accessed); the paper cites it for the existence
  of a three-armed numerical example only.
- Bat83, Vog60: not read; their constants $0.612$ and $0.752$ are cited through [KNS17, Theorem 1]
  and [Kol17, (3)], which were read. Vog60a: Section 1 read (OpenAlex). FvZ70: abstract read.
- ACFS02: not read; $\frac1{20}$ is cited through [GMS19, Appendix B.1] (read), the uniform
  position of the good arm through [LS, Exercise 15.2], and ACFS02 is only "see also" in the paper.
- CBL06: not read (metadata, table of contents and errata only); its constant is cited through
  [LWKW26, Section 5.2].
- Fan53: not accessible (PNAS, PMC, Europe PMC, JSTOR, Unpaywall, Semantic Scholar; PMC captcha
  again on 2026-11-16). Fan52 was read through the OCR text of the archive.org scan, the opening
  sentence of Theorem 2 verbatim. Neither is used any more: `prop:four`(a) now rests on Sion's
  theorem in the form of Mathlib (`Sion.minimax'`, whose statement was read in
  `.lake/packages/mathlib/Mathlib/Topology/Sion.lean`); Sio58 (OCR, Theorem 3.4 and its corollary)
  is cited as the original source of that theorem.
- Unread works cited only as "see also" for context: Man87, EKNJ87, Kie57, Hal69, Ste56, Obl04, DP16,
  FG21, KW24, KZ21, CB97, Cov66, GPS16, BEZ20, BCZ97, BP13, Rod78. Textbooks used for standard facts:
  EK86, Bil95, Bil99, KS91, RY99, Kal02, Kec95.

## Changes

None: version 1 (in refereeing). The revisions during refereeing are recorded in the notebook.
