# Candidate directions of StochasticBandits

The open questions of accepted papers that the scope referee rated as candidates (interest,
novelty, fit), added by the loop when the paper is merged (`scripts/certify.py add-candidates`).
A writer may take an entry `C<n>` like a direction `D<n>` of [ROADMAP.md](ROADMAP.md): its paper
lists it in `directions` (META.toml). **Append-only**: entries are never edited, renumbered or
deleted; `garden` (or the owner) may add a line `Dropped (<date>, <role>, <model>): <reason>`
under an entry. The status is computed (AGENTS.md, section 4): candidate, taken (an open pull
request serves it), done by P<nnn> (a paper on `main` serves it), covered (a rejected paper served
it), dropped.

## C1 (2026-11-16, from P001v1 oq:anytime)
- Title: an anytime policy with the optimal constant
- Statement: For $K\ge2$ and a regular class $\Cl$, is there an anytime policy $\pi$ (not knowing $T$) with $\limsup_T\sup_{\nu\in\Cl^K}\RT(\pi,\nu)/\sqrt T=\sbar\VK_K$?
- Extends: D19, D5
- Source: papers/P001-minimax-constant, version 1, label oq:anytime
- Rating: interest high; novelty open. Queries: "anytime bandit policy without knowledge of horizon achieves exact minimax regret constant …" (2026-11-16); "anytime algorithm achieves same asymptotic minimax regret constant …" (round 3); fit D19(b), toward D5 (`\extends{D19, D5}`) (referee-scope, pull request #22, head bb040918eb32)

## C2 (2026-11-16, from P001v1 oq:V3)
- Title: three arms
- Statement: Compute $\VK_3$, with rigorous bounds whose ratio is at most $1.2$.
- Extends: D19
- Source: papers/P001-minimax-constant, version 1, label oq:V3
- Rating: interest medium; novelty open. Kol25 (read in full today) has only a numerical three-arm example and says bounds for $J>2$ are not known. Queries: the Kol25 query above (2026-11-16); "three-armed Gaussian bandit minimax risk computed value certified bounds …" (round 3); fit D19(c) (referee-scope, pull request #22, head bb040918eb32)

## C3 (2026-11-16, from P001v1 oq:many)
- Title: many arms
- Statement: Does $\lim_{K\to\infty}\VK_K/\sqrt K$ exist, and is it larger than $\kap\approx0.9025$?
- Extends: D19
- Source: papers/P001-minimax-constant, version 1, label oq:many
- Rating: interest high; novelty open. Queries: "limit of normalized minimax regret K-armed bandit sqrt(T) …" (2026-11-16); "minimax regret K-armed bandit as K tends to infinity limit of constant …" (round 3); fit D19(c) (referee-scope, pull request #22, head bb040918eb32)

## C4 (2026-11-16, from P001v1 oq:V2)
- Title: the value for two arms
- Statement: Is the two-point prior on the half-gap least favorable for the limit game with $K=2$ on all of $\R^2$, and is there a closed form for $\VK_2$?
- Extends: D19
- Source: papers/P001-minimax-constant, version 1, label oq:V2
- Rating: interest medium; novelty open. Queries: "two-armed Gaussian bandit least favorable prior two-point symmetric proof … 0.637 closed form" (2026-11-16); "least favorable prior two-armed Gaussian bandit … 0.637 proof" (round 3); fit D19(a), (c) (referee-scope, pull request #22, head bb040918eb32)

## C5 (2026-11-17, from P004v1 oq:boundary)
- Title: The exact boundary for IMED
- Statement: Let $P\in\Sm$ with $\mean(P)\in(0,1)$, let $\bar F(y)\coloneqq\Prob_P(X<-y)$, and run \imed{} on the \term{w:instance}{instance} $(P,\delta_0)$; let $d^\star\coloneqq\log(1/(1-\mean(P)))$. (a) Does $\lim_T\E \Np_2(T)/\log T=1/d^\star$ hold whenever $\int_1^Ty\bar F(y)\,dy=o(\log T)$, for example when $\bar F(y)$ is of order $1/(y^2\log y)$, where the variance is infinite? (b) If $y^2\bar F(y)\to\kappa>0$, does $\E \Np_2(T)/\log T$ converge, and is its limit $1/d^\star+2\kappa/(e\,\mean(P)^2)$? A heuristic count of the frozen-index mechanism (a jump $Y$ at the $s$-th pull costs about $Y/(e\,\mean(P))$ pulls of arm $2$ when $Y\gg s$) gives this constant; Theorem~\ref{thm:counter}(ii) proves only the excess $\kappa/(4e)$. The method stops in Proposition~\ref{prop:key}, whose one-jump term uses $\E Y^2$: a version truncated at the horizon would require the other terms, in particular the H\"older step of Lemma~\ref{lem:moments}, to be redone with constants uniform in $T$.
- Extends: D9
- Source: papers/P004-imed-finite-variance, version 1, label oq:boundary
- Rating: interest medium; novelty open (queries 6, 10, 12, 20, 32); fit D9 (referee-scope, pull request #37, head 31ccdee3e5d0)

## C6 (2026-11-17, from P004v1 oq:second-order)
- Title: The second-order term under a finite variance
- Statement: Under the assumptions of Theorem~\ref{thm:main}, is $\E \Np_i(T)-\log T/\Kinf(\nu_i,\ms)=O(1)$, as \citet[Theorem~5]{HT15} proves when every arm has a moment generating function near $0$? Or at least $O((\log T)^{\omega})$ for an explicit $\omega<1$, as \citet[Corollary~4]{HT15} gives with $\omega=10/11$ under an exponential moment of one \term{w:optimal}{optimal} arm? Theorem~\ref{thm:main} gives only $o(\log T)$: optimising $\delta$ requires the dependence of $\Gam(\nu_j,\ms-\delta)$ on $\delta$, which goes through the exponent $\gamma$ of Lemma~\ref{lem:moments} (with $\gamma-1$ of order $\delta$) and the parameters of \eqref{eq:gammabound}, and that of $\Lt_i(\delta)$, neither of which we tracked.
- Extends: D9
- Source: papers/P004-imed-finite-variance, version 1, label oq:second-order
- Rating: interest medium; novelty open (queries 5, 14); fit D9 (referee-scope, pull request #37, head 31ccdee3e5d0)
