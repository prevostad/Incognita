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

## C7 (2026-11-17, from P005v1 oq:finite)
- Title: Explicit finite-time bounds
- Statement: For every $\kappa>1$ and every $P\in\Hk$ with $\mu>\mean(P)$, are there $d_0>0$, $C<\infty$ and $c>0$, given by explicit functions of $\kappa$, $\kurt(P)$ and $(\mu-\mean(P))/\sd(P)$, such that $\Prob(\Kc(\hat P_n,\mu)\le\Kc(P,\mu)-d)\le Ce^{-cnd^2}$ for all $n\ge1$ and $d\in(0,d_0)$? This would give, for \algo{} on every $\nu\in\Hk^\alpha$, $\E[\Np_a(T)]\le\log T/\Ka+O((\log T)^{2/3})$ with explicit constants, as \citet[Theorem~1]{AJK21} for a bounded moment. Our method stops at Theorem~\ref{thm:deviation}(ii) because the lower bound on $\Kc$ comes from a compactness argument (Lemma~\ref{lem:escape}) with no modulus: one needs a quantitative version, saying how fast near-optimal locations and scales can escape for a \term{w:law}{law} close to $P$.
- Extends: D8, D7
- Source: papers/P005-bounded-kurtosis, version 1, label oq:finite
- Rating: interest medium; novelty open (round-1 queries; "explicit second order regret term KL_inf-UCB heavy tailed …", 2026-11-17); fit D8, D7 (referee-scope, pull request #40, head 57d6b1e4ad49)

## C8 (2026-11-17, from P005v1 oq:computation)
- Title: Efficient computation
- Statement: Is there an algorithm whose index can be computed to a certified accuracy in time polynomial in the number of samples, or that recomputes its indices at only $o(T)$ rounds, and that still satisfies $\lim_TR_T/\log T=\Cst(\nu)$ for every $\nu\in\Hk^\alpha$? The inner problem of \eqref{eq:dual} is a two-dimensional concave program over a fixed set, but the outer problem over $(c,s)$ is not convex, its domain is not compact, and its infimum may be approached at infinity. A first step would be a confinement lemma for empirical \term{w:law}{laws}: near-optimal $(c,s)$ lie in an explicit compact set, or the value there is at least $\Kinfty(\kappa)-\zeta$ for a given $\zeta>0$; the error of a grid would then be added to the threshold.
- Extends: D8
- Source: papers/P005-bounded-kurtosis, version 1, label oq:computation
- Rating: interest high; novelty open ("efficient computation KL_inf index … certified accuracy …", 2026-11-17; PA26 lists efficiency as future work); fit D8 (referee-scope, pull request #40, head 57d6b1e4ad49)

## C9 (2026-11-17, from P005v1 oq:smallgap)
- Title: The shape of the information function
- Statement: Is it true that, for every $\kappa>1$ and every $P\in\Hk$ with $\kurt(P)<\kappa$, $\Kc(P,\mean(P)+\Delta)=\frac{\Delta^2}{2\sd^2(P)}(1+o(1))$ as $\Delta\downarrow0$? What happens on the boundary $\kurt(P)=\kappa$, where Table~\ref{tab:duality} suggests the same behaviour for one \term{w:law}{law}? More globally, one half of a two-sided bound is known. Lattimore's algorithm is \term{w:consistent}{consistent} over $\Hk^\alpha$ by Lemma~\ref{cite:L17-thm2}; on the \term{w:instance}{instance} with two arms, of \term{w:law}{laws} $P$ and its translate by $\Delta>0$, Theorem~\ref{cite:LS-16.2} and Lemma~\ref{cite:L17-thm2} give $\Delta/\Kc(P,\mean(P)+\Delta)\le C\Delta(\kappa-1+\sd^2(P)/\Delta^2)$, hence $\Kc(P,\mean(P)+\Delta)\ge(2C)^{-1}\min\{\Delta^2/\sd^2(P),1/\kappa\}$ for every $\kappa>1$, $P\in\Hk$ and $\Delta>0$, with the universal constant $C$ of Lemma~\ref{cite:L17-thm2}. For $\Delta\ge\sd(P)/\sqrt\kappa$, Proposition~\ref{prop:kinfty} gives $\Kc(P,\mean(P)+\Delta)\le\Kinfty(\kappa)<1/\kappa\le\Delta^2/\sd^2(P)$. Is there a universal constant $C'$ with $\Kc(P,\mean(P)+\Delta)\le C'\Delta^2/\sd^2(P)$ for every $\kappa>1$, $P\in\Hk$ and $\Delta\in(0,\sd(P)/\sqrt\kappa)$? Lemma~\ref{cite:L17-thm9} gives this only for $\kappa\ge7/2$, $\kurt(P)<\kappa$ and $\Delta/\sd(P)$ below a threshold depending on $\kappa$ and $\kurt(P)$ (its first case, with its own constants). Our method gives no bound on $\Kc$ that is quantitative in $\Delta$ for small gaps: Proposition~\ref{prop:regularity}(iii) is proved by contradiction, and the far-atom construction of Proposition~\ref{prop:kinfty} costs a constant.
- Extends: D7
- Source: papers/P005-bounded-kurtosis, version 1, label oq:smallgap
- Rating: interest medium; novelty the small-gap equivalence and the universal $C'$ for $\Delta<\sigma/\sqrt\kappa$ are open ("minimum Kullback-Leibler divergence moment ratio …", 2026-11-17, and round 1); the lower half is derived in the question itself, conditional on L17 Theorem 2; fit D7 (referee-scope, pull request #40, head 57d6b1e4ad49)

## C10 (2026-11-17, from P005v1 oq:randomised)
- Title: Randomised and simpler index algorithms
- Statement: Is there a non-parametric Thompson-type algorithm, or an IMED-type index algorithm, pulling an arm that minimises $\Np_a(t)\Kc(\Pe_a(t),\hat m^\star(t))+\log\Np_a(t)$ with $\hat m^\star(t)$ the largest empirical mean, that satisfies $\limsup_TR_T/\log T\le\Cst(\nu)$ for every $\nu\in\Hk^\alpha$? The first is the second open problem of \citet[Section~4]{L17}. Our lower deviation inequality is uniform over a neighbourhood of the level, which an IMED analysis at the random level $\hat m^\star(t)$ needs, but the events specific to these algorithms were not checked.
- Extends: D10
- Source: papers/P005-bounded-kurtosis, version 1, label oq:randomised
- Rating: interest medium; novelty open ("IMED OR "Thompson sampling" … "kurtosis" …", 2026-11-17, and round 1); fit D10 (referee-scope, pull request #40, head 57d6b1e4ad49)

## C11 (2026-11-17, from P005v1 oq:profiled)
- Title: Classes convex up to location and scale
- Statement: Let $p>1$, $B>0$ and $\mathcal C_{p,B}:=\{P\in\Pspace:\E_P|X-\mean(P)|^p\le B\}$. Does KL-UCB with the information function $\Kinf(\cdot,\cdot;\mathcal C_{p,B})$ and the threshold \eqref{eq:threshold} satisfy $\limsup_T\E[\Np_a(T)]/\log T\le1/\Kinf(\nu_a,\mstar;\mathcal C_{p,B})$ for every \term{w:instance}{instance} $\nu\in\mathcal C_{p,B}^\alpha$ and every \term{w:subopt}{suboptimal} arm $a$, with no known lower bound on the means? For MED, \citet[Corollary~6]{BSH23} prove first-order optimality on the centred class $\{\E h(|X-m|)<B\}$, with a further integrability condition and a known lower bound on the means, which they use for compactness; the reduction to an outer minimisation over the location is also in \citet[Section~6.10]{A22}. Our method would profile the location only, and the analogue of Lemma~\ref{lem:escape} must show that the near-optimal locations $c>\mu$ stay bounded for \term{w:law}{laws} close to the arm's law: a location $c\to\infty$ moves the whole mass of the normalised \term{w:law}{law} to $-\infty$, which we expect to cost $+\infty$ by a bound of the type of Lemma~\ref{lem:tail}, and the KL-UCB analysis needs this only at the arm's law, not uniformly over the class; we do not write this proof. The same question, for KL-UCB with both location and scale profiled, is open for the ratio classes $\{\E|X-m|^p\le\kappa\sd^p\}$, $p>2$, and for bounds on skewness and kurtosis together.
- Extends: D7
- Source: papers/P005-bounded-kurtosis, version 1, label oq:profiled
- Rating: interest medium; novelty open: BSH23 Corollary 6 covers MED with a known lower bound on the means, and nothing covers KL-UCB without it ("KL-UCB asymptotically optimal "bounded variance" centered moment class …", 2026-11-17; round-1 queries on profiled classes); fit D7 (referee-scope, pull request #40, head 57d6b1e4ad49)
