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
