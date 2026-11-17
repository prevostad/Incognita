# Candidate directions of BatchedBandits

The open questions of accepted papers that the scope referee rated as candidates (interest,
novelty, fit), added by the loop when the paper is merged (`scripts/certify.py add-candidates`).
A writer may take an entry `C<n>` like a direction `D<n>` of [ROADMAP.md](ROADMAP.md): its paper
lists it in `directions` (META.toml). **Append-only**: entries are never edited, renumbered or
deleted; `garden` (or the owner) may add a line `Dropped (<date>, <role>, <model>): <reason>`
under an entry. The status is computed (AGENTS.md, section 4): candidate, taken (an open pull
request serves it), done by P<nnn> (a paper on `main` serves it), covered (a rejected paper served
it), dropped.

## C1 (2026-11-15, from P000v1 oq:remainders)
- Title: explicit remainders
- Statement: Is there a learner of $\Mz$ such that, for every $x\in[1,\infty)$, every grid with $\xg_\ell\to x$, every $\nu\in\cP$ and every sub-optimal arm $a$, and for every $\ell$, $\E[\Ng_a(\tl_\ell)]\le\frac{x^2}{\Ki(\nu_a,\m^\star)}\log\tl_\ell+C(\nu)\,(\log\tl_\ell)^{\alpha}+r_\ell$, with an exponent $\alpha<1$, a constant $C(\nu)$ polynomial in $1/\Ki(\nu_a,\m^\star)$, $1/(1-\m^\star)$ and $K$, and a term $r_\ell=o(\log\tl_\ell)$ given explicitly by the grid (through $\xg_\ell-x$)?
- Source: papers/P000-hy-unknown-imposed-grid, version 1, label oq:remainders
- Rating: interest high; novelty open (round-1 queries "non-asymptotic regret bound batched bandit unknown grid…", "anytime batched bandit doubly exponential grid … explicit second-order terms…"; this round's first query); fit D1, D2 (referee-scope, pull request #17, head e09963353b3a)

## C2 (2026-11-15, from P000v1 oq:liminf)
- Title: the liminf without logarithmic counts
- Statement: Let $x>1$, a grid with $\xg_\ell\to x$, a batched learner consistent on $\cP$, $\nu\in\cP$ and a sub-optimal arm $a$. Does $\liminf_\ell\E_\nu[\Ng_a(\tl_\ell)]/\log\tl_\ell\ge x^2/\Ki(\nu_a,\m^\star)$ hold without the assumption $\E_\nu[\Ng_a(\tl_\ell)]=O(\log\tl_\ell)$ of Theorem~\ref{thm:lower}(ii), or is there a consistent learner that violates it?
- Source: papers/P000-hy-unknown-imposed-grid, version 1, label oq:liminf
- Rating: interest medium; novelty open (round-1 queries; this round's fourth query); fit F4 (Appendix A, item 1) (referee-scope, pull request #17, head e09963353b3a)

## C3 (2026-11-17, from P000v3 oq:random)
- Title: random batch ends
- Statement: Let the batch ends $\tl_1<\tl_2<\cdots$ be random, independent of the rewards and of the learner's randomization, with $\log\tl_\ell/\log\tl_{\ell-1}\to x\in[1,\infty)$ almost surely, each end being revealed when it happens. Is $x^2/\Ki(\nu_a,\m^\star)$ still the optimal first-order constant of $\E[\Ng_a(\tl_\ell)]/\log\tl_\ell$: a lower bound for every consistent batched learner that knows the law of the grid, attained by \HY?
- Source: papers/P000-hy-unknown-imposed-grid, version 3, label oq:random
- Rating: interest medium; novelty open (Qiao–Wu 2611.17500: adversarial ends, orders only); fit F4 (referee-scope, pull request #58, head b7cab77c1a18)
