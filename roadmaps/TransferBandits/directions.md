# Candidate directions of TransferBandits

The open questions of accepted papers that the scope referee rated as candidates (interest,
novelty, fit), added by the loop when the paper is merged (`scripts/certify.py add-candidates`).
A writer may take an entry `C<n>` like a direction `D<n>` of [ROADMAP.md](ROADMAP.md): its paper
lists it in `directions` (META.toml). **Append-only**: entries are never edited, renumbered or
deleted; `garden` (or the owner) may add a line `Dropped (<date>, <role>, <model>): <reason>`
under an entry. The status is computed (AGENTS.md, section 4): candidate, taken (an open pull
request serves it), done by P<nnn> (a paper on `main` serves it), covered (a rejected paper served
it), dropped.

## C1 (2026-11-15, from P002v1 oq:nonparametric)
- Title: The nonparametric model
- Statement: In the model where the target and source laws are any laws on $[0,1]$, with $d=W_1$ or $d=\TV$, deterministic sizes $N'_a(T)/\log T\to c_a$ and the consistency class of Definition~\ref{def:class} on that model: is there a learner with $\lim_T\E N_a(T)/\log T=D^{[0,1]}_a(c_a)$, the constant of Definition~\ref{def:constant} with the infimum over pairs of laws on $[0,1]$ (the lower bound of \cite[Theorem~3]{PMM25})? The method of types fails: for a continuous law, $\KL(\hat\nu_{1,s},q)=\infty$ for every $q$ close to $\nu_1$, and a dual (Honda--Takemura type) statistic has a functional multiplier ($B$ in Lemma~\ref{lem:weak-duality}), bounded for $\TV$ and Lipschitz for $W_1$, whose union bounds cost $e^{O(s)}$. Extends D8.
- Source: papers/P002-transfer-drift-between-laws, version 1, label oq:nonparametric
- Rating: interest high; novelty open (queries "asymptotically optimal bandit bounded rewards prior samples ... Wasserstein constraint ..." and "transfer learning multi-armed bandit ... Wasserstein ..." found none); fit D8 (referee-scope, pull request #24, head ebbe0ac57ba5)

## C2 (2026-11-15, from P002v1 oq:misspecification)
- Title: Misspecification
- Statement: For $(\nu,\nu')\in\Simp^K\times\Simp^K$ with $d(\nu_1,\nu'_1)\ge L_1$ (arm 1 the unique optimal arm): describe the regret of \Alg{} as in K5. Is the threshold quantity $\mu'_1+\omega_d(\nu'_1)=\max\{m(q):d(q,\nu'_1)\le L_1\}$, which replaces $\mu'_1+L_1$ of K5, so that the regret stays logarithmic iff $\mu_a<\mu'_1+\omega_d(\nu'_1)$ for every suboptimal $a$? Extends D8(c) and K5.
- Source: papers/P002-transfer-drift-between-laws, version 1, label oq:misspecification
- Rating: interest medium; novelty open (queries "KL-UCB-Transfer misspecified source total variation ..." and "bandit offline data distribution shift total variation ..." found only mean-shift works; K5 is the mean case); fit D8 (c) (referee-scope, pull request #24, head ebbe0ac57ba5)

## C3 (2026-11-15, from P002v1 oq:random)
- Title: Random source sizes
- Statement: On $\Simp$, let the source sizes be chosen by a source strategy as in the roadmap (the first $N'_k$ values of an i.i.d.\ stack of $\nu'_k$, $N'_k$ a stopping time of the source data, with $\limsup_T\E N'_a(T)/\log T<\infty$). Does \Alg{} satisfy $\limsup_T\E N_a(T)/\log T\le\limsup_T\E\big[D_a(N'_a(T)/\log T)\big]$, the analogue of K3(i) (for the mean gap, $D^{\dmean}_a(N'_a/\log T)\log T=(\log T-N'_a\Kop)_+/\Ko$)? The term of the optimal arm survives (the proof of Lemma~\ref{lem:source} gives a bound summable over the sizes), but Lemma~\ref{lem:sub-constant} splits on the source sample of $a$ with a deterministic size. Extends D1 and D8.
- Source: papers/P002-transfer-drift-between-laws, version 1, label oq:random
- Rating: interest medium; novelty open (query "bandit historical data random number of samples ... N' K_inf ..." and round-1 query found only PMRM26, mean drift); fit D1, D8 (referee-scope, pull request #24, head ebbe0ac57ba5)

## C4 (2026-11-16, from P003v1 oq:deterministic)
- Title: Deterministic sizes against size rules
- Statement: For $L\in(0,1)^K$, let $\mathcal C^{\rm det}_L$ be the class of Definition~\ref{def:consistency} with the source strategies restricted to deterministic sizes ($\Np^{(T)}\equiv n(T)$ for sequences $n(T)\in\N^K$), and $\mathcal C^{\rm game}_L$ the class with the strategies restricted to prior bandit games (Definition~\ref{def:prior-game}) over $T'(T)$ rounds. Then $\ClL\subset\mathcal C^{\rm game}_L\subset\mathcal C^{\rm det}_L$. Is either inclusion strict: is there a transfer learner, consistent for every deterministic sequence of sizes, that fails against an adaptive strategy, for instance one that keeps sampling the source of the optimal arm until its empirical mean looks low? Theorem~\ref{thm:main} cannot separate the classes, since it sees the strategy only through $\E \Np_k$; a separation needs a learner whose use of the source is valid for fixed sizes only (confidence bounds that are not uniform in the sample size), and must keep consistency on the closed set $\PcL$, including $\mean'_1+L_1=\mean_1$. The answer says whether the class of a lower bound depends on how the source was collected.
- Extends: D1
- Source: papers/P003-transfer-setting, version 1, label oq:deterministic
- Rating: interest medium; novelty open. The queries of rounds 1–3 ("bandit with historical data consistency fails when historical samples collected adaptively …", "offline-to-online bandit adaptively collected offline data logging policy unknown …") and this round's "transfer bandit lower bound source samples collected adaptively …" (2026-11-16) found no separation of the classes; fit D1 (referee-scope, pull request #29, head b3394d876118)
