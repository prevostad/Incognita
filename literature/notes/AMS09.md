# AMS09: Exploration–exploitation tradeoff using variance estimates in multi-armed bandits

| | |
|---|---|
| Work | J.-Y. Audibert, R. Munos, Cs. Szepesvári, *Exploration–exploitation tradeoff using variance estimates in multi-armed bandits*, Theoretical Computer Science 410(19), 1876–1902, 2009 |
| Identifiers | DOI 10.1016/j.tcs.2009.01.016 |
| Read | Authors' version (sites.ualberta.ca/~szepesva/papers/ucbtuned-journal.pdf), text layer: §3.2 Theorem 2 with (10)–(12) and the proof of (10)–(11); §5 opening; §5.1 in full (index (25), Theorem 7, Lemma 3 and their proofs, Theorem 8, its proof, the remark after it). Earlier (roadmap draft, 2026-11-14): abstract, §1 overview, Theorem 10 and footnote 5, Theorem 13 statement |
| By, date | Claude Opus 5.5 (revise, P007), 2026-11-17 (the parts of §3.2 and §5.1) |

Numbering of the authors' version; the journal numbering was not checked. The statements below
are transcriptions from the text layer of the PDF (its mathematics is garbled in places and was
reconstructed from the layout), in the source's notation: $K$ arms, rewards in $[0,b]$, $T_k(n)$ the
number of pulls of arm $k$ among the first $n$ rounds, $\bar X_{k,s}$ the mean of the first $s$
rewards of $k$, $R_n=\sum_k\Delta_kT_k(n)$ the pseudo-regret, $k^*$ an optimal arm, $\mu^*$ the best
mean.

## Results

- **Theorem 2 (§3.2, for UCB-V under Assumption A1).** (i) After $K$ plays, each arm has been pulled
  once. (ii) For any arm $k$, $n\in\mathbb N^+$, $\tau\in\mathbb R$ and integer $u>1$, (10)–(11) bound
  $T_k(n)$ and $\mathbb E[T_k(n)]$ by $u$ plus the rounds at which $B_{k,s,t}>\tau$ for some
  $u\le s\le t-1$ or $\tau\ge B_{k^*,s^*,t}$ for some $1\le s^*\le t-1$; and (12):
  $\mathbb P(T_k(n)>u)\le\sum_{t=u+1}^n\mathbb P(B_{k,u,t}>\tau)+\mathbb P(\exists s:1\le s\le n-u,\ B_{k^*,s,u+s}\le\tau)$,
  "from a direct argument that uses that the exploration function $\mathcal E_{s,t}$ is a
  nondecreasing function with respect to $t$". (10) and (11) hold "independently of the form of
  $B_{k,s,t}$".
- **(25), §5.1.** UCB1 with exploration coefficient $\rho$: $B_{k,s,t}:=\bar X_{k,s}+b\sqrt{\rho\log t/s}$;
  "in the original version of UCB1, the exploration coefficient was set to $\rho=2$".
- **Lemma 3.** For $n\ge2$ and $u=\lceil(2b/\Delta_k)^2\rho\log n\rceil$, for any $u\le s\le t\le n$,
  $\mathbb P(B_{k,s,t}>\mu^*)\le e^{-s\Delta_k^2/(2b^2)}$ (Hoeffding).
- **Theorem 7.** For $\rho>1$, $\mathbb E[R_n]\le\sum_{k:\Delta_k>0}\big(\frac{4b^2}{\Delta_k}\rho\log n+\Delta_k(\frac32+\frac1{2(\rho-1)})\big)$.
- **Theorem 8.** For $\rho>1/2$, $v_k=(2b/\Delta_k)^2$, $r_0=\sum_k\Delta_k(1+\rho v_k\log n)$ and any
  $x\ge1$,
  $\mathbb P(R_n>r_0x)\le\sum_{k:\Delta_k>0}\big\{n^{-2\rho x+1}+\frac{((1+\rho v_k\log n)x)^{-2\rho+1}}{2\rho-1}\big\}$ (29).
  The proof bounds each arm: $\mathbb P(T_k(n)>(1+\rho v_k\log n)x)\le n^{-2\rho x+1}+\frac{((1+\rho v_k\log n)x)^{1-2\rho}}{2\rho-1}$.
- **Remark after Theorem 8.** The second term of (29) is only polynomial in $x$, and "this bound
  cannot be improved": for some reward laws, $\mathbb P(R_n>z)\ge1/(Cz^C)$ for $z$ large (Theorem 10
  for UCB-V).

## Techniques

- Tail of a count at a single count (proof of Theorem 8, with (12) at $u=u_k=\lfloor(1+\rho v_k\log n)x\rfloor$
  and $\tau=\mu^*$): the first sum of (12) by Lemma 3 (Hoeffding for arm $k$ at the count $u_k$,
  $\le n^{-2\rho x}$ per round), the second by Hoeffding for the optimal arm at the rounds $u_k+s$
  ($\le(u_k+s)^{-2\rho}$), summed by an integral: $\le u_k^{1-2\rho}/(2\rho-1)$.
- The decomposition (10)–(11) generalises and improves the analysis of ACF02.

## Where Incognita uses it

- `papers/P007-stochastic-setting/`: the source of the argument of `prop:ucb-tails` (remark after it,
  `sec:related` "Gap with the literature", `sec:attribution`); with $b=1$, $\rho=2$, $x=1$ the per-arm
  bound gives a tail in $(\log n)^{-3}$, of which `prop:ucb-tails` ($(\log T)^{-2}$) is a weaker form.
- Roadmap StochasticBandits, KNOWN.md K32 (Theorem 10 and footnote 5).
