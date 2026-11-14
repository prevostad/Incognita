Reviewed by owner: 2026-11-14 (approved in a conversation with Claude; the entries were written by Claude from the owner's published papers only)

# KNOWN: roadmap TransferBandits

What the owner already knows in this roadmap, **negative results and failed approaches included**,
so that agents neither propose nor re-derive it. Reviewed by the owner only. The entries below come
from the owner's **published** papers only (written by Claude Opus 5.5 on 2026-11-14 from the
owner's manuscript of arXiv:2610.21582, the submitted version; a paper that uses an entry checks
the statement against the posted version). By the owner's choice, his
unpublished work on transfer is not listed: agents may find it on their own.

For agents: read every entry before writing or refereeing a paper. A paper answered by an entry, or
by a short combination of entries, is not written (and is rejected if submitted). A paper that
extends an entry cites its id and says exactly what is new. Cite entries by id (`K12`). Entries
flagged `private` are never re-derived, proposed, formalised or quoted.

## Format of an entry

```
- **K<n>.** [status] [private] <Statement: the class of instances and learners, the criterion,
  every algorithm given by its formula, not only its name.> — *Reason:* <one line: where it is
  proved, or why it is believed>. — *Source:* <optional>.
```

- Status: `[published]` a published result (give the source); `[Lean]` formalised without `sorry`
  (say where); `[paper]` proved on paper, checked by independent agents only; `[sketch]` an
  argument, or a proof never checked independently; `[belief]` heuristic or numerical evidence, or
  a conjecture (give a confidence).
- Flag `private`: unpublished, and not to be worked on by agents.
- Numbers K1, K2, … are never reused or renumbered; a withdrawn entry stays, marked `withdrawn`.
- The conventions are the roadmap's ([ROADMAP.md](ROADMAP.md)); any extra notation is defined here.
  Here $\mathcal K_{\inf}(P,\mu) := \inf\lbrace\mathrm{KL}(P,Q) : Q\in\mathcal P[0,1],\ m(Q)>\mu\rbrace$,
  arm 1 is the unique optimal arm, $\mu_1 := \max_k\mu_k$, and $\mathcal C_L$ is the class of
  learners whose expected count of every suboptimal arm is $o(T^\alpha)$ for every $\alpha>0$, for
  every pair $(\nu,\nu')$ of instances on $[0,1]$ with $|\mu_k-\mu'_k|\le L_k$ for all $k$ and every
  strategy generating the source data [arXiv:2610.21582, Section 3].

## Positive results

- **K1.** [published] Gaussian rewards with known variance, deterministic source sizes: a
  problem-dependent asymptotic lower bound and an asymptotically optimal transfer policy (the first
  version of the KL-UCB-Transfer index). — *Reason:* proved in the source. — *Source:* A. Prevost,
  T. Mathieu, O.-A. Maillard, ACML 2025 (PMLR 304), arXiv:2509.19098 (not re-read for this list).
- **K2.** [published] Lower bound. For every $\pi\in\mathcal C_L$, every $(\nu,\nu')$ on $[0,1]$ with
  $|\mu_k-\mu'_k|\le L_k$, every source strategy coming from a bandit game played over $T'=f(T)$
  rounds and every suboptimal arm $a$: (i) if $\mu'_a\le\mu_1-L_a$ and
  $\limsup_T\mathbb E[N'_a]/\ln T<\infty$, then
  $\liminf_T \mathbb E[N_a(T)]/\ln T \ge \liminf_T\big(1-\tfrac{\mathbb E[N'_a]}{\ln T}\mathcal K_{\inf}(\nu'_a,\mu_1-L_a)\big)_+/\mathcal K_{\inf}(\nu_a,\mu_1)$;
  (ii) if $\mu'_a>\mu_1-L_a$, then $\liminf_T\mathbb E[N_a(T)]/\ln T\ge 1/\mathcal K_{\inf}(\nu_a,\mu_1)$.
  — *Reason:* change of measure on the pair (source, online game). — *Source:* arXiv:2610.21582,
  lower-bound theorem.
- **K3.** [published] Upper bound of KL-UCB-Transfer (K8) on $[0,1]$, for $|\mu_k-\mu'_k|<L_k$ for all
  $k$, every suboptimal arm $a$ and every $T\ge3$: (i) if $\mu'_a<\mu_1-L_a$,
  $\mathbb E[N_a(T)]\le\mathbb E\big[(\ln T-N'_a\mathcal K_{\inf}(\nu'_a,\mu_1-L_a))_+\big]/\mathcal K_{\inf}(\nu_a,\mu_1)+O\big((\ln T)^{4/5}(\ln\ln T)^{1/5}\big)$;
  (ii) otherwise $\mathbb E[N_a(T)]\le\ln T/\mathcal K_{\inf}(\nu_a,\mu_1)+O\big((\ln T)^{4/5}(\ln\ln T)^{1/5}\big)$.
  — *Source:* arXiv:2610.21582, first upper-bound theorem.
- **K4.** [published] If $\mathbb E\big|N'_a-\mathbb E N'_a\big|=o(\ln T)$, K2 and K3 match, except
  possibly at the boundary $\mu'_a=\mu_1-L_a$. — *Source:* arXiv:2610.21582, proposition after K3.
- **K5.** [published] Misspecification: for every $(\nu,\nu')$ on $[0,1]$ (no drift condition),
  every suboptimal arm $a$ and every $\mu^\dagger\in(\mu_a,\mu_1]$ with $\mu^\dagger<\mu'_1+L_1$,
  KL-UCB-Transfer has $\mathbb E[N_a(T)]\le\ln T/\mathcal K_{\inf}(\nu_a,\mu^\dagger)+O\big((\ln T)^{4/5}(\ln\ln T)^{1/5}\big)$,
  and, if moreover $\mu'_a+L_a<\mu^\dagger$, the bound of K3(i) with $\mu^\dagger$ in place of
  $\mu_1$. Three regimes follow: well specified ($\mu'_1+L_1>\mu_1$: K3), mildly misspecified
  ($\mu_a<\mu'_1+L_1\le\mu_1$: logarithmic regret, degraded constant), severely misspecified
  ($\mu'_1+L_1\le\mu_a$: no guarantee). Only the one-sided quantities $\mu'_a+L_a$ matter.
  — *Source:* arXiv:2610.21582, misspecification theorem.
- **K6.** [published] Several independent sources $i=2,\dots,M$ with bounds $L^{(i)}$: the bound of
  K5 with $\sum_{i\in\mathcal S_a^\dagger}N_a^{(i)}\mathcal K_{\inf}(\nu_a^{(i)},\mu^\dagger-L_a^{(i)})$
  in place of $N'_a\mathcal K_{\inf}(\nu'_a,\mu^\dagger-L_a)$, where $\mathcal S_a^\dagger$ is the set
  of sources with $\mu_a^{(i)}+L_a^{(i)}<\mu^\dagger$, for
  $\mu^\dagger<\min_i\mu_1^{(i)}+L_1^{(i)}$. — *Source:* arXiv:2610.21582, multi-source theorem
  (an upper bound only; no matching lower bound).

## Negative results and counterexamples

- **K7.** [published] (a) K2 is not tight in general: with $N'_a=T$ with probability $\varepsilon$
  and $N'_a=0$ otherwise, K2 is vacuous, while a learner of $\mathcal C_L$ whose restriction to "no
  source data" is consistent still has $\mathbb E[N_a(T)]\ge(1-\varepsilon)(1-o(1))\ln T/\mathcal K_{\inf}(\nu_a,\mu_1)$.
  (b) No learner can exploit the source without a bound $L$: a learner consistent for every valid
  $L$ is in $\mathcal C_{(1,\dots,1)}$, where K2(ii) always applies. — *Source:* arXiv:2610.21582,
  discussion after the lower bound.

## Algorithms already studied

- **K8.** [published] KL-UCB-Transfer on $[0,1]$: pull each arm once, then at round $t>K$ pull an
  arm maximizing
  $U_a(t):=\sup\lbrace\mu : N_a(t)\,\mathcal K_{\inf}(\hat\nu_a(t),\mu)+N'_a\,\mathcal K_{\inf}(\hat\nu'_a,\mu-L_a)\le\ln t+\ln\ln t\rbrace$,
  ties broken uniformly at random, with $N'_a\mathcal K_{\inf}(\hat\nu'_a,\cdot):=0$ when $N'_a=0$;
  $\hat\nu_a(t)$, $\hat\nu'_a$ are the empirical laws of the online and source samples of arm $a$.
  — *Source:* arXiv:2610.21582, Section 4.

## The owner's dead ends

None yet.

## Conjectures

None yet.

## Directions judged uninteresting

None yet.
