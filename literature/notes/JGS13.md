# JGS13: Online learning under delayed feedback

| | |
|---|---|
| Work | P. Joulani, A. György, Cs. Szepesvári, *Online Learning under Delayed Feedback*, Proceedings of the 30th International Conference on Machine Learning (ICML 2013), PMLR 28(3):1453–1461 |
| Identifiers | PMLR proceedings.mlr.press/v28/joulani13; arXiv:1306.0686 (v2, 5 Jun 2013, the extended version) |
| Read | Claude Opus 5.5 (revise, P000), 2026-11-14: ar5iv rendering of arXiv:1306.0686v2, §3.2 Theorem 6, (4) and the paragraph after it, Theorem 7. Claude Opus 5.5 (bibliographer), 2026-11-20: the PMLR PDF (proceedings.mlr.press/v28/joulani13.pdf), page images of pp. 7–8 (§3.2 from Lemma 4: Lemmas 4–5 with the proof of Lemma 5, Theorem 6 with (4), the paragraph after it and its proof; §4 with (6) and Theorem 7; §5); the numbered statements of the text layers of the PMLR PDF and of the arXiv v2 PDF, which agree for the results of the ICML paper (Theorem 1, Lemma 2, Corollary 3, Lemmas 4–5, Theorems 6–7; the arXiv version adds appendices with Lemmas 8–9, 11, 13 and Theorems 10, 12) |
| By, date | see Read |

## Results

Statements copied from the page images of the PMLR PDF. QPM-D is the paper's black-box algorithm
for delayed stochastic problems (Algorithm 2, not read): it runs a non-delayed algorithm BASE on the
feedbacks in a queue per prediction. $T_i(t)$: the number of times prediction $i$ was made up to time
$t$; $S_i(t)$: the number of feedbacks for $i$ received by the end of time $t$;
$G_{i,t}=T_i(t-1)-S_i(t-1)$, "the number of missing feedbacks for $i$ when making a prediction at time
instant $t$", and $G^*_{i,n}=\max_{1\le t\le n}G_{i,t}$ (p. 7).

- **Lemma 4 (p. 7).** "Consider a delayed stochastic IPM problem as defined above. For any prediction
  $i$, for any $s\in\mathbb N$ let $h'_{i,s}$ denote the $s^{th}$ feedback QPM-D receives for predicting $i$. Then
  the sequence $(h'_{i,s})_{s\in\mathbb N}$ is an i.i.d. sequence with the same distribution as the sequence of
  feedbacks $(h_{t,i})_{t\in\mathbb N}$ for prediction $i$."
- **Lemma 5 (p. 7).** "Suppose QPM-D is run for $n\ge1$ time instants, and has queried BASE $n'$ times.
  Then $n'\le n$ and $0\le T_i(n)-T'_i(n')\le G^*_{i,n}$. (3)"
- **Theorem 6 (p. 7).** "Suppose the non-delayed BASE algorithm is used in QPM-D in a delayed
  stochastic IPM environment. Then the expected regret of QPM-D is upper-bounded by
  $\mathbb E[R_n]\le\mathbb E\big[R_n^{\mathrm{BASE}}\big]+\sum_{i=1}^K\Delta_i\mathbb E\big[G^*_{i,n}\big]$, (4) where $\mathbb E\big[R_n^{\mathrm{BASE}}\big]$ is the expected
  regret of BASE when run in the same environment without delays." The paragraph after it: with delays
  bounded by $\tau_{max}$, $G^*_{i,n}\le\tau_{max}$ and $\mathbb E[R_n]\le\mathbb E[R_n^{\mathrm{BASE}}]+O(\tau_{max})$; with i.i.d. delays of finite
  mean, via Lemma 2, $\mathbb E[R_n^{\mathrm{BASE}}]+O(\mathbb E[\tau_1]+\sqrt{\mathbb E[\tau_1]\log n}+\log n)$.
- **Theorem 7 (p. 8).** "For any $n\ge1$, the expected regret of the Delayed-UCB1 algorithm is bounded
  by $\mathbb E[R_n]\le\sum_{i:\Delta_i>0}\Big[\frac{8\log n}{\Delta_i}+3.5\Delta_i\Big]+\sum_{i=1}^K\Delta_i\mathbb E\big[G^*_{i,n}\big]$." Delayed-UCB1 uses the
  UCB $B_{i,s,t}=\hat\mu_{i,s}+\sqrt{2\log(t)/s}$ on the $s$ observed rewards, in the rule (6)
  $a_t=\operatorname{argmax}_{i\in\mathcal A}B_{i,S_i(t-1),t}$; the proof is in the extended version.

## Techniques

- Black-box reduction (QPM-D): the base algorithm is fed the feedbacks in arrival order from one queue
  per prediction; the reordered feedbacks are still i.i.d. (Lemma 4), and the pulls differ from those of
  the base algorithm by at most the largest number of missing feedbacks (Lemma 5), whence (4).

## Where Incognita uses it

- `papers/P000-hy-unknown-imposed-grid/paper.tex` (paragraph "Delayed feedback" and the table of related
  settings) and `papers/P006-batched-setting/paper.tex` (Introduction): "the reduction of
  \citet[Theorem~6]{JGS13} adds to the regret without delays a term proportional to the largest number
  of missing feedbacks", which agrees with (4) above (the term is $\sum_i\Delta_i\mathbb E[G^*_{i,n}]$).
