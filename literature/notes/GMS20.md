# GMS20: Fano's inequality for random variables

| | |
|---|---|
| Work | S. Gerchinovitz, P. Ménard, G. Stoltz, *Fano's Inequality for Random Variables*, Statistical Science 35(2), 178–201, 2020 |
| Identifiers | DOI 10.1214/19-STS716 (Crossref: issued 2020-05-01), arXiv 1702.05985 (v1 2017-02-20, v2 2018-09-19, v3 2019-06-10) |
| Read | Metadata (Crossref, arXiv abstract page). ar5iv HTML rendering of arXiv:1702.05985 (no version shown; presumably v3), read by targeted queries: table of contents, Corollary 2, Corollary 3, Section 3 up to (4)–(5), Lemma 6 (statement), occurrences of "bandit" in characters 0–200000 of the page; Appendix D list. Not read: proofs, Section 4 in full, Section 5 in full, the last part of the page (Appendix G onward), the published version |
| By, date | Claude Opus 5.5 (revise, P001), 2026-11-15 |

Numbering is that of the ar5iv rendering; it may differ from the published article.

## Results

- **Corollary 2, §2.3, "Data-processing inequality with expectations of random variables".** For
  $X$ "taking values in $[0,1]$": $\mathrm{div}_f(\mathbb E_{\mathbb P}[X],\mathbb E_{\mathbb Q}[X])\le\mathrm{Div}_f(\mathbb P,\mathbb Q)$.
  The kl/KL form is the case $f(x)=x\ln x$ (stated for general $f$).
- **Corollary 3, "Joint convexity of $\mathrm{Div}_f$".** "All $f$-divergences $\mathrm{Div}_f$ are jointly
  convex, i.e., for all probability distributions $\mathbb P_1,\mathbb P_2$ and $\mathbb Q_1,\mathbb Q_2$ on the
  same measurable space, and all $\lambda\in(0,1)$,
  $\mathrm{Div}_f\bigl((1-\lambda)\mathbb P_1+\lambda\mathbb P_2,(1-\lambda)\mathbb Q_1+\lambda\mathbb Q_2\bigr)\le(1-\lambda)\mathrm{Div}_f(\mathbb P_1,\mathbb Q_1)+\lambda\mathrm{Div}_f(\mathbb P_2,\mathbb Q_2)$."
  Derived "as an elementary consequence of Lemma 1 applied to an augmented probability space"
  (Lemma 1: data processing).
- **Section 3, (4)–(5), N pairs with averaging.** "Using first the joint convexity of the
  Kullback-Leibler divergence (Corollary 3), and second the data-processing inequality with the
  indicator functions $X=\mathbb 1_{A_i}$ (Lemma 1), we get"
  $\mathrm{kl}\bigl(\frac1N\sum_{i=1}^N\mathbb P_i(A_i),\frac1N\sum_{i=1}^N\mathbb Q_i(A_i)\bigr)\le\frac1N\sum_{i=1}^N\mathrm{kl}(\mathbb P_i(A_i),\mathbb Q_i(A_i))\le\frac1N\sum_{i=1}^N\mathrm{KL}(\mathbb P_i,\mathbb Q_i)$.
  "Therefore, we have $\mathrm{kl}(\overline p,\overline q)\le\overline K$" (4), with (5)
  $\overline p=\frac1N\sum_i\mathbb P_i(A_i)$, $\overline q=\frac1N\sum_i\mathbb Q_i(A_i)$, $\overline K=\frac1N\sum_i\mathrm{KL}(\mathbb P_i,\mathbb Q_i)$.
  Stated with events $A_i$; no display with $[0,1]$-valued $Z_i$ inside kl was found.
- **Lemma 6 (Fano-type, $[0,1]$-valued $Z_i$).** Under $0<\frac1N\sum_i\mathbb E_{\mathbb Q_i}[Z_i]<1$:
  $\frac1N\sum_{i=1}^N\mathbb E_{\mathbb P_i}[Z_i]\le\frac1N\sum_{i=1}^N\mathbb E_{\mathbb Q_i}[Z_i]+\sqrt{\dfrac{\frac1N\sum_{i=1}^N\mathrm{KL}(\mathbb P_i,\mathbb Q_i)}{-\ln\bigl(\frac1N\sum_{i=1}^N\mathbb E_{\mathbb Q_i}[Z_i]\bigr)}}$;
  particular case "if $N\ge2$ and $Z_1+\dots+Z_N=1$ a.s.", with $1/N$ in the first term. Proof not read.
- **Theorem 10, §5.2** (robust sequential learning with sparse losses, full information): a lower
  bound $\min\{\frac{s}{16N}T,\frac1{32}\sqrt{\frac{Ts}{N}\ln N}\}$. Hypotheses not read.
- No bandit lower bound of order $\sqrt{KT}$ was found (characters 0–200000 of the ar5iv page);
  "bandit" occurs only in a remark "in the same spirit as for the bandit lower bounds derived by
  Kaufmann et al. 2016 and Garivier et al. 2018" and in the references.

## Techniques

Data processing for expectations of $[0,1]$-valued variables (Corollary 2), joint convexity of
$f$-divergences from data processing on an augmented space (Corollary 3), then a lower bound on kl
(Section 4, "Reduction to Bernoulli distributions"; "Any lower bound on div_f leads to a Fano-type
inequality"). Applications: posterior concentration rates (§5.1), sparse-loss online learning (§5.2),
Cramér's theorem for Bernoulli (§6.1).

## Where Incognita uses it

`papers/P001-minimax-constant/`: thm:bounds, Main result, Closest known, Attribution.
