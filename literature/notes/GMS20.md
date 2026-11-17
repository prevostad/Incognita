# GMS20: Fano's inequality for random variables

| | |
|---|---|
| Work | S. Gerchinovitz, P. Ménard, G. Stoltz, *Fano's Inequality for Random Variables*, Statistical Science 35(2), 178–201, 2020 |
| Identifiers | DOI 10.1214/19-STS716 (Crossref: issued 2020-05-01), arXiv 1702.05985 (v1 2017-02-20, v2 2018-09-19, v3 2019-06-10) |
| Read | Metadata (Crossref, arXiv abstract page). ar5iv HTML rendering of arXiv:1702.05985 (no version shown; presumably v3), read by targeted queries: table of contents, Corollary 2, Corollary 3, Section 3 up to (4)–(5), Lemma 6 (statement), occurrences of "bandit" in characters 0–200000 of the page; Appendix D list. Not read: proofs, Section 4 in full, Section 5 in full, the last part of the page (Appendix G onward), the published version |
| Read (2) | arXiv:1702.05985v3 PDF (10 Jun 2019, dated June 12, 2019 on p. 1), page images: p. 1 (abstract), p. 2 (§1), p. 6 (§3, Proposition 4 and its proof, (4)–(6)), pp. 7–9 (§4 opening, §4.1 (7)–(9), §4.2 (10)–(15), §4.3 Lemma 5), pp. 21–25 (end of §6; §7 in full: opening, §7.1 with Proposition 14 and its proof, Remark 2, §7.2 with Theorem 15, (37)–(39) and the Discussion) |
| By, date | Claude Opus 5.5 (revise, P001), 2026-11-15; Claude Opus 5.5 (revise, P008), 2026-11-17 (Read (2)) |

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

### From the arXiv v3 PDF (Read (2), numbering of v3)

- **Proposition 4 (§3, p. 6)** is the statement whose proof gives (4)–(6) above. Its last step, copied:
  "Noting that $\overline p\ln(\overline p)+(1-\overline p)\ln(1-\overline p)\geqslant-\ln(2)$, we have, by definition of
  $\mathrm{kl}(\overline p,\overline q)$, $\mathrm{kl}(\overline p,\overline q)\geqslant\overline p\ln(1/\overline q)-\ln(2)$, thus
  $\overline p\leqslant\frac{\mathrm{kl}(\overline p,\overline q)+\ln(2)}{\ln(1/\overline q)}$ (6) where $\overline q\in(0,1)$ by assumption."
- **(10), §4.2 "Lower bounds on kl" (p. 8), copied.** "The most classical bound was already used in
  Section 3: for all $p\in[0,1]$ and $q\in(0,1)$,
  $$\mathrm{kl}(p,q)\geqslant p\ln(1/q)-\ln(2),\qquad\text{thus}\qquad p\leqslant\frac{\mathrm{kl}(p,q)+\ln(2)}{\ln(1/q)}.\qquad(10)$$
  It is well-known that this bound can be improved by replacing the term $\ln(2)$ with $\ln(2-q)$: for all
  $p\in[0,1]$ and $q\in(0,1)$,
  $$\mathrm{kl}(p,q)\geqslant p\ln(1/q)-\ln(2-q),\qquad\text{thus}\qquad p\leqslant\frac{\mathrm{kl}(p,q)+\ln(2-q)}{\ln(1/q)}.\qquad(11)$$"
  Also (12): $p\leqslant0.21+0.79\,q+\frac{\mathrm{kl}(p,q)}{\ln(1/q)}$ ("A (novel) consequence"), proofs of (11)–(12) in §8.1
  (not read); (13): $\mathrm{kl}(p,q)\geqslant\max\{\ln(1/q),2\}(p-q)^2$, thus $p\leqslant q+\sqrt{\frac{\mathrm{kl}(p,q)}{\max\{\ln(1/q),2\}}}$,
  the first inequality "stated and proved by Ordentlich and Weinberger [2005]".
- **§4.1 (7)–(9)**: the Bernoulli reductions for countably many pairs (7), a parameter set with a prior (8),
  and $[0,1]$-valued $Z_\theta$ (9), the latter by convexity of $\mathrm{div}_f$, Jensen, and Lemma 2.
  **Lemma 5 (§4.3)**: the continuous Fano inequality from (8) and (10).
- **§7 "References and comparison to the literature" (pp. 22–25), summary with short quotations.**
  - Main innovations: alternatives $\mathbb Q_i,\mathbb Q_\theta$ that vary, and arbitrary $[0,1]$-valued $Z_i,Z_\theta$
    not summing to 1, both in reduction (9), "our main new result". Partitions or $Z_1+\dots+Z_N=1$ were
    usual requirements (Gushchin 2003), with one exception: Chen et al. (2016) noted that a partition is
    unnecessary, which the authors say was known to them as early as Stoltz (2007).
  - "Generalization to $f$–divergences (not a new result)": Gushchin (2003); also Chen et al. (2016).
  - "On the two-step methodology used (not a new result)": Bernoulli reduction then a lower bound on kl,
    "well-known" for disjoint events or $Z_i$ summing to 1 (Han and Verdú 1994, Gushchin 2003, Chen et al.
    2016; also Zhang 2006, Harremoës and Vajda 2011); "the conjunction of a Bernoulli reduction and the
    use of a lower bound on the kl function was already present in Han and Verdú [1994]". Other proofs for
    finitely many hypotheses: Cover and Thomas (2006, Theorem 2.11.1), Yu (1997, Lemma 3), Ibragimov and
    Has'minskii (1981, Chapter VII, Lemma 1.1).
  - "On the reductions to Bernoulli distributions": (9) new at this generality; (4) and (7) "already known
    and used by Han and Verdú [1994, Theorems 2, 7 and 8]"; (8) in spirit in Chen et al. (2016) with a
    constant alternative; Duchi and Wainwright (2013) preliminary results towards (8); a special case of
    (9) in Gushchin (2003).
  - "On the lower bounds on the kl function (not really a new result)", copied: "The inequalities (10)
    are folklore knowledge. The first inequality in (11) can be found in Guntuboyina [2011]; the second
    inequality is a new (immediate) consequence. The inequalities (13) are a consequence, which we derived
    on our own, of a refined Pinsker's inequality stated by Ordentlich and Weinberger [2005]."
  - §7.1: the "generalized Fano's inequality" of Chen et al. (2016) restated and extended to $[0,1]$-valued
    losses as Proposition 14 (proof from (9) and (11)); Remark 2: Han and Verdú (1994), Theorem 8, is the
    special case $\Theta=\mathcal A$, $L=\mathbb 1_{\{\theta\neq\theta'\}}$ (infinite-order Rényi entropy), for discrete $\Theta$.
  - §7.2: Birgé's lemma (Theorem 15, partitions, $N\ge2$, constants $c_N$ in (37)) compared with the
    versions (38)–(39) obtained from (11), (10) and (13); (39) interpolates between Pinsker and Fano.

## Techniques

Data processing for expectations of $[0,1]$-valued variables (Corollary 2), joint convexity of
$f$-divergences from data processing on an augmented space (Corollary 3), then a lower bound on kl
(Section 4, "Reduction to Bernoulli distributions"; "Any lower bound on div_f leads to a Fano-type
inequality"). Applications: posterior concentration rates (§5.1), sparse-loss online learning (§5.2),
Cramér's theorem for Bernoulli (§6.1).

## Where Incognita uses it

`papers/P001-minimax-constant/`: thm:bounds, Main result, Closest known, Attribution.
`papers/P008-transfer-lower-bound/` (revision of 2026-11-17: (10) and the §7 remarks on its origin).
