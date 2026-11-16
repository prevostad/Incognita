# CBL06: Prediction, learning, and games

| | |
|---|---|
| Work | N. Cesa-Bianchi, G. Lugosi, *Prediction, Learning, and Games*, Cambridge University Press, 2006 |
| Identifiers | DOI 10.1017/CBO9780511546921 (Crossref: type monograph, issued and published-print 2006-03-13, published-online 2009-12-03; ISBN 9780521841085 print, 9780511546921 electronic). The authors' page https://cesa-bianchi.di.unimi.it/predbook/ gives ISBN 0521841089, "March 2006", 406 pages |
| Read | **The book itself was not accessed** (not open access). Read: Crossref record; the authors' book page (table of contents of Chapter 6); the authors' errata (https://cesa-bianchi.di.unimi.it/predbook/errata.pdf, "Errata (September 8, 2006)", 3 pages, no entry for Chapter 6). Theorem 6.11 is known only through secondary sources, listed below |
| By, date | Claude Opus 5.5 (revise, P001), 2026-11-15 |

## Results

- **Table of contents of Chapter 6 (authors' page).** "6 Prediction with limited feedback": 6.1
  Introduction, 6.2 Label efficient prediction, 6.3 Lower bounds, 6.4 Partial monitoring, 6.5 A general
  forecaster for partial monitoring, 6.6 Hannan consistency and partial monitoring, 6.7 Multi-armed
  bandit problems, 6.8 An improved bandit strategy, 6.9 Lower bounds for the bandit problem, 6.10 How
  to select the best action, 6.11 Bibliographic remarks, 6.12 Exercises. (No page numbers given.)
  That Theorem 6.11 lies in Section 6.9 is not checked.
- **Theorem 6.11: not read.** Its statement, constant, and conditions on $n$ and $N$ (or $K$) were not
  seen in the book or in any source quoting it verbatim. Secondary sources:
  - [LWKW26, §5.2, p. 18]: "For $K\ge2$, the Bernoulli instances used in the lower-bound construction
    of Cesa-Bianchi et al. (2006, Theorem 6.11) imply
    $\inf_\pi\sup_{\mathbf p\in[0,1]^K}R_T(\pi,\mathbf p)\ge(\sqrt2-1)\sqrt{KT}/\sqrt{32\log(4/3)}>0.1365\sqrt{KT}$."
    This is LWKW26's consequence for Bernoulli pseudo-regret, not a quotation of the theorem; it
    states no condition on $T$. See notes/LWKW26.md.
  - [GMS19, paragraph after the theorem of Appendix B.1, ar5iv rendering]: "The constant $1/20$ can
    actually be improved into $1/8$, see Cesa-Bianchi and Lugosi 2006, Theorem 6.11" (see
    notes/GMS19.md; read in an earlier session).
  - Search-engine snippets only (not read): arXiv:1108.4961 attributes the bandit minimax lower bound
    to "Auer et al. (2002) (also, Cesa-Bianchi and Lugosi (2006, Theorem 6.11))"; JMLR 12 (2011),
    "X-Armed Bandits", uses "the proof of the lower bound of Cesa-Bianchi and Lugosi (2006, Section
    6.9)" with arms Ber(1/2) and one Ber(1/2+η).
  - The condition "$n\ge K^2/(4\log(4/3))$" and the form of the regret (expected regret against an
    adversary or a randomised stochastic construction) were **not seen** in any source read.

## Techniques

Not read.

## Where Incognita uses it

`papers/P001-minimax-constant/`: the "improved into $1/8$" remark (quoted through GMS19) and the
referee's claim that LWKW26 §5.2 restates Theorem 6.11. Neither the constant nor the conditions of
Theorem 6.11 may be attributed to CBL06 until the book is read.
