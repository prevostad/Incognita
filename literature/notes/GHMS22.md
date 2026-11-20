# GHMS22: KL-UCB-Switch

| | |
|---|---|
| Work | A. Garivier, H. Hadiji, P. Ménard, G. Stoltz, *KL-UCB-Switch: Optimal Regret Bounds for Stochastic Bandits from Both a Distribution-Dependent and a Distribution-Free Viewpoints*, Journal of Machine Learning Research 23(179):1–66, 2022 |
| Identifiers | JMLR https://jmlr.org/papers/v23/20-717.html; arXiv:1805.05071 (v3, 1 Jul 2022) |
| Read | agent (roadmap draft), 2026-11-14, and Claude Opus 5.5 (revise, P000, P006), 2026-11-14 and 2026-11-17: see `index.md` (arXiv v3; Appendix B.1 in the ar5iv rendering). Claude Opus 5.5 (bibliographer), 2026-11-20: the JMLR PDF (jmlr.org/papers/volume23/20-717/20-717.pdf, header "Journal of Machine Learning Research 23 (2022) 1-66", "Submitted 7/20; Revised 10/21; Published 6/22"), page images of pp. 7–8 ((2)–(4), §2.1 with Algorithm 1, (5)–(8)), p. 21 (Lemma 11, Corollaries 12–13, Proposition 14) and pp. 40–41 (Appendix B opening, B.1: the proof of (19) in full and of (20) up to the bound $\mathrm{KL}(\nu,\nu')\ge\mathrm{KL}(\nu,\nu'_\alpha)+2\varepsilon(\mathrm E(\nu)-\mathrm E(\nu'))$); the numbered statements and appendix headings of the text layers of the JMLR PDF and of the arXiv v3 PDF, which agree (Lemma 11, Lemma 18, B.1 "Proof of the Regularity Lemma (Lemma 11)", B.3, B.4, Appendix C, Appendix D "Proof of the Variational Formula (Lemma 21)") |
| By, date | see Read |

## Results

Statements copied from the page images of the JMLR PDF. $\mathcal P[0,1]$: the laws on $[0,1]$; $\mathrm E(\nu)$
the mean; $\mathrm{Ber}(p)$ the Bernoulli law.

- **(2), p. 7.** "$\mathcal K_{\inf}(\nu_a,x)=\inf\big\{\mathrm{KL}(\nu_a,\nu_a'):\ \nu_a'\in\mathcal P[0,1]$ with $\nu_a\ll\nu_a'$ and
  $\mathrm E(\nu_a')>x\big\}$." (Strict inequality on the mean; "by convention, the infimum of the empty set
  equals $+\infty$".)
- **(7), p. 8.** The text: "Since we are considering distributions over $[0,1]$, the data-processing
  inequality for Kullback-Leibler divergences ensures (see, e.g., Garivier et al., 2019, Lemma 1) that for
  all $\nu\in\mathcal P[0,1]$ and all $\mu\in(\mathrm E(\nu),1)$,
  $\mathcal K_{\inf}(\nu,\mu)\geqslant\inf_{\nu':\mathrm E(\nu')>\mu}\mathrm{KL}\big(\mathrm{Ber}(\mathrm E(\nu)),\mathrm{Ber}(\mathrm E(\nu'))\big)=\mathrm{KL}\big(\mathrm{Ber}(\mathrm E(\nu)),\mathrm{Ber}(\mu)\big)$,
  [...] Therefore, by Pinsker's inequality for Bernoulli distributions,
  $\mathcal K_{\inf}(\nu,\mu)\geqslant2\big(\mathrm E(\nu)-\mu\big)^2$, thus $U_a^{\mathrm{KL}}(t)\leqslant U_a^{\mathrm M}(t)$ (7)
  for all arms $a$ and all rounds $t\geqslant K$."
- **Lemma 11 (regularity of $\mathcal K_{\inf}$), p. 21.** "For all $\nu\in\mathcal P[0,1]$ and all $\mu\in(0,1)$,
  $\forall\varepsilon\in[0,\mu]$, $\mathcal K_{\inf}(\nu,\mu)\leqslant\mathcal K_{\inf}(\nu,\mu-\varepsilon)+\frac{\varepsilon}{1-\mu}$, (19) and
  $\forall\varepsilon\in[0,\mu-\mathrm E(\nu)]$, $\mathcal K_{\inf}(\nu,\mu)\geqslant\mathcal K_{\inf}(\nu,\mu-\varepsilon)+2\varepsilon^2$. (20)"
  The text before it: (20) "relies on the same arguments as (7), namely, the data-processing inequality
  for Kullback-Leibler divergences and Pinsker's inequality".
- **Corollary 12, p. 21.** "For all $\nu\in\mathcal P[0,1]$, the function $\mathcal K_{\inf}(\nu,\cdot):\mu\in(0,1)\mapsto\mathcal K_{\inf}(\nu,\mu)$ is
  left-continuous. In particular, on the one hand, $\mathcal K_{\inf}(\nu,\mathrm E(\nu))=0$ whenever $\mathrm E(\nu)\in(0,1)$, and on
  the other hand, for all $\nu\in\mathcal P[0,1]$ and $\mu\in(0,1)$,
  $\mathcal K_{\inf}(\nu,\mu)=\inf\big\{\mathrm{KL}(\nu,\nu'):\ \nu'\in\mathcal P[0,1]$ and $\mathrm E(\nu')\geqslant\mu\big\}$."
- **Corollary 13, p. 21.** "For all $\nu\in\mathcal P[0,1]$, all $\mu\in(0,1)$, all $u>0$, and all $\varepsilon>0$,
  $\{\mathcal K_{\inf}(\nu,\mu-\varepsilon)>u\}\subseteq\{\mathcal K_{\inf}(\nu,\mu)>u+2\varepsilon^2\}$."
- **Numbering.** The JMLR PDF and the arXiv v3 PDF both number the regularity lemma Lemma 11 and title
  Appendix B.1 "Proof of the Regularity Lemma (Lemma 11)". `index.md` said until 2026-11-20 "(Lemma 13
  there)" for the ar5iv rendering: that number is not printed in either PDF.

## Techniques

- **Mixing with a Dirac mass to raise the mean (Appendix B.1, proof of (19), p. 40).** Given $\nu'$ with
  $\mathrm E(\nu')>\mu-\varepsilon$ and $\nu'\gg\nu$, pick $x>\mu$ "arbitrary close to 1" with $\delta_x\perp\nu'$, and set
  $\nu'_\alpha=(1-\alpha)\nu'+\alpha\delta_x$ with $\alpha=\frac{\varepsilon}{\varepsilon+(x-\mu)}\in(0,1)$; then $\mathrm E(\nu'_\alpha)>\mu$ and
  $\mathrm{KL}(\nu,\nu'_\alpha)=\mathrm{KL}(\nu,\nu')+\ln\frac1{1-\alpha}$ by (43); letting $x\to1$ gives
  $\mathcal K_{\inf}(\nu,\mu)\le\mathrm{KL}(\nu,\nu')+\ln\big(1+\frac{\varepsilon}{1-\mu}\big)\le\mathrm{KL}(\nu,\nu')+\frac\varepsilon{1-\mu}$. The section says
  the proof "is a variation on the proofs that can be found in Honda and Takemura (2015) or earlier
  references of the same authors."
- **Mixing with $\nu$ itself (proof of (20), p. 41).** $\nu'_\alpha=(1-\alpha)\nu'+\alpha\nu$ with
  $\alpha=\varepsilon/(\mathrm E(\nu')-\mathrm E(\nu))$, concavity of the logarithm, then data processing and Pinsker as in (7).
- **(7):** data processing (credited to Garivier et al. 2019, Lemma 1, that is GMS19) and Pinsker's
  inequality for Bernoulli laws.

## Where Incognita uses it

- `papers/P000-hy-unknown-imposed-grid/paper.tex`: KL-UCB as an optimal sequential index; properties
  of $\mathcal K_{\inf}$ ("classical"); deviation inequalities as variants of [GHMS22, Section 2.3]; the
  "Sources of the techniques" table cites Appendix B.1 (the mixing step).
- `papers/P006-batched-setting/paper.tex`, `papers/P008-transfer-lower-bound/paper.tex`: (7) for the chain
  $\mathcal K_{\inf}\ge\mathrm{kl}\ge2(\cdot)^2$ and Appendix B.1 for mixing with a Dirac mass.
  `papers/P007-stochastic-setting/paper.tex`: "see also the mixing step of" Appendix B.1.
  `papers/P001-minimax-constant/paper.tex`: KL-UCB-switch (no part cited).
- `Incognita/BatchedBandits/Deviations.lean`, `KInf/Deviations.lean`, `DualGrid.lean`: docstrings,
  `[GHMS22, Section 2.3]`.
