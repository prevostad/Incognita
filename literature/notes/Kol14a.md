# Kol14a: Robust normal two-armed bandit and parallel data processing (MMAS '14)

| | |
|---|---|
| Work | Alexander V. Kolnogorov, *Robust Normal Two-Armed Bandit and Parallel Data Processing*, in: *Recent Advances in Mathematical Methods in Applied Sciences. Proceedings of the 2014 International Conference on Mathematical Models and Methods in Applied Sciences (MMAS '14) and Proceedings of the 2014 International Conference on Economics and Applied Statistics (EAS '14)*, Saint Petersburg State Polytechnic University, Saint Petersburg, Russia, September 23–25, 2014, Mathematics and Computers in Science and Engineering Series, Volume 32, pp. 32–40. Editors (front matter): Yuri B. Senichenkov, V. Korablev, Igor Chernorytski, N. Korovkin, S. Pozdnjkov, Klimis Ntalianis; associate editor Massimo Ceraolo. **Publisher not stated in the front matter as returned** (hosted on the INASE library, conference listed on europment.org; WSEAS/INASE/Europment family, unverified) |
| Identifiers | ISBN 978-1-61804-251-4; ISSN 2227-4588; no DOI found. Paper PDF https://www.inase.org/library/2014/russia/bypaper/MEAS/MEAS-02.pdf; front matter https://www.inase.org/library/2014/russia/bypaper/MEAS/MEAS-00.pdf; volume listing https://www.inase.org/library/2014/ |
| Read | **parts**, from MEAS-02.pdf fetched through https://r.jina.ai/ (running head "Recent Advances in Mathematical Methods in Applied Sciences", ISBN 978-1-61804-251-4, pp. 32–40): list of lemmas and theorems with their status, the game-theory sentences, setting, numerics, reference list. The fetch tool returned only short quoted pieces and paraphrases; no statement was obtained verbatim in full. Front matter (title, series, editors, ISBN, ISSN, TOC: p. 32) from MEAS-00.pdf the same way |
| By, date | Claude Opus 5.5 (revise, P001), 2026-11-15 |

## Results

Abstract: only fragments obtained ("Incomes are assumed to be normally distributed with unit variances";
"the control may be implemented in parallel almost without the lack of its quality"; "According to the
main theorem of the theory of games, we search minimax strategy and minimax risk ..."; "the worst prior
distribution is symmetric and asymptotically uniform one.").

Setting: Gaussian two-armed bandit, unit variances, $\Theta=\{|m_1-m_2|\le2c\}$; close set
$\Theta'=\{|m_1-m_2|\le2cN^{-1/2}\}$; initial stage of $2M_0$ alternating pulls, $\varepsilon_0=M_0/N$; then a
Bayes threshold rule (action 1 if $Z>T(n_1,n_2)$).

- **Vogel quoted.** $0.530\le(DN)^{-1/2}R^M_N(\Theta)\le0.752$ ($D=0.25$, Bernoulli), said to be "easily
  generalized" to the normal case with $D=1$.
- **Minimax = Bayes, assumed.** "Minimax and Bayesian approaches are related by the main theorem of the
  theory of games." "According the main theorem of theory o games under mild conditions the equality
  holds" (sic), $R^M=R^B(\Lambda_0)=\sup R^B$. No proof or hypotheses.
- **Lemma 1, proved:** the Bayes risk is a continuous concave function of the prior (paraphrase).
- **Lemma 2, not proved:** swapping the arms and a common shift of the means do not change the Bayes risk;
  "Let's discuss these properties without proof."
- **Lemma 3, not proved:** for $\nu_a$ as in (12), as $a\to\infty$ the Bayes risk splits into an initial-stage
  term plus an integral of risks; "The following lemma is given without proof."
- **Theorems 1–2, proved:** recursions for $R_{n_1,n_2}(Z)$ for the prior (12), $a\to\infty$, and the
  invariant unit-horizon form (Theorem 2 by change of variables). **Theorem 3, proved:** factorisation of
  the singular solution by a normal density (as in [Kol14, Theorem 2]).
- **No theorem gives the limit of $N^{-1/2}R^M_N$**, and the words "rigorous" and "heuristic" do not
  occur (per the fetch tool).
- **Numerics.** Table I: $N=15$: $d_N=5.5$, $\max r_N=0.77$; $N=30$: $1.7$, $0.66$; $N=50$: $1.7$, $0.65$;
  Bayes risk at $\varepsilon_0=0.02$ approximately 0.651. No 0.637.

## Techniques

Game-theory minimax = Bayes (taken as given); concavity of the Bayes risk in the prior and symmetry/shift
invariance to reduce to a symmetric, asymptotically uniform prior (Lemmas 1–2; Lemma 2 unproved);
invariant recursion; factorisation of the singularity. References include Kolnogorov ALCOSP 2010, ARC 72
(2011), ARC 73 (2012), "ARC (submitted)" (presumably Kol14), Robbins 1952, Fabius–van Zwet 1970, Vogel 1960.

## Where Incognita uses it

papers/P001-minimax-constant/: Attribution (defect SC2.1; Kol16's reference [15]).
