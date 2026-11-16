# Kol16: Contributions to the asymptotic minimax theorem for the two-armed bandit

| | |
|---|---|
| Work | A. V. Kolnogorov, *Contributions to the Asymptotic Minimax Theorem for the Two-Armed Bandit Problem*, International Journal of Mathematics and Computers in Simulation, Volume 10, 2016, pp. 129–132 (NAUN). **The year on the article and on the journal page is 2016, not 2015** (the year 2015 of the report of referee-scope on P001 is a slip); hence the key `Kol16` |
| Identifiers | E-ISSN 1998-0159; no DOI (none on the NAUN page or the PDF; no Crossref record found by bibliographic query); PDF http://www.naun.org/main/NAUN/mcs/2016/a362002-057.pdf; volume page https://www.naun.org/cms.action?id=12110 |
| Read | whole (the NAUN PDF, pp. 129–132; running head "INTERNATIONAL JOURNAL OF MATHEMATICS AND COMPUTERS IN SIMULATION Volume 10, 2016 ISSN: 1998-0159"); the volume page for title, author, pages |
| By, date | Claude Opus 5.5 (revise, P001), 2026-11-15 |

## Results

Abstract (verbatim): "The asymptotic minimax theorem for Bernoully two-armed bandit problem states that
the minimax risk has the order $N^{1/2}$ as $N\to\infty$, where $N$ is the control horizon, and provides
lower and upper estimates. It can be easily extended to normal two-armed bandit. For normal two-armed
bandit, we generalize the asymptotic minimax theorem as follows: the minimax risk is approximately equal
to $0.637N^{1/2}$ as $N\to\infty$."

- **Theorem 1, §I, p. 129: Vogel's theorem, quoted.** "the following asymptotic minimax theorem was
  proved by W. Vogel in [9]: Theorem 1: The following estimates hold as $N\to\infty$ for Bernoulli
  two-armed bandit: $0.612\le(DN)^{-1/2}R^M_N(\Theta)\le0.752$ (2) with $D=0.25$ being the maximal variance
  of one-step income. Presented here the lower estimate was obtained in [10]. The upper estimate was
  obtained in [9] for the following strategy." Threshold $\alpha(DN)^{1/2}$, "$\alpha\approx0.584$ and the
  maximal value of expected losses corresponds to $|m_1-m_2|\approx3.78(D/N)^{1/2}$." Remark 1: "The
  estimates (2) can be easily extended to considered normal two-armed bandit with a glance that $D=1$ in
  this case."
- **(3), §I, p. 130: the claimed estimate.** "The goal of the present paper is to improve the estimates
  (2) for the normal two-armed bandit. We propose the following estimate:
  $\lim_{N\to\infty}(DN)^{-1/2}R^M_N(\Theta)\approx0.637$. (3)"
- **§II: minimax = Bayes, assumed.** "According to this theorem [the main theorem of the theory of
  games] the minimax risk (1) is equal to the Bayesian risk (4) calculated over the worst prior
  distribution corresponding to the maximum of the Bayesian risk." "It was proved in [14], [15] that
  asymptotically the worst prior distribution density can be chosen the following $\nu_a(m,v)=\kappa_a(m)\rho(v)$ (5)".
- **Theorem 2, §II, p. 130: recursion, proof by reference.** "The following theorem, which was proved in
  [14], [15], holds." Invariant recursion (6)–(8) with initial stage $\varepsilon_0=M_0N^{-1}$.
- **Lemma 1 and Theorem 3, §III, p. 131: by reference, no proof.** "The following results were obtained
  in [15], [16], [17] for the set of close expectations $\Theta_N=\{|m_1-m_2|\le2cN^{-1/2}\}$." Lemma 1:
  existence of the limits $r(\varrho;u,t_1,t_2)=\lim_{\varepsilon\to0}r_\varepsilon(\varrho;u,t_1,t_2)$,
  uniformly bounded, Lipschitz in $u$ (same wording as [Kol17, Theorem 3], first half). "Theorem 3: The
  minimax risk on the set of close expectations $\Theta_N=\{|m_1-m_2|\le2cN^{-1/2}\}$ satisfies the
  estimate $\lim_{N\to\infty}N^{-1/2}R^M_N(\Theta_N)=\sup_\varrho r(\varrho;0,0,0)$, (9) where
  $r(\varrho;0,0,0)=\lim_{\varepsilon_0\to0}r(\varrho;0,\varepsilon_0,\varepsilon_0)$."
- **PDE (12)–(13), §III: formal.** "Let's assume that $r_\varepsilon(u,t_1,t_2)$ has continuous partial
  derivatives of proper orders and show that equations (7) may be reduced to the form (10)"; then "as
  $\varepsilon\downarrow0$ we obtain the differential equation" (12) with conditions (13) (same as
  [Kol17, (26)–(27)]).
- **Numerics, §III, p. 131.** "Calculations of $r(\varrho;u,t_1,t_2)$ according to formulas (14), (15)
  were implemented with $\Delta u=0.023$, $\Delta t=2000^{-1}$, $\varepsilon_0=0.001$ for $|u|\le2.3$. It was
  assumed that $\varrho(w)$ is degenerated distribution density concentrated at two points $w=\pm d$. For
  $0.5\le d\le2.5$ maximum of $2d\varepsilon_0+r(\varrho;0,\varepsilon_0,\varepsilon_0)$ was approximately
  equal to 0.637 at $d\approx1.57$."
- **§IV, p. 132: initial stage, numerical only.** A "modified Vogel's strategy" (threshold on the
  initial stage, then the Bayes strategy) to handle $|m_1-m_2|\le2C$; illustrated by Fig. 1, no proof.
  Conclusion: "A generalization to the asymptotic minimax theorem for normal two-armed bandit has been
  given."

Normalization: $(DN)^{-1/2}R^M_N$ with $D$ the one-step variance ($D=1$ in the Gaussian computation),
i.e. $R/(\sigma\sqrt N)$; $d$ is the half-gap in units of $N^{-1/2}$.

## Techniques

None new in this paper: it summarizes [14] Kolnogorov, Autom. Remote Control 73(4) (2012) 689–701;
[15] Kolnogorov, MMAS'14 proceedings (2014) 32–40; [16] Kolnogorov, Autom. Remote Control 75(12) (2014)
2124–2134; [17] Kolnogorov, *On a Limiting Description of Robust Parallel Control in a Random
Environment*, Autom. Remote Control 76(7) (2015) 1229–1241 (references as printed, not checked). The
2015 paper [17], not this one, is the source the limit statements are credited to.

## Where Incognita uses it

papers/P001-minimax-constant/: Main result (Context), Closest known, Attribution.
