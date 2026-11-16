# Kol14: Robust parallel control in a random environment and data processing optimization

| | |
|---|---|
| Work | A. V. Kolnogorov, *Robust Parallel Control in a Random Environment and Data Processing Optimization*, Automation and Remote Control 75(12), 2014, pp. 2124–2134 (Pleiades). Russian original: А. В. Колногоров, *Робастное параллельное управление в случайной среде и оптимизация обработки данных*, Автоматика и телемеханика, 2014, № 12, с. 42–55 (section «Робастные и адаптивные системы») |
| Identifiers | DOI 10.1134/S0005117914120042 (Crossref: vol. 75, issue 12, pp. 2124–2134, print 2014-12, online 2014-12-17); Math-Net.ru at14162; received 22.08.2012 (as given on the Math-Net.ru page); presented by A. V. Nazin; affiliation (Math-Net.ru) Yaroslav-the-Wise State University, Novgorod |
| Read | **Russian original, parts**: list of Theorems 1–3 and Lemmas 1–5 with their status, the full statement of Theorem 3, first and last sentences of its proof (Appendix), the game-theory sentence, setting, numerics, conclusion, reference list; from the PDF https://www.mathnet.ru/php/getFT.phtml?jrnid=at&paperid=14162&what=fullt&option_lang=rus fetched through https://r.jina.ai/. The fetch tool returned only quoted pieces (at most ~120 characters) and paraphrases, not the raw text; quotations below are those pieces (extraction artefacts like "66" for $\le$ normalised). Statements of Theorems 1–2 and Lemmas 1–5 not obtained verbatim. English abstract and metadata from https://www.mathnet.ru/php/archive.phtml?wshow=paper&jrnid=at&paperid=14162&option_lang=eng and https://api.crossref.org/works/10.1134/S0005117914120042. **Not accessed: the English translation**. English renderings of Russian quotes are my own |
| By, date | Claude Opus 5.5 (revise, P001), 2026-11-15 |

## Results

English abstract (Math-Net.ru, verbatim): "Consideration was given to the control of processing large amounts
of data, provided that there are two alternative methods of processing with different and a priori
unknown efficiencies. It was required to determine the most efficient method and maintain its
preferable use. With the use of parallel processing this may be carried out in a relatively small number
of steps and actually without losses in the control performance, that is, without increasing the
minimax risk. An invariant equation with a solution containing a singularity at $t=0$ was previously
obtained to describe the control. This solution was represented as a product with one cofactor being the
density of the normal distribution which is singular at $t=0$ and the other, the nonsingular one, the
solution to a new equation. Numerical experiments demonstrated that this new equation offers greater
possibilities for calculations. In particular, it enabled one to improve the asymptotic estimates of the
minimax risk."

Setting: Gaussian two-armed bandit, «f(x|mℓ) = (2π)^{−1/2} exp{−(x − mℓ)²/2}», $\theta=(m_1,m_2)$;
«ΘN = {θ : |m1 − m2| ≤ 2cN^{−1/2}}» «содержит среды с близкими математическими ожиданиями (константа c > 0
произвольна)». Initial stage: «сначала оба варианта применяются по M0 = ε0N раз»; «Оптимальная стратегия
при t1 + t2 ≤ 2ε0 применяет варианты по очереди». No threshold (Vogel-type) rule on the initial stage; the
closeness check on aggregated data is the heuristic of [1] («В [1] предложена эвристическая процедура»).

- **Minimax = Bayes, assumed (game theory).** «Объединяет минимаксный и байесовский подходы основная
  теорема теории игр, согласно которой при широких предположениях минимаксный риск совпадает с
  байесовским, вычисленным относительно наихудшего априорного распределения, соответствующего максимуму
  байесовского риска, а минимаксная стратегия совпадает с соответствующей байесовской.» ("The minimax and
  Bayes approaches are united by the main theorem of game theory, according to which, under broad
  assumptions, the minimax risk coincides with the Bayes risk computed for the worst prior ...") Next: «На
  этом свойстве основан алгоритм численного определения минимаксных стратегии и риска.» The worst prior:
  «асимптотически наихудшая плотность распределения может быть выбрана в виде» $\nu_a=\kappa_a\rho$ (§2).
- **Theorem 1, from [1] = Kol12, no proof here.** «В [1] установлены следующие результаты, которые
  сформулируем в виде теоремы.» Opening «Положим s = ZN^{−3/2} ...»: optimal strategy and recursion (1)
  (paraphrase).
- **Theorem 2, proved in the Appendix.** «Пусть rε(s, t1, t2) является решением ...»: the solution of
  (1), (2) factors as a normal density (singular at $t=0$) times a nonsingular function solving (5), (6)
  (paraphrase).
- **Lemmas 1–5, proved in the Appendix** («Доказательства теорем 2 и 3 и лемм 1–5 приведены в
  Приложении»), paraphrase: uniform bound vanishing as $u\to\pm\infty$ (L1); Lipschitz in $u$ (L2);
  Lipschitz in $\rho$ (L3); piecewise-constant approximation of $\rho$ with error $O(\Delta w)$ (L4);
  existence of a uniformly bounded limit of $r_\varepsilon$ as $\varepsilon\to0$ (L5, partly via «[1, лемма 5]»).
  «Отметим, что в лемме 5 ничего не говорится о существовании пределов r(ϱ; u, t1, t2) при t1 → 0 или при
  t2 → 0. Можно, однако, установить существование предела r(ϱ; 0, ε0, ε0) при ε0 → 0.»
- **Theorem 3 (the limit), proved in the Appendix, conditional on the game-theory step.** Verbatim: «Т е о
  р е м а 3. Для минимаксного риска в области ΘN = {|m1 − m2| ≤ 2cN^{−1/2}} справедлива асимптотическая
  оценка lim_{N→∞} N^{−1/2}R^M_N(ΘN) = sup_ϱ r(ϱ; 0, 0, 0), (12) где r(ϱ; 0, 0, 0) = lim_{ε0→0} r(ϱ; 0, ε0, ε0).»
  Proof (Appendix) begins «Рассмотрим (4). Покажем, что r̂ε(ϱ, ε0) = rε(ϱ; 0, ε0, ε0) + o(1), (П.8) где o(1) → 0
  равномерно при ε0 → 0.»; it uses «Так как минимаксный риск совпадает с байесовским на наихудшем
  априорном распределении» and the two-sided bound sup_ϱ r̂ε(ϱ, ε0) ≤ N^{−1/2}R^M_N(Θ) ≤ sup_ϱ (2l(ϱ, ε0) +
  r̂ε(ϱ, ε0)) (upper bound: the initial stage is non-optimal); ends «Так как ε = N^{−1}, то, переходя в (П.9)
  к пределу при N → ∞, а затем при ε0 → 0 и используя (П.10) и (П.11), получаем (12). Теорема 3 доказана.»
  So the limit (12) is proved *given* minimax = Bayes over the worst prior of the form $\kappa_a\rho$ on
  $\Theta_N$ (game theory and [1], not proved here). Whether the upper bound is uniform in $\theta$ or only
  Bayes-averaged was not determined from the pieces returned. This is the first place the formula of
  [Kol16, Theorem 3] and [Kol17, (21)] appears with a proof.
- **Numerics.** «байесовский риск при ε0 = 0,02 ... приблизительно равен 0,651», prior «сосредоточена в двух
  точках w = ±1,7 с вероятностями 0,5»; from [1], the largest losses at «|m1 − m2| ≈ 3,4N^{−1/2}». No value
  0.637 in this paper.
- **Conclusion.** «Установлено существование непрерывного равномерно ограниченного предела решения нового
  уравнения»; claims «точная асимптотическая при N → ∞ оценка минимаксного риска в произвольной области
  ΘN». Open directions: «описание предельного (при ε → 0) решения несингулярного уравнения» (possibly by
  PDEs), and the minimax risk on $|m_1-m_2|\le2C$ fixed in $N$.

Not found: «без доказательства», «строг», «нестрог».

## Techniques

Game-theory minimax = Bayes (taken as given); asymptotically uniform worst prior (from [1]); invariant
recursion; factorisation of the singular solution by a normal density (Theorem 2); Lipschitz and
equicontinuity estimates and piecewise-constant approximation of the prior (Lemmas 1–5); sandwich between
the Bayes risk with a truncated horizon and with a suboptimal initial alternating stage, then
$N\to\infty$, $\varepsilon_0\to0$ (proof of Theorem 3).

## Where Incognita uses it

papers/P001-minimax-constant/: Attribution (defect SC2.1; Kol16's reference [16]).
