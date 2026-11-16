# Kol12: Parallel design of robust control in the stochastic environment (two-armed bandit)

| | |
|---|---|
| Work | A. V. Kolnogorov, *Parallel Design of Robust Control in the Stochastic Environment (the Two-Armed Bandit Problem)*, Automation and Remote Control 73(4), 2012, pp. 689–701 (Pleiades). Russian original: А. В. Колногоров, *Робастное параллельное управление в случайной среде (задаче о двуруком бандите)*, Автоматика и телемеханика, 2012, № 4, с. 114–130 (section "Robust and Adaptive Systems") |
| Identifiers | DOI 10.1134/S000511791204008X (Crossref: vol. 73, issue 4, pp. 689–701, print 2012-04, online 2012-04-15); Math-Net.ru at3793; received 24.11.2010; presented by A. V. Nazin; affiliation Yaroslav-the-Wise Novgorod State University |
| Read | **Russian original, parts**: Theorems 1–2, Lemma 5, the proof of Theorem 2 (first and last sentences), the sentences on the game-theory step, numerics, conclusion, reference list; from the PDF https://www.mathnet.ru/php/getFT.phtml?jrnid=at&paperid=3793&what=fullt&option_lang=rus fetched through https://r.jina.ai/. The fetch tool returned only quoted pieces (at most ~120 characters each) and paraphrases, not the raw text: quotations below are those pieces (text-extraction artefacts such as "66" for $\le$ normalised); the full statement of Theorem 1 and Lemmas 1–4 was not obtained verbatim. English abstract and metadata from https://www.mathnet.ru/php/archive.phtml?wshow=paper&jrnid=at&paperid=3793&option_lang=eng and https://api.crossref.org/works/10.1134/S000511791204008X. **Not accessed: the English translation** (Springer). English renderings of Russian quotes are my own |
| By, date | Claude Opus 5.5 (revise, P001), 2026-11-15 |

## Results

English abstract (Math-Net.ru, verbatim): "The problem of rational behavior in the stochastic environment, also
known as the two armed bandit problem, is considered in the robust (minimax) setting. A parallel
strategy is proposed leading to control, which is arbitrary close to the optimal one for environments
with gains having gaussian cumulative distribution functions with unit variance. The invariant recursive
equation is obtained for computing the minimax strategy and risk, which are to be found as Bayesian ones
associated with the worst-case a priori distribution. As a result, the well-known Vogel's estimates of
the minimax risk can be improved. Numerical experiments show that the strategy is efficient in the
environments with non-gaussian distributions, e.g., the binary ones."

Setting: Gaussian two-armed bandit, unit variances; «Θ = {(m1, m2) : |m1 − m2| ≤ 2cN^{−1/2}}», $0<c<\infty$;
initial stage: the strategy «вначале применяет каждый вариант по M0 раз», $\varepsilon_0=M_0N^{-1}$; then a
Bayes threshold rule «применять первый вариант, если S > T(t1, t2), и второй, если S < T(t1, t2)», thresholds
computed numerically.

- **(1), §1: Vogel, quoted.** «Известна асимптотическая минимаксная теорема Фогеля [7], гласящая, что при
  N → ∞ 0,530 ≤ (DN)^{−1/2}R^M_N(Θ) ≤ 0,752, (1)» ("Vogel's asymptotic minimax theorem [7] is known, stating
  that as $N\to\infty$ ..."), $D=0.25$. (The lower constant printed is 0.530, not Bather's 0.612.)
- **Minimax = Bayes: taken from earlier work, not proved here.** «Используем результаты [8, 9], где
  установлена применимость основной теоремы теории игр, согласно которой минимаксный риск совпадает с
  байесовским на наихудшем априорном распределении.» ("We use the results of [8, 9], where the
  applicability of the main theorem of game theory was established, according to which the minimax risk
  coincides with the Bayes risk on the worst prior.") [8] = Kolnogorov, АиТ 2011 № 5 (ARC 72(5) 1017–1027);
  [9] = Kolnogorov, IFAC ALCOSP 2010. Also: «В [8, 9] установлено, что наихудшее априорное распределение
  является симметрическим»; the asymptotically worst prior «может быть выбрана в виде» $\nu_a(u,v)=\kappa_a(u)\rho(v)$.
- **Theorem 1, proved in the Appendix** («Доказательство теоремы 1 приведено в Приложении»; relies on
  «[8, теорема 4]»). Opening: «Пусть νa(u, v) = κa(u)ρ(v), где κa(u) ...»: the invariant recursion (3)–(4)
  for the normalised Bayes risk and the formula (5)–(6) for the limit of the Bayes risk as $a\to\infty$
  (paraphrase; statement not obtained verbatim).
- **Lemmas 1–4, proved in the Appendix** (paraphrase): Lipschitz in $t_1,t_2$ for $t_\ell>\varepsilon_0$
  uniformly in $\varepsilon$ (L1); Lipschitz in $S$ (L2); equicontinuity in the density $\rho$ (L3, using
  «[8, лемма 2]»); approximation by piecewise-constant $\rho^*$ with error $\le c\Delta w$ (L4).
- **Lemma 5, proved in the Appendix.** «При всех S и всех t1, t2, для которых определены решения уравнений
  (3), (4), существуют пределы» $r(S,t_1,t_2)=\lim_{\varepsilon\to+0}r_\varepsilon(S,t_1,t_2)$ (and for
  $r^{(\ell)}$), «причем r(S, t1, t2) удовлетворяют условиям Липшица с константами, указанными в (13), (14).
  Это позволяет доопределить r(S, t1, t2) по непрерывности на все допустимые S, t1, t2.» The limits
  $\hat r(\varrho,\varepsilon_0)$, $r(\varrho,\varepsilon_0)$ exist and are given by (18).
- **Theorem 2 (two-sided bound, not a limit).** Verbatim: «Для минимаксного риска в области
  Θ = {|m1 − m2| ≤ 2cN^{−1/2}} при N → ∞ справедлива асимптотическая оценка
  sup_ϱ r̂(ϱ, ε0) ≤ N^{−1/2}R^M_N(Θ) ≤ sup_ϱ r(ϱ, ε0), (19) где r̂(ϱ, ε0) и r(ϱ, ε0) определены в (18).»
  ((18): $\hat r$ is an integral of $r(s,\varepsilon_0,\varepsilon_0)$ over $s$; $r(\varrho,\varepsilon_0)=4\varepsilon_0c\int w\varrho(w)dw+\hat r$,
  as paraphrased by the fetch tool.) Proof begins: «Так как минимаксный риск совпадает с байесовским на
  наихудшем априорном распределении (в том числе при сделанных ограничениях на класс стратегий), то из
  (5), (6) следует, что при ε = 1/N, обеспечивающем оптимальное управление при t > 2ε0, справедливы
  неравенства sup_ϱ r̂_ε(ϱ, ε0) ≤ N^{−1/2}R^M_N(Θ) ≤ sup_ϱ r_ε(ϱ, ε0), (20) причем оценка снизу обусловлена
  неполным временем управления (только при t > 2ε0), а оценка сверху – тем, что на начальном этапе
  управление неоптимально.» Ends: «Переходя в (20) к пределу при N → ∞ и используя (21), получаем (19).»
  So the minimax = Bayes step is assumed (from [8, 9]), and no limit is claimed: «улучшить оценку (1) снизу
  не удается, так как не ясно, насколько близки r̂(ϱ, ε0) и r̂_ε(ϱ, ε0).»
- **Numerics.** With «ε = ε0 = 0,02» the maxima are «приблизительно равными 0,65 и 0,59 при d = 1,6 и
  d = 1,4 соответственно»; «значение 0,59 может служить оценкой снизу»; bound (22) «N^{−1/2}R^M_N(Θ) ≤ 0,65»
  (printed range «|m1 − m2| ≤ 32 N^{−1/2}», probably 3.2 with a lost comma).
- **Conclusion.** «Установлено существование предела решения инвариантного рекуррентного уравнения»;
  «Стратегия имеет пороговый характер, определяется численными методами и легко табулируется. Но ее
  применение оправдано только к таким агрегированным данным, которые имеют близкие математические
  ожидания.» The split of data on the initial stage is heuristic («одна эвристическая процедура для такого
  разделения предложена выше»).

Not found in the parts returned: «без доказательства», «строг», «нестрог».

## Techniques

Worst-case prior via the game-theory minimax theorem (applicability credited to [8, 9], Kolnogorov 2011
and 2010); asymptotically uniform-in-mean prior $\kappa_a(u)\rho(v)$; invariant recursion in normalised
variables; existence of the $\varepsilon\to0$ limit by Lipschitz/equicontinuity estimates (Lemmas 1–5);
initial stage of $2M_0$ alternating pulls whose suboptimality gives the gap between the two bounds in
(19); numerical thresholds; Monte Carlo check on Bernoulli (aggregated) data.

## Where Incognita uses it

papers/P001-minimax-constant/: Attribution (defect SC2.1; Kol16's reference [14]).
