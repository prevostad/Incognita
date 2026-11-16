# Kol11: Finding minimax strategy and minimax risk in a random environment (two-armed bandit)

| | |
|---|---|
| Work | A. V. Kolnogorov, *Finding Minimax Strategy and Minimax Risk in a Random Environment (the Two-Armed Bandit Problem)*, Automation and Remote Control 72(5), 2011, pp. 1017–1027. Russian original: А. В. Колногоров, *Нахождение минимаксных стратегии и риска в случайной среде (задаче о двуруком бандите)* (title as printed in the PDF heading), Автоматика и телемеханика, 2011, № 5, с. 127–138 |
| Identifiers | DOI 10.1134/S0005117911050092 (as shown on Math-Net.ru); Math-Net.ru at1708; received 22.03.2010; presented by A. V. Nazin; affiliation (Math-Net.ru) Yaroslav-the-Wise State University, Novgorod |
| Read | **Russian original, parts**: section list, the statements of Theorem 1 (verbatim) and the openings of Theorems 2–4 and Lemmas 1–2, the definitions of strategy, loss, minimax and Bayes risk, the key sentences of the proof of Theorem 1 (Appendix), the numerics of §4, the first sentences of the conclusion, the reference list (briefly); from the PDF https://www.mathnet.ru/php/getFT.phtml?jrnid=at&paperid=1708&what=fullt&option_lang=rus fetched through https://r.jina.ai/ (a direct fetch of the PDF timed out). The fetch tool returned only quoted pieces (at most ~120 characters) and paraphrases, not the raw text; quotations below are those pieces (formulas as extracted, normalised). The full proof of Theorem 1, Theorems 2–4 in full and the proofs of Lemmas 1–2 were not obtained verbatim. English abstract and metadata from https://www.mathnet.ru/php/archive.phtml?wshow=paper&jrnid=at&paperid=1708&option_lang=eng. **Not accessed: the English translation**, nor Crossref. English renderings of Russian quotes are my own |
| By, date | Claude Opus 5.5 (revise, P001), 2026-11-16 |

## Results

English abstract (Math-Net.ru, verbatim, reassembled from pieces): "Minimax strategy and risk in a stationary
random environment are found as Bayesian ones corresponding to the worst prior distribution. For
environments with normally distributed incomes with unit variance and expectations that depend only on
the alternative selected, this distribution can be chosen to be symmetric and asymptotically uniform. This
lets one use numerical methods. The results can be used for systems with parallel data processing, in
particular, for controlling environments with distributions other than normal."

Sections: 1 Введение; 2 О связи минимаксного и байесовского подходов; 3 Свойства асимптотически наихудшего
априорного распределения; 4 Численная оптимизация и возможные применения; 5 Заключение; Приложение
(proofs of Theorems 1–4 and Lemmas 1–2).

Setting: two-armed bandit, horizon $N$, rewards normal with unit variance,
$f(x|m_\ell)=(2\pi)^{-1/2}\exp\{-(x-m_\ell)^2/2\}$, $\theta=(m_1,m_2)$; loss (regret)
«L_N(σ, θ) = E_{σ,θ}(Σ_n ((m1 ∨ m2) − ξ_n)) (1)». Parameter set (fixed, not $N$-dependent):
$\Theta=\{|m_1-m_2|\le 2c_1,\ |m_1+m_2|\le 2c_2\}$, «где 0 < c1 < ∞, 0 < c2 < ∞.» «Условие c2 < ∞ нужно для
того, чтобы Θ было компактным множеством, однако, предполагается, что c2 достаточно велико.» ("The
condition $c_2<\infty$ is needed for $\Theta$ to be compact; however, $c_2$ is assumed sufficiently large.")
Strategies: «стратегия σ, которая в момент времени n является измеримой функцией текущей предыстории
процесса, т.е. полученных откликов x^{n−1} = x1, ..., x_{n−1} на выбранные варианты y^{n−1} = y1, ..., y_{n−1}.
Множество стратегий обозначим через Σ.» $\sigma$ gives the probability of choosing each arm (behavioural,
randomised strategies; all such strategies, no batch or initial-stage restriction). Mixed strategies:
«распределений μ и Λ на множествах Σ и Θ». Definitions: «R^M_N(Θ) = inf_Σ sup_Θ L_N(σ, θ) (2) называется
минимаксным риском», «R^B_N(Λ) = inf_Σ ∫_Θ L_N(σ, θ)Λ(dθ) (4) называется байесовским риском».

- **Theorem 1 (minimax = Bayes, finite $N$, compact $\Theta$, all strategies).** §2: «Справедлив аналог
  основной теоремы теории игр.» Verbatim: «Т е о р е м а 1. Рассматриваемая игра имеет цену и минимаксные
  стратегии обоих игроков. Иными словами, существуют наихудшее априорное распределение Λ0 на Θ и минимаксная
  смешанная стратегия μ0 на Σ, такие что inf_{μ} sup_{Λ} L_N(μ, Λ) = L_N(μ0, Λ0) = sup_{Λ} inf_{μ} L_N(μ, Λ). (5)»
  ("Theorem 1. The game under consideration has a value and minimax strategies of both players. In other
  words, there exist a worst prior $\Lambda_0$ on $\Theta$ and a minimax mixed strategy $\mu_0$ on $\Sigma$ such
  that ... (5).") Then: «Множества {μ} и Σ совпадают, поэтому с учетом равенств ... т.е. минимаксные стратегия
  и риск совпадают с байесовскими на наихудшем априорном распределении.» ("The sets $\{\mu\}$ and $\Sigma$
  coincide, hence ... i.e. the minimax strategy and risk coincide with the Bayes ones for the worst prior.")
- **Proof of Theorem 1 (Appendix): compactness and continuity, citing Borovkov.** «Для доказательства
  равенства (5) достаточно установить, что в множествах Σ, Θ можно определить расстояния ρ_Σ, ρ_Θ, которые
  превращают их в компактные метрические пространства, а функция L_N(σ, θ) равномерно непрерывна по
  совокупности переменных σ, θ. Это следует, например, из свойств статистических игр общего вида [11, с. 129].»
  ([11] = А. А. Боровков, *Математическая статистика. Доп. главы*, М.: Наука, 1984.) The metric on $\Sigma$
  (as extracted): $\rho_\Sigma(\sigma^{(1)},\sigma^{(2)})=\sum_{y_1}|\pi^{(1)}(y_1)-\pi^{(2)}(y_1)|+\sum_{n=2}^N\sum_{y_n}\int_{\mathbb R^{n-1}}|\pi^{(1)}(y_n,x^{n-1})-\pi^{(2)}(y_n,x^{n-1})|\prod_{\nu<n}e^{-x_\nu^2/4}\,dx^{n-1}$,
  a weighted $L^1$ distance. Then: «Очевидно, полученное метрическое пространство ограничено. Полнота его
  устанавливается аналогично полноте пространства суммируемых функций (см., например, [12, с. 352]). Из
  ограниченности и полноты следует его компактность.» ("Obviously the metric space obtained is bounded. Its
  completeness is established as for the space of integrable functions ... Boundedness and completeness imply
  its compactness.") Mixed = behavioural: «Покажем, что множества Σ и {μ} совпадают. Достаточно проверить, что
  для любого 0 < α < 1 и любых стратегий σ(1), σ(2) ∈ Σ найдется стратегия σ ∈ Σ» (with the convex combination of
  losses; continuation not obtained verbatim). No mention of Wald, von Neumann, Ky Fan, Sion, Karlin, weak
  topology, or invariance in the proof (as reported by the fetch tool). *Remark (mine, not the paper's):* in an
  infinite-dimensional weighted-$L^1$ space, "bounded and complete" does not imply compact (total boundedness
  is needed), so the compactness step of the proof, as quoted, is not valid as written; the conclusion may
  still hold by another route (e.g. a weak topology on behavioural strategies).
- **Lemma 1 (invariance).** «Следующие преобразования λ̃ априорной плотности распределения λ не меняют
  байесовский риск, т.е.» (paraphrase: swapping $m_1,m_2$; shifting both means by a common constant).
- **Lemma 2.** «Байесовский риск является непрерывной вогнутой функцией априорного распределения, т.е.»
  (paraphrase: Lipschitz bound (9) in $L^1$ distance of priors, concavity (10)).
- **Theorem 2 (asymptotically worst prior).** «Не уменьшающая байесовский риск плотность распределения при
  a → ∞ может быть выбрана в виде ν(u, v) = κ_a(u)ρ(v), (11) где κ_a(u) – постоянная плотность на отрезке ∣u∣ ≤ a, а
  ρ(v) – симметрическая» ... (density on $|v|\le c_1$; $u,v$ presumably the half-sum/half-difference of means).
- **Theorem 3.** «Оптимальная стратегия на первых двух шагах применяет оба варианта по очереди, при этом
  lim_{a→∞} R^B_N(ν(u, v)) = 2L(ρ(v)) + ∫_{−∞}^{∞} R^B_{N−2}(μ(u, v∣x, z)) q(z)dz, (14)».
- **Theorem 4 (recursion).** «Пусть ν(u, v) выбрана из условия (11) и a → ∞. Тогда R_{n1,n2}(·) = min(...)»:
  recursive equations (15)–(16) for the Bayes risk, zero terminal values at $n_1+n_2=N$ (paraphrase).
- **No limit as $N\to\infty$.** The only limits are $a\to\infty$ ((14), (17)). §1 quotes Vogel [9]:
  «0,530 ≤ (DN)^{−1/2}R^M_N(Θ) ≤ 0,752» (3), $D=0.25$ (Bernoulli), said to carry over to the normal case with
  $D=1$ (paraphrase). Numerics (§4), $r_N(d)=N^{-1/2}R^B_N$: «Максимумы r_N(d) оказались приблизительно равными
  0,77, 0,66, 0,65 при d = 5,5; 1,7; 1,7 соответственно.» ($N=15,30,50$, paraphrase) «Первое значение не
  согласуется, так здесь максимум находится на границе в области монотонного роста r_N(d).»
- **Conclusion.** «Предложен метод отыскания минимаксных стратегии и риска, основанный на характеризации
  наихудшего априорного распределения ... и дальнейшей численной оптимизации.» «Полученная пороговая стратегия
  легко табулируется и допускает применение в системах с параллельной обработкой данных.»

## Techniques

Game-theoretic minimax theorem for the statistical game (strategies $\times$ priors), via claimed compact
metrisations of $\Sigma$ and $\Theta$ and uniform continuity of $L_N$, citing Borovkov 1984 [11, p. 129];
identification of mixed with behavioural strategies; invariance of the Bayes risk under arm swap and common
shift (Lemma 1); concavity and continuity of the Bayes risk in the prior (Lemma 2); asymptotically uniform
prior in the half-sum $\kappa_a(u)\rho(v)$, $a\to\infty$ (Theorem 2); recursion (Theorems 3–4); numerics.

## Where Incognita uses it

papers/P001-minimax-constant/: Attribution of the minimax = Bayes step (defect SC3.6; Kol12's reference
[8], credited there with establishing «применимость основной теоремы теории игр»).
