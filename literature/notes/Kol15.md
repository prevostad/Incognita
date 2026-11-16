# Kol15: On a limiting description of robust parallel control in a random environment

| | |
|---|---|
| Work | A. V. Kolnogorov, *On a Limiting Description of Robust Parallel Control in a Random Environment*, Automation and Remote Control 76(7), 2015, pp. 1229–1241 (Pleiades). Russian original: А. В. Колногоров, *К предельному описанию робастного параллельного управления в случайной среде*, Автоматика и телемеханика, 2015, № 7, с. 111–126 (section "Stochastic Systems, Queuing Systems") |
| Identifiers | DOI 10.1134/S0005117915070085 (Crossref: vol. 76, issue 7, pp. 1229–1241, print 2015-07, online 2015-07-09); Math-Net.ru at14258; received 22.08.2012 («Поступила в редакцию 22.08.2012», printed in the article); presented by A. V. Nazin; affiliation Yaroslav-the-Wise Novgorod State University |
| Read | **Russian original, parts**: the list of Theorems 1–3 and Lemmas 1–3, П.1–П.3 with their status, the crediting sentence of Theorem 1, the game-theory sentences, the bounds of §5, the passages on rigour (§4), the conclusion (§6), the reference list; from the PDF https://www.mathnet.ru/php/getFT.phtml?jrnid=at&paperid=14258&what=fullt&option_lang=rus fetched through https://r.jina.ai/ (direct fetch timed out). The fetch tool returned only quoted pieces (at most ~120 characters) and paraphrases; no theorem was obtained verbatim in full. English abstract only summarised (Math-Net.ru page https://www.mathnet.ru/php/archive.phtml?wshow=paper&jrnid=at&paperid=14258&option_lang=eng); metadata from it and https://api.crossref.org/works/10.1134/S0005117915070085. **Not accessed: the English translation**. English renderings of Russian quotes are my own |
| By, date | Claude Opus 5.5 (revise, P001), 2026-11-15 |

## Results

Russian abstract, first sentence (verbatim): «Установлены пороговый характер и некоторые предельные свойства
оптимальной стратегии управления.» The rest (paraphrase): a limiting description of the earlier invariant
integro-difference equation by a second-order PDE; numerics show the solutions are close.

Setting: Gaussian two-armed bandit; «ΘN = {(m1, m2) : |m1 − m2| ≤ 2cN^{−1/2}; 0 < c < ∞}»; «сначала оба
варианта применяются по M0 = ε0N раз»; $M=\varepsilon N$. No Vogel threshold on the initial stage; the data
split is «одна эвристическая процедура» of [1].

- **Minimax = Bayes, assumed.** «Предметом исследования статьи является минимаксное (и, следовательно,
  робастное) управление, которое в силу основной теоремы теории игр ищется как байесовское, соответствующее
  наихудшему априорному распределению.» ("The subject is minimax (hence robust) control, which by the main
  theorem of game theory is sought as the Bayes control for the worst prior.") Same phrase in §2.
- **Theorem 1, from [2] = Kol14, not proved here.** «В [2] установлены следующие результаты, которые
  сформулируем в виде теоремы 1.» Content (paraphrase): normalised variables, recursion (1)–(2), Bayes risk
  formula (3); «Оптимальная стратегия при t ≤ 2ε0 (n ≤ 2ε0N) применяет варианты по очереди»; existence of
  limits «существуют пределы r(u, t1, t2) = lim» $_{\varepsilon\to0}r_\varepsilon$; «Эти пределы равномерно
  ограничены и удовлетворяют условиям Липшица по u при всех u, t1, t2.» Formula (3) is for the Bayes risk:
  «Байесовский риск, соответствующий асимптотически наихудшему распределению, вычисляется по формуле»
  $N^{-1/2}\lim_{a\to\infty}R^B_N(\nu_a(m,v))=2l(\varrho,\varepsilon_0)+\hat r_\varepsilon(\varrho,\varepsilon_0)$,
  with $2l(\varrho,\varepsilon_0)=4\varepsilon_0c\int_0^\infty w\varrho(w)dw$.
- **Theorem 2, proved in the Appendix** («Проводится по индукции»): for $\varepsilon>0$, $t_1+t_2\le1-\varepsilon$,
  $r^{(1)}_\varepsilon-r^{(2)}_\varepsilon=-\varepsilon F_\varepsilon$ with $F_\varepsilon$ increasing in $u$, tending to
  $\pm\infty$: the Bayes strategy is of threshold type (paraphrase). (Cited as [11, теорема 2] in [Kol20,
  Theorem 4].)
- **Theorem 3, proved in the Appendix:** in each region $D^\ell_\delta$, $\delta>0$, where one arm is used for
  all small $\varepsilon$, the limit function «является обобщенным решением дифференциального уравнения (14)»
  (paraphrase: a generalized solution of the second-order PDE).
- **Lemmas 1, 3** (symmetry $r_\varepsilon(u,t_1,t_2)=r_\varepsilon(-u,t_2,t_1)$), **Lemma 2** (bound on
  $F_\varepsilon$, threshold $|T_\varepsilon|=o(\delta_0)$), **П.1–П.3** (auxiliary): proved in the Appendix.
- **No limit of the minimax risk is stated; two-sided bounds, called preliminary.** §5: «в соответствии с
  [1] оценки снизу и сверху при малых ε0 можно дать в виде» $\sup_\varrho r(0,\varepsilon_0,\varepsilon_0)\le N^{-1/2}R_N(\Theta_N)\le\sup_\varrho\big(4\varepsilon_0c\int w\varrho(w)dw+r(0,\varepsilon_0,\varepsilon_0)\big)$;
  «Эти оценки, однако, являются предварительными из-за отсутствия результатов по сходимости решений»
  ("These bounds are, however, preliminary because of the lack of results on convergence of solutions").
  Numerically, for $\varepsilon_0=0.001$, $d\approx1.57$, the bounds are «приблизительно равны 0,634 и 0,637
  соответственно»; Bather's lower bound [5] «не меньше, чем 0,612» is quoted.
- **The PDE is reached non-rigorously.** §4: «Строгое описание предельного поведения функции r(u, t1, t2)
  оказалось трудной задачей, к решению которой сделаны пока только первые шаги. Начнем с нестрогих
  рассуждений.» ("A rigorous description of the limiting behaviour of r turned out to be a hard problem, on
  which only first steps have been made so far. We start with non-rigorous reasoning.") Then «Продолжая
  нестрогие рассуждения, заметим, что если считать возможным переход к пределу ...» and «Отметим, что для
  строгости приведенных рассуждений не хватало только результатов по сходимости производных» (of
  $r_\varepsilon$), hence the weak (generalized-solution) formulation of Theorem 3.
- **Conclusion (§6).** «Установлен пороговый характер стратегии и получены рекуррентные формулы для
  вычисления порогов. Осталось недоказанным существование предельных при ε ↓ 0 значений порогов, хотя
  соответствующее предположение кажется оправданным и подтверждается численными экспериментами. Тем не
  менее удалось установить существование областей, в которых определенные варианты применяются при любых
  достаточно малых ε > 0.» Also: «теоретическое обоснование этого факта пока отсутствует и может быть темой
  дальнейшего исследования.» (the exact antecedent of «этого факта» was not obtained).

«без доказательства» does not occur (per the fetch tool).

## Techniques

Game-theory minimax = Bayes (taken as given); results of [1] = Kol12 and [2] = Kol14 restated as Theorem 1;
threshold structure by induction (Theorem 2); symmetry lemmas; formal Taylor expansion to a second-order
HJB-type PDE, made into a generalized-solution statement on regions where one arm is used (Theorem 3);
finite differences (Samarskii). References: [1] Kol12, [2] Kol14 («принята к печати в АиТ»), [3]
Vladimirov, [4] Samarskii, [5] Bather 1983.

## Where Incognita uses it

papers/P001-minimax-constant/: Attribution (defect SC2.1; Kol16's reference [17]).
