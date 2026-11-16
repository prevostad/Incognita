# Kol20: Gaussian two-armed bandit: limiting description

| | |
|---|---|
| Work | A. V. Kolnogorov, *Gaussian Two-Armed Bandit: Limiting Description*, Problems of Information Transmission 56(3), 2020, pp. 278–301. Russian original: А. В. Колногоров, *Гауссовский двурукий бандит: предельное описание*, Проблемы передачи информации 56(3), 2020, с. 86–111 (section «Теория автоматов») |
| Identifiers | DOI 10.1134/S0032946020030059 (English; Crossref: Pleiades, vol. 56, issue 3, pp. 278–301, print 2020-07, online 2020-10-19); DOI 10.31857/S0555292320030055 (Russian, printed on p. 86); Math-Net.ru ppi2323; UDC 621.391.1 : 519.713 : 517.977.5; received 06.04.2020, revised and accepted 02.06.2020; RFBR grant 20-01-00062 |
| Read | **whole Russian original** (pp. 86–111), from the PDF of the full issue 56(3) at https://new.ras.ru/upload/iblock/234/8ea1p9t9by9bkh21r7qac30wrnhscgdj.pdf; English abstract from https://www.mathnet.ru/php/archive.phtml?wshow=paper&jrnid=ppi&paperid=2323&option_lang=eng (returned by the fetch tool in quoted pieces); metadata from Math-Net.ru and Crossref. **Not accessed: the English translation** (Springer, login). Quotations below are from the Russian; the English renderings are my own faithful translations, not the published translation, and the numbering is the Russian one (the translation should use the same, not checked) |
| By, date | Claude Opus 5.5 (revise, P001), 2026-11-15 |

## Results

Abstract (Russian, verbatim, p. 86): «Для гауссовского двурукого бандита, который возникает при анализе
пакетной обработки данных, изучается предельное поведение минимаксного риска, если горизонт управления
$N$ неограниченно растет. Минимаксный риск ищется как байесовский, вычисленный относительно наихудшего
априорного распределения. Показано, что наиболее высокие требования к управлению предъявляются в
области "близких" распределений, где математические ожидания доходов различаются на величину порядка
$N^{-1/2}$. В области "близких" распределений получены рекуррентное интегро-разностное уравнение для
нахождения байесовского риска относительно наихудшего априорного распределения в инвариантной форме с
горизонтом управления, равным единице, и дифференциальное уравнение в частных производных второго
порядка в предельном случае. Результаты позволяют оценить качество пакетной обработки. Например,
минимаксный риск, соответствующий пакетной обработке данных, разбитых на 50 пакетов, может быть лишь
на 2% выше своего предельного значения, если число пакетов неограниченно растет. В случае
бернуллиевского двурукого бандита показано, что оптимальная обработка данных по одному не является
более эффективной, чем пакетная, если $N$ неограниченно растет.» English abstract on Math-Net.ru begins
"For a Gaussian two-armed bandit, which arises when batch data processing is analyzed, the minimax risk
limiting behavior is investigated as the control horizon $N$ grows infinitely."

Setting (§1): Gaussian two-armed bandit with known variances $D_1,D_2$, unknown means,
$\Theta=\{|m_1-m_2|\le2C\}$, loss (1.1), minimax risk (1.2), Bayes risk (1.3).

**What is established, and how, in the paper's own words (Russian verbatim, then my translation):**

- §1, p. 87 (minimax = Bayes, taken from game theory): «Объединяет минимаксный и байесовский подходы
  основная теорема теории игр, согласно которой при широких предположениях выполнено равенство
  $R^M_N(\Theta)=\sup_\lambda R^B_N(\lambda)$, (1.4)» — "The minimax and Bayesian approaches are united by
  the main theorem of game theory, according to which, under broad assumptions, the equality (1.4)
  holds". No hypotheses are stated and no proof for this setting is given.
- §1, p. 87 (the claim): «В данной статье изучаются предельные свойства минимаксных стратегии и риска,
  если число обрабатываемых пакетов неограниченно растет. Установлено, что при $N\to\infty$ существует
  предел для нормированного минимаксного риска $N^{-1/2}R^M_N(\Theta)$, что позволяет оценить качество
  пакетной обработки.» — "This paper studies the limiting properties of the minimax strategy and risk as
  the number of processed batches grows without bound. It is established that as $N\to\infty$ there
  exists a limit of the normalized minimax risk $N^{-1/2}R^M_N(\Theta)$, which allows one to assess the
  quality of batch processing."
- §1, p. 88 (what is not proved): «В § 4 показано, что если количество обрабатываемых пакетов
  неограниченно растет, то существует непрерывный предел у решения этого уравнения, а само
  инвариантное рекуррентное уравнение переходит в дифференциальное уравнение в частных производных
  второго порядка. Строгое доказательство этого результата требует некоторых дополнительных оценок
  гладкости предельного решения, которые пока не получены. Но численные эксперименты, представленные в
  § 5, подтверждают близость решений рекуррентного и дифференциального уравнений.» — "In § 4 it is
  shown that if the number of batches grows without bound, the solution of this equation has a
  continuous limit, and the invariant recursive equation itself turns into a second-order partial
  differential equation. A rigorous proof of this result requires some additional smoothness estimates
  of the limiting solution, which have not yet been obtained. But the numerical experiments of § 5
  confirm that the solutions of the recursive and differential equations are close."
- §3, p. 94 (worst prior, from [1] = Kolnogorov, ППИ 54(1) 2018): «В [1] установлено, что асимптотически
  наихудшая априорная плотность распределения может быть выбрана в виде $\nu_a(m,v)=\varkappa_a(m)\rho(v)$
  (3.1)» — "It was established in [1] that asymptotically the worst prior density can be chosen of the
  form (3.1)", $\varkappa_a$ uniform on $|m|\le a$, $a\to\infty$.
- §4, p. 100 (the PDE): «Строгое обоснование этого вывода требует равномерных оценок производных
  $r_\varepsilon(u,t_1,t_2)$, поэтому ограничимся нестрогими рассуждениями, дополнив их результатами
  численного моделирования в § 5.» — "A rigorous justification of this derivation requires uniform
  estimates of the derivatives of $r_\varepsilon(u,t_1,t_2)$, so we restrict ourselves to non-rigorous
  reasoning, supplemented by the numerical results of § 5."
- §7, p. 110: «В силу основной теоремы теории игр это позволяет находить минимаксные стратегию и риск»
  — "By the main theorem of game theory this allows one to find the minimax strategy and risk".

No numbered theorem states the limit of the *minimax* risk: Theorem 6 gives the limit of the Bayes risk
for a fixed prior $\varrho$; passing to $\sup_\varrho$ and to the minimax risk rests on (1.4) and the
choice (3.1), not on a stated theorem.

**Numbered results** (one line each; "proved" = a proof is given in the paper):

- **Теорема 1 (§2, p. 88), proved.** «В области "близких" распределений порядок максимальных потерь не
  ниже $N^{1/2}$. Если же известно, что $|m_1-m_2|\ge\delta>0$, то порядок максимальных потерь не
  превосходит $\ln(N)$.» ("In the domain of close distributions the order of the maximal losses is not
  below $N^{1/2}$. If $|m_1-m_2|\ge\delta>0$ is known, the order of the maximal losses does not exceed
  $\ln N$.") In the proof (two-point class, Neyman–Pearson rule) the bracket $2x\int_0^1\Phi(-xt^{1/2})dt$
  has maximum «приблизительно равно 0,53» at $x\approx1.22$, in units $(\tilde DN)^{1/2}$,
  $\tilde D^{1/2}=0.5(D_1^{1/2}+D_2^{1/2})$.
- **Леммы 1–3 (§2), proved.** Threshold-crossing probability bounds; Lemma 1 «использует идею,
  предложенную в [5]» (Vogel).
- **Теорема 2 (§2, p. 93), proved.** Estimates (2.13)–(2.15) for the strategy $\sigma^*$ (threshold on an
  initial stage $n_0=\varepsilon_0N$, then $\sigma$). **Следствие 1**: for every $\varepsilon>0$,
  $\limsup_N(DN)^{-1/2}|R^M_N(\Theta_{cN^{-1/2}})-R^M_N(\Theta_C)|\le\varepsilon$ for suitable parameters,
  so the analysis may be restricted to close distributions.
- **Теорема 3 (§3, p. 95), proof by change of variables in [1].** For the prior (3.1), $a\to\infty$, Bayes
  strategy and risk from the invariant recursion (3.3)–(3.6). «Теорема доказывается путем выполнения
  замены переменных (3.2) в уравнениях (3.8)–(3.11) из [1].»
- **Теорема 4 (§3, p. 96), proof by reference.** $\Delta r_\varepsilon=r^{(1)}_\varepsilon-r^{(2)}_\varepsilon$
  is decreasing in $u$, hence the Bayes strategy is of threshold type. «В случае $D_1=D_2=1$
  эквивалентная теорема доказана в [11] (см. [11, теорема 2]). Доказательство легко переносится на
  рассматриваемый случай.» ([11] = Kolnogorov, АиТ 2015, № 7, 111–126.)
- **Теорема 5 (§3, p. 96), proof by change of variables in [1].** Recursion (3.7)–(3.9) for the losses
  of a given strategy.
- **Леммы 4–8 (§4), proved.** Bounds (4.1)–(4.4) on $r_\varepsilon$ and $\partial_ur_\varepsilon$
  (Lemmas 4–6), the bound (4.8) in $t_1$ (Lemma 7), continuity in the variances (Lemma 8). **Следствие 2**:
  increments in $t_1$ of order $\delta^{1/2}$; «нетрудно установить, что ... ограничена величиной
  порядка $\delta$, однако соответствующая равномерная оценка пока не получена» ("one can easily show it
  is of order $\delta$, but the corresponding uniform estimate has not yet been obtained").
- **Теорема 6 (§4, p. 100), proved (short proof).** Verbatim: «При всех $u,t_1,t_2$, при которых
  определено решение уравнения (3.3)–(3.5), существует непрерывный предел
  $r(u,t_1,t_2)=\lim_{\varepsilon\to+0}r_\varepsilon(u,t_1,t_2)$, который можно доопределить по
  непрерывности на все допустимые $u,t_1,t_2$ ($t_1\ge\varepsilon_0$, $t_2\ge\varepsilon_0$, $t_1+t_2\le1$).
  Этот предел равномерно ограничен, имеет равномерно ограниченную производную по $u$ и равномерно
  непрерывен по $t_1,t_2$ с константами, указанными в (4.3), (4.4), (4.8) и (4.9) соответственно. При
  $\rho_N(v)=N^{-1/2}\varrho(w)$, $w=N^{1/2}v$ и $\varepsilon_0\to+0$ для байесовского риска (3.6)
  справедлива асимптотическая оценка
  $\lim_{N\to\infty}N^{-1/2}R^B_N(\rho_N(v))=\lim_{\varepsilon_0\to0}r(\varrho;0,\varepsilon_0,\varepsilon_0)$,
  (4.11) где в обозначении $r(\varrho;0,\varepsilon_0,\varepsilon_0)$ явно указана зависимость от
  $\varrho(w)$.» (The signs $\ge,\le$ in the parenthesis were lost in text extraction and restored from
  context.) Translation: for all $u,t_1,t_2$ where the solution of (3.3)–(3.5) is defined, the continuous
  limit $r=\lim_{\varepsilon\to+0}r_\varepsilon$ exists, extends by continuity, is uniformly bounded, has
  a uniformly bounded $u$-derivative and is uniformly continuous in $t_1,t_2$; and (4.11) holds for the
  Bayes risk. Proof: $r_\varepsilon$ is nonnegative and nondecreasing in $\varepsilon$, hence has a limit;
  continuity by passing to the limit in (4.3), (4.4), (4.8), (4.9).
- **PDE (4.12)–(4.13), derived non-rigorously** (quote above):
  $\min_{\ell=1,2}\big(\frac{\partial r}{\partial t_\ell}+\frac{D_\ell t_{\bar\ell}^2}{2(t')^2}\frac{\partial^2r}{\partial u^2}+g^{(\ell)}(u,t_1,t_2)\big)=0$,
  $\bar\ell=3-\ell$, $r=0$ at $t_1+t_2=1$; finite-difference schemes (4.14), (4.15).
- **Теорема 7 (§6, p. 105), proved.** Recursion (6.7)–(6.11) for the Bayes risk of the Bernoulli
  two-armed bandit (one-by-one processing).
- **Теорема 8 (§6, p. 109), proved (computation).** If $\tilde r$ solves (6.16)–(6.17), then $r$ defined by
  $\tilde r(z,t_1,t_2)=r(z/t',t_1,t_2)f_{t_1^*t_2^*t'}(z)$ solves (4.12)–(4.13). The derivation of (6.16)
  itself from the Bernoulli recursion assumes smoothness («Предполагая, что $\tilde r(x_1,\cdot)$ является
  достаточно гладкой функцией») and so is formal; the conclusion (Bernoulli one-by-one no better than
  batch, §6, §7) inherits this.

**Numbers (§5, Рис. 3, p. 102–103)**, $D_1=D_2=1$, $\varrho$ two-point symmetric at $w=\pm d$:
batch, $\varepsilon=\varepsilon_0=0.02$ (50 batches), $\Delta u=0.005$, $|u|\le2.5$: «Максимум байесовского
риска $r_\varepsilon(d)$ приблизительно равен 0,652 при $d\approx1,6$»; limit from (4.14),
$\Delta t=2000^{-1}$, $\varepsilon_0=0.004$, $\Delta u=0.025$, $|u|\le2.5$: «Максимум байесовского риска
при $d\approx1,6$ приблизительно равен 0,637, т.е. меньше, чем для пакетной обработки, приблизительно на
2%.» Fig. 1–2 use $D_1=1$, $D_2=0.5$, $\varrho$ at $d_1=1.49$, $d_2=-1.53$ with weights 0.54, 0.46.
Vogel's constant appears only in a remark (§2, p. 92): the threshold strategy gives at most
$2e^{-1/2}(DN)^{1/2}\approx1.213(DN)^{1/2}$; «В [5, 6] дана более точная оценка множителя 0,752 (при
$D=0,25$)». Bather's 0.612 is not quoted in this paper; [13] Bather is cited for the choice of prior in
§6. Normalization: $N^{-1/2}\times$ risk with unit variances, i.e. $R/(\sigma\sqrt N)$; $d$ is the half-gap
in units of $N^{-1/2}$.

## Techniques

Worst-case prior (game theory, taken as given; prior form (3.1) from [1]); reduction to "close"
alternatives by an initial threshold stage (§2, Vogel's threshold idea, Lemma 1 credited to [5]);
invariant recursion in $(u,t_1,t_2)$ (§3); a priori bounds via Gaussian convolution of exponentials
(Lemmas 4–7); monotonicity of the Bayes risk in the batch size for the limit $\varepsilon\to0$
(Theorem 6); formal Taylor expansion to a second-order HJB equation (§4); Fokker–Planck computation of
absorption probabilities (Lemma 3); local CLT and a diffusion limit of the Bernoulli recursion with a
uniform-in-mean prior on a strip (§6, prior "близкая к данной" credited to Bather [13]).

## Where Incognita uses it

papers/P001-minimax-constant/: Main result (Context), Closest known, Attribution.
