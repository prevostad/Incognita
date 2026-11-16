# Adu25: Risk and optimal policies in bandit experiments

| | |
|---|---|
| Work | K. Adusumilli, *Risk and Optimal Policies in Bandit Experiments*, Econometrica 93(3), May 2025, pp. 1003–1029 |
| Identifiers | DOI 10.3982/ECTA21075, arXiv 2112.06363 (v1 13 Dec 2021, ..., v16 3 May 2025) |
| Read | arXiv v16 (HTML rendering https://arxiv.org/html/2112.06363v16): table of contents; §2.2.3 (definitions of $s$, $\mu(s)$, $\mu^+(s)$, $L$, PDE (2.8)); §2.4 in full; opening of §3; §3.3 in full (recursion (3.2)–(3.3), Theorems 3 and 4); opening of §5 and Assumption 1, Theorem 5; §5.4 in full; §6: setting, (6.1), (6.2) and the two sentences after it, Theorem 6 (in summary only); §7 in full. arXiv v1 (PDF dated "This version: December 14, 2021", read as extracted text through https://r.jina.ai/https://arxiv.org/pdf/2112.06363v1): table of contents; §2.3 "Minimax risk" in full; the sentence of §4.5 about the minimax theorem, (4.12). Metadata: Crossref record of 10.3982/ecta21075 and the Econometric Society page https://www.econometricsociety.org/doi/10.3982/ECTA21075. Not read: proofs, appendices, §4 (numerics), §5.1–5.3 beyond the sentences quoted, the Econometrica typeset version itself (its equation numbers may differ from v16) |
| By, date | Claude Opus 5.5 (revise, P001), 2026-11-15 |

**How the text was obtained.** The pages were read through a fetch tool that returns quotations of at
most about 125 characters; long sentences were therefore collected in consecutive pieces and joined
here, and displayed formulas are the LaTeX of the HTML rendering (for v1, a PDF text extraction, whose
LaTeX was reconstructed). Statements marked "verbatim" were joined from such pieces; statements marked
"summary" are not quotations. Before freezing a cited node, compare with the PDF.

## Setting (v16)

- Rewards of arm $k$ are normal with local means: "Suppose each time an arm k is pulled, a reward,
  Y(k), is drawn from the normal distribution" with mean "$\mu_{k,n}:=\mu_k/\sqrt n$"; the loss is the
  cumulative regret payoff, rescaled by $n^{-1/2}$ (summary). $\sigma$ is the reward standard deviation.
- §2.2.3 (one-armed bandit): state $s\equiv\{x(t):=x_1(t),q(t):=q_1(t),t\}$;
  $\mu^+(s):=\mathbb E_{\mu|s}[\max\{\mu,0\}]$, $\mu(s):=\mathbb E_{\mu|s}[\mu]$;
  $L[f]:=\partial_q f+\mu(s)\partial_x f+\tfrac12\sigma^2\partial_x^2 f$; PDE (2.8):
  $\partial_t V^*+\mu^+(s)+\min\{-\mu(s)+L[V^*](s),0\}=0$ if $t<1$, $V^*(s)=0$ if $t=1$ (as rendered,
  simplified notation).
- §3, first sentences (verbatim): "For simplicity, the results in this section are stated for the
  one-armed bandit problem. However, all our results extend to the general MAB problem with
  straightforward adjustments to the proofs" (the sentence continues; not read further).
- §5, verbatim: "We now relax the Gaussian assumption, and suppose that rewards are distributed according
  to some parametric model $P_\theta$, with $\theta$ unknown." and "For the rest of this section, we
  focus on the one-armed bandit for simplicity."

## Results

- **(2.9) and (2.10), §2.4 (v16), verbatim.** "Following Wald (1945), we define minimax risk as the
  value of a two player zero-sum game played between nature and the DM. Nature's action consists of
  choosing a prior, $m_0\in\mathcal P$, over $\bm\mu$, while the DM chooses the policy rule $\pi$. The
  minimax risk $\bar V^*$ is defined as
  $\bar V^*=\sup_{m_0\in\mathcal P}V^*(0;m_0)=\sup_{m_0\in\mathcal P}\inf_{\pi\in\Pi}V_\pi(0;m_0)$ (2.9)
  where $V_\pi(0;m_0)$ and $V^*(0;m_0)$ denote the ex-ante Bayes risk under a policy $\pi$, and the
  minimal Bayes risk, when the prior is $m_0$. The equilibrium action of nature is termed the
  least-favorable prior, and that of the DM, the minimax policy. Under a minimax theorem, which holds if
  there is a Nash equilibrium to the game (with proper priors), the sup and inf operations in (2.9) can
  be interchanged, so that
  $\sup_{m_0\in\mathcal P}\inf_{\pi\in\Pi}V_\pi(0;m_0)=\inf_{\pi\in\Pi}\sup_{m_0\in\mathcal P}V_\pi(0;m_0)=\inf_{\pi\in\Pi}\sup_{\bm\mu}V_\pi(0;\bm\mu)$ (2.10)."
  (Equation labels (2.9), (2.10) inferred from the cross-references "in (2.9)" and "by (2.10)".)
- **§2.4 (v16), one-armed constant, verbatim.** "For one-armed bandits, we conjecture, and verify
  numerically by solving the two player game, that the least favorable prior, $m_0^*$, involves only
  two support points at $\{\underline\mu,\bar\mu\}$, with $\underline\mu<0$ and $\bar\mu>0$." ...
  "Indeed, for $\sigma=1$, it turns out $m_0^*$ has a two point support at $\underline\mu\approx-2.5$
  and $\bar\mu\approx1.7$ with $m_0^*(\bar\mu)\approx0.415$." ... "Based on the above analysis, we find
  that the sharp lower bound on the (unscaled) minimax risk of any one-armed bandit algorithm is given
  by $0.373\sigma\sqrt n$. By contrast, existing theoretical results only demonstrate a $\sigma\sqrt n$
  rate. Computing the least favorable prior when there are more than two arms is a lot more demanding.
  We conjecture, however, that it has a discrete support."
- **Theorem 3, §3.3 (v16), verbatim** (one-armed bandit, Gaussian rewards, by the opening of §3; the
  text credits Jakobsen et al. (2019), Theorem 2.1). Setting: "Let $\Delta t$ denote a small time
  increment, and $\mathcal T_{\Delta t}:=\{t_1,\dots,t_L\}$ a set of grid points for time, where
  $t_1=0$, $t_L=1$ and $t_l-t_{l-1}=\Delta t$ for all $l$. The optimal piece-wise constant policy,
  $\pi^*_{\Delta t}:\mathcal X\times\mathcal Q\times\mathcal T_{\Delta t}\mapsto\{0,1\}$, is allowed to
  change only at the time points on the grid $\mathcal T_{\Delta t}$." ... "Define
  $V^*_{\Delta t,l}(x,q)$ as the Bayes risk, in the diffusion regime, at state $(x,q,t_{L-l})$ under
  $\pi^*_{\Delta t}(\cdot)$." It satisfies the recursion (3.2)
  $V^*_{\Delta t,l+1}(x,q)=\min\{S_{\Delta t}[V^*_{\Delta t,l}](x,q),\,V^*_{\Delta t,l}(x,q)+\Delta t\cdot\mu^+(x,q)\}$,
  $V^*_{\Delta t,0}=0$, with $S_{\Delta t}$ the solution operator of (3.3).
  **Theorem 3:** "Suppose $\mu^+(\cdot),\mu(\cdot)$ are Lipschitz continuous. Then, there exists
  $C<\infty$ that depends only on the Lipschitz constants of $\mu^+(\cdot),\mu(\cdot)$ such that
  $0\le\max_l\{V^*_{\Delta t,l}(\cdot)-V^*(\cdot,t_{L-l})\}\le C(\Delta t)^{1/4}$ uniformly over
  $\mathcal X\times\mathcal Q$." Section 3.3 states (verbatim) that "a bandit experiment with such a
  policy is equivalent to a batched bandit experiment, where the data is forced to be considered in
  batches. The results in this section thus give an upper bound on the welfare loss due to batching."
- **Theorem 4, §3.3 (v16), verbatim.** "Suppose $\mu^+(\cdot),\mu(\cdot)$ are Lipschitz continuous and
  $\sup_s\mu^+(s)<\infty$." Then
  $\lim_{n\to\infty}|V_{\pi^*_{\Delta t},n}(0)-V^*(0)|\le C(\Delta t)^{1/4}$ (the fixed-$n$ use of
  $\pi^*_{\Delta t}$, "one simply sets $t=\lfloor i/n\rfloor$, where $i$ is the current period", as printed).
- **Theorem 5, §5.2 (v16), summary.** Under Assumption 1 (DQM of $\{P_\theta\}$,
  $\mathbb E_{P_{\theta_0}}[\exp|\psi(Y)|]<\infty$, $\sqrt n\mu_n(h)=\dot\mu_0h+\delta_n|h|^2$, prior
  support "a compact set $\{h:|h|\le\Gamma\}$ for some $\Gamma<\infty$", Hölder $\mu,\mu^+$): (ii)
  $\lim_n V_n^*(0)=V^*(0)$, with $V^*$ solving the PDE; (iii) a rate under Lipschitz $\mu,\mu^+$ (not read in full).
- **(5.8), §5.4 (v16), verbatim; parametric, one-armed bandit (by §5).** "Let $V_{n,\pi}(0,h)$ denote
  the fixed-$n$ frequentist risk of policy $\pi$ when the local parameter is $h$, and write $V^*(0)$ as
  $V^*(0,m_0)$ to make explicit its dependence on the prior $m_0$. In Appendix C, we use Theorem 5 to
  derive a lower bound on asymptotic minimax risk as
  $$\lim_{n\to\infty}\inf_{\pi\in\Pi}\sup_{|h|\le\Gamma}V_{n,\pi}(0;h)\ge\sup_{m_0\in\mathcal P}V^*(0;m_0)=\bar V^*,\qquad(5.8)$$
  where $\mathcal P$ is the set of all compactly supported distributions, and $\bar V^*$ is just the
  asymptotic minimax risk in the Gaussian setting as in (2.9). Proving the sharpness of the lower bound
  (5.8) is more involved, however, and left for future research."
- **(6.2), §6 (v16); nonparametric, one-armed bandit.** Setting (summary with short quotations): the
  reward distributions are in "the class of probability distributions with bounded variance and
  dominated by some measure"; around $P_0$ with $\mu(P_0)=0$ one takes "smooth one-dimensional
  parametric sub-models" $P_{t,\bm h}$ with score $\bm h$ in the tangent space $T(P_0)$, at
  $t=1/\sqrt n$; $\psi$ is the efficient influence function of the mean, (6.1); $V^*(0,m_0)$ denotes
  "the minimal Bayes risk in the one-armed bandit setting" under the prior $m_0$. Verbatim: "Suppose
  that $\mathbb E[\exp|Y|]<\infty$ and $\mathcal P$ is the set of all compactly supported $m_0$. Then,
  Theorem 6 implies
  $$\sup_{I\in\mathbb N}\lim_{n\to\infty}\inf_{\pi\in\Pi}\sup_{\bm h\in\mathcal H_I}V_{n,\pi}(0;\bm h)\ge\sup_{m_0\in\mathcal P}V^*(0,m_0)=\bar V^*,\qquad(6.2)$$"
  where $\sup_I$ "denotes the supremum over all finite" ($I$-dimensional) subspaces $\mathcal H_I$ "of
  the tangent space" (pieces as quoted). After (6.2): the left-hand side "is the value of minimax
  risk" (credited to van der Vaart 2000, Theorem 25.21) and "The right hand side of (6.2) is simply the
  lower bound on minimax risk under Gaussian rewards" (pieces verbatim, sentence ends not read).
- **Theorem 6, §6 (v16), summary only.** Under Assumption 2 (appendix): (i)
  $\lim_n V_n^*(0;\rho_0)=V^*(0;m_0)$; (ii) under Lipschitz $\mu,\mu^+$, the piecewise-constant policy
  attains $V^*(0;m_0)$ up to $O(\Delta t^{1/4})$.
- **§7, Conclusion (v16), verbatim.** "In this article, we derive sharp lower bounds for Bayes and
  minimax risk of bandit algorithms under diffusion asymptotics and suggest ways to numerically compute
  the corresponding optimal policies." ... "We show that all bandit problems, be they parametric or
  non-parametric, are asymptotically equivalent to Gaussian bandits. Furthermore, it is asymptotically
  sufficient to restrict attention to just two state variables per arm. For minimax risk, the paper
  only proves a lower bound. While we believe the bound is tight, further work is needed to show
  this." The rest of §7 ("Unknown σ.", "Other sequential experiments.") does not mention more than two
  arms; the phrases "left for future research" and "a lot more demanding" are not in §7 (they are in
  §5.4 and §2.4, quoted above).
- **v1, §2.3 "Minimax risk", verbatim** (v1 has §2.3 = Minimax risk; v16 has §2.3 = Comparison with
  existing methods and §2.4 = Minimax risk). After (2.8) $\bar V^*=\sup_{m_0\in\mathcal P}V^*_{m_0}(0)=\sup_{m_0\in\mathcal P}\inf_{\pi\in\Pi}V_{\pi,m_0}(0)$:
  "Under a minimax theorem, the sup and inf operations in (2.8) can be interchanged, so that
  $\sup_{m_0}\inf_\pi V_{\pi,m_0}(0)=\inf_\pi\sup_{m_0}V_{\pi,m_0}(0)=\inf_{\pi\in\Pi}\sup_\mu V_{\pi,\mu}(0)$.
  The last term, $\inf_{\pi\in\Pi}\sup_\mu V_{\pi,\mu}(0)$, is the more common definition of minimax
  risk, though whether the minimax theorem holds in the bandit context is an open question. In any
  event, the inequality $\inf_{\pi\in\Pi}\sup_\mu V_{\pi,\mu}(0)\ge\sup_{m_0\in\mathcal P}\inf_{\pi\in\Pi}V_{\pi,m_0}(0)$
  always holds, so $\bar V^*$ gives a lower bound on minimax risk even under this definition." (LaTeX
  of the displays reconstructed from PDF text.) v1 §4.5 gives the parametric bound as (4.12) (the later
  (5.8)), and says: "The first equality is immediate, but the second requires a minimax theorem."

## Techniques

Diffusion (local, $1/\sqrt n$) asymptotics of the bandit experiment; Bayes risk as the viscosity
solution of a second-order HJB PDE in the sufficient statistics $(x,q,t)$ per arm (§2.2, §3.1–3.2);
piecewise-constant policies through a semi-discrete scheme, error $(\Delta t)^{1/4}$ from Jakobsen et
al. (2019), Theorem 2.1 (§3.3); limits of experiments (LAN/DQM) to pass from Gaussian to parametric
(§5, Theorem 5) and nonparametric (§6, Theorem 6) rewards; minimax lower bound by "Bayes risk under any
prior lower-bounds the minimax risk" plus the Bayes-risk limit (Appendix C, not read); numerical
solution of the nature–DM game for the least-favourable prior (§2.4, §4).

## Where Incognita uses it

`papers/P001-minimax-constant/`: Main result (Context), Closest known, Attribution.
