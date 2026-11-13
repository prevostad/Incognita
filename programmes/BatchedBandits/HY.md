# The algorithm HY and the proof routes

Companion of [PROGRAMME.md](PROGRAMME.md), for agents who formalise or extend the owner's results
on batched bandits. Source: A. Prevost, *Batched bandits on an unknown imposed grid: the optimal
constant x²/K_inf for every x ≥ 1* (manuscript, 2026), whose statements are verified in the owner's
private Lean project. Everything here uses the conventions of the programme, and
$d_a := K_{\inf}(\nu_a, m^\star)$.

## Statements to reach

On every grid with $x_\ell \to x \in [1, \infty)$, every $\nu$ with rewards in $[0,1]$ and
$m^\star < 1$, every suboptimal arm $a$:

1. **Lower bound, "explore two batches ahead".** Every batched learner that is consistent at batch
   ends, even one that knows the grid, has
   - if $x = 1$: $\liminf_\ell \mathbb E N_a(t_\ell)/L_\ell \ge 1/d_a$ (this holds on every grid);
   - if $x > 1$: $\limsup_\ell \mathbb E N_a(t_\ell)/L_\ell \ge x^2/d_a$, and the same with
     $\liminf$ if $\mathbb E N_a(t_\ell) = O(L_\ell)$;
   - for the regret: $\liminf_\ell \mathrm{Reg}(t_\ell)/L_\ell \ge x^2 \sum_{c:\Delta_c>0} \Delta_c / K_{\inf}(\nu_c, m^\star)$
     when $x = 1$, or when $x > 1$ and every suboptimal count is $O(L_\ell)$.
2. **Upper bound.** HY with its default parameters (below) is a deterministic learner of $M_0$,
   consistent, with $\lim_\ell \mathbb E N_a(t_\ell)/L_\ell = x^2/d_a$ and the matching regret limit.
   Non-asymptotic forms: for $x = 1$,
   $\mathbb E N_a(t_L) \le L_L/d_a + (2/d_a + 4c^\star/d_a^2)\,\varepsilon L_L + R_1(\varepsilon)$
   for every $\varepsilon \in (0, \varepsilon_0]$ and every $L$, with $c^\star := (2-m^\star)/(1-m^\star)$;
   for $x > 1$, with a constant margin $\omega$,
   $\mathbb E N_a(t_\ell) \le (1+\omega)(1/d_a + 3c^\star\varepsilon/d_a^2)\,H_\ell + R_x(\varepsilon)$
   where $H_\ell := \max_{k \le \ell} y_{k-1} L_k$ and $H_\ell/L_\ell \to x^2$. The remainders do
   not depend on $L$ or $\ell$ and are astronomically large.
3. **All rounds.** HY also has $\lim_t \mathbb E N_a(t)/\log t = x^2/d_a$ over all rounds.

## The algorithm HY$(w_0, \beta, \omega, \vartheta, \gamma)$

Parameters: pseudo-count $w_0 \ge 0$, net exponent $\beta \ge 2$, non-increasing margins
$\omega_\ell \in (0,1]$, activation exponents $\vartheta_\ell \in (0,1]$, consistency margins
$\gamma_\ell \in (0, 1/2]$, all functions of $t_1, \dots, t_\ell$.
Defaults: $w_0 := 1$, $\beta := 2$, $\omega_\ell := 2^{-k_\ell}$ with
$k_\ell := \lfloor \frac14 \log_2 \max(L_\ell, 1) \rfloor$, $\vartheta_\ell := 1/\log\log t_\ell$
if $t_\ell \ge e^e$ and $1$ otherwise, $\gamma_\ell := \min(1/2, \max(L_\ell,1)^{-1/4})$.

Batch 1 pulls the arms in turn. At each batch end $t_\ell$, with $N_c := N_c(t_\ell)$:

- $y_\ell := x_\ell^2$, $U_{\ell+1} := \lceil L_\ell^\beta \rceil$ ($U_1 := 1$, $y_0 := 1$),
  $s_\ell := \lfloor t_\ell^{1+\vartheta_\ell} \rfloor$.
- **Pseudo-observation.** $\tilde\nu_c := (N_c \hat\nu_c + w_0 \delta_0)/(N_c + w_0)$, with mean
  $\tilde m_c$.
- **Leader and IMED divergences.** $\hat c_\ell \in \arg\max_c \tilde m_c$ (fixed tie rule),
  $\tilde K_\ell(c) := K_{\inf}(\tilde\nu_c, \tilde m_{\hat c_\ell})$.
- **Test divergences.** Well-sampled arms $W_\ell := \{c : N_c \ge U_\ell/2\}$; reference
  $r_\ell \in \arg\max_{c \in W_\ell} \tilde m_c$ ($\hat c_\ell$ if $W_\ell = \emptyset$); test level
  $\hat\mu_\ell := \tilde m_{r_\ell}$; $\hat K_\ell(c) := K_{\inf}(\tilde\nu_c, \hat\mu_\ell)$.

In batch $\ell+1$, at round $t$ (the learner knows $t$, not $t_{\ell+1}$):

- **IMED phase, $t \le s_\ell$.** Pull a minimiser of
  $N_c(t-1)\tilde K_\ell(c) + y_\ell \log N_c(t-1)$, the leader if it is one.
- **Paced phase, $t > s_\ell$**, using only data up to $t_\ell$:
  - consistency threshold: $\hat\Lambda_1 := L_1$; for $\ell \ge 2$, with
    $Q_\ell := \{c \notin W_\ell : c \ne \hat c_{\ell-1}\}$,
    $\hat\Lambda_\ell := \min\big(L_\ell, \min_{c \in Q_\ell}[N_c \hat K_{\ell-1}(c)/y_{\ell-1} + \log N_c]\big)$,
    and $h_\ell := (1-\gamma_\ell)\, y_{\ell-1} \hat\Lambda_\ell$;
  - verdicts: $c \ne \hat c_\ell$ is *rejected* if $\hat K_\ell(c) > 0$ and $N_c \hat K_\ell(c) \ge h_\ell$,
    *ambiguous* otherwise;
  - paced targets: $n_{\ell,c}(t) := K - 1 + U_{\ell+1}$ if ambiguous, and
    $K - 1 + \min(U_{\ell+1}, \lceil (1+\omega_\ell) y_\ell \log t / \hat K_\ell(c) \rceil)$ if rejected;
  - rule: pull the first $c \ne \hat c_\ell$ (fixed order) with $N_c(t-1) < n_{\ell,c}(t)$, else the
    leader.

Each test costs $K$ evaluations of $K_{\inf}$ (one-dimensional concave maximisations); each round
$O(K)$ operations. $K_{\inf}$ is used through its dual form
$K_{\inf}(G,\mu) = \sup_{\lambda \in [0, 1/(1-\mu))} \mathbb E_G \log(1 - \lambda(X-\mu))$
(Honda–Takemura 2010).

## Proof routes

**Lower bound.** For $x = 1$, the classical change of measure (Lai–Robbins; Garivier–Ménard–Stoltz
2019, fundamental inequality) applied to the observations available at the end of batch
$\ell + 1$: they contain the actions of batch $\ell+1$ but only the rewards of batches $\le \ell$, so
$N_a(t_\ell)$ must pay for the horizon $t_{\ell+1}$. For $x > 1$, a sharper change of measure tilts
only the rewards of $a$ in batch $\ell$ towards a distribution $G$ of mean exactly $m^\star$ with
$\mathrm{KL}(\nu_a, G) \approx d_a$ ("boundary tilt"). The instances where $\nu_a$ is replaced by
$(1-s)G + s\delta_0$ (barely suboptimal) or $(1-s)G + s\delta_1$ (barely optimal) explain these
histories equally well; giving or not giving the bulk of batch $\ell+1$ to $a$ is a polynomial loss
under one of them, so consistency forces $N_a(t_{\ell-1}) d_a \gtrsim L_{\ell+1}$, that is
$N_a(t_\ell) \gtrsim L_{\ell+2}/d_a \approx x^2 L_\ell/d_a$. The mechanism is Lorden's (1983,
proof of Theorem 3). Logarithmic counts are used for the tightness of the number of pulls of $a$
in batch $\ell$, which is decided at $t_{\ell-1}$.

**Upper bound, $x > 1$.** Decompose $N_a(t)$ over batches. (i) Structure: a queue lemma shows every
demand is served after an initial burst $O(K U_{\ell+1})$; an arm not well sampled at $t_{\ell+1}$
was rejected at $t_\ell$; from some rank the threshold is deterministic ($\hat\Lambda_\ell = L_\ell$).
(ii) Leader: a suboptimal leader requires an optimal arm rejected at the previous test against a
level below the second mean plus $\varepsilon$, or a poorly sampled suboptimal arm above
$m^\star - 3\varepsilon$; both have probability $\lesssim t_{\ell+1}^{-(1+\eta)}$ thanks to a strict
gain $\eta > 0$ in the deviation inequalities of $nK_{\inf}$. (iii) Good batches: the plan evaluated
at the actual end aims above the present threshold, so $a$ is planned at
$(1+\omega) y_\ell \log t / d_a$ up to $\varepsilon$; other mistakes cost a polylogarithmic net,
summed by a layer-cake argument.

**Upper bound, $x = 1$: the water level.** A batch of IMED rounds satisfies a deterministic
property: every arm pulled in it had, at the start, a logarithmic count below the final water level
of the batch. With $x_\ell \to 1$ this gives many "high" batches whose leaders have $t^{1-\delta}$
observations; a chain argument shows that an arm with few observations was explored at level
$\approx \log t_j$ in each high batch. HY keeps this property because an activated batch first runs
$\approx t_\ell^{1+\vartheta_\ell}$ IMED rounds, whose most-pulled arm certifies a water level above
$\log t_\ell$.

**Consistency threshold.** An ambiguous arm costs a net $\approx L_\ell^\beta$. If $a \in Q_\ell$, then
$N_a \hat K_{\ell-1}(a) \ge y_{\ell-1}(\hat\Lambda_\ell - \log N_a)$ by definition, and $a$ is rejected
as soon as $\hat K_\ell(a) \ge (1 - \gamma_\ell/2)\hat K_{\ell-1}(a)$, which fails with probability
$e^{-c\sqrt{L_\ell}/\log^2 L_\ell}$; activated batches are sparse on the logarithmic scale, so the
nets are summable.

## Where the formal versions live

The owner's Lean development (`Bandits/Batch/PaperHY/` in a private project on LML) proves
items 1–3 without `sorry`, with the remainders existential. Until it is ported here, these are
formalisation targets (see "Known results to formalise" in [PROGRAMME.md](PROGRAMME.md)).
