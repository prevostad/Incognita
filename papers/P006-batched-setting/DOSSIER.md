# Dossier of P006-batched-setting, version 1

Refereed and versioned with `paper.tex`, never compiled into the PDF: what the referees and the
owner need and the reader does not. It changes only with a new version of `paper.tex` after
acceptance. Private KNOWN entries are cited by id only, never quoted.

## Roadmap correspondence

- Item served: **F0** of `roadmaps/BatchedBandits/ROADMAP.md`, the setting paper (kind
  `definitions`). The roadmap's mentions of "P000 (F0)" are the old numbering: the setting paper is
  P006 (renumbering of 2026-11-16, pull request #44).
- The roadmap asks for "the Definitions above, their basic relations, witnesses and exclusions".

### The Definitions table, row by row

Names of the dependencies read on GitHub on 2026-11-16 at the pinned revisions of
`lake-manifest.json` (LML `efbe5d2`, LMLExplore `b4e0ab9`); nothing was compiled. "Planned" names
are proposals for `formalize-statements`, which records the final names in `blueprint.md`.

| Roadmap row | Node | Planned Lean name | How it specialises or wraps the dependencies |
|---|---|---|---|
| arms | `def:instance` | — | a type `α` with `[Fintype α]` (and `[DecidableEq α]`, `[MeasurableSpace α]` discrete); $K$ = `Fintype.card α`, hypothesis `2 ≤ Fintype.card α`. Never `Fin K`. |
| (laws on $[0,1]$, needed by the row $K_a$) | `def:instance` ($\mathcal M$, $m(Q)$) | `Incognita.BatchedBandits.unitLaws : Set (Measure ℝ)`, `{Q | IsProbabilityMeasure Q ∧ ∀ᵐ x ∂Q, x ∈ Set.Icc 0 1}` (**new name**: the roadmap describes this set, "the probability measures on ℝ concentrated on [0,1]", without naming it) | the mean $m(Q)$ is `Q[id]`, as in LML's `gap` and LMLExplore's `dInf`. |
| instance, class $\mathcal P$ | `def:instance` | `Incognita.BatchedBandits.unitBandits α : Set (Kernel α ℝ)`: `IsMarkovKernel ν`, `∀ a, ∀ᵐ x ∂(ν a), x ∈ Set.Icc 0 1`, `(⨆ a, (ν a)[id]) < 1` | an LML bandit `ν : Kernel α ℝ`; $m^\star$ = `⨆ a, (ν a)[id]`; $\Delta_c$ = LML's `gap ν c`. The paper writes $Q([0,1])=1$, equivalent to the `∀ᵐ` form for a probability measure. |
| $K_a$ | `def:kinf` | reuse `LMLExplore.Bandits.dInf unitLaws (ν a) (⨆ b, (ν b)[id])` (an `ℝ≥0∞`) | `dInf M P m := ⨅ Q ∈ {Q ∈ M ∣ m < Q[id]}, klDiv P Q` is exactly the paper's primal $\mathcal K_{\inf}(P,m)$ with $\mathcal M$ = `unitLaws` ($\inf\emptyset=\infty$ in `ℝ≥0∞`). $\mathrm{KL}$ = Mathlib's `InformationTheory.klDiv`. $\mathrm{kl}(p,q)$ = `klDiv` of two Bernoulli measures (LMLExplore's `dInf_range_bernoulliMeasure` uses them). |
| grid | `def:grid` | `Incognita.BatchedBandits.Grid (K : ℕ)` (structure: `t : ℕ → ℕ`, `t_zero : t 0 = 0`, `strictMono : StrictMono t`, `two_le : max 2 K ≤ t 1`), `Grid.batchOf g n := Nat.find (∃ ℓ, 1 ≤ ℓ ∧ n < g.t ℓ)` | **Shape change, justified in the paper (Def. `def:grid` and the remark after it):** the condition $t_1\ge\max(2,K)$ is part of the grid, so the structure takes the number of arms as a parameter. The roadmap names the structure `Grid` with no parameter; with `Grid` alone the condition must be a separate hypothesis of every statement. Either is fine; the formaliser decides and records it. Also planned: `Grid.IsFiner g g' : Set.range g'.t ⊆ Set.range g.t` (the paper's "finer"). |
| $L_\ell$, $x_\ell$ | `def:logratio` | `Grid.logEnd g ℓ := Real.log (g.t ℓ)`, `Grid.ratio g ℓ := if ℓ ≤ 1 then 1 else logEnd ℓ / logEnd (ℓ-1)` | `Real.log`; at ℓ = 0 `logEnd` is the junk value `log 0 = 0` and `ratio` the value 1; the paper never uses $L_0$ (Lemma `lem:grid`(iii) gives $L_\ell\ge\log2$ for $\ell\ge1$). |
| learner | `def:learner` | reuse LML `Learning.Algorithm Unit α ℝ` (`policy n : Kernel (Hist Unit α ℝ n × Unit) α`), law `trajMeasure alg (Environment.bandit ν)`, coordinates `IT.action`, `IT.feedback`; any other realisation through `IsAlgEnvSeq` | the paper's $\pi_t$ is `policy (t-1)` (rounds from 0, paragraph "Rounds numbered from zero"); $A_t$ = `IT.action (t-1)`, $R_t$ = `IT.feedback (t-1)`. The observation type is `Unit` (no context). |
| batched learner on a grid | `def:batched`, `lem:mask` | `Incognita.BatchedBandits.IsBatched (alg : Algorithm Unit α ℝ) (g : Grid K) : Prop`; helper `Incognita.BatchedBandits.maskHist` | 0-based: `∀ ℓ n, g.t ℓ ≤ n → n < g.t (ℓ+1) → ∀ h h' : Hist Unit α ℝ n, (∀ i, (h i).action = (h' i).action) → (∀ i : Fin n, (i : ℕ) < g.t ℓ → (h i).feedback = (h' i).feedback) → alg.policy n (h, ()) = alg.policy n (h', ())`. Lemma `lem:mask` is the kernel form `alg.policy n = (alg.policy n).comap (mask × id)`. |
| information model $M_k$ | `def:infomodel` | `Incognita.BatchedBandits.InfoModel (k : ℕ∞) (π : Grid K → Algorithm Unit α ℝ) : Prop` | (a) `∀ g, IsBatched (π g) g`; (b) `∀ g g' ℓ n, (∀ j : ℕ, 1 ≤ j → (j : ℕ∞) ≤ ℓ + k → g.t j = g'.t j) → n in batch ℓ+1 of g and of g' → (π g).policy n = (π g').policy n`. For `k = ⊤` the hypothesis of (b) forces `g.t = g'.t`, so (b) holds by `Grid.ext`. |
| counts, regret | `def:counts`, `lem:counts` | reuse LML `pullCount IT.action c t` and `regret ν IT.action t` | `pullCount A a t` counts the rounds `0, …, t-1`, i.e. the paper's rounds $1,\dots,t$: the paper's $N_c(t)$ is `pullCount IT.action c t` with no shift, in particular at $t=t_\ell$. The paper's $\mathcal R_{\nu,\pi}(t)$ is the integral of LML's pathwise `regret` (LML's `integral_regret_eq_sum_gap_mul_integral_pullCount`); `lem:counts` is `sum_pullCount`-type facts and `regret_eq_sum_pullCount_mul_gap`. |
| (sequential consistency) | `def:seqcons` | reuse `LMLExplore.Bandits.IsConsistent alg E` | identical: `∀ ν ∈ E, ∀ p > 0, (∫ regret … n) / n ^ p → 0`. |
| consistency at batch ends | `def:consistent`, `lem:consist-regret` | `Incognita.BatchedBandits.IsConsistentAtBatchEnds (alg) (g : Grid K) (E : Set (Kernel α ℝ)) : Prop` | `∀ ν ∈ E, ∀ c, 0 < gap ν c → ∀ p > 0, Tendsto (fun ℓ ↦ (∫ ω, (pullCount IT.action c (g.t ℓ) ω : ℝ) ∂(trajMeasure alg (Environment.bandit ν))) / (g.t ℓ : ℝ) ^ p) atTop (𝓝 0)`, with `[IsMarkovKernel ν]` as in `IsConsistent`. |

Example objects (witnesses, names proposed for `Incognita/BatchedBandits/…` and the catalogue):
`Grid.sequential s`, `Grid.geometric s`, `Grid.doublyExp s` (`def:exgrids`); the learners
`roundRobin`, `constAlg c`, `reactAlg`, `frozenLeader g`, `parityAlg k g`, `ucbAlg`
(`def:exlearners`; LML already has `RoundRobin.lean` and `Algorithm.deterministic`: reuse them;
if LML or LMLExplore has a UCB algorithm with a regret bound, `cite:ACF02-thm1` and Step 1 of the
proof of `cor:ucb` may be replaced by it, the formaliser decides). `cor:ucb` is the witness of
consistency on the whole class $\mathcal P$; Step 1 of its proof (the reward-stack model has the
law of `trajMeasure`) is the part a formaliser should expect to cost most.

### The basic relations the roadmap asks for

| Roadmap sentence | Node |
|---|---|
| "$M_k$ is contained in $M_{k+1}$" | `thm:main`(i) (for all $k\le k'$ in $\mathbb N\cup\{\infty\}$, strict when $k<k'$) |
| "on the grid whose batches after the first have size 1, a batched learner is a sequential one" | `thm:main`(iii), first half: on $\mathsf S_s$, batched ⇔ the first $s$ policies ignore the rewards (every batched learner is an LML algorithm by definition; the constraint is only on the first batch) |
| "consistency at batch ends relates to LMLExplore's `IsConsistent`, so that LMLExplore's lower bounds apply" | `thm:main`(iii), second half: equivalence with `def:seqcons` = `IsConsistent`. Then `LMLExplore.Bandits.eventually_mul_log_le_integral_pullCount_of_klDiv` (consistency on any class containing $\nu$ and one alternative $\nu'$) applies verbatim on $\mathsf S_s$; `eventually_mul_log_le_integral_pullCount_of_isConsistent` needs a product class $\{\nu: \nu_a\in M_a\}$, which $\mathcal P$ is not ($m^\star<1$), so the one-alternative form is the one to use. The paper says this in words (paragraph "Interpretation" after `thm:main`) and does not restate the lower bound: it is the content of F1. |
| "a learner that reacts to a reward inside its batch is not batched on a grid with a batch of size ≥ 2" | `prop:witnesses`(c), `React` (batched on no grid, since batch 1 always has size $t_1\ge2$) |
| "a learner that reads $t_{j+1}$ during batch $j+1$ is in $M_1$ but not in $M_0$" | `prop:witnesses`(d) with $k=0$: `Par^{(0)}` reads $t_{b(t)}$, i.e. $t_{j+1}$ during batch $j+1$; and the general $k$ |
| "a witness and an exclusion for each definition" | `prop:witnesses`, `prop:kinf`(i),(iv), Table `tab:witnesses` |
| "The translation of the grid to 0-based rounds is fixed once, by the setting paper" | paragraph "Rounds numbered from zero" after `def:exgrids` |

Beyond the roadmap's list, the paper adds `thm:main`(ii) (refinement), `prop:kinf` (bounds and
Bernoulli value of $K_{\inf}$, positivity and finiteness of $K_a$ on $\mathcal P$), `cor:ucb` (a
non-degenerate witness of consistency at the batch ends on $\mathcal P$, on $\mathsf S_K$) and
`lem:grid`, `lem:counts`, `lem:mask`, `lem:consist-regret`.

### What the item asks that the paper does not give

- The dual formula of $\mathcal K_{\inf}$, its continuity and the deviation inequalities: item F2
  (external, shared with StochasticBandits). The paper uses only the primal definition (the
  roadmap's Definitions table also defines $K_a$ by `dInf`, the primal form).
- The realisation of a batched learner with explicit internal randomisation $U$ and reward stacks
  (P000's `def:stacks` and `lem:stacks`): not part of the roadmap's table, left to the paper that
  needs it (P000 proves it itself; LML provides `rewardByCount` and `arrayMeasure`).
- The change of measure for the observations available at the end of batch $\ell+1$ (the
  divergence decomposition with $N_c(t_\ell)$ while the actions run to $t_{\ell+1}$): the core of
  F1, not a definition.
- The existence of a learner consistent at the batch ends on all of $\mathcal P$ on a general
  grid: direction D4, not addressed. On $\mathsf S_K$ it is `cor:ucb` (UCB1 of [ACF02, Theorem 1],
  the cited node `cite:ACF02-thm1`, through `thm:main`(iii)); `Const_c` on $\mathcal P_c$ remains
  the degenerate witness valid on every grid.

### Acceptance criteria of the roadmap

1. Information model, class, criterion stated: each definition states them; `thm:main` is
   explicit about $E\subseteq\mathcal P$ and the grids. Met.
2. Closest known: below. Met (KNOWN.md has no entries).
3. One grid and one instance satisfying all hypotheses at once: paragraph "An instance satisfying
   every hypothesis at once" in `sec:examples` ($\nu=(\mathrm{Ber}(0.7),\mathrm{Ber}(0.5))$, $\mathsf D_2$,
   `Const_{c_1}`). Cases $x=1$ ($\mathsf S_s$, $\mathsf G_s$), $K=2$, Bernoulli: `prop:witnesses`(b),
   `prop:kinf`(iv) and the numbers. The bounds $1/K_a$, $x^2/K_a$: no bound is proved, so there is
   nothing to check against them; $1/K_a$ is computed (11.47).
4. Lower bound class explicit: no lower bound. N/A; the classes are defined (`def:batched`,
   `def:infomodel`, `def:consistent`).
5. Algorithm defined completely and in its information model: the example learners are given by
   formulas (`def:exlearners`), with their model proved (`prop:witnesses`(c)–(d)). Met.
6. First-order constant: N/A.
7. "Optimal" never defined: met (no evaluative definition).
8. Not a "not important on their own" result: it is the roadmap's F0.

### Conventions of the roadmap changed

- `Grid` takes the number of arms as a parameter (above).
- The roadmap's class $E$ in "consistency at batch ends" is kept as a parameter $E\subseteq\mathcal P$.
- The paper names a grid $g=(t_\ell)_\ell$ (not $t$) to avoid a clash with the round $t$.
- The paper writes $\mathcal K_{\inf}$ and $K_a$ (roadmap: $K_a := \mathcal K_{\inf}(\nu_a,m^\star)$, Appendix A
  of the roadmap writes $d_a$): same object.
- The roadmap's batch sizes $B_\ell$ are kept as $B_\ell := t_\ell-t_{\ell-1}$; the grid is given by its
  ends, as in the roadmap's Definitions table.

## Closest known

- **KNOWN.md** (`roadmaps/BatchedBandits/KNOWN.md`): first line `Reviewed by owner: no`, no entry
  at all. Nothing to compare; no private entry used.
- **P000 (library, accepted), Section "Setting"** (`def:grid`, `def:ass-x`, `def:model`, `def:kinf`,
  `def:learner`, `def:M0`, `def:stacks`). The same objects, written for one paper. Correspondence,
  so that P000's statements can be formalised on top of P006:
  - P000 `def:grid` ↔ P006 `def:grid` + `def:logratio` (same batches $(t_{\ell-1},t_\ell]$, same
    $B_1\ge\max(2,K)$, $x_1:=1$; P000 writes $\mathsf L_\ell$ for $L_\ell$). P000's `def:ass-x`
    ($x_\ell\to x$) is a hypothesis of its statements, not a definition here.
  - P000 `def:model` ↔ P006 `def:instance` (same class $\mathcal P$; P000 also defines
    $\mathbf m_{(2)}$ and $\Delta$, the smallest gap, which stay in P000).
  - P000 `def:kinf` ↔ P006 `def:kinf`: **P000 defines $\mathcal K_{\inf}$ by the dual formula**
    (with the convention $\mathcal K_{\inf}(G,1):=0$ if $\mathbb E_G X=1$, $+\infty$ otherwise), P006
    by the primal infimum (the roadmap's `dInf`). They agree for $\mu\in[0,1)$ by
    [HT10, Theorem 8] (P000's cited node `cite:honda2010asymptotically-primal`), which is item F2;
    at $\mu=1$ they differ (primal: $+\infty$ always). P000 evaluates $\mathcal K_{\inf}$ at levels
    $<1$ only (its pseudo-observation at 0 keeps the means below 1), so the difference is harmless,
    but a formaliser of P000 must bridge the two forms through F2.
  - P000 `def:learner` ↔ P006 `def:learner` + `def:batched` + `def:counts` + `def:consistent`
    with $E=\mathcal P$ (P000: "consistent on $\mathcal P$ (for the given grid)"). Same counts
    ($N_c(t)$, round $t$ included) and the same regret.
  - P000 `def:M0` ↔ P006 `def:infomodel` with $k=0$: P000 says "depends on the grid only through
    $t_1,\dots,t_\ell$ and $t$" for a round of batch $\ell+1$; P006 makes it a property of a family
    indexed by grids, with the comparison restricted to grids for which $t$ is in batch $\ell+1$ of
    both.
  - P000 `def:stacks` (and its `lem:stacks`): not in P006 (see above).
  No result of P000 is used, so P000 is not cited in `paper.tex` and `depends_on` is empty.
- **[GMS19, Definition 1]** (uniformly fast convergent strategies) and **[LS, Definition 16.1]**:
  sequential consistency, with counts or regret. `def:consistent` is the first along the batch ends;
  `lem:consist-regret` is the equivalence of the two along any subsequence of rounds;
  `thm:main`(iii) recovers the sequential notion on $\mathsf S_s$. No derivation attempt needed:
  the paper's statements about consistency are elementary.
- **[GMS19, §1.2]**: the primal $\mathcal K_{\inf}$ with $\inf\emptyset=+\infty$; `def:kinf` is its
  specialisation to the model $\mathcal M$ of laws on $[0,1]$.
- **[QW26] (Qiao–Wu, arXiv:2611.17500, v1 of 12 Nov 2026), the closest published model.** Update
  times $t_1<\dots<t_B=T$ imposed by the environment (adversarially); a batch-aware learner is given
  them all in advance, a batch-oblivious one is told when each batch ends; within a batch the
  stochastic-bandit learner commits to a sequence of arms. Correspondence: imposed grid = P006's
  grid (finite, with $t_B=T$, against P006's infinite grids); batch-aware ≈ $\mathcal M_\infty$;
  batch-oblivious ≈ $\mathcal M_0$ under P006's reading of `def:infomodel` (it knows the past ends
  and that the batch has not ended), except that their Algorithm 1 takes the horizon $T$ as input;
  the commitment within a batch = P006's `def:batched` (a policy that sees the rewards up to the
  last end can be realised as a sequence of arms drawn at the start of the batch). Criterion:
  regret at horizon $T$ up to constants, $O(\alpha^2\log(NT)\sum1/\Delta_i)$ (Theorem 1) and
  $\Omega(\alpha^{3/2}\sum1/\Delta_i)$ on a hard instance (Theorem 4), with
  $\alpha=\max_j b_j/t_{j-1}=\max_j(t_j/t_{j-1})-1$, a ratio of ends. **Attempt to derive P006's
  results from it:** `thm:main`(i) needs the intermediate $\mathcal M_k$, which QW26 does not
  define; for $k=0$ against $k=\infty$, the strictness is P006's `prop:witnesses`(d) with $k=0$ and
  is not stated in QW26 (their gap between aware and oblivious is about regret, not the classes).
  `thm:main`(ii)–(iii) are about consistency at the batch ends, which QW26 does not define (no
  asymptotic statement, no $\mathcal K_{\inf}$). `prop:kinf` is not about batches. So nothing of
  P006 follows from QW26; P006's batched learner and the two end models are credited to it
  (sec:related, tab:comparison, sec:attribution). Their $\alpha$ against P006's $x_\ell$: on
  $\mathsf G_s$ (doubling) $\alpha=1$ and $x_\ell\to1$; on $\mathsf D_s$ ($t_\ell=t_{\ell-1}^2$),
  $\alpha=\infty$ on an infinite grid while $x_\ell=2$: the two measures of growth differ, which
  the paper says in one sentence.
- **[PGPK21] (and [PGPK22], linear bandits)**: batches of a common size $b$ imposed by the
  environment; Theorem 3.1 bounds $R_n(\pi^b)$ between $R_n(\pi)$ and $bR_M(\pi)$ under two
  assumptions on the policy. A special case of imposed grids ($t_\ell=\ell b$, which is $\mathsf S$-
  like only for $b=1$); no information model, no consistency notion. Nothing of P006 follows.
- **[KO21b, §II.A]**: imposed batches, ends decided at the previous end, possibly adversarially;
  P006 does not contain this model (random or history-dependent grids are out of scope, said in
  the Scope paragraph).
- **[PRCS16], [GHRZ19], [JTXHXG21]**: chosen grids; not this setting (Table `tab:comparison`).
- Novelty is not claimed: after QW26, the paper says "We are not aware of" a published definition
  of the intermediate models $\mathcal M_k$, $1\le k<\infty$, of consistency at the batch ends, or
  of their relation to the sequential notions. The attribution audit decides.
- **`prop:kinf`(iii)**: the lower half is known: $\mathcal K_{\inf}\ge\mathrm{kl}$ of the means is
  [CGMMS13, §6.1] (the display after Corollary 1, via Hoeffding's bound on the moment-generating
  function and the variational formulas), and the chain $\mathcal K_{\inf}\ge2(\cdot)^2$ is
  [GHMS22, (7)] (data processing [GMS19, Lemma 1], then Pinsker). The upper bound
  $\log\frac{1-p}{1-\mu}$ refines the uniform $-\log(1-\mu)$ of [HT10, Lemma 14]; the refined form
  was not found printed (searches below). The paper attributes all this in sec:overview,
  sec:related and sec:attribution.

## Sanity checks

- **$K=2$**: every statement holds with $K=2$; $\mathsf S_2$, $\mathsf G_2$, $\mathsf D_2$ are the
  smallest grids ($t_1=2$). `Par^{(k)}` needs two arms $c_1\ne c_2$, available since $K\ge2$.
- **$x_\ell\to1$ and $x>1$**: $\mathsf S_s$ and $\mathsf G_s$ have $x_\ell\to1$, $\mathsf D_s$ has $x_\ell=2$
  (computed in `notebook/constants.txt`).
- **Bernoulli rewards**: `prop:kinf`(iv) gives $\mathcal K_{\inf}(\mathrm{Ber}(p),m)=\mathrm{kl}(p,m)$
  for $p\le m<1$, the same value as LMLExplore's `dInf_range_bernoulliMeasure` (which takes the
  infimum over Bernoulli laws only): the infimum over all laws on $[0,1]$ is not smaller, by the
  data-processing step of the proof. Numbers: $\mathrm{kl}(0.5,0.7)=0.0872\in[0.08,0.5108]$.
- **$m^\star=1$**: $K_a=+\infty$ (`prop:kinf`(i)): excluded from $\mathcal P$, consistent with the
  roadmap's pinned $m^\star<1$ and with HT10's dual formula ($\mu<1$).
- **Ties (several optimal arms)**: allowed everywhere; consistency only constrains suboptimal arms;
  `Const_c` on $\mathcal P_c$ covers instances with several optimal arms.
- **$N=0$ / first batch**: `lem:grid`(ii), $b(t)=1$ iff $t\le t_1$; batch 1 sees no reward
  ($t_0=0$); $t_1\ge K$ lets `RR` pull every arm once, so `FL` has $n_c\ge1$ after batch 1.
- **Infinite divergences**: $\mathrm{kl}(p,1)=+\infty$ handled in `lem:kl`; `prop:kinf`(iii) lower
  bound allows $Q=\delta_1$ (mean 1).
- **0-based translation**: checked against LML's definitions: `pullCount A a t` counts `range t`
  (rounds `0..t-1`), `regret ν A t` sums `range t`, `history … n` holds rounds `0..n-1`, so the
  policy at LML round `n` sees rounds `< n`; batch $\ell+1$ is LML rounds `t ℓ .. t (ℓ+1) - 1` and
  may see feedback of rounds `< t ℓ`.
- **Consistency with `[Lean]` entries of KNOWN.md**: none exist. With the roadmap's known results:
  the roadmap's lower bounds quantify over "batched learners consistent at batch ends, even one
  that knows the grid" = learners batched on a fixed grid (`thm:main`(i): the components of
  $M_\infty$) and consistent in the sense of `def:consistent` with $E=\mathcal P$; HY is "a
  deterministic learner of $M_0$" = a family in `InfoModel 0`.
- **Example satisfying everything at once**: `sec:examples`, last paragraph.

## Weak points

1. `def:infomodel`, condition (b) for $k=0$: the comparison is between grids for which the
   current round $t$ is in batch $\ell+1$ of both. This lets a learner of $M_0$ use the fact that
   the batch has not ended yet (it is still being asked to play), which is the intended meaning of
   "doubly anytime" and P000's `def:M0`, but a stricter reading (independence of the whole future
   of the grid, including whether $t\le t_{\ell+1}$) would give a different, smaller class. A
   referee may prefer the other reading; nothing in this paper depends on it, but HY's membership
   does (it is fine under this reading).
2. `def:batched`: batching is a pointwise invariance of the kernels $\pi_t(\cdot\mid h)$. It is
   the natural notion for LML's `Algorithm`, but P000 realises learners with an explicit internal
   randomisation $U$ (as in [GMS19, §1.1]); the equivalence between the two realisations is not
   proved here (it is P000's `lem:stacks`(iii) direction only). If a later paper needs a learner
   whose kernel is not obviously batched (for instance one that draws a random grid guess once),
   its batching must be checked on the kernels.
3. `cor:ucb`, Step 1 of the proof (added in revision round 1): the identification of the law of
   the reward-stack model of [ACF02] with $\mathbb P_{\nu,\pi}$ of `def:learner`. The argument
   (replace the stack of arm $c$ from index $j$ on by zeros; the run up to round $t-1$ is unchanged
   on $\{N_c(t-1)=j-1\}$, so the $j$-th reward of $c$ is independent of the history there) is
   standard but written here for a deterministic learner only, which is all `cor:ucb` needs.
   Round 2 (SC2.1): [LS, §4.6] state the equivalence (p. 65 of the online edition: the law of
   $A_1,X_1,\dots,A_n,X_n$ "is the same for all choices (Exercise 4.4)"), and Exercise 4.4 (p. 69)
   asks to show that the random-table and reward-stack models satisfy condition (b) of §4.6, with
   Doob's optional stopping theorem as a hint; uniqueness of the law under (a)–(b) is their
   Proposition 4.8 (Exercise 4.2). The paper now credits LS in Step 1, in the paragraph before
   `cite:ACF02-thm1` and in `sec:attribution`. The argument written here (zeroing the stack) differs
   from LS's hint; it avoids optional stopping, which a Lean proof would otherwise need for the
   random index $N_c(t-1)+1$.
4. `prop:kinf`(iii), upper bound, and `lem:kl`: the step $\mathrm{KL}(P,Q_u)=\int\log\frac{dP}{dQ_u}dP\le\log\frac1{1-u}$
   uses that the density is bounded; in Mathlib, `klDiv` is $+\infty$ unless the log-likelihood
   ratio is integrable, which holds here (bounded above, negative part integrable for probability
   measures) but must be shown. The continuity of $\mathrm{kl}(p,\cdot)$ at $q=p=0$ and the
   conventions $0\log0$ are the other places where junk values can bite.

## Searches

- Revision round 2 (2026-11-17, claude-opus-5-5): no search query; the scope referee's round-2
  queries (the reward-stack model and LS §4.6; Agrawal 1995 as the source of the UCB1 index;
  imposed batch ends with a lookahead; consistency on a fixed grid) found nothing that changes the
  comparison. Page read: the free online edition of LS (tor-lattimore.com/downloads/book/book.pdf,
  text layer), §4.6 pp. 63–65 in full (Definition 4.7, conditions (a)–(b), Proposition 4.8, the
  density (4.7), the random-table and reward-stack models and the sentence on their equivalence),
  §4.10 Exercises 4.1–4.4 (p. 69). Recorded in `literature/index.md` and `literature/notes/LS.md`.
- Revision round 1 (2026-11-17, claude-opus-5-5):
  - "bandit batches imposed by environment learner knows next batch end lookahead information
    model consistency asymptotic regret": QW26 (arXiv:2611.17500, imposed batches, batch-aware and
    batch-oblivious learners), PGPK22, batched nonparametric contextual bandits (arXiv:2402.17732,
    chosen grids), batched linear bandits (chosen grids); nothing on a graded lookahead
    $\mathcal M_k$ or on consistency at imposed batch ends.
  - "\"batch-oblivious\" OR \"batch-aware\" stochastic bandits Lai Robbins asymptotic constant batch
    ends": only chosen-grid works (JXXG21, E$^4$ for linear bandits, PRCS16, EKMM21); no imposed-grid
    asymptotic constant.
  - "Rioul Pinsker inequality history survey Csiszár Kullback Kemperman optimal constant arXiv":
    Rio23 (GSI 2023) and its extended version (Information Geometry 2024); Reid–Williamson
    (arXiv:0901.0356, Appendix D, not used).
  - The scope referee's report of round 1 lists ten further queries (imposed batch sizes,
    Provodin et al., uniformly good policies with a grid, delayed feedback, the upper bound of
    $\mathcal K_{\inf}$, $\mathcal K_{\inf}\ge\mathrm{kl}$, Pinsker's history); their findings are
    taken into account above (QW26, PGPK21–22, CGMMS13 §6.1, GHMS22 (7), HT10 Lemma 14, Rio23).
  - Pages read (2026-11-17): arXiv abs pages of 2611.17500, 2111.02071, 2202.06657, 1805.05071v3;
    the HTML of 2611.17500v1 (first part: setting, Definition 1, Theorems 1–4, Propositions 1, 3);
    the PDF of 2111.02071v1 (§2, Theorem 3.1); the PDF of arXiv:1210.1136v4 (§5 Theorem 2, §6.1,
    §6.2 opening); the HTML of 1805.05071v3 (§2.1, (5)–(8)); the author PDF of ACF02 (§1, §2,
    Theorem 1, Figure 1); the author PDF of Rio23 (§2–§4 opening). Recorded in
    `literature/index.md` and `literature/notes/ACF02.md`.
- Version 1 (2026-11-16): no web search engine queries were run. Pages read on 2026-11-16:
  - arXiv abs page of arXiv:1505.00369 (PRCS16): the abstract ("split trials into a small number
    of batches", "close to minimax optimal regret bounds"); it does not mention static or adaptive
    grids or the number of arms.
  - arXiv abs page of arXiv:1904.01763 (GHRZ19): the abstract (K arms; lower bounds "even if the
    batch sizes are determined in an adaptive manner").
  - GitHub, `LeanMachineLearning/LML` at `efbe5d2`: `SequentialLearning/Algorithm.lean`,
    `IonescuTulceaSpace.lean`, `FiniteActions.lean` (`pullCount`, `rewardByCount`),
    `SumRewards.lean`, `StationaryEnv.lean` (`Environment.bandit`), `Deterministic.lean`,
    `Online/Bandit/Regret.lean` (`regret`, `gap`), `RewardByCountMeasure.lean`,
    `ArrayProbSpace.lean` (declarations and docstrings only).
  - GitHub, `LeanMachineLearning/LMLExplore` at `b4e0ab9`: `Bandits/LaiRobbins.lean` (`IsConsistent`,
    `dInf`, the Lai–Robbins theorems), file list of `Bandits/`.

## Reading notes

- Every citation of `paper.tex` rests on a part recorded as read in `literature/index.md` (by
  earlier sessions): GMS19 (§1.1, §1.2, Definition 1, Lemma 1; verbatim in
  `literature/notes/GMS19.md`), LS (§16.1 Definition 16.1, Theorem 16.2), HT10 (Theorem 8),
  CGMMS13 (§5 Theorem 2), JTXHXG21 (whole; Theorem 4), KO21b (whole; §II.A), JGS13 (Theorem 6),
  GHMS22 (Appendix B.1, the mixing step), PRCS16 (whole), GHRZ19 (whole). HT15, EKMM21, JXXG21 are
  "see also". LR85 and BK96 are cited as classics for the Lai–Robbins–Burnetas–Katehakis bound and
  the definition of the divergence (AGENTS.md §5.2 allows it).
- `cite:GMS19-lem1` restates Lemma 1 of GMS19 with the printed typo ($Z:\Omega\to[0,1]$, $\Gamma$
  meant) corrected and said so, and the $\sigma$-algebra renamed $\mathcal S$ (round 1, SC1.4).
- Added in round 1: QW26 (setting, Definition 1, Theorems 1–4), PGPK21 (§2, Theorem 3.1), PGPK22
  (abstract only: "see also"), CGMMS13 §6.1 (the display $d_{\mathrm{BER}}(E\nu,E\nu')\le
  \mathrm{KL}(\nu,\nu')$) and §5 Theorem 2 (its model $\mathcal F$), GHMS22 (7), ACF02 (Theorem 1
  and Figure 1, verbatim in `literature/notes/ACF02.md`; `cite:ACF02-thm1` restates it in the
  reward-stack form, with the renaming line), Rio23 (§3: Csiszár 1967 Theorem 4.1 with the
  one-line proof (16), Kullback 1967, Kemperman 1969; §4: Schützenberger 1953). The original
  papers of Csiszár, Kullback, Kemperman and Schützenberger were not read: the paper cites them only
  through Rio23, by name and year, without a bibliography entry.
- Added in round 2: LS §4.6 (the sentence stating that the reward-stack and canonical models give
  the same law, and Exercise 4.4), cited in Step 1 of the proof of `cor:ucb` and in
  `sec:attribution`.

## Changes

None (version 1).
