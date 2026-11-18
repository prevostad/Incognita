# Blueprint of P000-hy-unknown-imposed-grid

Lean names of the paper's nodes. Statuses are computed by the audit, not stored here.

| Label | Kind | Lean name | Notes |
|---|---|---|---|
| def:grid | definition | Incognita.BatchedBandits.Grid, Incognita.BatchedBandits.Grid.logEnd, Incognita.BatchedBandits.Grid.ratio | reused from P006; $\mathsf L_\ell$ = `g.logEnd ℓ`, $x_\ell$ = `g.ratio ℓ` |
| def:ass-x | definition | (inline) | `Filter.Tendsto g.ratio Filter.atTop (nhds x)` with `1 ≤ x` |
| def:model | definition | Incognita.BatchedBandits.unitBandits, Incognita.BatchedBandits.unitLaws | reused from P006; $\mathbf m^\star$ = `⨆ b, ∫ y, id y ∂(ν b)`, $\Delta_c$ = `Bandits.gap ν c` (LML) |
| def:kinf | definition | LMLExplore.Bandits.dInf, Incognita.BatchedBandits.HY.pseudoKinf | $\mathcal K_{\inf}(\nu_a,\mathbf m^\star)$ in the statements = `dInf unitLaws (ν a) m⋆` (primal form, reused, as in P006); inside HY, `HY.pseudoKinf` (dual form, rational $\lambda$, new) |
| def:learner | definition | Incognita.BatchedBandits.IsBatched, Incognita.BatchedBandits.IsConsistentAtBatchEnds, Learning.pullCount | reused from P006 and LML; $\mathfrak R(t)$ written inline as `∑ c, gap ν c * E[pullCount … c t]` |
| def:M0 | definition | Incognita.BatchedBandits.InfoModel | reused from P006, `InfoModel 0` |
| def:stacks | definition | (not defined) | proof device; LML's `IsAlgEnvSeq` and the array probability space of LML serve the same purpose for `prove` |
| def:hy | definition | Incognita.BatchedBandits.hyAlg, Incognita.BatchedBandits.hy, Incognita.BatchedBandits.HY.next | new; with the default parameters `Grid.hyOmega`, `Grid.hyTheta`, `Grid.hyGamma` and the grid quantities `Grid.netSize` ($U_j$), `Grid.imedEnd` ($s_\ell$); statistics `HY.count`, `HY.pseudoMean`, `HY.pseudoKinf`, `HY.leader`, `HY.reference`, `HY.imedKinf`, `HY.testKinf`, `HY.imedIndex`, `HY.imedArm`, `HY.threshold`, `HY.target`, `HY.pacedArm` |
| def:hy-vocab | definition | (not defined) | vocabulary; "activated" is `g.imedEnd θ ℓ < g.t (ℓ + 1)` |
| thm:lower | frozen | Incognita.Statements.P000.lower_liminf_of_tendsto_ratio_one | (i); proof: Incognita.P000.lower_liminf_of_tendsto_ratio_one |
| thm:lower | frozen | Incognita.Statements.P000.lower_limsup | (ii), first claim, through thm:main(a) for every $x\ge1$; proof: Incognita.P000.lower_limsup |
| thm:lower | frozen | Incognita.Statements.P000.lower_liminf | (ii), second claim, through thm:main(a) for every $x\ge1$; proof: Incognita.P000.lower_liminf |
| thm:lower | frozen | Incognita.Statements.P000.lower_regret_liminf | (iii); proof: Incognita.P000.lower_regret_liminf |
| thm:upper | frozen | Incognita.Statements.P000.hy_isConsistent | consistency; proof: Incognita.P000.hy_isConsistent |
| thm:upper | frozen | Incognita.Statements.P000.hy_tendsto_count | limit of the counts; proof: Incognita.P000.hy_tendsto_count |
| thm:upper | frozen | Incognita.Statements.P000.hy_tendsto_regret | limit of the regret; proof: Incognita.P000.hy_tendsto_regret |
| thm:main | frozen | Incognita.Statements.P000.lower_limsup | (a), first claim |
| thm:main | frozen | Incognita.Statements.P000.lower_liminf | (a), second claim |
| thm:main | frozen | Incognita.Statements.P000.hy_infoModel_zero | (b), HY is a learner of $\mathcal M_0$; proof: Incognita.P000.hy_infoModel_zero |
| thm:main | frozen | Incognita.Statements.P000.hy_isConsistent, Incognita.Statements.P000.hy_tendsto_count | (b), consistency and limit (stated for every $w_0\ge0$, $\beta\ge2$, which contains the default $w_0=1$, $\beta=2$) |
| thm:main | frozen | Incognita.Statements.P000.lower_regret_limsup | regret, lower bound; proof: Incognita.P000.lower_regret_limsup |
| thm:main | frozen | Incognita.Statements.P000.hy_tendsto_regret | regret of HY |
| lem:onebatch | frozen | Incognita.Statements.P000.one_batch_ahead | frozen as the roadmap's item F1 ("its one-batch lemma"); gives thm:lower(i) on every grid; proof: Incognita.P000.one_batch_ahead |
| cite:honda2010asymptotically-primal | cited | (added by prove) | |
| cite:garivier2019explore-dataprocessing | cited | (added by prove) | check first what LMLExplore's `InstanceDependentLowerBound` and `LaiRobbins` provide (roadmap, item F1) |
| lem:primal | lemma | (added by prove) | |
| lem:kinf | lemma | (added by prove) | P006 froze `kinf_bounds`, `kinf_bounds_of_gap_pos`; `HY.pseudoKinf_eq_zero_of_le_pseudoMean` is item "mean ≥ level ⇒ 0" for the dual form |
| lem:pseudo, lem:hoeffding, lem:grid, lem:single, lem:pair, lem:theta, lem:lowerdev, lem:upperdev, lem:stacks, lem:sums, lem:diag, lem:distinct, lem:chain | lemma | (added by prove) | |
| def:empkinf | definition | (proof-internal, not defined) | the empirical $\mathcal K_{\inf}$ is `HY.pseudoKinf`; $\Phi$, $\Psi$ are proof-internal |
| lem:tilts, lem:com, lem:typ | lemma | (not formalised) | not needed by the Lean route to `lem:twobatches`(ii), see `flem:twobatches` of `formalisation.tex` and the Open problems |
| def:tilt, def:Q | definition | (proof-internal, not defined) | |
| lem:imedround, lem:service, lem:W, lem:sparse | lemma | (added by prove) | |
| def:backlog, def:water | definition | (proof-internal, not defined) | |
| def:constA, def:ranksA, def:H, def:evA | definition | (proof-internal, not defined) | |
| lem:constA, lem:ranksA, lem:H, lem:decompA, lem:probasA, lem:sumsA, lem:structA, lem:thrA, lem:leaderA, lem:countsA, lem:goodA | lemma | (added by prove) | |
| prop:dyA | proposition | (added by prove) | non-asymptotic bound for $x>1$; not frozen (not a headline) |
| def:constC, def:ranksC, def:evC, def:amb, def:high | definition | (proof-internal, not defined) | |
| lem:constC, lem:decompC, lem:controlC, lem:sumC, lem:lowmass, lem:growth, lem:levelC, lem:goodhigh, lem:highC, lem:fewC, lem:logcountC, lem:optW, lem:pullsC, lem:amb | lemma | (added by prove) | |
| prop:fixedC | proposition | (added by prove) | non-asymptotic bound for $x=1$; not frozen (not a headline) |
| lem:onebatch | lemma (general form) | Incognita.BatchedBandits.eventually_lt_integral_pullCount_div_log_t_succ | proved; route in `formalisation.tex` (Bretagnolle–Huber in place of data processing; the strict primal formula in place of `lem:kinf`(v) and `lem:primal`) |
| thm:lower | theorem, (i) (general form) | Incognita.BatchedBandits.eventually_lt_integral_pullCount_div_log_t | proved on every grid (the hypothesis $x_\ell\to1$ is not used) |
| thm:lower | theorem, (ii) second claim (general form) | Incognita.BatchedBandits.eventually_lt_integral_pullCount_div_log_t_of_isBigO | proved for every $x>0$; first claim through `lower_limsup` (Case B: `flem:caseB`) |
| thm:lower | theorem, (iii) (general form) | Incognita.BatchedBandits.eventually_lt_regret_div_log_t_of_forall | from the per-arm bounds; $x=1$: `flem:regret-one` |
| lem:twobatches | lemma, (ii) (general form) | Incognita.BatchedBandits.eventually_lt_integral_pullCount_div_log_t_add_two | proved at the index $\ell+1$, by the route `flem:twobatches` of `formalisation.tex`; (i) not formalised (not needed) |
| thm:main | theorem, (b) first claim (general form) | Incognita.BatchedBandits.infoModel_zero_hy | proved for all real $w_0$, $\beta$ |
| flem:masked-law | lemma (formalisation.tex) | Incognita.BatchedBandits.map_history_maskFeedback_eq, Incognita.BatchedBandits.isAlgEnvSeqUntil_maskFeedback | "the actions up to $t_{\ell+1}$ are $\mathcal H_\ell$-measurable" of `sec:app-lower`, as an equality of laws |
| flem:switch-kl | lemma (formalisation.tex) | Incognita.BatchedBandits.klDiv_map_hist_switch | Step 2 of the proof of `lem:onebatch` |
| flem:onebatch-finite | lemma (formalisation.tex) | Incognita.BatchedBandits.exp_neg_le_of_seesRewardsUpTo | Steps 2–4 of the proof of `lem:onebatch`, at a finite horizon |
| flem:mean-lt-one | lemma (formalisation.tex) | Incognita.BatchedBandits.integral_id_lt_one_of_klDiv_ne_top | "$H\ne\delta_1$" in Step 1 of the proof of `lem:onebatch` |
| flem:hy-congr | lemma (formalisation.tex) | Incognita.BatchedBandits.HY.next_congr, Incognita.BatchedBandits.isBatched_hyAlg | HY is batched, for all parameters |
| flem:hy-grid | lemma (formalisation.tex) | Incognita.BatchedBandits.HY.next_hy_eq_of_t_eq | HY with the default parameters reads only $t_0,\dots,t_\ell$ in batch $\ell+1$ |
| flem:liminf-sum | lemma (formalisation.tex) | Incognita.BatchedBandits.eventually_lt_sum_mul | `thm:lower`(iii), "the liminf of a finite sum" |
| flem:liminf-mul | lemma (formalisation.tex) | Incognita.BatchedBandits.eventually_lt_mul_of_tendsto | |
| flem:log-ratio | lemma (formalisation.tex) | Incognita.BatchedBandits.Grid.tendsto_log_t_add_two_div_log_t | $\log t_{\ell+2}/\log t_\ell=x_{\ell+1}x_{\ell+2}\to x^2$ |
| flem:caseA | lemma (formalisation.tex) | Incognita.BatchedBandits.eventually_lt_div_log_t_of_eventually_lt_div_log_t_add_two | Case A of the proof of `thm:lower`(ii), from the conclusion of `lem:twobatches`(ii) |
| flem:caseB | lemma (formalisation.tex) | Incognita.BatchedBandits.frequently_lt_div_log_t_of_not_isBigO | Case B of the proof of `thm:lower`(ii) |
| flem:regret-one | lemma (formalisation.tex) | Incognita.BatchedBandits.eventually_lt_regret_div_log_t | `thm:lower`(iii) for $x=1$, on every grid |
| flem:com-one-sided | lemma (formalisation.tex) | Incognita.BatchedBandits.withDensity_map_hist_le, Incognita.BatchedBandits.setLIntegral_stepKernel_le | one-sided change of measure for the histories of a run |
| flem:switch-kl-left | lemma (formalisation.tex) | Incognita.BatchedBandits.klDiv_map_hist_switch_left, Learning.IsAlgEnvSeq.isAlgEnvSeqUntil_of_feedback_eq | the switched environment with the bandit on the right |
| flem:dp | lemma (formalisation.tex) | Incognita.BatchedBandits.exp_neg_div_le_of_klBer_le | data processing, multiplicative form |
| flem:alt-laws | lemma (formalisation.tex) | Incognita.BatchedBandits.exists_unitLaws_mean_mem_Ioo, Incognita.BatchedBandits.mix_mem_unitLaws, InformationTheory.klDiv_mix_le, Incognita.BatchedBandits.exists_two_alternatives | the alternative instances $\kappa^+,\kappa^-$ (replaces `lem:tilts`) |
| flem:twobatches-finite | lemma (formalisation.tex) | Incognita.BatchedBandits.two_batches_finite | the finite-horizon inequality two batches ahead |
| flem:twobatches | lemma (formalisation.tex) | Incognita.BatchedBandits.eventually_lt_integral_pullCount_div_log_t_add_two, Incognita.BatchedBandits.two_batches_step, Incognita.BatchedBandits.two_batches_arith, Incognita.BatchedBandits.rhs_le_of_counts_le | `lem:twobatches`(ii) |
| flem:regret-caseB | lemma (formalisation.tex) | Incognita.BatchedBandits.frequently_lt_regret_div_log_t_of_not_isBigO | the regret `limsup` when some count is not logarithmic |

The satisfiability witnesses are in `Incognita/P000/Witnesses.lean`
(`Incognita.P000.<name>_satisfiable`, one per frozen statement).

## Modelling decisions

1. **Setting reused from P006.** Arms, instances, grids, batched learners, information models and
   consistency at the batch ends are P006's objects (`Grid`, `unitBandits`, `unitLaws`,
   `IsBatched`, `InfoModel`, `IsConsistentAtBatchEnds`), so that P006's results apply. Arms are a
   `Fintype α` with `MeasurableSingletonClass α` and `DecidableEq α`; `K ≥ 2` is the hypothesis
   `hK : 2 ≤ Fintype.card α` of every statement; grids are `Grid (Fintype.card α)` (the paper's
   $B_1\ge\max(2,K)$ is a field of the structure).
2. **Rounds from 0.** The paper's round $t\in(t_\ell,t_{\ell+1}]$ is the Lean round
   `n = t - 1 ∈ [t ℓ, t (ℓ+1))`, i.e. `g.batchOf n = ℓ + 1`. Quantities at batch ends do not shift:
   the paper's $N_c(t_\ell)$ is `pullCount IT.action c (g.t ℓ)`. Inside HY, the current count
   $N_c(t-1)$ is `pullCount' n h c` (pulls in the history of the `n` rounds before `n`), the
   statistics at $t_\ell$ use the rounds `< t ℓ`, and the paper's $\log t$ is `log (n + 1)`.
3. **$\mathcal K_{\inf}$.** In the frozen statements, $\mathcal K_{\inf}(\nu_a,\mathbf m^\star)$
   is LMLExplore's `dInf unitLaws (ν a) m⋆` (infimum of `klDiv` over laws on $[0,1]$ of mean
   $>\mathbf m^\star$), as the roadmap plans and P006 does; the paper's Definition `def:kinf`
   identifies it with its dual formula ([HT10, Theorem 8]). The statements use its `toReal`,
   faithful because it is finite and positive for $\nu\in\mathcal P$ and a sub-optimal arm.
   Inside HY the divergence of the pseudo-empirical law is computed by the dual formula
   (`HY.pseudoKinf`), with the supremum over **rational** $\lambda$, as the paper's own remark in
   `def:kinf` allows ("for an empirical distribution, the supremum can be taken over rational
   $\lambda$"); this makes measurability provable. For rewards in $[0,1]$ the function of
   $\lambda$ is continuous on $[0,1/(1-\mu))$, so the rational and real suprema agree; this
   equality is not proved here (Open problems). The case $\mu = 1$ of the paper is the branch
   $\mu\ge1$ (`0` if the pseudo-mean is 1, `∞` otherwise); values in `ℝ≥0∞`.
4. **HY as an LML algorithm.** `hyAlg w₀ β ω θ γ g := Algorithm.deterministic (HY.next …)`, with the
   measurability of the action function proved (`HY.measurable_next`): every step is a
   composition of measurable statistics with LML's measurable `argmax`/`argmin` and
   `Measurable.ite`. The parameters $\omega_\ell,\vartheta_\ell,\gamma_\ell$ are sequences
   `ℕ → ℝ`; the default ones (`Grid.hyOmega`, `Grid.hyTheta`, `Grid.hyGamma`) are functions of
   `g.t ℓ`, so that `hy w₀ β g := hyAlg w₀ β g.hyOmega g.hyTheta g.hyGamma g` is the paper's
   HY$(w_0,\beta,\omega^{\mathrm{dy}},\vartheta,\gamma)$, and `fun g ↦ hy w₀ β g` is the family over
   grids whose membership in $\mathcal M_0$ is frozen (`hy_infoModel_zero`).
5. **Tie rules.** The paper fixes the tie rules and does not use them. Here: the leader and the
   reference are LML's `argmax` (a fixed function of the vector of values); the IMED arm is the
   leader when it minimises $J_\ell$, and LML's `argmin` of $J_\ell$ otherwise; the "first arm in a
   fixed order" of the paced rule is the arm of smallest index in `Fintype.equivFin α` (computed as
   the unique maximiser of minus the index on the demanding arms); batch 1 plays the arm of index
   `n mod K` (the arms in turn). Nothing else in HY is left free.
6. **Pieces of HY, one by one** (paper Definition `def:hy` → Lean, at the round `n` of batch
   `ℓ + 1`, `r = t ℓ`): $N_c$ = `HY.count h r c`; $\tilde{\mathbf m}_c$ = `HY.pseudoMean w₀ h r c`
   (sum of the rewards of `c` before `r` divided by `N_c + w₀`); $\hat c_\ell$ = `HY.leader w₀ h r`;
   $\tilde K_\ell(c)$ = `HY.imedKinf w₀ h r c`; $W_\ell$ = `HY.IsWellSampled h r (U ℓ)` ($U\le 2N_c$,
   i.e. $N_c\ge U/2$); $r_\ell$ = `HY.reference`; $\hat K_\ell(c)$ = `HY.testKinf w₀ h r (U ℓ) c`;
   $J_\ell(c,t)$ = `HY.imedIndex w₀ (x_ℓ²) h r c` in `EReal` (`0 · ∞ = 0`, `N · ∞ = ∞` for
   $N\ge1$, the paper's convention); $\hat\Lambda_\ell$ ($\ell\ge2$) = `HY.threshold` (computed in
   `ℝ≥0∞` with $\min\emptyset=\infty$, then `toReal`, finite because it is at most $\mathsf
   L_\ell$), $\hat\Lambda_1=\mathsf L_1$; $h_\ell=(1-\gamma_\ell)y_{\ell-1}\hat\Lambda_\ell$ with
   $y_{\ell-1}$ = `g.ratio (ℓ-1) ^ 2` (`g.ratio 0 = 1` gives $y_0=1$); $n_{\ell,c}(t)$ =
   `HY.target` (`h / ∞ = 0` as the paper says); the rule = `HY.pacedArm`; $U_j$ = `Grid.netSize`,
   $s_\ell$ = `Grid.imedEnd`.
7. **Limits.** Real sequences that may be unbounded: $\liminf_\ell u_\ell\ge L$ is
   `∀ c < L, ∀ᶠ ℓ in atTop, c < u ℓ`, $\limsup_\ell u_\ell\ge L$ is
   `∀ c < L, ∃ᶠ ℓ in atTop, c < u ℓ`, limits are `Filter.Tendsto … (nhds L)`. These are the forms
   the author's own Lean statements used (DOSSIER.md, section 7). $O(\log t_\ell)$ is
   `Asymptotics.IsBigO Filter.atTop`.
8. **Regret.** The paper's pseudo-regret $\mathfrak R(t)=\sum_c\Delta_c\,\mathbb E[N_c(t)]$ is
   written as this sum (it equals the expectation of LML's `regret` by
   `integral_regret_eq_sum_gap_mul_integral_pullCount`); $C_x$ sums over
   `Finset.univ.filter (0 < gap ν ·)`.
9. **Which items are frozen, and how.** Theorem `thm:lower`(ii) assumes $x>1$; a satisfiability
   witness for that hypothesis would need a batched learner consistent on $\mathcal P$ on a grid
   with $x>1$, which only Theorem `thm:upper` provides. Its two claims are frozen through
   Theorem `thm:main`(a), which states them for every $x\ge1$ (`lower_limsup`, `lower_liminf`;
   the paper's proof of `thm:main`(a) is "(a) is Theorem `thm:lower`"), so nothing of
   `thm:lower`(ii) is lost and every frozen statement has a witness. In `lower_liminf` and
   `lower_regret_liminf` the paper's condition "$x=1$, or $x>1$ and the counts are logarithmic" is
   written "$x=1$ or the counts are logarithmic", equivalent since $x\ge1$. The counts in
   `thm:main`(a) ("its counts are logarithmic") are those of the arm $a$, as in
   `thm:lower`(ii). Theorem `thm:upper` is frozen for every $w_0\ge0$, $\beta\ge2$ (its last
   sentence), which contains the default parameters; `thm:main`(b) is then these statements plus
   `hy_infoModel_zero`. Lemma `lem:onebatch` is frozen because the roadmap's item F1 is "its
   one-batch lemma". The non-asymptotic Propositions `prop:dyA` and `prop:fixedC` are proof steps,
   not headlines, and are not frozen.
10. **Witnesses.** Two arms (`Bool`), the Bernoulli instance $(\mathrm{Ber}(0.7),\mathrm{Ber}(0.5))$
    of P006, the sequential grid $\mathsf S_2$ ($x=1$), and LMLExplore's KL-UCB as the consistent
    batched learner: it is consistent on the bandits with rewards in $[0,1]$
    (`KLUCB.isConsistent`), hence at the batch ends of every grid, and it is batched on
    $\mathsf S_2$ (`Incognita.P000.klucb_isBatched_sequential_two`: at the round 1 the only arm of
    index `⊤` is the arm not pulled at the round 0, so it ignores that reward).

## Back-translations

Read from the Lean alone (notation: $\mathbb E[N_c(t)]$ is
`∫ ω, pullCount IT.action c t ω ∂(trajMeasure alg (Environment.bandit ν))`, $K_c$ is
`(dInf unitLaws (ν c) (⨆ b, ∫ y, id y ∂(ν b))).toReal`, $\mathfrak R(t)=\sum_c \mathrm{gap}(c)\,
\mathbb E[N_c(t)]$, $C_x=x^2\sum_{c:\mathrm{gap}(c)>0}\mathrm{gap}(c)/K_c$; every statement has a
finite type of at least two arms with the discrete σ-algebra, a grid for that number of arms, a
Markov kernel $\nu$ in `unitBandits α`, and, for the lower bounds, an algorithm `alg` batched on
the grid and consistent at its batch ends on `unitBandits α`).

- **`one_batch_ahead`.** For every grid, every batched learner consistent on $\mathcal P$, every
  $\nu\in\mathcal P$ and every arm $a$ with positive gap: for every $c<1/K_a$, eventually in
  $\ell$, $c<\mathbb E[N_a(t_\ell)]/\log t_{\ell+1}$. *Differences with `lem:onebatch`:* none
  beyond the conventions (liminf written with $c<1/K_a$; $\mathcal K_{\inf}$ in primal form).
- **`lower_liminf_of_tendsto_ratio_one`.** On every grid whose ratios tend to 1, for every such
  learner, $\nu$ and $a$: for every $c<1/K_a$, eventually $c<\mathbb E[N_a(t_\ell)]/\log t_\ell$.
  *Differences with `thm:lower`(i):* none (its "on every grid" remark is `one_batch_ahead`).
- **`lower_limsup`.** For every $x\ge1$ and every grid whose ratios tend to $x$, every such learner,
  $\nu$, $a$: for every $c<x^2/K_a$, frequently $c<\mathbb E[N_a(t_\ell)]/\log t_\ell$, i.e.
  $\limsup\ge x^2/K_a$. *Differences:* it is `thm:main`(a) first claim verbatim; for `thm:lower`(ii)
  (first claim) it is the case $x>1$, and it adds the case $x=1$, which the paper also asserts in
  `thm:main`(a).
- **`lower_liminf`.** Same hypotheses, plus "$x=1$, or $\mathbb E[N_a(t_\ell)]=O(\log t_\ell)$":
  for every $c<x^2/K_a$, eventually $c<\mathbb E[N_a(t_\ell)]/\log t_\ell$. *Differences:*
  `thm:main`(a) second claim, "counts logarithmic" read for the arm $a$ (as in `thm:lower`(ii));
  it contains `thm:lower`(i) (for $x=1$) and `thm:lower`(ii) second claim (for $x>1$).
- **`lower_regret_liminf`.** For every $x\ge1$, every grid with ratios $\to x$, every such learner
  and $\nu$, if $x=1$ or every arm of positive gap has $\mathbb E[N_c(t_\ell)]=O(\log t_\ell)$:
  for every $c'<C_x$, eventually $c'<\mathfrak R(t_\ell)/\log t_\ell$. *Differences with
  `thm:lower`(iii):* "$x>1$ and logarithmic" replaced by the equivalent "logarithmic" (given
  $x\ge1$).
- **`lower_regret_limsup`.** For every $x\ge1$, every grid with ratios $\to x$, every such learner
  and $\nu$: for every $c'<C_x$, frequently $c'<\mathfrak R(t_\ell)/\log t_\ell$. *Differences
  with `thm:main` (regret):* none.
- **`hy_infoModel_zero`.** For every $w_0\ge0$, $\beta\ge2$, the family of algorithms
  `g ↦ hy w₀ β g` is in `InfoModel 0`: each is batched on its grid, and at a round of batch
  $\ell+1$ of two grids that agree on $t_1,\dots,t_\ell$ the two policies coincide. *Differences
  with `thm:main`(b):* the claim "HY is a learner of $\mathcal M_0$", for every $w_0\ge0$,
  $\beta\ge2$ (the defaults are $1$, $2$); "knows neither the grid nor the instance" is this
  property plus the fact that the definition of `hy` uses no instance.
- **`hy_isConsistent`.** For every grid with ratios $\to x\ge1$ and every $w_0\ge0$, $\beta\ge2$,
  `hy w₀ β g` is consistent at the batch ends of `g` on `unitBandits α`. *Differences with
  `thm:upper`:* none (general $w_0$, $\beta$ as its last sentence).
- **`hy_tendsto_count`.** Same, for $\nu\in\mathcal P$ and $a$ of positive gap:
  $\mathbb E[N_a(t_\ell)]/\log t_\ell\to x^2/K_a$ under `hy w₀ β g`. *Differences:* none.
- **`hy_tendsto_regret`.** Same, for $\nu\in\mathcal P$: $\mathfrak R(t_\ell)/\log t_\ell\to C_x$
  under `hy w₀ β g`. *Differences:* none (the theorem's arm $a$ is not used by this claim).

## Open problems

- **Rational and real suprema in HY's $\mathcal K_{\inf}$.** `HY.pseudoKinf` takes the dual
  supremum over rational $\lambda$ (the paper's remark in `def:kinf`). Its equality with the real
  supremum for rewards in $[0,1]$, and with the primal `dInf` of the pseudo-empirical law, is not
  proved in this pull request; `prove` will need it (lemma `lem:kinf` and the dual formula). It
  does not affect the statements' meaning on runs, whose rewards lie in $[0,1]$ almost surely.
- **Theorem `thm:lower`(ii) is not frozen with its own hypothesis $x>1$** (modelling decision 9).
  If a separate statement is wanted, its satisfiability witness can only come after
  `hy_isConsistent` is proved, from HY on the grid $\mathsf D_2$ ($x=2$).
- **Proof-internal definitions** (`def:stacks`, `def:empkinf`, `def:tilt`, `def:Q`,
  `def:backlog`, `def:water`, `def:constA`, `def:ranksA`, `def:H`, `def:evA`, `def:constC`,
  `def:ranksC`, `def:evC`, `def:amb`, `def:high`, `def:hy-vocab`) are not defined: proof pull
  requests add only lemmas and theorems, so `prove` will either write them inline or ask for a
  statements pull request.
- **Lemma `lem:twobatches`(i) (the form with tightness in probability) and Lemmas `lem:tilts`,
  `lem:com`, `lem:typ` are not formalised** (prove, 2026-11-17): the Lean route to
  `lem:twobatches`(ii) (`formalisation.tex`, `flem:twobatches`) does not use them. It replaces the
  boundary tilt and the typical values of the log-likelihood ratios by a one-sided change of
  measure (`flem:com-one-sided`: $\rho^-\ge(1-s)\rho^+$ costs a factor $1-s$ per pull of $a$ in
  batch $\ell+1$) and multiplicative data processing (`flem:dp`); no concentration is needed. The
  paper uses part (i) only to prove part (ii).
