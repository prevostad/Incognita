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
| lem:kinf | lemma | Incognita.BatchedBandits.HY.pseudoKinf_le_ofReal_log, Incognita.BatchedBandits.HY.pseudoKinf_eq_zero_of_le_pseudoMean, Incognita.BatchedBandits.HY.pseudoKinf_mono, Incognita.BatchedBandits.HY.ofReal_sq_div_eight_le_pseudoKinf, Incognita.BatchedBandits.HY.pseudoKinf_le_pseudoKinf_sub_add, Incognita.BatchedBandits.log_le_log_one_sub_mul | (i)–(vi) in that order, for the pseudo-empirical laws $\tilde\nu_c$ of HY (`HY.pseudoKinf`, any $w_0\ge0$; $w_0=0$ is the empirical law), rewards in $[0,1]$, level $\mu\in[0,1)$, $N_c+w_0>0$; (v) written $\mathcal K_{\inf}(\mu)\le\mathcal K_{\inf}(\mu-\varepsilon)+\varepsilon/(1-\mu)$ in `ℝ≥0∞`; "$\kappa$ non-decreasing" of (i) not stated; for a general law $G$ (needed by `lem:lowerdev`, `lem:upperdev`) not formalised. P006 froze `kinf_bounds`, `kinf_bounds_of_gap_pos` (primal form) |
| lem:pseudo | lemma | Incognita.BatchedBandits.HY.pseudoKinf_zero_le, Incognita.BatchedBandits.HY.mul_pseudoKinf_le, Incognita.BatchedBandits.HY.pseudoMean_le_pseudoMean_zero, Incognita.BatchedBandits.HY.pseudoMean_zero_sub_le_pseudoMean, Incognita.BatchedBandits.HY.pseudoMean_zero_sub_le_of_le | (i), (ii), (iii) (two inequalities), last claim; $G$ is the empirical law of the history (`w₀ = 0`); (ii) in `ℝ≥0∞` with $w_0\kappa(\mu)$ as `ofReal` |
| lem:hoeffding | lemma | Incognita.measureReal_add_le_sum_range_le, Incognita.measureReal_sum_range_le_sub_le, Incognita.measure_exists_ge_abs_div_sub_gt_le | (a) upper and lower tails, (b); for independent variables in $[0,1]$ with a common mean (weaker than i.i.d.) |
| lem:grid | lemma | Incognita.BatchedBandits.exists_dualGrid_le_sum_log, Incognita.BatchedBandits.dualGrid_mem, Incognita.BatchedBandits.dualGridSize_le | the hypothesis $n\mathcal K_{\inf}(\widehat G,r)\ge z\ge2$ is used as "some $\lambda$ has $F(\lambda)\ge z-1$", which it implies; stated with $z'=z-1\ge1$ |
| lem:sums | lemma | Incognita.BatchedBandits.Grid.sum_mul_rpow_le, Incognita.BatchedBandits.Grid.rpow_neg_div_le, Incognita.BatchedBandits.Grid.sum_mul_one_add_log_rpow_le, Incognita.BatchedBandits.sum_ceil_sub_mul_le, Incognita.BatchedBandits.le_sum_mul_ite_exists, Incognita.BatchedBandits.Grid.sum_mul_log_pow_four_le, Incognita.BatchedBandits.Grid.sum_mul_rpow_le_one_add, Incognita.BatchedBandits.sum_range_le_add_integral, Incognita.BatchedBandits.integral_exp_neg_mul_rpow_inv | (i), (ii), (iv), (v), (vi); the sums over $\ell\ge2$ as partial sums over `Finset.Ico 2 L` for every `L`; (iv) with the finite sum $\sum_{n<v_j}$ in place of the series (stronger), $g\ge0$ not needed; (v) for each $i$ with $E_i$ in place of the maximum; (iii) for the partial sums of the series, with $f$ integrable on $(0,\infty)$ |
| lem:diag | lemma | Incognita.BatchedBandits.Grid.exists_seq_tendsto_zero_div_log_t, Incognita.BatchedBandits.exists_seq_tendsto_zero_div_tendsto_zero | for every $f$ (the hypothesis $f\ge0$ is not needed) |
| lem:distinct | lemma | Incognita.BatchedBandits.sum_ite_le_sum_Icc_of_monotone, Incognita.BatchedBandits.sum_ite_sub_le_of_monotone | general form: a nondecreasing sequence $N_j$ of integers (the counts $N_a(t_j)$ of a run), sums over `Finset.Ico 2 (L + 1)` |
| lem:chain | lemma | Incognita.BatchedBandits.exists_le_mul_or_forall_le_mul_of_monotone | "every $j'\ge\max S$" written "every $j'$ that bounds $S$" |
| lem:single | lemma | Incognita.BatchedBandits.measure_exists_le_sum_log_le, Incognita.BatchedBandits.measure_exists_le_sum_log_le', Incognita.BatchedBandits.measureReal_le_sum_log_le, Incognita.BatchedBandits.integral_exp_mul_log_le_one | the event $\{n\mathcal K_{\inf}(\hat\nu_n,r)\ge z\}$ written as the larger event "some $\lambda\in[0,\frac1{1-r})$ has $F(\lambda)\ge z-1$"; for independent variables in $[0,1]$ with a common mean; only $r<1$ is used (the paper's $r<m$ is implied by $2\eta r\le m-r$ for $\eta>0$) |
| lem:pair | lemma | Incognita.BatchedBandits.measure_exists_le_sum_log_le_and_le_sum, Incognita.BatchedBandits.integral_exp_mul_log_add_le_one | same event as `lem:single`; for independent variables in $[0,1]$, with the moment conditions for each variable (the paper's $\Phi_\nu$, $\Psi_\nu$ for an i.i.d. stack) |
| lem:theta | lemma | Incognita.BatchedBandits.exists_tilt, Incognita.BatchedBandits.exp_mul_integral_exp_le_one_and_le_one_sub, Incognita.BatchedBandits.half_mul_min_log_pos_and_min_pos | (i), (ii); for a random variable $Y\in[0,1]$ with mean $m<\mathbf m^\star<1$ (the law $\nu$ of an arm); (ii) assumes $\Phi^\star,\Psi^\star>0$ (the paper's Step 3 proves them from $\PP(Y<1)>0$) and holds for every $\varepsilon\le\varepsilon_\theta$ |
| lem:lowerdev | lemma | Incognita.BatchedBandits.measure_forall_sum_log_le_le, Incognita.BatchedBandits.log_one_sub_mul_mem | for every $\lambda$ in place of an $\varepsilon'/4$-optimal one, with the event "every $\lambda''$ has $F(\lambda'')\le N(\E_\nu[\log(1-\lambda(Y-\mu))]-3\varepsilon'/4)$", which contains $\{\mathcal K_{\inf}(\hat\nu_N,\mu)\le\mathcal K_{\inf}(\nu,\mu)-\varepsilon'\}$ for an $\varepsilon'/4$-optimal $\lambda$; independent variables of law $\nu$ on $[0,1]$ |
| lem:upperdev | lemma | Incognita.BatchedBandits.measure_exists_add_le_sum_log_le, Incognita.BatchedBandits.log_sub_log_le_abs_div | for every upper bound $K$ of the dual formula of $\mathcal K_{\inf}(\nu,\mu)$, with the event "some $\lambda$ has $F(\lambda)\ge n(K+7\varepsilon'/8)$", which contains $\{\mathcal K_{\inf}(\hat\nu_n,\mu)\ge\mathcal K_{\inf}(\nu,\mu)+\varepsilon'\}$ |
| def:empkinf | definition | (proof-internal, not defined) | the empirical $\mathcal K_{\inf}$ is `HY.pseudoKinf`; $\Phi$, $\Psi$ are proof-internal |
| lem:tilts, lem:com, lem:typ | lemma | (not formalised) | not needed by the Lean route to `lem:twobatches`(ii), see `flem:twobatches` of `formalisation.tex` and the Open problems |
| def:tilt, def:Q | definition | (proof-internal, not defined) | |
| lem:imedround | lemma | Incognita.BatchedBandits.HY.imedIndex_imedArm_lt, Incognita.BatchedBandits.HY.imedKinf_imedArm_ne_top, Incognita.BatchedBandits.HY.mul_toReal_imedKinf_add_lt, Incognita.BatchedBandits.HY.imedKinf_leader, Incognita.BatchedBandits.pullCount_le_max_of_forall, Incognita.BatchedBandits.hyAlg_ae_pullCount_le_max, Incognita.BatchedBandits.ae_feedback_mem_Icc | Steps 1–2 for one round of `HY.imedArm` on a history with rewards in $[0,1]$ (the claim $\tilde K_\ell(c)<\infty$ for $N_c(t-1)\ge1$); the consequence (Step 3) for any sequence of actions, with $g(k)=y_\ell\log(k+1)$, and along almost every run of HY on an instance of $\mathcal P$ (`hyAlg_ae_pullCount_le_max`, for $w_0\ge0$, with $\tilde K_\ell(c)\ge D>0$ frozen at $t_\ell$) |
| lem:service | lemma | Incognita.BatchedBandits.pullCount_le_max_target, Incognita.BatchedBandits.pullCount_sub_le_target, Incognita.BatchedBandits.backlog_le, Incognita.BatchedBandits.target_sub_le_pullCount, Incognita.BatchedBandits.card_le_card_filter_not_mem, Incognita.BatchedBandits.backlog_step, Incognita.BatchedBandits.backlog_lindley, Incognita.BatchedBandits.two_mul_min_ceil_sub_le, Incognita.BatchedBandits.HY.pullCount'_pacedArm_lt_target, Incognita.BatchedBandits.HY.target_le_pullCount'_of_pacedArm_eq, Incognita.BatchedBandits.hyAlg_ae_paced_rule, Incognita.BatchedBandits.hyAlg_ae_backlog_le, Incognita.BatchedBandits.hyAlg_ae_backlog_le_of_le, Incognita.BatchedBandits.HY.two_mul_target_sub_le | abstract form: any sequence of actions in which a pulled non-leader has a demand and the leader is pulled only when no non-leader has one (HY's paced rule; the order is not used), nondecreasing targets at most $B=U_{\ell+1}+K-1$; (b) with the slow arrivals of Step (b2) as a hypothesis, and Step (b2) proved for one target $\min(U,\lceil f\log t\rceil)$ (`two_mul_min_ceil_sub_le`); one round of `HY.pacedArm` satisfies the two hypotheses, and so does almost every run of HY in a paced phase (`hyAlg_ae_paced_rule`, with the statistics frozen at $t_\ell$, `flem:frozen`); (b) along almost every run of HY under the paper's condition $s_\ell\log s_\ell\ge2(K-1)U_{\ell+1}$, with $\vartheta_\ell\ge0$, $(1+\omega_\ell)y_\ell\ge0$, $s_\ell\ge2$, $K\ge2$ (`hyAlg_ae_backlog_le_of_le`); (a) and (c) along a run follow from the abstract lemmas and `hyAlg_ae_paced_rule` (not stated separately) |
| lem:W | lemma | Incognita.BatchedBandits.log_pullCount_le_index, Incognita.BatchedBandits.log_div_card_le_index, Incognita.BatchedBandits.HY.imedIndex_imedArm_le, Incognita.BatchedBandits.hyAlg_ae_log_pullCount_le_imedIndex, Incognita.BatchedBandits.hyAlg_ae_log_le_imedIndex, Incognita.BatchedBandits.hyAlg_ae_log_le_imedIndex', Incognita.BatchedBandits.hyAlg_ae_one_le_pullCount, Incognita.BatchedBandits.hyAlg_ae_mul_log_pullCount_le_imedIndex | Steps 1–2 in abstract form: for any sequence of actions and indices $I_t(c)$ nondecreasing in $t$, minimised by the arm pulled at an IMED round and at least $y\log N_c(t-1)$ ($y\ge0$), (W2) at the IMED rounds and $\min_cI_{t_j+1}(c)\ge y\log((s_{j-1}-t_{j-1})/K)$ (given $N_c(t_{j-1})\ge1$); Steps 1–2 along almost every run of HY (`hyAlg_ae_log_pullCount_le_imedIndex`, `hyAlg_ae_log_le_imedIndex`, for a batch $\ell+1$, $\ell\ge1$, with the indices $J_\ell=y_\ell I$; every count at $t_\ell$ is at least $1$, `hyAlg_ae_one_le_pullCount`); (i), (W2) at every round, along almost every run for a batch that is not activated or satisfies the third condition defining $\ell_W$ (`hyAlg_ae_mul_log_pullCount_le_imedIndex`; Step 3 only needs $N_c(t_\ell)\le t_\ell$); the rank $\ell_W$ itself is not formalised |
| lem:sparse | lemma | Incognita.BatchedBandits.Grid.card_activated_le, Incognita.BatchedBandits.Grid.sum_activated_le, Incognita.BatchedBandits.Grid.mul_logEnd_lt_logEnd_succ | the count for every finite set of such batches (the paper's $k\ge1$ is not needed); the sum with bounds $M_k$ of $f$ on the blocks in place of the suprema, over the blocks below $2^\kappa$; Step 1 for every $\vartheta$ |
| def:backlog, def:water | definition | (proof-internal, not defined) | |
| def:constA, def:ranksA, def:H, def:evA | definition | (proof-internal, not defined) | |
| lem:H | lemma | Incognita.BatchedBandits.Grid.tendsto_iSup_ratio_sq_mul_logEnd_div, Incognita.BatchedBandits.tendsto_iSup_Icc_div_of_tendsto | the limit at the batch ends, $\mathsf H_j/\mathsf L_j\to x^2$, with $\mathsf H_j$ written inline as `⨆ k : Finset.Icc 1 j, g.ratio (k - 1) ^ 2 * g.logEnd k`; the limit over all rounds, $\mathsf H(t)/\log t\to x^2$, not formalised |
| lem:ranksA | lemma | Incognita.BatchedBandits.Grid.logEnd_add_le_pow_mul, Incognita.BatchedBandits.Grid.eventually_two_le_imedEnd_and_le_t_sub_imedEnd, Incognita.BatchedBandits.eventually_mul_rpow_add_one_le_exp, Incognita.BatchedBandits.Grid.eventually_ratio_le, Incognita.BatchedBandits.Grid.eventually_le_mul_logEnd_rpow, Incognita.BatchedBandits.Grid.eventually_add_mul_logEnd_le_netSize, Incognita.BatchedBandits.Grid.eventually_le_netSize, Incognita.BatchedBandits.Grid.eventually_le_mul_logEnd, Incognita.BatchedBandits.Grid.tendsto_hyGamma, Incognita.BatchedBandits.Grid.eventually_threshold_ge | (R3) for margins $\gamma_\ell\to0$ (the default ones, `Grid.tendsto_hyGamma`), $x>0$, $\eta>0$ and any constant in place of $w_0\kappa(\mathbf m^\star+\bar\varepsilon)$; (T3) as $C\le U_\ell$ and $C\le D\mathsf L_\ell$ for large $\ell$; the last claim, $\mathsf L_{k+i}\le x_+^i\mathsf L_k$ when $x_j\le x_+$ for $j>k$; Step 2, (R2) for every large batch with the default $\vartheta$ when $x>1$ (`Grid.eventually_two_le_imedEnd_and_le_t_sub_imedEnd`, for every $\beta$ and every number of arms; it gives the structural hypotheses of `hyAlg_ae_pullCount_le_max_target_and_netSize_le_sub` and the lemmas after it); (R1) $x_\ell\le x_+$ for any $x_+>x$, (T1)-(T2) ($C\le D\mathsf L_\ell^{\beta-1}$, $D>0$, $\beta>1$) and (T4) ($K+1+C\mathsf L_{\ell+1}\le U_{\ell+1}$) for every large $\ell$; the ranks themselves (Definition `def:ranksA`, proof-internal) are not formalised: each condition is a statement "for every large $\ell$" |
| lem:constA | lemma | Incognita.BatchedBandits.iSup_integral_add_lt_one_and_integral_add_lt_sub, Incognita.BatchedBandits.exists_tilt_moment_le | (a) for every $\varepsilon\in(0,\min(\Delta/5,(1-\mathbf m^\star)/2)]$, $\Delta$ any lower bound of the positive gaps and $\mathbf m_2\le\mathbf m^\star-\Delta$; (c), the moment conditions of `lem:pair` for the law of one sub-optimal arm (a tilt $\theta>0$, $c_\theta>0$, $\varepsilon_\theta>0$; every $\varepsilon\le\varepsilon_\theta$, level $r\le\mathbf m^\star+\varepsilon$ and gain $\eta\ge0$ with $2\eta\kappa(r)\le c_\theta$), from `lem:theta`; the deviation inequalities of (b)-(c) are used through `lem:single`, `lem:pair` in the bounds of `lem:probasA`(b); (d) is not formalised (it needs `lem:kinf`(v) for the law $\nu_a$, which is formalised only for the pseudo-empirical laws) |
| lem:sumsA | lemma | Incognita.BatchedBandits.Grid.sum_netSize_mul_le, Incognita.BatchedBandits.Grid.sum_batch_mul_le, Incognita.BatchedBandits.Grid.netSize_le_one_add_rpow | (a), for nonnegative numbers $p_k\le C\,U_k^4t_{k+1}^{-(1+\eta)}$ on $[k_0,L)$, $k_0\ge1$ (the bound of `lem:probasA`(b) on $\PP(\mathcal V_k)+\PP(\Pi_k)$, $C=(1+K)C_\eta$), partial sums, $\beta\ge1$; (b) for numbers $a_i\le c\,e^{-\varepsilon^2\mathsf L_{i-2}^\beta}$ (the bound on $\PP(\mathcal A_{i-1}^c)+\PP(\mathcal A_i^c)$, $c=2c_{\mathcal A}(\varepsilon)$) and $v_i\le C\,U_i^4t_{i+1}^{-(1+\eta)}$, with $\mathsf L_{i+1}\le x_+^3\mathsf L_{i-2}$ and any bound $S\ge\sup_{y\ge0}(2x_+^3y-\varepsilon^2y^\beta)$ as hypotheses: $\sum B_{i+1}(a_i+v_i)\le(c/2)e^S+C\sigma_{4\beta}(\eta)$ |
| lem:probasA | lemma | Incognita.BatchedBandits.measure_exists_wellSampled_abs_sub_gt_le, Incognita.BatchedBandits.measure_lt_mul_pseudoKinf_le, Incognita.BatchedBandits.measure_lt_mul_pseudoKinf_and_le_le, Incognita.BatchedBandits.measure_le_pullCount_pseudoKinf_lt_le, Incognita.BatchedBandits.measure_le_pullCount_lt_pseudoKinf_le | (b) for the traces of $\mathcal V$ ($\le C_\eta U^3e^{-(1+2\eta)z}$) and of $\Pi$ for one sub-optimal arm ($\le C_\eta U^4e^{-(1+2\eta)z}$), with the hypotheses of `lem:constA`(b)-(c) (the gain $2\eta r\le m-r$; the moment conditions of `lem:pair` for $\nu_c$) and any level $z>0$; the paper's $t_{\ell+1}^{-(1+\eta)}$ is then $e^{-(1+2\eta)z_\ell}$ with (R3); (a) and (c), for the traces of the events on the run at a cutoff $t$ (the event at the count $N_c(t)$; each trace is contained in the paper's event on the stacks), for every learner; (a) $\le K\cdot2e^{-\varepsilon^2U}/(1-e^{-2\varepsilon^2})=c_{\mathcal A}(\varepsilon)e^{-\varepsilon^2U}$; (c) for $\mathcal L$ with the level $A-3\varepsilon'/4$, $A=\E_{\nu_a}[\log(1-\lambda(Y-\mu))]$ for any $\lambda$ (the paper's $\Delta_\varepsilon$ for an $\varepsilon/4$-optimal $\lambda$), and for $\mathcal U$ with any upper bound $K^+$ of the dual formula of $\Kinf(\nu_a,\mu)$; bounds $e^{-\rho'u}/(1-e^{-\rho'})$ and $n_ge^{-\rho'u}/(1-e^{-\rho'})$ (the paper's $C_{\mathcal{LU}}(\varepsilon)e^{-r_\varepsilon u}$ for each event); `lem:constA`(b)-(c) themselves (the existence of the gain $\eta$ and of the tilt) are not formalised |
| lem:stacks | lemma | Incognita.BatchedBandits.HY.pseudoMean_zero_history_eq, Incognita.BatchedBandits.sum_comp_rewardByCount_eq, Incognita.BatchedBandits.HY.pseudoLogMean_zero_history_eq | the stacks are LML's rewards by count `rewardByCount A R c m` on `P.prod (streamMeasure ν)` (independent, of law $\nu_c$: LML's `iIndepFun_rewardByCount_add_one_action`, `hasLaw_rewardByCount_add_one`); on a run, the empirical mean and the dual function of the empirical $\Kinf$ of $c$ at $t$ are those of the first $N_c(t)$ rewards of its stack |
| lem:structA | lemma | Incognita.BatchedBandits.hyAlg_ae_pullCount_le_max_target_and_netSize_le_sub, Incognita.BatchedBandits.hyAlg_ae_le_pullCount_mul_testKinf_of_two_mul_pullCount_lt, Incognita.BatchedBandits.hyAlg_ae_netSize_le_two_mul_pullCount_reference, Incognita.BatchedBandits.hyAlg_ae_netSize_le_pullCount_or_le_mul_log, Incognita.BatchedBandits.hyAlg_ae_min_netSize_le_pullCount, Incognita.BatchedBandits.HY.target_sub_le_imp, Incognita.BatchedBandits.HY.le_target_sub, Incognita.BatchedBandits.HY.testKinf_reference | along almost every run, for a batch $\ell+1$ whose (R2) conditions are hypotheses (in place of $\ell\ge\ell_A-4$; "$\ell\in\mathrm{Act}$" follows from the length of the paced phase), with $\vartheta_\ell\ge0$, $(1+\omega_\ell)y_\ell\ge0$ ($\omega_\ell\ge0$ for (S4)), $K\ge2$; the leader, the threshold and the targets frozen at $t_\ell$ given as `L`, `thr`, `tgt`; (S1)-(S2) `hyAlg_ae_pullCount_le_max_target_and_netSize_le_sub` (any environment), (S3) `hyAlg_ae_le_pullCount_mul_testKinf_of_two_mul_pullCount_lt` (with $N\hat K_\ell\ge h_\ell$, "rejected", in `ℝ≥0∞`), "in particular $r_\ell\in W_{\ell+1}$" `hyAlg_ae_netSize_le_two_mul_pullCount_reference` (on $\mathcal P$), (S4) without division `hyAlg_ae_netSize_le_pullCount_or_le_mul_log` ($N_c\ge U_{\ell+1}$ or $N_c\kappa(\hat\mu_\ell)\ge y_\ell\mathsf L_{\ell+1}$, which also covers $\kappa=0$) and in the paper's form `hyAlg_ae_min_netSize_le_pullCount` (with `x / 0 = 0`) |
| lem:thrA | lemma | Incognita.BatchedBandits.hyAlg_ae_threshold_eq, Incognita.BatchedBandits.HY.threshold_eq_of_forall | along almost every run, for $\ell\ge2$ with (R2) at $\ell$ as hypotheses and $\omega_{\ell-1}\ge0$: `HY.threshold … = g.logEnd ℓ`, so $h_\ell=(1-\gamma_\ell)y_{\ell-1}\mathsf L_\ell$ |
| lem:leaderA | lemma | (see flem:leaderA-run) | proved along almost every run with the events of `def:evA` read on the run (`formalisation.tex`, `flem:leaderA-run`); the paper's $\mathbf m_2$ is any bound $\bar m$ of the sub-optimal means, its $z_\ell$ any $z$ with $z+w_0\kappa(\mathbf m^\star+\varepsilon)\le\bar h_{\ell-1}$, and the conditions of `lem:constA`(a) are hypotheses |
| lem:countsA | lemma | Incognita.BatchedBandits.hyAlg_ae_logEnd_div_log_le_pullCount | along almost every run, with (R2) at $\ell-1$, $\ell$ (paper's indices), (T1) $\kappa_\varepsilon\mathsf L_{\ell-1}^{\beta-1}\ge1$, $\mathbf m^\star+\varepsilon<1$ and the trace of $\mathcal A_{\ell-1}$ on the run (upper half: $\hat{\mathbf m}_c(t_{\ell-1})\le\mathbf m_c+\varepsilon$) as hypotheses; conclusion $N_c(t_\ell)\ge\mathsf L_{\ell-1}/\kappa_\varepsilon$ for every arm (stronger than $u_\ell(\varepsilon)=\mathsf L_{\ell-2}/\kappa_\varepsilon$); the second claim is the same lemma one index lower |
| lem:goodA | lemma | (see flem:goodA-run) | Steps 2-4 along almost every run, with the facts of Step 1 as hypotheses (`formalisation.tex`, `flem:goodA-run`) |
| lem:decompA | lemma | (see flem:decompA-run) | (a) Case 1 is `flem:goodA-run`, Cases 2-3 and (b) are `flem:decompA-run`; the combination of the three cases with the indicators of the events (eq:DA) is not stated (it needs the events on the stacks) |
| prop:dyA | proposition | (added by prove) | non-asymptotic bound for $x>1$; not frozen (not a headline) |
| def:constC, def:ranksC, def:evC, def:amb, def:high | definition | (proof-internal, not defined) | |
| lem:growth | lemma | Incognita.BatchedBandits.Grid.log_t_le_of_growth, Incognita.BatchedBandits.Grid.log_t_add_sub_le | the induction of the proof is `Grid.log_t_add_sub_le` |
| lem:lowmass | lemma | Incognita.BatchedBandits.exists_card_le_sum_low_le, Incognita.BatchedBandits.t_sub_eq_sum_pullCount_sub, Incognita.BatchedBandits.sum_Ico_pullCount_sub_le | abstract form: for any sequence of actions and water levels $\Lambda_i$ satisfying (W2) in the batches $[\ell_W,\ell)$ (the hypothesis that Lemma `lem:W`(i) provides for HY) |
| lem:levelC | lemma | Incognita.BatchedBandits.exists_rank_le_card_filter_le, Incognita.BatchedBandits.one_add_pow_le_exp | abstract form: on a grid with $x_\ell\to1$, a rank $L_0$ (depending on $g$, $m'$, $K$, $\ell_W$ and the grid) that works for every sequence $\Lambda$ with the conclusion of `lem:lowmass` |
| lem:highC | lemma | Incognita.BatchedBandits.HY.pseudoKinf_pos_and_le_mul_pseudoKinf | for the statistics of HY at the cutoff $t_{i-1}$, with (W1) at the level $v$ for the arm $c$ as a hypothesis ($N\tilde K_{i-1}(c)/y_{i-1}\ge v-\log N$, in `ℝ≥0∞`), $1\le N\le\bar N$ and $y_{i-1}\ge1$; conclusions in `ℝ≥0∞` |
| lem:constC, lem:decompC, lem:controlC, lem:sumC, lem:fewC, lem:optW, lem:pullsC, lem:amb | lemma | (added by prove) | |
| lem:goodhigh | lemma | Incognita.BatchedBandits.card_filter_lt_le_card | Step 2 only, in abstract form: for nondecreasing counts and leaders $L_i$ with $N_{L_i}(t_i)\ge u$ on a finite set of batches, at most $K$ of them have $N_{L_i}(t_{i-1})<u$; Steps 1 and 3 are not formalised |
| lem:logcountC | lemma | Incognita.BatchedBandits.hyAlg_ae_le_mul_pullCount_of_le_imedIndex | along almost every run, for one batch $i$ (Lean index `ℓ`, $i=\ell+1$) whose IMED index of the arm at its end is at least $y_{i-1}v$ (the water level $\Lambda_i\ge v$, with $v=(1-\delta)\mathsf L_j$ for a high batch) and whose IMED level is $\tilde{\mathbf m}^\star_{i-1}\le\rho<1$: $v\le(\kappa(\rho)+1)N_c(t_i)$ (then $\le(\kappa(\rho)+1)N_c(t_{j-1})$ for $i\le j-1$); the choice of a good high batch (`lem:goodhigh`) is not formalised |
| prop:fixedC | proposition | (added by prove) | non-asymptotic bound for $x=1$; not frozen (not a headline) |
| lem:onebatch | lemma (general form) | Incognita.BatchedBandits.eventually_lt_integral_pullCount_div_log_t_succ | proved; route in `formalisation.tex` (Bretagnolle–Huber in place of data processing; the strict primal formula in place of `lem:kinf`(v) and `lem:primal`) |
| thm:lower | theorem, (i) (general form) | Incognita.BatchedBandits.eventually_lt_integral_pullCount_div_log_t | proved on every grid (the hypothesis $x_\ell\to1$ is not used) |
| thm:lower | theorem, (ii) second claim (general form) | Incognita.BatchedBandits.eventually_lt_integral_pullCount_div_log_t_of_isBigO | proved for every $x>0$; first claim through `lower_limsup` (Case B: `flem:caseB`) |
| thm:lower | theorem, (iii) (general form) | Incognita.BatchedBandits.eventually_lt_regret_div_log_t_of_forall | from the per-arm bounds; $x=1$: `flem:regret-one` |
| lem:twobatches | lemma, (ii) (general form) | Incognita.BatchedBandits.eventually_lt_integral_pullCount_div_log_t_add_two | proved at the index $\ell+1$, by the route `flem:twobatches` of `formalisation.tex`; (i) not formalised (not needed) |
| thm:main | theorem, (b) first claim (general form) | Incognita.BatchedBandits.infoModel_zero_hy | proved for all real $w_0$, $\beta$ |
| flem:masked-law | lemma (formalisation.tex) | Incognita.BatchedBandits.map_history_ite_lt_eq, Learning.IsAlgEnvSeq.isAlgEnvSeqUntil_ite_lt | "the actions up to $t_{\ell+1}$ are $\mathcal H_\ell$-measurable" of `sec:app-lower`, as an equality of laws |
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
| flem:alt-laws | lemma (formalisation.tex) | Incognita.BatchedBandits.exists_unitLaws_mean_mem_Ioo, Incognita.BatchedBandits.mix_mem_unitLaws, Incognita.klDiv_mix_le, Incognita.BatchedBandits.exists_two_alternatives | the alternative instances $\kappa^+,\kappa^-$ (replaces `lem:tilts`) |
| flem:twobatches-finite | lemma (formalisation.tex) | Incognita.BatchedBandits.pow_mul_exp_neg_le_integral_pullCount_div_add | the finite-horizon inequality two batches ahead |
| flem:twobatches | lemma (formalisation.tex) | Incognita.BatchedBandits.eventually_lt_integral_pullCount_div_log_t_add_two, Incognita.BatchedBandits.mul_log_t_add_two_lt_integral_pullCount, Incognita.BatchedBandits.mul_lt_of_mul_neg_add_neg_div_le, Incognita.BatchedBandits.two_mul_integral_pullCount_div_add_le_rpow_div | `lem:twobatches`(ii) |
| flem:upper-assembly | lemma (formalisation.tex) | Incognita.BatchedBandits.isBigO_log_t_of_eventually_div_lt, Incognita.BatchedBandits.isConsistentAtBatchEnds_of_isBigO, Incognita.BatchedBandits.isConsistentAtBatchEnds_of_upper, Incognita.BatchedBandits.tendsto_div_log_t_of_upper, Incognita.BatchedBandits.tendsto_regret_div_log_t_of_tendsto, Incognita.BatchedBandits.hy_isConsistent_of_upper, Incognita.BatchedBandits.hy_tendsto_count_of_upper, Incognita.BatchedBandits.hy_tendsto_regret_of_upper | the proof of `thm:upper` after the upper bounds: the three frozen statements of `thm:upper` from the $\limsup$ bound for HY |
| flem:frozen | lemma (formalisation.tex) | Incognita.BatchedBandits.HY.count_history, Incognita.BatchedBandits.HY.pseudoMean_history, Incognita.BatchedBandits.HY.pseudoKinf_history, Incognita.BatchedBandits.HY.leader_history, Incognita.BatchedBandits.HY.imedKinf_history, Incognita.BatchedBandits.HY.reference_history, Incognita.BatchedBandits.HY.testKinf_history, Incognita.BatchedBandits.HY.threshold_history, Incognita.BatchedBandits.HY.target_history, Incognita.BatchedBandits.HY.imedIndex_history, Incognita.BatchedBandits.HY.imedIndex_history_mono, Incognita.BatchedBandits.hyAlg_ae_action_eq, Incognita.BatchedBandits.HY.next_of_imedPhase, Incognita.BatchedBandits.HY.next_of_pacedPhase, Incognita.BatchedBandits.hyAlg_ae_imedIndex_action_le | the statistics of HY at a batch end are frozen along a run; the actions of a run are HY's rule |
| flem:rational-sup | lemma (formalisation.tex) | Incognita.BatchedBandits.HY.pseudoKinf_eq_iSup_real, Incognita.BatchedBandits.HY.ofReal_pseudoLogMean_le_pseudoKinf, Incognita.BatchedBandits.HY.continuousAt_pseudoLogMean, Incognita.BatchedBandits.HY.pseudoKinf_le_of_forall | the remark of `def:kinf`: the rational and real suprema of HY's dual formula agree (first Open problem below, now proved) |
| flem:regret-caseB | lemma (formalisation.tex) | Incognita.BatchedBandits.frequently_lt_regret_div_log_t_of_not_isBigO | the regret `limsup` when some count is not logarithmic |
| flem:leaderA-run | lemma (formalisation.tex) | Incognita.BatchedBandits.hyAlg_ae_integral_leader_eq_iSup, Incognita.BatchedBandits.hyAlg_ae_pseudoMean_reference_le, Incognita.BatchedBandits.HY.reference_spec, Incognita.BatchedBandits.HY.pseudoMean_le_leader, Incognita.BatchedBandits.HY.ofReal_le_mul_pseudoKinf_zero_add | `lem:leaderA` with the events read on the run; Lean indices: the paper's $\ell$ is `ℓ + 2` |
| flem:goodA-run | lemma (formalisation.tex) | Incognita.BatchedBandits.hyAlg_ae_le_mul_testKinf_and_pullCount_le_max, Incognita.BatchedBandits.HY.testKinf_le_imedKinf, Incognita.BatchedBandits.HY.target_le_of_rejected, Incognita.BatchedBandits.hyAlg_ae_pullCount_le_max' | `lem:goodA`, Steps 2-4; `hyAlg_ae_pullCount_le_max'` is `lem:imedround` along a run with $\tilde K_\ell(c)\ge D$ in `ℝ≥0∞`; Lean indices: the paper's $\ell$ is `ℓ + 1` |
| flem:decompA-run | lemma (formalisation.tex) | Incognita.BatchedBandits.hyAlg_ae_net_le, Incognita.BatchedBandits.pullCount_le_add_sub, Incognita.BatchedBandits.le_max_add_sum_of_step | `lem:decompA`(a) Cases 2-3 and (b) |

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
  supremum for rewards in $[0,1]$ and a level $\mu\in[0,1)$ is proved (prove, 2026-11-18:
  `HY.pseudoKinf_eq_iSup_real`, `flem:rational-sup`); its equality with the primal `dInf` of the
  pseudo-empirical law is not proved (the upper bound uses only the dual formula). It does not
  affect the statements' meaning on runs, whose rewards lie in $[0,1]$ almost surely.
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
