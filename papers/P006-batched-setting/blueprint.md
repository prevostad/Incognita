# Blueprint of P006-batched-setting

Lean names of the paper's nodes. Statuses are computed by the audit, not stored here.

| Label | Kind | Lean name | Notes |
|---|---|---|---|
| def:instance | definition | Incognita.BatchedBandits.unitLaws, Incognita.BatchedBandits.unitBandits | new; $\mathcal M$ and $\mathcal P$; $m(Q)$ = `Q[id]`, $m^\star$ = `⨆ a, (ν a)[id]`, $\Delta_c$ = `Bandits.gap ν c` (LML) |
| def:kinf | definition | LMLExplore.Bandits.dInf | reused: $\mathcal K_{\inf}(P,\mu)$ = `dInf unitLaws P μ`; KL = `InformationTheory.klDiv`; $\mathrm{kl}$ = `LMLExplore.klBer`; $\mathrm{Ber}(p)$ = `ProbabilityTheory.bernoulliMeasure (1 : ℝ) 0 p` |
| def:learner | definition | Learning.Algorithm, Learning.trajMeasure, Learning.Environment.bandit | reused (LML): `Algorithm Unit α ℝ`; $\pi_t$ = `alg.policy (t - 1)`; $\mathbb P_{\nu,\pi}$ = `trajMeasure alg (Environment.bandit ν)` |
| def:counts | definition | Learning.pullCount, Bandits.regret | reused (LML); $N_c(t)$ = `pullCount IT.action c t` (no shift); $\mathcal R_{\nu,\pi}(t)$ = `∫ ω, regret ν IT.action t ω ∂(trajMeasure …)` |
| lem:counts | lemma | (added by prove) | LML has `sum_pullCount`, `regret_eq_sum_pullCount_mul_gap`, `integral_regret_eq_sum_gap_mul_integral_pullCount` |
| def:seqcons | definition | LMLExplore.Bandits.IsConsistent | reused |
| def:grid | definition | Incognita.BatchedBandits.Grid, Incognita.BatchedBandits.Grid.batchOf, Incognita.BatchedBandits.Grid.IsFiner | new; `Grid K` takes the number of arms |
| def:logratio | definition | Incognita.BatchedBandits.Grid.logEnd, Incognita.BatchedBandits.Grid.ratio | new |
| lem:grid | lemma | (added by prove) | already in the library: `Grid.le_t`, `Grid.batchOf_eq_iff`, `Grid.t_batchOf_sub_one_le`, `Grid.lt_t_batchOf`, `Grid.log_two_le_logEnd`, `Grid.one_lt_ratio` |
| def:exgrids | definition | Incognita.BatchedBandits.Grid.sequential, Incognita.BatchedBandits.Grid.geometric, Incognita.BatchedBandits.Grid.doublyExp | new |
| def:batched | definition | Incognita.BatchedBandits.SeesRewardsUpTo, Incognita.BatchedBandits.IsBatched | new; "ignores the rewards" = `SeesRewardsUpTo alg n 0` |
| lem:mask | lemma | (added by prove) | |
| def:infomodel | definition | Incognita.BatchedBandits.InfoModel | new; `k : ℕ∞` |
| def:consistent | definition | Incognita.BatchedBandits.IsConsistentAtBatchEnds | new |
| lem:consist-regret | lemma | (added by prove) | |
| thm:main | frozen | Incognita.Statements.P006.infoModel_mono | (i), inclusions; proof: Incognita.P006.infoModel_mono |
| thm:main | frozen | Incognita.Statements.P006.infoModel_strict | (i), strictness; proof: Incognita.P006.infoModel_strict |
| thm:main | frozen | Incognita.Statements.P006.isBatched_iff_exists_infoModel_top | (i), components; proof: Incognita.P006.isBatched_iff_exists_infoModel_top |
| thm:main | frozen | Incognita.Statements.P006.isBatched_of_isFiner | (ii), batching; proof: Incognita.P006.isBatched_of_isFiner |
| thm:main | frozen | Incognita.Statements.P006.isConsistentAtBatchEnds_of_isFiner | (ii), consistency; proof: Incognita.P006.isConsistentAtBatchEnds_of_isFiner |
| thm:main | frozen | Incognita.Statements.P006.isBatched_sequential_iff | (iii), batching; proof: Incognita.P006.isBatched_sequential_iff |
| thm:main | frozen | Incognita.Statements.P006.isConsistentAtBatchEnds_sequential_iff | (iii), consistency; proof: Incognita.P006.isConsistentAtBatchEnds_sequential_iff |
| prop:kinf | frozen | Incognita.Statements.P006.kinf_eq_top_of_one_le | (i); proof: Incognita.P006.kinf_eq_top_of_one_le |
| prop:kinf | frozen | Incognita.Statements.P006.kinf_eq_zero_of_lt_mean | (ii); proof: Incognita.P006.kinf_eq_zero_of_lt_mean |
| prop:kinf | frozen | Incognita.Statements.P006.kinf_bounds | (iii); proof: Incognita.P006.kinf_bounds |
| prop:kinf | frozen | Incognita.Statements.P006.kinf_bernoulli | (iv); proof: Incognita.P006.kinf_bernoulli |
| prop:kinf | frozen | Incognita.Statements.P006.kinf_bounds_of_gap_pos | (v); proof: Incognita.P006.kinf_bounds_of_gap_pos |
| def:exlearners | definition | Learning.Algorithm.const, Incognita.BatchedBandits.reactAlg, Incognita.BatchedBandits.parityAlg | `Const_c` = `Algorithm.const (Measure.dirac c)` (LML, reused); `React`, `Par^{(k),g}` new; `RR`, `FL^g`, `UCB` not defined in this pull request (see Open problems); in place of `FL^g` as a witness that uses the rewards, the new learner `Incognita.BatchedBandits.firstRewardAlg` (not a node of the paper); $\mathcal P_c$ written inline as `{ν \| ν ∈ unitBandits α ∧ gap ν c = 0}` |
| prop:witnesses | witnesses | (not frozen) | the checks of the definitions (AGENTS.md 6.4), proved in `Incognita/BatchedBandits/` as lemmas; item by item below |
| cor:ucb | corollary | (not frozen) | see Open problems |
| cite:GMS19-lem1 | cited | LMLExplore.klBer_integral_le_klDiv | reused (LMLExplore), in the form used by the paper ($Z=\mathrm{id}$, laws on $[0,1]$); used only in the proof of prop:kinf(iii) |
| cite:ACF02-thm1 | cited | (not formalised) | used only by cor:ucb |
| lem:kl | lemma | LMLExplore.monotoneOn_klBer, LMLExplore.tendsto_klBer_nhdsGT, LMLExplore.klBer_self, LMLExplore.ofReal_two_mul_sq_le_klBer | reused (LMLExplore): monotonicity, right-continuity on $[p,1)$, $\mathrm{kl}(p,p)=0$, Pinsker |
| flem:infomodel-mono | lemma (formalisation.tex) | Incognita.BatchedBandits.InfoModel.mono | thm:main (i), inclusions |
| flem:grid-eq | lemma (formalisation.tex) | Incognita.BatchedBandits.Grid.eq_of_forall_one_le_t_eq | |
| flem:infomodel-top | lemma (formalisation.tex) | Incognita.BatchedBandits.infoModel_top_iff | $\mathcal M_\infty$ = families of batched learners |
| flem:components | lemma (formalisation.tex) | Incognita.BatchedBandits.isBatched_iff_exists_infoModel_top | thm:main (i), components; `Const_a` in place of `RR` |
| flem:strict | lemma (formalisation.tex) | Incognita.BatchedBandits.exists_infoModel_and_not_infoModel | thm:main (i), strictness, via `Par^{(k)}` |
| flem:last-end-finer | lemma (formalisation.tex) | Incognita.BatchedBandits.Grid.t_batchOf_sub_one_le_of_isFiner | |
| flem:batched-finer | lemma (formalisation.tex) | Incognita.BatchedBandits.IsBatched.of_isFiner | thm:main (ii), batching |
| flem:consistent-coarser | lemma (formalisation.tex) | Incognita.BatchedBandits.IsConsistentAtBatchEnds.of_isFiner | thm:main (ii), consistency |
| flem:batched-seq | lemma (formalisation.tex) | Incognita.BatchedBandits.isBatched_sequential_iff | thm:main (iii), batching |
| flem:seq-cons-of-ends | lemma (formalisation.tex) | Incognita.BatchedBandits.IsConsistentAtBatchEnds.isConsistent_of_sequential | thm:main (iii), consistency, (⇒); replaces the route through lem:consist-regret |
| flem:ends-of-seq | lemma (formalisation.tex) | LMLExplore.Bandits.IsConsistent.isConsistentAtBatchEnds | already in the library (`Incognita/BatchedBandits/Consistency.lean`); thm:main (iii), consistency, (⇐) |
| flem:kl-density | lemma (formalisation.tex) | Incognita.klDiv_le_ofReal_neg_log_of_smul_le | `Incognita/ForMathlib/InformationTheory/KullbackLeibler/Basic.lean`; $cP\le Q\Rightarrow\mathrm{KL}(P,Q)\le\log(1/c)$ |
| flem:kl-mixture | lemma (formalisation.tex) | Incognita.klDiv_le_ofReal_neg_log_smul_add_smul | $\mathrm{KL}(P,(1-u)P+uR)\le\log(1/(1-u))$ |
| flem:mixture-in-M | lemma (formalisation.tex) | Incognita.BatchedBandits.smul_add_smul_dirac_one_mem_unitLaws, Incognita.BatchedBandits.integral_id_smul_add_smul_dirac_one | $(1-u)P+u\delta_1\in\mathcal M$, its mean |
| flem:dinf-anti | lemma (formalisation.tex) | Incognita.BatchedBandits.dInf_anti | |
| prop:kinf, items | lemma | Incognita.BatchedBandits.dInf_unitLaws_eq_top_of_one_le, Incognita.BatchedBandits.dInf_unitLaws_eq_zero_of_lt_integral, Incognita.BatchedBandits.klBer_le_dInf_unitLaws, Incognita.BatchedBandits.dInf_unitLaws_le_ofReal_log, Incognita.BatchedBandits.dInf_unitLaws_bernoulliMeasure | general forms of (i)-(iv) in `Incognita/BatchedBandits/KInf.lean`; the frozen proofs are in `Incognita/P006/KInf.lean` (route: formalisation.tex, "Formal route to Proposition prop:kinf") |

### prop:witnesses, item by item

| Item | Lean | Status |
|---|---|---|
| (a) Bernoulli instances with all $p_c<1$ are in $\mathcal P$ | `Incognita.BatchedBandits.bernoulliBandit_mem_unitBandits_of_lt_one` | proved |
| (a) an arm $\delta_1$ excludes an instance from $\mathcal P$ | `Incognita.BatchedBandits.not_mem_unitBandits_of_integral_eq_one` (any arm of mean 1) | proved |
| (a) an arm $\mathcal N(0,1)$ excludes an instance from $\mathcal P$ | — | not done (the law `δ_2` is excluded from $\mathcal M$ instead: `dirac_two_not_mem_unitLaws`) |
| (b) $\mathsf S_s,\mathsf G_s,\mathsf D_s$ are grids | `Grid.sequential`, `Grid.geometric`, `Grid.doublyExp` (by construction) | proved |
| (b) $x_\ell=2$ on $\mathsf D_s$ | `Grid.ratio_doublyExp` | proved |
| (b) $x_\ell\to1$ on $\mathsf S_s$ and $\mathsf G_s$ | `Grid.tendsto_ratio_sequential`, `Grid.tendsto_ratio_geometric` (and the closed form `Grid.ratio_geometric`) | proved |
| (b) $t_\ell=\ell$ is not a grid | `Grid.not_exists_t_eq_id` | proved |
| (c) `Const_c` batched on every grid | `isBatched_const` | proved |
| (c) `RR` batched on every grid; `FL^g` batched and not ignoring the rewards | — | not done (`RR`, `FL` not defined); the same two properties for the simpler learner `firstRewardAlg` (pulls $c_1$ in batch 1, then $c_2$ or $c_1$ according to the first reward): `isBatched_firstRewardAlg`, `not_seesRewardsUpTo_zero_firstRewardAlg` |
| (c) `React` batched on no grid | `not_isBatched_reactAlg` | proved |
| (d) $(\mathrm{Const}_c)_g\in\mathcal M_0$ | `infoModel_const` | proved |
| (d) $\mathrm{FL}\in\mathcal M_0$ | — | not done; for `firstRewardAlg`: `infoModel_firstRewardAlg` |
| (d) $\mathrm{Par}^{(k)}\in\mathcal M_{k+1}$, $\notin\mathcal M_k$ | `infoModel_parityAlg`, `not_infoModel_parityAlg` | proved |
| (e) `Const_c` consistent on $\mathcal P_c$, every grid | `isConsistentAtBatchEnds_const` (on `{ν \| gap ν c = 0}` ⊇ $\mathcal P_c$) | proved |
| (e) `Const_c` not consistent on $\mathcal P$ | `not_isConsistentAtBatchEnds_const` (on any class with an instance where $c$ is suboptimal; $\mathcal P$ has one, `Incognita.P006.example_instance`) | proved |
| (e) `RR` not consistent on $\mathcal P$ | — | not done |

## Modelling decisions

1. **Arms.** A type `α` with `[Fintype α]` (`[Finite α]` where only finiteness is used) and the
   discrete σ-algebra, written `[MeasurableSingletonClass α]` (for a finite type every set is then
   measurable). This is the paper's "finite set $\mathcal A$, discrete" (Definitions
   `def:instance`, `def:learner`). The discrete σ-algebra is not cosmetic: with a coarser one,
   distinct Dirac masses on the arms could coincide and the strictness of the chain $\mathcal M_k$
   could fail. `[DecidableEq α]` is added where counts are used (`pullCount`). The roadmap's
   convention $K\ge2$ is the hypothesis `hK : 2 ≤ Fintype.card α` of each item of `thm:main`,
   which fixes it.
2. **Laws and instances.** `unitLaws = {Q | IsProbabilityMeasure Q ∧ ∀ᵐ x ∂Q, x ∈ [0,1]}`
   (equivalent to $Q([0,1])=1$ for a probability measure). `unitBandits α = {ν | (∀ a, ν a ∈
   unitLaws) ∧ ⨆ a, (ν a)[id] < 1}`, as the roadmap plans (`Set (Kernel α ℝ)`); a member is a
   Markov kernel (`isMarkovKernel_of_mem_unitBandits`), so no separate `IsMarkovKernel` field. The
   name `unitLaws` is new: the roadmap describes the set without naming it.
3. **$\mathcal K_{\inf}$, KL, kl.** Reused: `LMLExplore.Bandits.dInf unitLaws P μ` is
   $\inf\{\mathrm{KL}(P,Q): Q\in\mathcal M, m(Q)>\mu\}$ in `ℝ≥0∞` with $\inf\emptyset=\infty$,
   exactly the paper's primal definition; `klDiv` (Mathlib) is the paper's KL for probability
   measures (`∞` when not absolutely continuous); `LMLExplore.klBer p q` is the KL between the
   Bernoulli laws on $\{0,1\}$ of means `p` and `q`, after clamping the arguments to $[0,1]$
   (harmless in every statement: the arguments are in $[0,1]$). Real quantities are compared with
   `ℝ≥0∞` values through `ENNReal.ofReal`, applied only to nonnegative reals.
4. **Learners, counts, regret, sequential consistency.** Reused from LML / LMLExplore: a learner is
   `Algorithm Unit α ℝ` (no observation, real rewards), whose policy `policy n` is a Markov kernel
   from the histories of the rounds `0, …, n-1`; the paper's $\pi_t$ is `policy (t-1)`. The law is
   `trajMeasure alg (Environment.bandit ν)`. `pullCount A c t` counts the rounds `0, …, t-1`, i.e.
   the paper's rounds $1,\dots,t$: the paper's $N_c(t)$ with no shift. Sequential consistency is
   LMLExplore's `IsConsistent` (regret $o(T^p)$ for every $p>0$), identical to `def:seqcons`.
5. **Rounds from 0** (the paper's paragraph "Rounds numbered from zero"): batch $\ell\ge1$ is the
   set of rounds `t (ℓ-1), …, t ℓ - 1`; the batch of a round `n` is `Grid.batchOf n =
   min {ℓ ≥ 1 | n < t ℓ}`, the paper's $b(n+1)$; quantities at a batch end `t ℓ` are unchanged.
6. **Grid.** A structure `Grid K` (fields `t`, `t_zero : t 0 = 0`, `strictMono`, `le_t_one :
   max 2 K ≤ t 1`). It takes the number of arms as a parameter, as DOSSIER.md proposes, because
   $t_1\ge\max(2,K)$ is part of the definition of a grid and the set $\mathcal G$ of grids indexes
   the families of `def:infomodel`: with a parameter-free `Grid`, condition (b) of $\mathcal M_k$
   would range over more grids than the paper's. Statements use `Grid (Fintype.card α)`.
   `logEnd ℓ = log (t ℓ)` (junk `0` at `ℓ = 0`, never used) and `ratio ℓ = logEnd ℓ / logEnd
   (ℓ-1)` for `ℓ ≥ 2`, `1` for `ℓ ≤ 1`. `IsFiner g g'` is `Set.range g'.t ⊆ Set.range g.t` (both
   contain `t 0 = 0`, which is not a batch end, so this is "every end of `g'` is an end of `g`").
7. **Sees the rewards up to $r$; batched.** `SeesRewardsUpTo alg n r`: equal kernel values
   `alg.policy n (h, ())` on two histories of length `n` with the same actions and the same rewards
   at the rounds `i < r` (the paper's $y_s=y'_s$ for $s\le\min(r,t-1)$, with $s=i+1$, $t=n+1$).
   This is the pointwise form of `def:batched`, not the masked form of `lem:mask`. `IsBatched alg g
   := ∀ n, SeesRewardsUpTo alg n (g.t (g.batchOf n - 1))`, the paper's "for every round $t\ge1$,
   $\pi_t$ sees the rewards up to $t_{b(t)-1}$"; `isBatched_iff` gives the form "during batch
   $\ell+1$, up to $t_\ell$". The definitions are stated for any action and feedback types
   (`Algorithm Unit 𝓐 𝓨`).
8. **Information models.** `InfoModel k π` for `k : ℕ∞` and `π : Grid K → Algorithm Unit 𝓐 𝓨`, a
   structure with (a) `isBatched : ∀ g, IsBatched (π g) g` and (b) `policy_eq`: for all grids
   `g, g'`, all `ℓ, n` with `g.batchOf n = ℓ + 1 = g'.batchOf n` and `g.t j = g'.t j` for every
   `j` with `1 ≤ j` and `(j : ℕ∞) ≤ ℓ + k`, `(π g).policy n = (π g').policy n` (equality of
   kernels). For `k = ⊤` (b) forces `g = g'` (`Grid.ext`), as in the paper.
9. **Consistency at the batch ends.** `IsConsistentAtBatchEnds alg g E`: for every `ν ∈ E` with
   `[IsMarkovKernel ν]` (the same binder as LMLExplore's `IsConsistent`), every `c` with
   `0 < gap ν c` and every `p > 0`, `E[pullCount IT.action c (g.t ℓ)] / (g.t ℓ)^p → 0` along
   `ℓ → ∞` in `ℕ` (the term at `ℓ = 0`, where `t 0 = 0`, does not affect the limit). The class
   $E\subseteq\mathcal P$ is a parameter; the statements carry `E ⊆ unitBandits α` as the paper
   does.
10. **Example learners.** `Const_c` is LML's `Algorithm.const (Measure.dirac c)` (it samples its
    action from $\delta_c$, so it is the deterministic learner that always pulls $c$). `React` and
    `Par^{(k),g}` are deterministic LML algorithms (`Algorithm.deterministic`), with the paper's
    rounds shifted by one. Since `FL^g` is not defined here, `firstRewardAlg c₁ c₂ g` (not in the
    paper) is the witness of `IsBatched` and of $\mathcal M_0$ that does not ignore the rewards.
11. **Splitting of `thm:main` and `prop:kinf`.** One frozen statement per claim: `thm:main`(i) has
    three claims (inclusion, strictness, components), (ii) and (iii) two each; `prop:kinf` one per
    item. Strictness is stated as the existence of an element of $\mathcal M_{k'}$ outside
    $\mathcal M_k$, which, with the inclusion, is the strict inclusion.
12. **What is not frozen.** `prop:witnesses` and `cor:ucb` are the witnesses and exclusions of the
    definitions (Table `tab:witnesses`); their formal counterparts are the checks of AGENTS.md 6.4,
    lemmas of `Incognita/`, proved in this pull request where the learner they use is defined (table
    above). The lemmas `lem:counts`, `lem:grid`, `lem:mask`, `lem:consist-regret`, `lem:kl` are
    for `prove`.

## Back-translations

Each reading is from the Lean alone, unfolding the definitions; then the differences with the node.
Common to the seven items of `thm:main`: `α` is a finite type with measurable singletons and at
least two elements; a learner is a sequence of Markov kernels `policy n` from histories of `n`
(observation, action, real reward) triples with trivial observation to `α`; a grid is a strictly
increasing `t : ℕ → ℕ` with `t 0 = 0` and `max 2 |α| ≤ t 1`.

### Incognita.Statements.P006.infoModel_mono (thm:main (i), inclusions)
From the Lean: for all `k ≤ k'` in `ℕ∞` and every family `π` of learners indexed by grids, if
(a) every `π g` is batched on `g` and (b) for all grids `g, g'`, all `ℓ, n` with `n` in batch `ℓ+1`
of both, agreement of `t j` for `1 ≤ j ≤ ℓ + k` implies `(π g).policy n = (π g').policy n`, then
the same holds with `k'` in place of `k`.
Paper: $\mathcal M_k\subseteq\mathcal M_{k'}$ for $k\le k'$ in $\mathbb N\cup\{\infty\}$.
Differences: none beyond the encoding (rounds from 0, `ℕ∞`); the hypothesis $K\ge2$ is carried.

### Incognita.Statements.P006.infoModel_strict (thm:main (i), strictness)
From the Lean: for all `k < k'` in `ℕ∞` there is a family `π` with `InfoModel k' π` and not
`InfoModel k π`.
Paper: the inclusion $\mathcal M_k\subseteq\mathcal M_{k'}$ is strict when $k<k'$.
Differences: strictness is written as the existence of an element of the difference; with
`infoModel_mono` this is the strict inclusion.

### Incognita.Statements.P006.isBatched_iff_exists_infoModel_top (thm:main (i), components)
From the Lean: for every learner `alg` and grid `g`, `alg` is batched on `g` (at every round `n`,
its policy is invariant under changes of the rewards of the rounds `≥ t (batchOf n - 1)`) iff there
is a family `π` in `𝓜_⊤` with `π g = alg`.
Paper: "$\pi$ is batched on $g$ iff $\pi=\pi^g$ for some $\Pi\in\mathcal M_\infty$".
Differences: none beyond the encoding.

### Incognita.Statements.P006.isBatched_of_isFiner (thm:main (ii), batching)
From the Lean: if every value of `g'.t` is a value of `g.t`, every learner batched on `g'` is
batched on `g`.
Paper: "Let $g$ be finer than $g'$ … Every learner batched on $g'$ is batched on $g$."
Differences: the class $E$ of item (ii) is unused by this claim and omitted.

### Incognita.Statements.P006.isConsistentAtBatchEnds_of_isFiner (thm:main (ii), consistency)
From the Lean: if every value of `g'.t` is a value of `g.t`, `E ⊆ unitBandits α`, and for every
Markov `ν ∈ E`, every arm `c` with positive gap and every `p > 0`,
`E_ν[#{s < g.t ℓ : A_s = c}] / (g.t ℓ)^p → 0` as `ℓ → ∞`, then the same holds with `g'`.
Paper: "every learner consistent at the batch ends of $g$ on $E$ is consistent at the batch ends of
$g'$ on $E$", $E\subseteq\mathcal P$.
Differences: counts in the rounds `0, …, t-1` (the paper's $1,\dots,t$); limits over all `ℓ ∈ ℕ`.

### Incognita.Statements.P006.isBatched_sequential_iff (thm:main (iii), batching)
From the Lean: for `s ≥ max 2 |α|`, with `t ℓ = s + ℓ - 1` (`ℓ ≥ 1`), a learner is batched on this
grid iff for every round `n < s` its policy takes the same value on all histories with the same
actions (it ignores the rewards).
Paper: "$\pi$ is batched on $\mathsf S_s$ iff $\pi_t$ ignores the rewards for every $t\le s$".
Differences: rounds `n = t - 1`, so $t\le s$ becomes `n < s`.

### Incognita.Statements.P006.isConsistentAtBatchEnds_sequential_iff (thm:main (iii), consistency)
From the Lean: for `s ≥ max 2 |α|` and `E ⊆ unitBandits α`, a learner is consistent at the batch
ends of `𝖲_s` on `E` iff for every Markov `ν ∈ E` and `p > 0`,
`E_ν[T m⋆ - ∑_{n<T} m_{A_n}] / T^p → 0` as `T → ∞`.
Paper: "consistent at the batch ends of $\mathsf S_s$ on $E$ iff sequentially consistent on $E$",
with $\mathcal R(T)=\sum_c\Delta_c\mathbb E N_c(T)$ and limits $T\to\infty$.
Differences: LML's pathwise regret, whose expectation is the paper's regret (LML's
`integral_regret_eq_sum_gap_mul_integral_pullCount`).

### Incognita.Statements.P006.kinf_eq_top_of_one_le (prop:kinf (i))
From the Lean: for a probability measure `P` on `ℝ` concentrated on `[0,1]` and `μ ≥ 1`, the
infimum of `klDiv P Q` over the probability measures `Q` concentrated on `[0,1]` with mean `> μ`
is `∞`.
Paper: $\mathcal K_{\inf}(P,\mu)=+\infty$ for $\mu\ge1$. Differences: none.

### Incognita.Statements.P006.kinf_eq_zero_of_lt_mean (prop:kinf (ii))
From the Lean: same `P`; if `μ < ∫ x dP`, that infimum is `0`.
Paper: $\mathcal K_{\inf}(P,\mu)=0$ for $\mu<p$. Differences: none.

### Incognita.Statements.P006.kinf_bounds (prop:kinf (iii))
From the Lean: same `P`, with `p = ∫ x dP ≤ μ < 1`:
`ofReal (2 (μ-p)²) ≤ klBer p μ ≤ dInf unitLaws P μ ≤ ofReal (log ((1-p)/(1-μ)))`, and
`dInf unitLaws P μ ≠ ∞`.
Paper: $2(\mu-p)^2\le\mathrm{kl}(p,\mu)\le\mathcal K_{\inf}(P,\mu)\le\log\frac{1-p}{1-\mu}<\infty$.
Differences: the comparisons with real numbers go through `ofReal` (the reals are $\ge0$); the
paper's "$<\infty$" is recorded as the finiteness of $\mathcal K_{\inf}(P,\mu)$ it expresses.

### Incognita.Statements.P006.kinf_bernoulli (prop:kinf (iv))
From the Lean: for `p ∈ [0,1]` and `p ≤ μ < 1`, the infimum of `klDiv (p δ_1 + (1-p) δ_0) Q` over
the probability measures `Q` concentrated on `[0,1]` with mean `> μ` is `klBer p μ`.
Paper: $\mathcal K_{\inf}(\mathrm{Ber}(p),\mu)=\mathrm{kl}(p,\mu)$ for $p\le\mu<1$. Differences:
none (the infimum is over all of $\mathcal M$, not over Bernoulli laws).

### Incognita.Statements.P006.kinf_bounds_of_gap_pos (prop:kinf (v))
From the Lean: for a finite discrete `α`, a kernel `ν` whose arms are laws on `[0,1]` with
`m⋆ = ⨆ b, ∫ x d(ν b) < 1`, and an arm `a` with `Δ_a = m⋆ - ∫ x d(ν a) > 0`:
`0 < ofReal (2Δ_a²) ≤ dInf unitLaws (ν a) m⋆ ≤ ofReal (log ((1 - m_a)/(1 - m⋆)))` and
`dInf unitLaws (ν a) m⋆ ≠ ∞`.
Paper: $0<2\Delta_a^2\le K_a\le\log\frac{1-m_a}{1-m^\star}<\infty$ for $\nu\in\mathcal P$ and $a$
suboptimal. Differences: as for (iii); the convention $K\ge2$ is implied by the existence of a
suboptimal arm and is not added.

## Open problems

- **Not formalised in this pull request: the learners `RR`, `FL^g`, `UCB` of `def:exlearners`,
  and `cor:ucb`.** They are witnesses (Table `tab:witnesses`), not basic relations. `UCB` is the
  paper's UCB1 (index $\bar y_c+\sqrt{2\log(t-1)/\max(n_c,1)}$, first $K$ rounds in a fixed order,
  first maximiser); LML's `Bandits.ucbAlgorithm` is a different index ($\log(n+1)$ with a parameter,
  arms `Fin K`), so `cor:ucb` would need a new definition and the identification of the
  reward-stack model of `cite:ACF02-thm1` with `trajMeasure` (Step 1 of its proof). A later
  statements pull request can add them; nothing here depends on them. The definitions'
  consistency check uses instead `Const_c` (witness on $\mathcal P_c$, exclusion on $\mathcal P$)
  and the known case `IsConsistent.isConsistentAtBatchEnds` (sequential consistency implies
  consistency at the batch ends of every grid).
- No node of the paper was found ambiguous, ill-typed or false; no erratum.
