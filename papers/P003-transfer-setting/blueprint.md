# Blueprint of P003-transfer-setting

Lean names of the paper's nodes. Statuses are computed by the audit, not stored here.

| Label | Kind | Lean name | Notes |
|---|---|---|---|
| def:laws | definition | `Incognita.TransferBandits.unitBandits` | laws on `[0,1]`: probability measures on `ℝ` concentrated on `[0,1]`; `KL` is Mathlib's `InformationTheory.klDiv`; `kl(p,q)` is `klDiv (Ber((1:ℝ),0,p)) (Ber((1:ℝ),0,q))`; `δ_x` is `Measure.dirac x` |
| def:instance | definition | `Incognita.TransferBandits.unitBandits` | an instance is a Markov kernel `Kernel α ℝ` of `unitBandits α`; means `(ν a)[id]`; "suboptimal" is `∃ b, (ν a)[id] < (ν b)[id]` |
| def:source-space | definition | `Incognita.TransferBandits.SourceSpace`, `sourceMeasure`, `boxRestrict`, `boxSigma` | `Ω' = (ℕ → I) × (α → ℕ → ℝ)`, stacks from index `0` |
| def:size-rule | definition | `Incognita.TransferBandits.IsSizeRule`, `IsSourceStrategy` | |
| def:source-data | definition | `Incognita.TransferBandits.Source`, `sourceData`, `sourceLaw`, `sourceMean` | pairs (sizes, kept values, `0` outside the box) |
| def:learner | definition | `Incognita.TransferBandits.TransferAlgorithm`, `TransferAlgorithm.ofAlgorithm` | bandit algorithms are LML's `Learning.Algorithm Unit α ℝ` |
| def:game | definition | `Incognita.TransferBandits.stepKernel`, `onlineKernel`, `gameMeasure`, `sourceCount`, `onlineCount` | |
| def:drift | definition | `Incognita.TransferBandits.DriftBound`, `TwoSidedDriftBound`, `meanBand` | |
| def:consistency | definition | `Incognita.TransferBandits.IsConsistent`, `IsConsistentOnUnit` | |
| thm:main | frozen | (a) `Incognita.Statements.P003.divergence_decomposition`; (b) `Incognita.Statements.P003.lookahead_divergence` | proofs: `Incognita.P003.divergence_decomposition`, `Incognita.P003.lookahead_divergence`; look-ahead map `Incognita.TransferBandits.lookahead` |
| cor:fundamental | frozen | `Incognita.Statements.P003.fundamental_inequality` | proof: `Incognita.P003.fundamental_inequality` |
| def:prior-game | definition | `Incognita.TransferBandits.PriorStrategy`, `PriorStrategy.state`, `PriorStrategy.counts` | |
| def:stopped-game | definition | `Incognita.TransferBandits.PriorStrategy.histSigma`, `PriorStrategy.IsStoppingTime`, `PriorStrategy.stoppedCounts` | |
| lem:prior-game | frozen | (a) `Incognita.Statements.P003.constSize_isSizeRule`; (b) `Incognita.Statements.P003.priorCounts_isSizeRule` | constant map `Incognita.TransferBandits.constSize` |
| lem:lookahead | frozen | `Incognita.Statements.P003.lookahead_not_isSizeRule` | |
| prop:stopped-games | frozen | (a) `Incognita.Statements.P003.stoppedCounts_isSizeRule`; (b) `Incognita.Statements.P003.two_arms_sizeRule_eq_stoppedCounts`; (c) `Incognita.Statements.P003.cyclicSize_not_stoppedCounts` | cyclic map `Incognita.TransferBandits.cyclicSize` |
| lem:learner-exclusion | frozen | `Incognita.Statements.P003.learner_exclusion` | |
| prop:drift | frozen | (a) `Incognita.Statements.P003.drift_of_twoSided`; (b) `…drift_of_mem_meanBand`; (c) `…drift_meanBand_inclusions`; (d) `…drift_all_pairs`; (e) `…drift_witness_exclusion` | |
| prop:classes | frozen | (a) `Incognita.Statements.P003.isConsistent_anti`; (b) `Incognita.Statements.P003.isConsistent_one` | |
| prop:witness | frozen | `Incognita.Statements.P003.ofAlgorithm_isConsistent` (first sentence); `Incognita.Statements.P003.ucb_isConsistentOnUnit` (UCB); `Incognita.Statements.P003.exists_isConsistent` ("`𝒞_L ≠ ∅`") | UCB is LML's `Bandits.ucbAlgorithm K c` |
| prop:exclusion | frozen | `Incognita.Statements.P003.followSource_not_isConsistent` | `π^tr` is `Incognita.TransferBandits.TransferAlgorithm.followSource` |
| cite:GMS19-Lemma1 | lemma | (added by prove) | data processing; Mathlib/LML may provide it |
| lem:kl-neg | lemma | (added by prove) | |
| lem:source-law | lemma | (added by prove) | |
| lem:wald | lemma | (added by prove) | |
| prop:source-kl | lemma | (added by prove) | |
| lem:mixture | lemma | (added by prove) | |
| lem:lml-history | lemma | (added by prove) | identifies `onlineKernel` with LML's `trajMeasure` |
| lem:online-kl | lemma | (added by prove) | |
| lem:prior-game (a) | proof | `Incognita.P003.constSize_isSizeRule` | `Incognita/P003/Drift.lean`, from `isSizeRule_constSize` |
| lem:prior-game (b) | proof | `Incognita.P003.priorCounts_isSizeRule` | `Incognita/P003/PriorGame.lean`; the case `τ ≡ T'` of prop:stopped-games (a) |
| prop:stopped-games (a) | proof | `Incognita.P003.stoppedCounts_isSizeRule` | `Incognita/P003/PriorGame.lean`; from `Incognita.TransferBandits.isSizeRule_of_eqOn_box` (a measurable size map whose event `{N' = n}` only reads the box of `n` is a size rule: `{N' = n}` is the preimage of itself under the `𝒢_n`-measurable map `ω ↦ ω̂`, box of `n` kept, `0` outside) and the lemmas `Incognita.TransferBandits.PriorStrategy.*` of `Incognita/TransferBandits/SizeRules.lean`: `measurable_state`, `sum_state_fst`, `measurable_stoppedCounts`, `stoppedCounts_eq_of_eqOn_box` (the game reads only the box of its counts) |
| prop:stopped-games (c), first part | lemma | `Incognita.P003.isSizeRule_cyclicSize`, `Incognita.P003.sum_cyclicSize_le` | `Incognita/P003/Cyclic.lean`; via `Incognita.TransferBandits.isSizeRule_of_eqOn_box`; the impossibility part of (c) remains open |
| lem:lookahead | proof | `Incognita.P003.lookahead_not_isSizeRule` | `Incognita/P003/Exclusions.lean`; the event `{N^la = 𝟏_{a₁}}` is not in `𝒢_{𝟏_{a₁}}` (two points with the same box, `boxRestrict_eq_of_le_one`) |
| lem:learner-exclusion | proof | `Incognita.P003.learner_exclusion` | `Incognita/P003/Exclusions.lean`; same two points, same source data |
| prop:drift (a)–(e) | proof | `Incognita.P003.drift_of_twoSided`, `…drift_of_mem_meanBand`, `…drift_meanBand_inclusions`, `…drift_all_pairs`, `…drift_witness_exclusion` | `Incognita/P003/Drift.lean`; means in `[0,1]`: `Incognita.TransferBandits.mean_mem_Icc`, `Incognita.TransferBandits.abs_mean_sub_mean_le_one` (`Incognita/TransferBandits/Means.lean`); counterexamples are constant Dirac kernels |
| prop:classes (a)–(b) | proof | `Incognita.P003.isConsistent_anti`, `Incognita.P003.isConsistent_one` | `Incognita/P003/Drift.lean`; `meanBand_mono`, `meanBand_eq_of_one_le`, `isConsistent_of_le`, `isConsistent_iff_of_one_le`, all in `Incognita.TransferBandits` (`Incognita/TransferBandits/Means.lean`) |

## Modelling decisions

Conventions fixed here for the roadmap TransferBandits (its Definitions table; "Lean: same
conventions as the BatchedBandits roadmap"). Files: `Incognita/TransferBandits/Setting.lean`,
`Consistency.lean`, `Examples.lean`, `PriorGame.lean`; checks in `Checks.lean`; witnesses in
`Incognita/P003/Witnesses.lean`.

1. **Arms.** A finite type `α` (`[Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]`,
   so every set of arms is measurable), with `2 ≤ Fintype.card α` in every statement (the paper's
   "Fix `K ≥ 2`", def:instance). The statements whose objects need no measurability on the arms
   (the five `drift_*` statements and `constSize_isSizeRule`) omit `[MeasurableSingletonClass α]`:
   they are then more general, and remain true, since every pair of instances their proofs need
   can be taken constant in the arm. Never `Fin K`, except for LML's UCB, which LML defines on
   `Fin K`. Where the paper uses arms `1, 2, 3` by name, the statements take distinct arms
   `a₁, a₂, a₃`; where it uses the order of `[K]` (`π^tr`: "the smallest arm", "arm `1`"), the
   arms are a finite linear order.
2. **Laws on `[0,1]` and instances.** As in LML and LMLExplore: a law on `[0,1]` is a probability
   measure on `ℝ` concentrated on `Set.Icc 0 1`, and an instance is a Markov kernel
   `ν : Kernel α ℝ` with `∀ a, ∀ᵐ x ∂(ν a), x ∈ Set.Icc 0 1` (`unitBandits α`, the paper's
   `𝒫^K`). The mean `m(P)` is the Bochner integral `P[id]`. `KL` is Mathlib's `klDiv`, which the
   paper states equals its `KL` (def:laws and the remark after it); `kl(p, q)` is the divergence
   between Mathlib's `Ber((1 : ℝ), 0, p)` and `Ber((1 : ℝ), 0, q)` with `p q : I`.
3. **Indices from 0.** The value `X'_{k,j}` (`j ≥ 1`) is `ω.2 k (j - 1)`; the box `B(n)` is
   `{(k, j) | j < n k}`; the round `t ≥ 1` is the round `t - 1`; an online history of `T` rounds
   is `Fin T → α × ℝ`; a learner's kernel of index `n` is the paper's `π_{n+1}`.
4. **Source space.** `SourceSpace α = (ℕ → I) × (α → ℕ → ℝ)`: the randomisation `U'` with values
   in `unitInterval` and law `volume^{⊗ℕ}` (the uniform law), and the stacks, with law
   `⊗_{k,j} ν'_k` (`Measure.infinitePi`, nested). The stacks are real-valued (the LML convention),
   with laws concentrated on `[0,1]`; the paper's `Ω'` is the subset where the stacks lie in
   `[0,1]`, which has full measure.
5. **Box σ-algebras.** `𝒢_n = boxSigma n`, the σ-algebra generated by `ω ↦ (U', (X'_{k,j})_{j < n_k})`
   (`MeasurableSpace.comap` of the restriction to the box). A size rule (`IsSizeRule`) is a
   measurable `N' : SourceSpace α → α → ℕ` with `{N' = n} ∈ 𝒢_n` for every `n`. A source strategy
   is `ρ : ℕ → SourceSpace α → α → ℕ` with every `ρ T` a size rule; the paper indexes horizons
   from `1`; the value at `T = 0` plays no role (asymptotic statements), and every strategy of the
   paper extends to one.
6. **Source data.** The paper's `𝒮 = ⨆_n [0,1]^{B(n)}` (a sigma type) is represented by
   `Source α = (α → ℕ) × (α → ℕ → ℝ)`: `D = (N', x)` with `x k j = X'_{k,j}` for `j < N'_k` and `0`
   outside the box (`sourceData`). The map from the disjoint union to this representation is a
   measurable injection with a measurable inverse on its (measurable) range, so the laws of `D`,
   their divergences and the transfer learners (kernels on `𝒮`, extended by composition with the
   inverse) correspond; the masked coordinates are a function of the sizes and carry no
   information. This avoids dependent types in every later proof.
7. **Learners.** `TransferAlgorithm α`: for each round `n`, a Markov kernel from
   `Source α × (Fin n → α × ℝ)` to `α` (the paper's kernels from `𝒮 × ℋ_{t-1}`). Rewards are
   real-valued, as in LML; the paper's kernels on `([K] × [0,1])^{t-1}` extend to real histories
   by clamping (lem:lml-history does this), and every kernel on real histories restricts to
   `[0,1]`-histories, which have full measure, so the laws of the game agree. Bandit algorithms
   (`σ`) are LML's `Learning.Algorithm Unit α ℝ`; `π^σ = TransferAlgorithm.ofAlgorithm σ`.
8. **Law of the game.** Literal composition products, as in def:game: `stepKernel π ν n =
   π_n ⊗ₖ ν` (the reward drawn from `ν` at the action), `onlineKernel π ν T` the iterated product
   `Q^t = Q^{t-1} ⊗ (π_t ⊗ ν)` from the Dirac mass at the empty history (the history of `t + 1`
   rounds assembled by LML's `MeasurableEquiv.finSuccProd`), and
   `gameMeasure ν' N' ν π T = sourceLaw ν' N' ⊗ₘ onlineKernel π ν T`. LML's `trajMeasure` is not
   used for transfer learners: the paper defines `κ^T` as this product, and lem:lml-history
   (a `prove` task) identifies it with LML's law, so that LML's divergence decomposition
   (`Learning.IsAlgEnvSeq.klDiv_map_history_bandit`) applies. For a bandit algorithm `σ`, the law
   `Q^T_{σ,ν}` of def:consistency is LML's `trajMeasure σ (Environment.bandit ν)` (its first `T`
   rounds), which is what lem:lml-history says it is.
9. **Counts and expectations.** `N'_k` is `sourceCount k` on the source data (and `N' ω k` under
   `P'_{ν'}`), `N_k(T)` is `onlineCount k` on the online history (and LML's `pullCount IT.action k T`
   for bandit algorithms). In thm:main and cor:fundamental the expectations are lower integrals in
   `ℝ≥0∞`, where `0 * ∞ = 0` (the paper's convention); in the consistency notions they are Bochner
   integrals in `ℝ` of bounded counts, divided by `(T : ℝ) ^ c`, with `Tendsto … atTop (𝓝 0)`.
10. **Drift conditions and `𝒞_L`.** `L : α → ℝ`, positive in every statement (the paper's
    `L ∈ (0,∞)^K`). `𝒫_L = meanBand L` contains its pairs of `𝒫^K × 𝒫^K` only. `IsConsistent L π`
    is def:consistency verbatim: every pair of `𝒫_L`, every source strategy, every suboptimal arm,
    every `c > 0`. `IsConsistentOnUnit σ` is the paper's consistency of a bandit algorithm on
    `𝒫^K` (pull counts, not regret; LMLExplore's `IsConsistent` is regret-based, and
    `Incognita.P003.isConsistentOnUnit_of_isConsistent` derives the first from the second).
11. **Prior games.** `PriorStrategy α`: one measurable map
    `(ℕ → I) × (Fin r → α × ℝ) → α` for every round `r : ℕ` (the game over `T'` rounds uses
    `r < T'`; the paper's family `(α_r)_{r ≤ T'}` extends arbitrarily). `state` computes the counts
    and the history recursively; the value observed at round `r` is the next unread value of the
    stack, `X'_{A'_r, C_{A'_r}(r)}` (0-based index `C_{A'_r}(r - 1)`). `𝓕'_r = histSigma g r`;
    a stopping time is `IsStoppingTime g T' τ`.
12. **Statements with several claims.** A node with items gets one theorem per item (prop:drift,
    prop:classes, prop:stopped-games, lem:prior-game, thm:main); a claim of a single item with
    several conclusions (thm:main (b), prop:drift (c)) is one conjunction. prop:witness has three
    sentences, one theorem each. lem:lookahead repeats a part of thm:main (b) and is frozen on its
    own, since it is a node.
13. **Not reused.** No existing object of LML, LMLExplore or Mathlib models a source phase, size
    rules (stopping points of a multiparameter filtration) or the class `𝒞_L`; LML's
    `IsAlgEnvSeq` could carry the source data as the observation of round `0`, but then the
    history of `0` rounds forgets it (thm:main includes `T = 0`), hence decision 8.

## Back-translations

Read from the Lean alone (definitions unfolded), then compared with the paper's node.

- **`divergence_decomposition`** (thm:main (a)). For a finite type `α` of arms with at least two
  elements, a measurable `N : (ℕ → I) × (α → ℕ → ℝ) → (α → ℕ)` such that each event `{N = n}` is
  determined by the randomisation and the values `ω.2 a j`, `j < n a`, a transfer learner `π`, a
  horizon `T` and four Markov kernels `ν, ν', ν₂, ν₂'` whose laws are concentrated on `[0,1]`,
  if `∫⁻ N(·) a d(P'_{ν'}) < ∞` for every arm, then the KL divergence between the law
  `P'_{ν'}∘D⁻¹ ⊗ κ^T_{π,ν}` and `P'_{ν₂'}∘D⁻¹ ⊗ κ^T_{π,ν₂}` equals
  `∑_a E[sizes a] KL(ν' a, ν₂' a) + ∑_a E[pulls of a] KL(ν a, ν₂ a)`, expectations under the first
  law, in `ℝ≥0∞`. Differences: none of substance; `(ν̃, ν̃')` renamed `(ν₂, ν₂')`; the
  representations of decisions 4, 6, 7.
- **`lookahead_divergence`** (thm:main (b)). With `N^la(ω) a₁ = 1` if `ω.2 a₁ 1 > 1/2` and `2`
  otherwise, `0` on the other arms: `N^la` is measurable, bounded, not a size rule; for `p ≠ q` in
  `(0,1)`, any learner, horizon and target instance `ν ∈ 𝒫^K`, if `ν' ∈ 𝒫^K` with
  `ν' a₁ = Ber(p)`, `ν₂' a₁ = Ber(q)` and `ν₂' = ν'` elsewhere, the divergence of the two laws of
  the game (same target `ν`) is `2 kl(p,q)`, the right-hand side of eq:main is `(2 - p) kl(p,q)`,
  and `(2 - p) kl(p,q) < 2 kl(p,q)`. Differences: arm `1` is any arm `a₁`; the paper asks the
  `[0,1]` hypothesis of `ν'_2, …, ν'_K` only (for `ν'_{a₁} = Ber(p)` it holds anyway).
- **`fundamental_inequality`** (cor:fundamental). Under the hypotheses of
  `divergence_decomposition`, for every measurable `Z` on (source data, history) with values in
  `[0,1]`, `kl(E_P Z, E_{P₂} Z) ≤ ∑_a E_{P'_{ν'}}[N a] KL(ν' a, ν₂' a) + ∑_a E_P[pulls of a]
  KL(ν a, ν₂ a)`, where `kl(x, y)` is the divergence between Bernoulli laws and the integrals are
  sent to `[0,1]` by `projIcc` (the identity there). Differences: none.
- **`constSize_isSizeRule`** (lem:prior-game (a)). A constant map is a size rule. Same.
- **`priorCounts_isSizeRule`** (lem:prior-game (b)). For every prior strategy and `T'`, the counts
  after `T'` rounds form a size rule, and each is at most `T'`. Same.
- **`lookahead_not_isSizeRule`** (lem:lookahead). The look-ahead map is measurable, bounded, and
  not a size rule. Same.
- **`stoppedCounts_isSizeRule`** (prop:stopped-games (a)). For a stopping time `τ ≤ T'` of the
  prior game (`{τ = r}` determined by the randomisation and the first `r` rounds), the counts after
  `τ` rounds form a size rule with total at most `T'`. Same.
- **`two_arms_sizeRule_eq_stoppedCounts`** (prop:stopped-games (b)). With exactly two arms, a size
  rule whose total is bounded is, at every point, the stopped counts of some prior strategy with a
  stopping time of the game over `sSup (range (total))` rounds. Same (the supremum is attained).
- **`cyclicSize_not_stoppedCounts`** (prop:stopped-games (c)). With three distinct arms among at
  least three, the cyclic map is a size rule with total at most `3`, and no `T'`, prior strategy
  and stopping time give stopped counts whose law under `P'_{ν'}` equals that of the cyclic map for
  every `ν' ∈ 𝒫^K`. Same.
- **`learner_exclusion`** (lem:learner-exclusion). For the sizes `1` on `a₁` and `0` elsewhere,
  no measurable real function of the source data equals `ω.2 a₁ 1` at every point, and no transfer
  learner's first kernel, on the source data and the empty history, is `δ_{a₁}` when
  `ω.2 a₁ 1 > 1/2` and `δ_{a₂}` otherwise, at every point. Difference: `f` is real-valued rather
  than `[0,1]`-valued, because the Lean stacks are real-valued (with `[0,1]`-valued `f` the claim
  would be trivially true at points where `ω.2 a₁ 1 ∉ [0,1]`); the content, `D` does not determine
  `X'_{1,2}`, is the same.
- **`drift_of_twoSided`**, **`drift_of_mem_meanBand`**, **`drift_meanBand_inclusions`**,
  **`drift_all_pairs`**, **`drift_witness_exclusion`** (prop:drift (a)–(e)). Read literally, with
  the sets of pairs restricted to `𝒫^K × 𝒫^K` and inclusions written as implications. Same.
- **`isConsistent_anti`** (prop:classes (a)). For positive `L ≤ L'`, the set of learners of
  `𝒞_{L'}` is contained in that of `𝒞_L`. Same.
- **`isConsistent_one`** (prop:classes (b)). `𝒞_L = 𝒞_𝟏` for `L ≥ 𝟏`; a learner is in `𝒞_L` for
  every positive `L` iff it is in `𝒞_𝟏`; and it is in `𝒞_𝟏` iff the condition of def:consistency
  holds for every pair of `𝒫^K × 𝒫^K`. Same.
- **`ofAlgorithm_isConsistent`** (prop:witness). If an LML bandit algorithm has
  `E[N_a(T)]/T^c → 0` on every `[0,1]` instance, every suboptimal arm and every `c > 0`, its
  source-ignoring learner is in `𝒞_𝟏` and in every `𝒞_L`. Same.
- **`ucb_isConsistentOnUnit`** (prop:witness). LML's `ucbAlgorithm K c` with `K ≥ 2` and
  `c > 1/2` is consistent on `𝒫^K` in that sense. Same (LML's UCB, as the paper says).
- **`exists_isConsistent`** (prop:witness). For every positive `L`, some transfer learner is in
  `𝒞_L`. Same.
- **`followSource_not_isConsistent`** (prop:exclusion). On a finite linear order of arms (at
  least two), the learner that always pulls the smallest arm maximising the source empirical means
  (when every arm has a source value; otherwise the smallest arm) is in no `𝒞_L`, and some
  `ν ∈ 𝒫^K`, constant sizes `n`, suboptimal arm `a` and `c > 0` give
  `E[N_a(T)]/T^c ↛ 0` for the game with source `ν' = ν` and sizes `n`. Same.

## Open problems

None: every headline node and every basic property of Section 4 is frozen. Two points for the
reviewer and for `prove`:

- `ucb_isConsistentOnUnit` freezes the paper's claim that LML's UCB with `c > 1/2` is consistent
  on rewards in `[0,1]`. LML's `Bandits.UCB.regret_le_of_gt_two` bounds the regret of
  `ucbAlgorithm K c` by `O(log n)` for `σ²`-sub-Gaussian rewards and `c > 2σ²`; rewards in `[0,1]`
  are `1/4`-sub-Gaussian, so the threshold is `c > 1/2`, the paper's. The step from regret to pull
  counts is `Incognita.P003.isConsistentOnUnit_of_isConsistent` (in `Witnesses.lean`).
- `lem:lml-history`, which the proofs of thm:main (a), prop:witness and prop:exclusion need, is
  the bridge between `onlineKernel` and LML's `trajMeasure`; it is a `prove` task.
