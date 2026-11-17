# Dossier of P007-stochastic-setting, version 1

Refereed and versioned with `paper.tex`, never compiled into the PDF: what the referees and the
owner need and the reader does not. It changes only with a new version of `paper.tex` after
acceptance. Private KNOWN entries are cited by id only, never quoted (this roadmap has none).

## Roadmap correspondence

- Item served: **F0, the setting** of roadmap StochasticBandits (kind `definitions`). The roadmap
  asks for "the Definitions above, the product-class identity for $C(\nu;\mathcal E)$, witnesses and
  exclusions" (ROADMAP.md, item F0), and lists as must-haves (Definitions section, after the table):
  KL-UCB consistent on Bernoulli instances and "always pull arm $a$" not; a super-fast convergent
  algorithm on $[0,1]$-valued instances; $C(\nu;\mathcal E) = 0$ on a class where the optimal arm
  alone identifies the instance; the product-class identity. The roadmap's pinned conventions say the
  identity is "proved by F0": it is `thm:main`. The roadmap lists no general lower bound for F0
  (F1 is the fundamental inequality, F5 the Graves–Lai lower bound); `cor:lower` only connects the
  identity with the cited bound of [GMS19, Theorem 1].

### Definitions table of the roadmap, row by row

Planned Lean names are those of the roadmap (namespace `Incognita.StochasticBandits` unless a reuse is
stated). The `formalize-statements` session records the final names in `blueprint.md`.

| Roadmap row | Node(s) | Planned Lean name | How it wraps the dependencies |
|---|---|---|---|
| arms, instance | `def:instance` | reuse | arms `α` with `[Fintype α] [Nonempty α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]`; an instance is `ν : Kernel α ℝ` with `[IsMarkovKernel ν]` (LML); means `(ν a)[id]`, gap LML `gap ν a`, optimal arms `{a | gap ν a = 0}` |
| laws, divergences | `def:laws` | reuse | `Measure ℝ` with `IsProbabilityMeasure`; `klDiv` (Mathlib, `ℝ≥0∞`); Bernoulli law and `klBer` as in LMLExplore (`LMLExplore/InformationTheory/KullbackLeibler/`) |
| $\mathcal K_{\inf}$ | `def:kinf` | reuse `LMLExplore.Bandits.dInf D P μ` | same definition (strict inequality, `ℝ≥0∞`, `⨅` over an empty set is `⊤`); **pitfall**: LMLExplore's mean is the Bochner integral `Q[id]`, which is `0` for a law without a finite mean, so `dInf` agrees with `def:kinf` only for models `D ⊆ 𝒫₁` (as in the paper, where a model is a subset of $\mathcal P_1$) |
| unstructured class | `def:product` | `productClass (D : α → Set (Measure ℝ)) : Set (Kernel α ℝ)` | LMLExplore's `LaiRobbins.lean` has no name: it writes the set inline, `{ν \| ∀ a, ν a ∈ M a}`; `productClass` is a definition equal to that set (prove `productClass D = {ν \| ∀ a, ν a ∈ D a}` by `rfl`), so the LMLExplore theorems apply verbatim |
| structured class | `def:product` | `Set (Kernel α ℝ)` | no new type (roadmap, Appendix A) |
| models: laws on $[0,1]$ | `def:models` ($\mathcal P[0,1]$); P006 `def:instance` ($\mathcal M$) | reuse `Incognita.BatchedBandits.unitLaws : Set (Measure ℝ)` (P006, merged before this paper) | probability measures with `∀ᵐ x ∂P, x ∈ Set.Icc 0 1`, the LMLExplore hypothesis `hν` of `klucb_regret_le`; the roadmap's row says that when BatchedBandits is merged first, this roadmap reuses its object (referee SC2.1); `depends_on` records P006v1 `def:instance`, `def:kinf`, `prop:kinf` |
| models: Bernoulli | `def:models` ($\mathcal B$) | `bernoulliLaws` | image of `[0,1]` under the Bernoulli law of LMLExplore; must contain $\delta_0,\delta_1$ (means 0 and 1) |
| models: semi-bounded | `def:models` ($\mathcal S$) | `semiBoundedLaws` | probability measures, integrable, `∀ᵐ x ∂P, x ≤ 1` |
| models: $\mathcal L_{\varepsilon,B}$ | `def:models` | `momentLaws ε B` | probability measures with `∫ x, |x|^(1+ε) ∂P ≤ B` **and** `Integrable (fun x ↦ |x|^(1+ε)) P` (otherwise the Bochner integral is 0 junk) |
| models: kurtosis | `def:models` ($\mathcal H_\kappa$) | `kurtosisLaws κ` | `Memℒp id 4 P`, `variance id P > 0`, centred 4th moment `≤ κ * variance^2`; for `κ > 1` |
| models: Gaussian | `def:models` ($\mathcal G$) | `gaussianLaws` | `{gaussianReal μ v \| μ : ℝ, v : ℝ≥0, v ≠ 0}`; **pitfall**: Mathlib's `gaussianReal μ 0` is the Dirac mass, excluded here |
| finite-mean laws | `def:laws` ($\mathcal P_1$) | `finiteMeanLaws` (new, needed for `lem:kinf-p1` and as the ambient set of models) | integrable probability measures |
| learner | `def:learner` | reuse LML `Algorithm Unit α ℝ` | LML's algorithm is an initial law on `α` and policy kernels from the history to `α`, exactly `def:learner` (our $p_0$ and $p_t$); the `Unit` is the absence of context |
| run | `def:run` | reuse LML `IsAlgEnvSeq O A R alg (Environment.bandit ν) P` | the two conditional-law properties of `def:run` are the content of `IsAlgEnvSeq` with the bandit environment; uniqueness of the law (Ionescu-Tulcea) is LML's `trajMeasure` |
| counts, regret | `def:regret` | reuse LML `pullCount A a T` (pulls in rounds `< T`), `regret ν A T` (pseudo-regret $\hat R_T$), expectations `P[...]` | $R_T(\pi,\nu)$ is `P[regret ν A T]`; the identity $\hat R_T=\sum_a\Delta_aN_a(T)$ is in LML (`regret_eq_sum_pullCount_mul_gap` or similar: check the name) |
| rewards by count | `lem:stack` | reuse LML `rewardByCount`, `hasLaw_rewardByCount_infinitePi`, `iIndepFun_rewardByCount_add_one` (`LeanMachineLearning/Online/Bandit/RewardByCountMeasure.lean`, read 2026-11-16 at LML `efbe5d2`) | the paper's proof (truncation in time) is the one of that file (`rewardByCountUntil`); the enlargement by an independent array is LML's `P.prod (streamMeasure ν)` |
| consistency | `def:consistent` | reuse `LMLExplore.Bandits.IsConsistent alg E` | same definition (regret / `n^p` → 0 for every `p > 0`, every Markov kernel of `E`) |
| horizon-dependent learner | `def:learner`, `def:consistent`, `def:family` | `IsConsistentFamily (π : ℕ → Algorithm Unit α ℝ) E` and a family version `…Family` of every predicate of `def:family` | regret, counts and laws at horizon `T` (at `n` for the tails) of `π T`; `lem:classes`(v) and `lem:family` are the constant family |
| $\alpha$-consistency (the paper's $\gamma$-consistency) | `def:consistent` | `IsAlphaConsistent alg E γ` | `∀ p > γ`; `γ ∈ [0,1)` as a hypothesis of the lemmas, not of the definition; the exponent is $\gamma$ in the paper because $\alpha$ is the type of arms |
| uniformly fast convergent | `def:ufc` | `IsUniformlyFastConvergent alg E` | not in the roadmap table but used by `cite:GMS19-thm1` (F2, F3 need it too) |
| uniformly super-fast convergent | `def:ufc` | `IsUniformlySuperFastConvergent alg E C` | `∀ ν ∈ E, ∀ a, 0 < gap ν a → ∀ T ≥ 2, P[pullCount A a T] ≤ C * log T / gap ν a ^ 2` |
| smarter than uniform | `def:smarter` | `IsSmarterThanUniform alg E` | `∀ T ≥ 1` (the bound is trivial at `T = 0`) |
| pairwise symmetric, monotonic | `def:pairwise`, `def:monotonic` (order $\preccurlyeq$ in the text before `def:monotonic`) | `IsPairwiseSymmetricOptimal alg E`, `IsMonotonic alg E` | [GMS19, Definitions 3–4], verbatim in `literature/notes/GMS19.md` (section added 2026-11-17); pairwise symmetry compares the **joint laws** of `(pullCount A a T, pullCount A a' T)` and of the swapped pair (not expectations); monotonicity is stated `∀ T ≥ 1` (the source has no quantifier on $T$, declared in the paper) |
| alternatives | `def:gl` | `alt` | `{ν' ∈ E \| a⋆ is not optimal for ν'}` with `a⋆` passed as an argument together with a uniqueness hypothesis, or `bestArm ν` of LMLExplore under a hypothesis of uniqueness |
| Graves–Lai constant | `def:gl` | `gravesLai` | `⨅ w : α → ℝ≥0∞, ⨅ (_ : ∀ ν' ∈ alt, 1 ≤ ∑ a, w a * klDiv (ν a) (ν' a)), ∑ a, w a * ENNReal.ofReal (gap ν a)`; ENNReal's `0 * ⊤ = 0` is the paper's convention; `x / 0 = ⊤` for `x ≠ 0` and `x / ⊤ = 0` in `ℝ≥0∞` match `thm:main` |
| tails | `def:tails` | `HasUpperTailedPullCount alg E f`, `HasUpperTailedRegret alg E f` | [SA11, Definition 1], verbatim in `literature/notes/SA11.md`; `f : ℕ → ℝ` positive on `n ≥ 2`; `∃ C C' > 0, ∀ ν ∈ E` with a unique optimal arm, `∀ n ≥ 2`, …; counts: `∀ a` suboptimal, `P (C * log n / gap ν a ^ 2 ≤ pullCount A a n) ≤ C' / f n`; regret: LML's pseudo-regret `regret ν A n` against `C * log n / Δmin`. **Changed from the source**: SA11's regret is the realised regret against the reward sequence of the optimal arm, not the pseudo-regret; the roadmap pins the pseudo-regret, and the paper declares the change |
| algorithms | `def:ucb` | reuse LML `ucbAlgorithm K c` with `c = 1` as far as possible | see the witnesses below; `imed`, `npts`, `klucbSwitch` are **deferred** to the papers that analyse them |

### Witnesses and exclusions (AGENTS.md §6.4), definition by definition

| Definition | Witness (node) | Known case (node) | Exclusion (node) |
|---|---|---|---|
| $\mathcal K_{\inf}$ | finite positive on $\mathcal P[0,1]$ below 1 (`lem:kinf-unit`(i), from `cite:INC-P006-prop:kinf`(iii)) | Bernoulli: $\mathrm{kl}(p,\mu)$ (`lem:kinf-unit`(ii)), Gaussian: $\frac12\log(1+(\mu-\mu_0)^2/v)$ (`lem:kinf-gauss`); LMLExplore's `dInf_range_bernoulliMeasure`, `dInf_range_gaussianReal` (known variance) | vanishes identically on $\mathcal P_1$ (`lem:kinf-p1`); $+\infty$ above the support (`cite:INC-P006-prop:kinf`(i)) |
| models | $\mathrm{Ber}(1/2)$, $\delta_0$, $\mathcal N(0,1)$ (`lem:kurt`(iii), `lem:semi`(iv)) | $\mathcal B\subseteq\mathcal P[0,1]\subseteq\mathcal S\subseteq\mathcal P_1$ (text after `def:models`) | $\delta_x\notin\mathcal H_\kappa$, skewed Bernoulli $\notin\mathcal H_\kappa$, $\delta_x\notin\mathcal L_{\varepsilon,B}$ for large $\lvert x\rvert$, $\mathcal N(\cdot,0)$ excluded from $\mathcal G$ by definition |
| consistency | `UCB` on $\mathcal P[0,1]^\alpha$ and $\mathcal B^\alpha$ (`prop:ucb`) | — | constant learner `π^b` (`lem:constant`) |
| $\gamma$-consistency | `UCB` (0-consistent) | consistency = 0-consistency (`def:consistent`) | `π^b`, `π^u` for every `γ < 1` (`lem:constant`) |
| uniform fast / super-fast | `UCB` with $C=13$ (`prop:ucb`) | — | `π^b` (`lem:constant`) |
| smarter than uniform | uniform learner `π^u` (`lem:constant`) | — | `π^b` on an instance where $b$ is suboptimal (`lem:constant`) |
| pairwise symmetric for optimal arms | `π^u` on every class (`lem:gms-classes`(i)) | — | `π^b` on $\mathcal B^\alpha$ (all arms $\mathrm{Ber}(1/2)$) (`lem:gms-classes`(ii)) |
| monotonic | `π^u` on every class (`lem:gms-classes`(i)) | — | the switching learner `π^sw` on $\mathcal B^\alpha$ (`lem:gms-classes`(iii)); note that `π^b` **is** monotonic (both sums are $T$ or $0$), so it is not an exclusion here |
| $f$-upper tailed counts / pseudo-regret | `UCB` on $\mathcal P[0,1]^\alpha$ with $f=\log^2$, constants $10,1$ (counts) and $10(K-1),K-1$ (`prop:ucb-tails`, `lem:tails`(i)); a weaker form of [AMS09, Theorem 8] ($\log^3$ for the same index) | counts imply pseudo-regret (`lem:tails`(i)), as [SA11, Proposition 2.1] | `π^b`, every unbounded $f$ (`lem:tails`(ii)) |
| family versions | constant family of `UCB` (`lem:family` + `prop:ucb`) | constant family = the learner (`lem:family`) | constant family of `π^b` (`lem:family` + `lem:constant`) |
| product class | $\mathcal B^\alpha$ | — | $\mathcal E_2$ of the example after `prop:gl-zero` is not a product class |
| Graves–Lai constant | positive on $\mathcal B^\alpha$ (`thm:main` + `lem:kinf-unit`) | product identity (`thm:main`), agreement with [CMP17, Theorem 1] (`lem:gl-reduction`) | $C=0$ on $\mathcal E_2$ (`prop:gl-zero`); $C=\infty$ on $\mathcal P_1^\alpha$ (`lem:kinf-p1` + `thm:main`) |

**KL-UCB.** The roadmap names KL-UCB as the consistency witness. The paper proves the witness for
UCB with a Hoeffding bonus instead (`prop:ucb`), which is stronger (uniform super-fast convergence on
all of $\mathcal P[0,1]^\alpha$, hence consistency on $\mathcal P[0,1]^\alpha\supseteq\mathcal
B^\alpha$), and complete. KL-UCB is mentioned in the text with its locus ([CGMMS13, Theorem 1];
since 2026-11-17 the note `literature/notes/CGMMS13.md` has Theorem 1 verbatim, so a later paper can
transcribe it). **For the Lean witness of consistency,
KL-UCB is the cheap route:** LMLExplore's `klucb` (on `α`, not `Fin K`) has
`klucb_regret_eventually_le` (when `∑ gap/klBer < c`) and
`klucb_regret_eventually_le_of_integral_bestArm_eq_one` (best mean 1), both giving
`∀ᶠ n, P[regret ν A n] ≤ c * log n` on `[0,1]`-valued instances; with
`LMLExplore.Bandits.isConsistent_of_eventually_le_mul_log` this gives
`IsConsistent klucb unitLaws-class`, hence on Bernoulli instances: exactly the roadmap's witness.
For super-fast convergence, LML's `UCB.expectation_pullCount_le_of_gt_two` (σ²-sub-Gaussian
rewards, `c > 2σ²`) with σ² = 1/4 (Hoeffding's lemma for `[0,1]`) and `c = 1` gives
`P[pullCount] ≤ 8 log(n+1)/Δ² + 5`, hence a super-fast constant (existential is enough for the
witness); but `ucbAlgorithm` is stated on `Fin K` (against the roadmap's "never `Fin K`"): a
transfer through an equivalence `α ≃ Fin K` is needed, or a proof of `prop:ucb` on `α`.

### Deferred, with the reason

- **Weak tail classes** [SA11, Definition 3] (constants chosen after the instance): not in the
  roadmap's table, and no listed paper uses them; a one-line variant of `def:tails`.
- *Formerly deferred, now defined (referee SC1.2, 2026-11-17)*: pairwise symmetric and monotonic
  learners (`def:pairwise`, `def:monotonic`), $f$-upper tailed counts and pseudo-regret
  (`def:tails`), the family versions of all predicates (`def:family`), each with a witness and an
  exclusion (`lem:gms-classes`, `lem:tails`, `prop:ucb-tails`, `lem:family`).
- **Algorithms `imed`, `npts`, `klucbSwitch`**: each is defined by the paper that analyses it
  (P004 defines IMED, `def:imed` there); a setting paper that defines them without results about them
  would add nodes no statement uses.
- **Dual formulas of $\mathcal K_{\inf}$** on $[0,1]$ and on semi-bounded laws: BatchedBandits F2
  (or StochasticBandits F10) and P004 (Appendix on the dual), by the roadmap's owner decision 1.
- **Several optimal arms in the Graves–Lai constant**: D17 (the roadmap says a paper allowing them
  states its definition).

### What the item asks that the paper does not give

- KL-UCB is not proved consistent in the paper (see above: UCB instead, KL-UCB cited); the Lean
  witness can use LMLExplore's `klucb`. (Referee-scope asked the owner whether UCB is acceptable.)
- The deferred items above (algorithms of later papers, dual formulas, weak tail classes, several
  optimal arms).

### Acceptance criteria of the roadmap, one by one

1. Model, class of algorithms, criterion: `thm:main` is an identity on unstructured classes (no
   algorithm); `cor:lower` names its class (consistent learners on $\mathcal D^\alpha$) and its
   criterion (liminf of $R_T/\log T$); `prop:ucb` is a finite-time bound valid for every $T\ge1$,
   anytime algorithm, tie rule arbitrary.
2. Closest known: below.
3. Explicit instance and the product-class identity: Section `sec:examples` (Bernoulli instance
   with $K=3$; $K=2$ in "Degenerate cases"); the identity is the main result itself.
4. Algorithm defined completely: `def:ucb`, `eq:ucb`, Algorithm `alg:ucb` (parameters none,
   tie rule any, initialisation through the index $+\infty$, anytime).
5. Constants explicit: `prop:ucb` ($8$, $2$, $5/4$, $13$).
6. No definition of "optimal": none.
7. Not routine: an F item (a definitions paper); criterion 7 does not apply ("unless the paper serves
   an F item").
8. Building block: not a lemma paper; the users are named (P004, P005, F1–F5, F9).
9. Constants: not applicable.
10. Not applicable.

### Conventions of the roadmap changed

- **Models are subsets of $\mathcal P_1$** (`def:kinf`), whereas the roadmap says "a set
  $\mathcal D$ of laws on $\mathbb R$": the constraint $m(Q)>\mu$ needs a finite mean, as in
  [GMS19, §1.2] and LMLExplore's `dInf` (whose Bochner mean is junk without integrability).
  Declared in the paper after `def:kinf` and under "Changes to the sources" (referee PF1.2).
- **"Structured class"** follows the roadmap: every class is a structured class, the unstructured
  classes $\prod_a\mathcal D_a$ being the special case (`def:product`; the first submission called
  "structured" only the classes that are not products, referee PF1.1).
- **Notation of the exponent of [SAE13, Definition 5]:** the paper writes $\gamma$-consistency for
  the source's (and the roadmap's) $\alpha$-consistency, because $\alpha$ is the set of arms
  (referee SC1.8). The planned Lean name `IsAlphaConsistent` is unchanged.
- Two generalisations, declared in the paper ("Changes to the sources", after `def:smarter`): the
  classes of learners are defined on arbitrary sets of instances, not only on $\mathcal D^\alpha$;
  $\gamma$-consistency is taken for $\gamma\in[0,1)$.
- The paper writes $\mathcal N(\mu,v)$ with $v$ the variance (as Mathlib's `gaussianReal μ v`).

### Users of these definitions, and the library papers (updated 2026-11-17)

- **P004** (IMED with finite variance, accepted, v1): semi-bounded laws $\mathcal S$ (`def:model`
  there, same set; P004 adds $\mathcal S_r$, $\mathcal M_r$ of its own), $\mathcal K_{\inf}(P,\mu;\mathcal D)$
  with the strict inequality (same), runs in a stack model with rounds from 0 (`lem:stack` here makes
  the link with runs defined by conditional laws), consistency [LS, Def. 16.1] and uniform fast
  convergence [GMS19, Def. 1] (same as `def:consistent`, `def:ufc` with $\mathcal E=\mathcal D^\alpha$),
  regret $\sum_a\Delta_a\mathbb EN_a(T)$ (same). *Overlap with library nodes* (referee SC2.3):
  P004 `lem:dualfacts`(a) is `lem:kinf-basic`(i) on $\mathcal S$; `lem:dualfacts`(b) contains
  `lem:kinf-basic`(iv) on $\mathcal S$, the value $+\infty$ of `lem:semi`(i) for $\mu\ge1$, and the
  value $0$ at the mean (which `lem:semi`(i) gives through its upper bound $\log1=0$).
- **P005** (bounded kurtosis, accepted, v1): $\mathcal H_\kappa$ (same set, $\kappa>1$), kurtosis and
  variance (same), $\mathcal K_{\inf}(P,\mu;\mathcal D)$ (same), rounds numbered from 1 with $N_a(T)$
  the pulls among the first $T$ rounds (the same quantity as ours, said in the text after
  `def:regret`), stack model (`lem:stack`), consistency over $\mathcal D^\alpha$ (same). *Overlap*:
  P005 `lem:mixkl` ($Q'\ge\theta Q$ gives $\mathrm{KL}(P,Q')\le\mathrm{KL}(P,Q)+\log(1/\theta)$) implies
  `lem:mix` (take $Q=P$, $\theta=1-\eta$); P005 `cor:largegap` ($\mathcal K_{\inf}(P,m+\Delta)=
  \mathcal K_{\inf}(P_0,\Delta/\sigma)$ on $\mathcal H_\kappa$) is the location–scale identity of
  `lem:kurt`(ii) with $\phi(x)=m+\sigma x$, stated by P005 for the standardised law.
- **Why P004 and P005 are not cited in `paper.tex`.** A citation of a library paper requires a
  `depends_on` entry (AGENTS.md §5.6, checked by CI), which records a result *used*, and makes this
  paper conditional on that paper's certification and subject to its dependency checks. Nothing of
  P004 or P005 is used here: the overlaps are one-line facts proved here in two or three lines, and
  P004, P005 are users of this paper's definitions, not sources. So the comparison is recorded here
  for the referees and the formalisers (who can prove one from the other in Lean), and not in the
  paper. (Referee SC2.3 asked for "see also"; see the notebook, 2026-11-17, round 2.)
- **P006** (BatchedBandits F0, accepted, v1): laws on $[0,1]$ $\mathcal M$ (`def:instance` there) =
  our $\mathcal P[0,1]$; its $\mathcal K_{\inf}(P,\mu)$ (`def:kinf` there) = our
  $\mathcal K_{\inf}(P,\mu;\mathcal P[0,1])$; its `prop:kinf` (i)–(v) is restated as
  `cite:INC-P006-prop:kinf` and used by `lem:kinf-unit` (which keeps only the two consequences and
  the Bernoulli model $\mathcal B$, absent from P006) and in the remarks and examples. P006's rounds
  start at 1 (ours at 0): not used by the cited node.

## Closest known

- **K1** (Lai–Robbins/Burnetas–Katehakis, in Lean in LMLExplore): the lower bound with the constant
  $\sum_a\Delta_a/d_{\inf}$ for unstructured classes. `cor:lower` is K1 for $\mathcal D^\alpha$ with the
  Graves–Lai constant on the right-hand side, through `thm:main`; nothing new beyond the identity.
- **K25** ([CMP17, Theorem 1]; Section 4 special case "unstructured, $c(x,\theta)=1/d(\theta(x),\theta(x^\star))$"):
  the closest statement to `thm:main`. Attempt to derive `thm:main` from it: CMP17's setting is a
  parametric family with a divergence $D(\theta,\lambda,x)$ and its Section 4 example states the
  value for the unstructured parametric case without the degenerate values; for a general model,
  $\mathcal K_{\inf}$ can be $0$ or $\infty$ and the infimum over $Q$ is not attained, and the
  roadmap's definition uses all alternatives and weights in $[0,\infty]$, not CMP17's $\Lambda(\theta)$
  and $\eta\ge0$. `lem:gl-reduction` shows the two formulations agree; `thm:main` then needs the
  arm-by-arm argument with every degenerate case. The derivation fails only at "general models"; the
  content is routine, as expected from an F0 item.
- **[VPG24, Example 3 with Propositions 1–2]** (Van Parys–Golrezaei, separable bandits; not in
  KNOWN.md; found by referee-scope, read in this revision, note `literature/notes/VPG24.md`): the
  nearest published statement of `thm:main`. Setting: a common finite set of rewards, $\mathcal P$
  closed convex (the separable case a product of closed sets $\mathcal P_x$, convex in their
  Proposition 2); the optimal rates are stated (without a written proof: "it can be verified") to be
  $\eta^\star(x')=1/I(P(x'),Q^\star_{x'})$ on deceitful arms (some law of $\mathcal P_{x'}$ has a mean
  larger than the best mean) and $0$ on the others; Proposition 2 gives the attainment and the
  equality of the strict and non-strict constraints on deceitful arms; example (9) has $C(P)=0$.
  *Attempt to derive `thm:main` from it:* for models of laws on a common finite set of rewards that
  are closed and convex, VPG24 gives the identity (with $\Delta_a/\mathcal K_{\inf}$ on deceitful arms,
  $0=\Delta_a/\infty$ on the others). It fails for general models: (a) infinite supports (Gaussian,
  semi-bounded, $\mathcal P_1$) are outside their setting ("future work", §8); (b) $\mathcal K_{\inf}=0$
  at a suboptimal arm, hence $C=\infty$, cannot occur on a finite set of rewards with closed models,
  and is not treated; (c) for non-closed or non-convex models the infimum need not be attained,
  while their rates use a minimiser $Q^\star$; (d) their constant uses the alternatives of the
  lower-bound program (6) with finite rates, our definition all alternatives and $w\in[0,\infty]$
  (bridged by `lem:gl-reduction`). The paper says this in `sec:related` ("Closest related work",
  "Gap with the literature").
- **[ATA89]** (finite parameter spaces) and **[GL97]** (controlled Markov chains): the origin of the
  constraint set over alternatives that keep the optimal law (VPG24, paragraph after Proposition 1);
  not read, cited as "see also" next to CMP17.
- **[LS, Corollary 25.2]** (linear case, K25): not used.
- **[GMS19, Theorem 1]** (K1, count form): cited as `cite:GMS19-thm1`, used in `cor:lower` only.
- **K5** (super-fast convergence, [GMS19, Definition 6]): `def:ufc` follows K5's transcription
  ($\mathbb EN_a(T)\le C\ln T/\Delta_a^2$ for all instances, suboptimal arms and $T\ge2$); the
  index records Definitions 5–6 as read on a page image.
- **K4** ([GMS19, Definition 2]): `def:smarter` follows K4's transcription.
- **K6** ([SAE13, Definition 5]): `def:consistent` follows K6's transcription.
- **K14** ([HT14, (2)–(3)]): `lem:kinf-gauss` recovers $D_{\inf}=\frac12\log(1+\Delta^2/\sigma^2)$, which
  is already [BK96, §4.4] (read 2026-11-17, note `literature/notes/BK96.md`; BK96's parameter set
  allows $\sigma_a^2=0$, our $\mathcal G$ excludes it).
- **[CGMMS13, §6.1, after Lemma 1]**: $d_{\rm BER}(E(\nu),E(\nu'))\le\mathrm{KL}(\nu,\nu')$ on
  $\mathfrak M_1([0,1])$, hence $\mathcal K_{\inf}\ge d_{\rm BER}$: the lower bound of
  `cite:INC-P006-prop:kinf`(iii), credited in the paragraph before `lem:kinf-unit` (P006 proves it
  with [GMS19, Lemma 1]; this paper no longer proves it, and no longer has the node
  `cite:GMS19-lem1`). The source prints its
  two "standard results" without the logarithm of the moment generating function (a slip; see the
  note), and does not state the monotonicity of $d_{\rm BER}(\mu_a,\cdot)$ that the step to
  $\mathcal K_{\inf}$ needs (our `lem:kl`).
- **[ACF02, Theorem 1]**: UCB1, $\mathbb E[T_j(n)]\le8\ln n/\Delta_j^2+1+\pi^2/3$ (end of the proof):
  `prop:ucb` is its analysis in our conventions (same leading constant $8$; our second term
  $2/\Delta^2+5/4$ is worse for small gaps, it comes from summing over the samples of $a$ only).
- **K33** ([SA11, Theorem 3.3]: no anytime policy is $f$-w$\mathcal T$ for $f$ growing faster than
  every power of $\log$, as the roadmap transcribes it): `prop:ucb-tails` gives $f=\log^2$ for UCB,
  which is consistent with it. [SA11, §2] states that UCB1 is $\log^3$-$\mathcal T$ and
  $\log^3$-$\mathcal R$ (credited to AMS09), so `prop:ucb-tails` is weaker than the published bound;
  the paper says so in the remark after it. `lem:tails`(i) is the union-bound step of [SA11,
  Proposition 2.1], credited in the remark after `lem:tails`.
- **K32** ([AMS09], read 2026-11-17 in this revision, authors' version, §5.1: Theorems 7–8 with their
  proofs, Lemma 3, and Theorem 2 (10)–(12) of §3.2): for UCB1 with index
  $\bar X_{k,s}+b\sqrt{\rho\log t/s}$, $\rho>1/2$, rewards in $[0,b]$, the proof of Theorem 8 gives
  $\mathbb P(T_k(n)>(1+\rho v_k\log n)x)\le n^{-2\rho x+1}+((1+\rho v_k\log n)x)^{1-2\rho}/(2\rho-1)$,
  $v_k=(2b/\Delta_k)^2$, by inequality (12) at the single count $u_k$: Hoeffding for arm $k$ at that
  count plus the optimal arm underestimated at the rounds $u_k+s$. With $b=1$, $\rho=2$ (the index of
  `eq:ucb`, their round $t+1$ being our round $t$), $x=1$: $\mathbb P(N_a(n)>1+8\log n/\Delta^2)\le
  n^{-3}+\frac13(1+8\log n/\Delta^2)^{-3}$. *Attempt to derive `prop:ucb-tails` from it:* the event
  $\{N_a(T)\ge10\log T/\Delta^2\}$ is contained in $\{N_a(T)>1+8\log T/\Delta^2\}$ only when
  $2\log T/\Delta^2\ge1$, which holds ($T\ge2$, $\Delta\le1$); then the bound
  $T^{-3}+\frac13(8\log T)^{-3}\Delta^6$ is at most $(\log T)^{-2}$, so `prop:ucb-tails` follows from
  AMS09 up to the translation of conventions (rounds from 0, arbitrary tie rule, the enlarged run).
  The paper keeps its self-contained proof (same argument, credited to AMS09) because the formalisers
  need it in these conventions, and says that it is a weaker form (referee SC2.2).
- **K11** ([HT15, Theorem 2]): the dual formula is not proved here (deferred); `lem:semi`(iii) is the
  trivial inequality.
- **K43** (ii) ([LS, Exercise 16.4]): $d_{\inf}=0$ for sub-Gaussian laws with unknown constant;
  `lem:kinf-p1` is the analogous (simpler) statement for $\mathcal P_1$.
- LMLExplore (Appendix B of the roadmap): `dInf`, `IsConsistent`, the Lai–Robbins theorems,
  `klucb`, `isConsistent_of_eventually_le_mul_log`; LML: `Algorithm`, `IsAlgEnvSeq`, `pullCount`,
  `regret`, `gap`, `ucbAlgorithm`, `rewardByCount`. Reused, never restated as new.

One library paper is cited: P006 (`depends_on = ["P006v1:def:instance", "P006v1:def:kinf",
"P006v1:prop:kinf"]`), for the values of $\mathcal K_{\inf}$ on laws on $[0,1]$
(`cite:INC-P006-prop:kinf`, referee SC2.1). P004 and P005 overlap with one-line facts and are not
cited (Users, above).

## Sanity checks

- $K=2$, Bernoulli: $C(\nu;\mathcal B^\alpha)=(p-q)/\mathrm{kl}(q,p)$ for $\nu=(\mathrm{Ber}(p),\mathrm{Ber}(q))$, $p>q$,
  $p<1$, which is the Lai–Robbins constant (K1) with $d_{\inf}=\mathrm{kl}$ (LMLExplore's
  `dInf_range_bernoulliMeasure`). For $p=1$: $C=0$, consistent with
  `klucb_regret_eventually_le_of_integral_bestArm_eq_one` (regret $o(\log n)$ when the best mean is 1).
- Gaussian, unknown variance: $C=2/\log2$ on $(\mathcal N(0,1),\mathcal N(-1,1))$, larger than the
  known-variance value $2$ (K14 vs the unit-variance Lai–Robbins constant $\sum 2/\Delta_a$).
- Degenerate values: $\mathcal K_{\inf}=0$ ($\mathcal P_1$) gives $C=\infty$; $\mathcal K_{\inf}=\infty$
  ($\mu\ge1$ on $\mathcal P[0,1]$) gives a zero contribution; empty $\mathrm{Alt}$ gives $C=0$;
  infinite weights only on the optimal arm.
- `prop:ucb`: the constants were checked numerically (`notebook/constants.txt`: $13/4\le5\log2$,
  $\zeta(3)-1\approx0.202\le1/4$). The bound $8\log T/\Delta^2+2/\Delta^2+5/4$ is consistent with
  LML's $8c\log(n+1)/\Delta^2+5$ for $c=1$, $\sigma^2=1/4$ (same leading term).
- Consistency with `[Lean]` entries of KNOWN.md: KNOWN.md has no `[Lean]` entry of the owner; the
  entries "in Lean" (K1, K3, K9, K13) are consistent with the definitions (same `dInf`, same
  `IsConsistent`).
- Explicit example: Section `sec:examples` (Bernoulli $K=3$, Gaussian, a three-point law).
- `prop:ucb-tails`: the constants $10$ and $1$ come from $2\log2>1$ (so $s:=\lceil10\log T/\Delta^2\rceil-1>8\log T/\Delta^2$),
  $1/(2s^2)\le1/(128\log^2T)$ and $T^{-4}\le\frac12\log^{-2}T$ for $T\ge2$. With several optimal arms the
  bound still holds (any optimal arm plays the role of $a^\star$), but `def:tails` only quantifies over
  instances with a unique optimal arm, as [SA11, Definition 1] ($\Delta\ne0$).
- `lem:gms-classes`(iii): `π^sw` at $T=2$ gives $\frac12$ against $0$; with $K=2$ the instance is
  $(\mathrm{Ber}(1/2),\mathrm{Ber}(1))$ and $\nu'=(\mathrm{Ber}(0),\mathrm{Ber}(1))$.

## Weak points

1. `lem:stack`, Step 2: the identity $\mathbb E[F(Y^{t+1})]=\mathbb E[F(Y^t)]$ uses that the
   conditional law of $X_t$ given $(H_t,A_t,Z)$ is $\nu_{A_t}$ and Fubini over the single coordinate
   $Z_{c(W)}$ whose index is random; the argument is written for a countable index set and a
   measurable $c$, which is right but compact. LML proves the same statement in Lean
   (`hasLaw_rewardByCount_infinitePi`), which is the safety net.
2. `prop:ucb-tails`, Steps 1–2: the reduction of $\{N_a(T)\ge10\log T/\Delta^2\}$ to one count $s$ and
   to the rounds $t\ge s$ (where an optimal arm is underestimated). It is the argument of [AMS09,
   proof of Theorem 8] (K32 above), checked by referee-proofs in round 2; the facts it shares with
   `prop:ucb` are now the node `lem:ucb-basic` (referee PF2.1). (The former weak point on `def:ufc`/`def:smarter` is resolved: [GMS19, Definitions 2 and
   6] are now verbatim in the note, and they agree with ours, $T\ge1$ and $T\ge2$.)
3. `def:monotonic` and `def:tails` are interpretations of their sources at two points, declared in
   the paper: [GMS19, Definition 4] has no quantifier on $T$ (we require every $T\ge1$, as for
   Definitions 2–3), and [SA11, Definition 1] uses the realised regret against the reward sequence of
   the optimal arm, which we replace by the pseudo-regret pinned by the roadmap (so the regret part of
   `def:tails` is a different predicate from SA11's $f$-$\mathcal R$; the counts part is the same). A
   later paper that cites a tail result of SA11 for the regret must translate it.
4. `cite:INC-P006-prop:kinf`: restated in our notation with the renaming paragraph; its item (v)
   is P006's for the class $\mathcal P$ = instances of $\mathcal P[0,1]^\alpha$ with $m^\star<1$, and
   P006's $\mathrm{kl}$ conventions at the endpoints ($\mathrm{kl}(p,q)=+\infty$ for $q\in\{0,1\}$,
   $q\ne p$) agree with `def:laws` ($y\log(y/0)=+\infty$ for $y>0$). The restatement is item by item
   that of P006 v1.
5. `cite:GMS19-thm1`: the restatement restricts the source's "for all bandit problems" to instances
   of $\mathcal D^\alpha$, and translates strategies with uniform randomisation into kernels (the
   renaming paragraph); this is weaker than the source, never stronger, but the translation of
   learners is argued in one sentence.

## Searches

- LMLExplore at `b4e0ab9` (GitHub API tree and raw files, 2026-11-16): `LMLExplore/Bandits/*.lean`
  listed; `LaiRobbins.lean` read for `IsConsistent`, `dInf`, the Lai–Robbins theorems,
  `isConsistent_of_eventually_le_mul_log` (no name for the product class: the set is written
  inline); `KLUCB.lean` for `klucbFam`, `klucb`, `klucb_regret_le`, `klucb_regret_eventually_le`,
  `klucb_regret_eventually_le_of_integral_bestArm_eq_one`; `UCB.lean` for
  `UCB.expectation_pullCount_le_of_gt_two`, `ucb_regret_le_sqrt` (LML's `ucbAlgorithm K c`, index
  $\hat\mu_a+\sqrt{2c\log(n+1)/T_a}$, sub-Gaussian rewards).
- LML at `efbe5d2` (GitHub API tree, 2026-11-16): `Online/Bandit/RewardByCountMeasure.lean` read for
  `rewardByCount`, `rewardByCountUntil`, `hasLaw_rewardByCount_infinitePi`,
  `iIndepFun_rewardByCount_add_one`.
- arXiv:1210.1136v4 (CGMMS13), abstract page and HTML (2026-11-16): Algorithm 2 and Theorem 1 of
  Section 4 (Bernoulli family covered with means in $(0,1)$); the exact constants of Theorem 1 were
  not copied (tool limit), so the paper cites Theorem 1 only for consistency in words.
- Revision of 2026-11-17 (Claude Opus 5.5, revise; sources fetched as PDFs and read on page images):
  arXiv:2007.07302v3 (VPG24; Crossref for its Management Science metadata and for ATA89, DOI
  10.1109/9.16415); arXiv:1602.07182v3 (GMS19 §3–§4, Definitions 2–4, 6, 7); arXiv:1107.4506v2 (SA11
  §1–§3); the authors' PDFs of ACF02 (homes.di.unimi.it/~cesabian) and BK96 (apdalab.org/mnk);
  arXiv:1210.1136v4 (CGMMS13 §4.2, §6.1); Crossref and the Celebratio Mathematica bibliography for
  Doob 1936 (D36), and Snell's obituary of Doob (J. Appl. Probab. 2005, p. 251) for what it proves;
  the paper "Doob, Ignatov and optional skipping" (Simons, Yang, Yao, Ann. Probab. 2002) was found
  but could not be opened. The novelty searches of referee-scope (report of 2026-11-17, "Queries")
  found VPG24 and no statement of `thm:main` with degenerate values.
- Revision round 2 (2026-11-17, Claude Opus 5.5, revise): the authors' version of AMS09
  (sites.ualberta.ca/~szepesva/papers/ucbtuned-journal.pdf, text layer): §3.2 Theorem 2 with
  (10)–(12), §5 opening, §5.1 in full (index (25), Theorem 7 and Lemma 3 with proofs, Theorem 8 with
  its proof and the remark after it). P006 `paper.tex` (v1, on `main`) for `def:instance`, `def:kinf`
  and `prop:kinf` (numbers 3.1, 3.2 and 4.2 from its reader build); P004 `lem:dualfacts` and P005
  `lem:mixkl`, `cor:largegap` (v1, on `main`).
- No further web search for novelty: the objects are classical (F item).

## Reading notes

- [GMS19, Lemma 1, Theorem 1]: verbatim in `literature/notes/GMS19.md`.
- [GMS19, Definitions 2, 6], [SAE13, Definition 5], [CMP17, Theorem 1 and Section 4], [HT14, Section 2],
  [HT15, Section 1, Theorem 2], [L17, Assumption 1], [AJK21, Section 2], [BCL13, Theorem 1],
  [CGMMS13, Section 5, Theorem 1], [GHMS22, Section 2, Appendix B.1], [RH20, Theorem 5],
  [CHK18, Section 1], [SA11, Definition 1], [LS, Definition 16.1, Theorem 16.2]: recorded as read in
  `literature/index.md`; not re-read in this session except CGMMS13 (above).
- Read in the revision of 2026-11-17 (notes added or extended): [VPG24, §3–§4.1], [GMS19, Definitions
  3–4] (and 2, 6, 7), [SA11, Definitions 1–3, Proposition 2.1], [ACF02, Theorem 1 and its proof],
  [BK96, §2, Theorem 1 and its proof, §4.4], [CGMMS13, §6.1]; [LS, §4.6] and [LS, Exercise 16.4] and
  [HT10, (5), Theorem 8] were recorded as read earlier.
- Unread, cited as classics or "see also": LR85 (classic), H63 (Hoeffding, classic), GL97, ATA89 and
  D36 ("see also"). LML is cited for the file `RewardByCountMeasure.lean`, read at `efbe5d2`.
