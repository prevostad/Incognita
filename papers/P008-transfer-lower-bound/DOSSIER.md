# Dossier of P008-transfer-lower-bound, version 1

Refereed and versioned with `paper.tex`, never compiled into the PDF: what the referees and the
owner need and the reader does not. It changes only with a new version of `paper.tex` after
acceptance. Private KNOWN entries are cited by id only, never quoted (the roadmap has none).

## Roadmap correspondence

- Items served (`directions` of META.toml): **F1, lower-bound part.** F1 reads: "The lower bound
  and the upper bound of KL-UCB-Transfer from arXiv:2610.21582, with the reduction from two-sided
  to one-sided drift. Start with the elementary lemmas they rest on (inequalities on positive parts
  such as $(a_+ - b_+) \le (a-b)_+$, the decomposition of the KL divergence of the history into a
  source phase and an online phase)." This paper gives:
  - the **lower bound** (Theorem 2 of PMRM26, K2): `cor:source` is Theorem 2 in the setting of
    P003; `thm:main` is the same bound for size rules, four drift sets and no unique optimal arm;
  - the **reduction from two-sided to one-sided drift for the lower bound**: `thm:main` holds with
    the same constant for $\mathcal P_L$, $\mathcal P^<_L$ (two-sided) and $\mathcal P^+_L$,
    $\mathcal P^{+,<}_L$ (one-sided); `lem:classes` (nesting); Section `sec:reduction`;
  - the **elementary lemmas of the lower bound**: the decomposition of the KL divergence into a
    source phase and an online phase is P003 (Theorem 4.1 and Corollary 4.2, used as
    `cite:INC-P003-cor:fundamental`); `lem:kl` (GMS19 (11) with its conventions); `lem:window`
    (PMRM26 Lemma 23); `lem:alternative`; `lem:rate`; and the positive-part inequalities named by
    F1, $(a_+-b_+)\le(a-b)_+$ and $|a_+-b_+|\le|a-b|$, with their consequence
    $|\mathbb E(\delta-DN)_+-(\delta-D\mathbb EN)_+|\le D\,\mathbb E|N-\mathbb EN|$ (`lem:positive-part`,
    PMRM26 Appendix D);
  - the **lower-bound half of Proposition 4 of PMRM26 (K4)**: `cor:concentration`, the bound of
    `thm:main` with the expectation outside the positive part when
    $\mathbb E|N'_a-\mathbb EN'_a|=o(\ln T)$, which is the form of the upper bound K3(i).
- What F1 asks that the paper does not give: **the upper bound of KL-UCB-Transfer** (Theorem 3 of
  PMRM26, K3), hence the matching statement of Proposition 4 (K4) itself (the paper cites it, says
  in words that `cor:concentration` combined with Theorem 3 gives it, and proves no upper bound),
  and the reduction for the upper bound. The paper says in words (Section `sec:reduction`, last
  sentence) that the reduction is immediate on the upper-bound side
  ($\mathcal P^<_L\subset\mathcal P^{+,<}_L$). A next paper on F1 should take the upper bound
  (PMRM26 Appendices B–C; the constants inside $h_1,h_2=O((\ln T)^{4/5}(\ln\ln T)^{1/5})$ are not made
  explicit in the source).
- Acceptance criteria of the roadmap, one by one:
  1. *The Main result states the source model, the drift condition, the consistency class and the
     criterion*: met. `thm:main`: source strategies of size rules with $\mathbb E_{\nu'}N'^{(T)}_k<\infty$
     (random, adaptive, depending on $T$ arbitrarily); four drift sets; the class $\mathcal C(\mathcal S)$
     of `def:class`; criterion $\liminf_T\mathbb E N_a(T)/\ln T$.
  2. *Closest known names the known result it extends and why it is not a corollary*: below (K2,
     K7, P003).
  3. *Sanity checks give one explicit (target, source, size strategy) satisfying all hypotheses*:
     `ex:bernoulli` (Section `sec:examples`) and below.
  4. *A lower bound states its class of learners explicitly*: `def:class`, with
     $\mathcal C(\mathcal P_L)=\mathcal C_L$ of PMRM26 / P003 Definition 3.9.
- Conventions of the roadmap changed, if any: none. The roadmap pins the one-sided strict drift
  $\mu_k-\mu'_k<L_k$ and "consistency is the notion of arXiv:2610.21582"; the paper uses P003's
  formal class for $\mathcal P_L$ (that notion) and adds the classes of the three other drift sets,
  declared in `def:drift`, `def:class`. Learners observe the source data $D$ (the roadmap's
  Definitions: "an LML algorithm whose initial state is the source data"; P003 Definition 3.6).

### Correspondence with the source (external paper)

The statement of Theorem 2 of PMRM26 is copied in `literature/notes/PMRM26.md` (Results). `cor:source`
is that statement in our notation: $\mathcal P([0,1])_L=\mathcal P_L$, $\mathcal C_L=\mathcal C(\mathcal P_L)$,
"a prior strategy $\pi'$ that comes from a bandit game played over $T'=f(T)$ rounds" = for each $T$
the counts of a prior bandit game over $f(T)$ rounds (P003 Definition 5.1),
$\mathbb E_{\nu',\pi'}[N'_a]=\mathbb E_{\nu'}[N'^{(T)}_a]$, $\mu_1=\mu^\star$ with arm 1 the unique
optimal arm, items (i), (ii) with the same hypotheses and the same right-hand sides. Two reading
choices, both those of P003 (accepted as the roadmap's F0):
- **The learner's observation.** In PMRM26 Appendix E the learner of the online phase sees $I_t$, the
  whole ordered prior history; P003's transfer learners see only the source data $D$. For a
  bandit-game source $D$ is a function of the ordered history, so every P003 learner is a learner
  of PMRM26, and our class $\mathcal C(\mathcal P_L)$ is the restriction of theirs to learners using
  $D$ only; on this subclass `cor:source` and Theorem 2 have the same conclusion. Learners that use
  the interleaving of the prior game are not covered (said in the Scope paragraph and the Related
  work).
- **"Every prior strategy"** in the class is read as every source strategy of size rules (P003).
- **$\mu_1=1$**: PMRM26 does not give a value to $1/\mathcal K_{\inf}(\nu_a,1)$; we take $0$ (said after
  `cor:source`).

Steps of the source proof filled in or simplified (marked in the paper where they are used):
- Continuity of $\mathcal K_{\inf}$ in its second argument (PMRM26 cites HT15 for it, in Case 2 of
  the proof): not a gap. It is published, HT10 Lemma 2 with Theorems 7(i) and 8 (continuity of
  $D_{\min}=D_{\inf}$ in $\mu<1$ on laws on $[0,1]$; note HT10). Choosing $Q'$ before $Q$
  (`lem:alternative`, Case 2) only makes our proof self-contained (a second use of `lem:window`
  instead of the continuity); the paper presents it as a simplification, not as a contribution
  (abstract, Gap paragraph, Step 2 of `sec:overview`, the remark after `lem:alternative`, the
  appendix of sources).
- Lemma 23 of PMRM26 states a sequence with means $\mu+\varepsilon_n$; we need a window of
  arbitrary width at an arbitrary level with $m(P)\le\mu$ (including $m(P)=\mu$, used at the
  boundary): `lem:window`, with the convexity step written out (density of $P$ with respect to the
  mixture, concavity of $\ln$).
- Membership of the alternative in the drift set (the source requires $|\tilde\mu_a-\tilde\mu'_a|\le L_a$
  in $G_a$ but does not check it for the sequences of Case 2): `lem:alternative` checks it for the
  four sets.
- The kl inequality at $q\in\{0,1\}$: `lem:kl`.

## Closest known

- **K2** (PMRM26, Theorem 2): the statement of `cor:source`. Attempt to derive `thm:main` from it:
  K2 is stated for bandit-game priors, the closed two-sided set, a unique optimal arm, and the
  hypothesis $\limsup_T\mathbb E N'_a/\ln T<\infty$ in (i). (1) Size rules that are not bandit games
  (P003 Proposition 5.5(c): cyclic size rules for $K\ge3$) are not covered by K2; its proof (Lemma 22)
  writes the prior phase as rounds of one bandit game, which a size rule is not. (2) For the
  one-sided sets, $\mathcal C(\mathcal P^+_L)\subset\mathcal C(\mathcal P_L)$, so K2 applies to these
  learners, but only at pairs of $\mathcal P_L$; at pairs of $\mathcal P^+_L\setminus\mathcal P_L$
  ($\mu'_a>\mu_a+L_a$) K2 says nothing. (3) Several optimal arms: not covered. (4) The removal of the
  $\limsup$ hypothesis in (i) is not a gain in substance (the conclusion is $0$ when it fails); the
  paper says so (paragraph Constants). So `thm:main` is a mild generalisation of K2, and
  `cor:source` is K2 in P003's setting. This is an external paper (F1): the claim is the blueprint
  of K2, not novelty.
- **K7(a)** (PMRM26 §4.2, tightness): the bound is not tight for fluctuating sizes. Consistent with
  `thm:main` (which sees only $\mathbb E N'_a$); quoted in the Scope paragraph and in the degenerate
  cases of `sec:examples`. `oq:fluctuations` asks for the version with $\mathbb E[(1-K'N'_a/\ln T)_+]$
  for value-driven sizes.
- **K7(b)**: a learner consistent for every $L$ gains nothing. Consistent: such a learner is in
  $\mathcal C(\mathcal P_{\mathbf 1_K})$ (P003 Proposition 5.8(b)), and for $L=\mathbf 1_K$ we have
  $\mu^\star-L_a=\mu^\star-1\le0\le\mu'_a$. Either $\mu'_a>\mu^\star-1$ (item (ii): the classical
  bound), or $\mu'_a=0$ and $\mu^\star=1$, where $K_a=\infty$ and the bound is $0$ anyway. So
  `thm:main` gives the classical constant for this class whenever it is non-trivial.
- **K3, K4** (upper bound of KL-UCB-Transfer, matching when sizes concentrate): K3 not proved
  here; `cor:concentration` is the lower-bound half of K4 (with `lem:positive-part`, PMRM26's own
  Appendix D argument, applied to the lower bound instead of the upper bound). `ex:bernoulli`
  remarks that K3 has the same first-order constant for deterministic sizes on that instance
  (strict two-sided drift, so K3's hypothesis holds).
- **K1** (ACML 2025, Gaussian, deterministic sizes): different model (Gaussian), deterministic sizes;
  not used.
- **P003** (library, `thm:main`, `cor:fundamental`): the divergence decomposition and the
  fundamental inequality with a source. Our `prop:fixed` is `cor:fundamental` with $Z=N_a(T)/T$ and
  `lem:kl`; the lower bound itself is not in P003 (its open question `oq:deterministic` is about the
  classes, not the bound).
- **P002** (library, `prop:lower`): a lower bound for a drift between laws, deterministic sizes, a
  known finite support, a class consistent for one sequence of sizes. Different model; with the mean
  gap as $d$ it gives the deterministic-size case of `thm:main` on finitely supported laws, for a
  larger class of learners, but not random sizes or general laws on $[0,1]$.
- **PMM25, Theorem 3**: deterministic sizes, pseudo-distance, constant written as a supremum over
  pairs of alternatives. With the mean gap as pseudo-distance one expects the deterministic-size
  case of `thm:main` (P002 identifies the supremum with $(1-cK')_+/K$ on finite supports, its C3
  statement); not checked here for general laws on $[0,1]$, so the paper does not claim it. It
  cannot give random or adaptive sizes.
- **CL24, Theorem 3** (arXiv:2405.02594v2, §4.1, proof in App. D.2; note CL24): regret lower bound
  for $(C,p)$-consistent policies (regret $\le CT^p$ on every instance of $\mathcal I_V$, one constant
  $C$; Definition 3), unit-variance Gaussian laws, deterministic offline sizes $T_S(a)$ (part of the
  instance), two-sided closed bias set $|\mu^{on}-\mu^{off}|\le V$. Its per-arm form (50) is, in our
  notation, $\mathbb E N_a(T)\ge((1-p)\ln T-T_S(a)\mathcal K'_{a,\epsilon})/((1+\epsilon)^2\mathcal K_a)-c_\epsilon$
  with the Gaussian $\mathcal K_a=\Delta^2/2$, $\mathcal K'_{a,\epsilon}=(\mu_a+(1+\epsilon)\Delta-V-\mu'_a)_+^2/2$
  (checked from (51)–(55): online KL $(1+\epsilon)^2\Delta^2/2$, offline KL $\max\{(1+\epsilon)\Delta-\omega,0\}^2/2$,
  $\omega=V+\mu^{off}-\mu^{on}$). So it is the Gaussian, deterministic-size, non-asymptotic counterpart
  of `thm:main`, with the same alternative (online mean raised, offline mean raised just into the
  bias constraint). Attempt to derive `thm:main` from it: impossible, (1) Gaussian laws vs laws on
  $[0,1]$; (2) deterministic sizes vs size rules (random, adaptive); (3) their class is uniform
  ($C$ fixed over $\mathcal I_V$), ours pointwise ($o(T^\alpha)$ for each pair and every $\alpha$),
  neither contains the other in general; (4) no one-sided sets. Conversely `thm:main` does not give
  theirs (Gaussian, non-asymptotic). Compared in the paper (Closest related work, Table 1), and MIN-UCB
  is one of the simulated algorithms.
- **YTC25, Theorem 5.1** (UAI 2025, arXiv:2505.23165): best-arm identification analogue (Gaussian,
  fixed $T_S$, $\delta$-PAC). Different problem; cited in Related work.
- **HZT26** (arXiv:2605.25789, preprint): free-exploration phase whose per-arm counts are chosen
  adaptively by the learner, same laws (no drift). Lemma 11 is the classical bound with the free
  pulls counted in $T_{i,T}$; Theorem 12 bounds the saving of $(\alpha,\beta)$-probably-saving policies.
  Not a special case of `thm:main` (the counts are chosen by the learner itself; regret counts only the
  second phase) nor conversely; cited as "see also" in Related work.
- **AJSS23, Theorem 2.1 and App. B.1, (10)** (arXiv:2306.09048v1, 2023): best-arm identification
  with offline data collected by an unknown adaptive policy on the online laws (no drift). Their (10)
  writes the expected log-likelihood ratio as $\sum_a(\mathbb E[N^o_a]+\mathbb E[N_a(\tau_\delta)])
  \mathrm{KL}(\mu_a,\tilde\nu_a)$: the step "for the source phase" of `prop:fixed`, with the source
  laws equal to the target laws, three years before PMRM26. Their lower bound sees the offline counts
  only through $\mathbb E[N^o_a]$, the limitation of the Scope paragraph and of `oq:fluctuations`.
  Different problem (fixed confidence, no drift), so it does not give `thm:main`; cited in Related
  work ("see also") and in App. E (round 3, SC3.1).
- **GMS19, Theorem 1**: the case without source; `thm:main` with $\mathbb E N'_a\equiv0$ gives it on
  $\mathcal P^K$ for source-ignoring learners.
- No `[Lean]` entry exists in KNOWN.md.

## Sanity checks

- **No source** ($N'\equiv0$): $x_a(T)=0$, the bound is $1/K_a$ (classical; GMS19 Theorem 1). ✓
- **$\mu^\star=1$**: $K_a=\infty$, bound $0$; no alternative exists. ✓
- **$\mu'_a>\mu^\star-L_a$**: $K'_a=0$ (P006 Prop. 4.2(ii)) and the bound is $1/K_a$ whatever the
  sizes, also for $x_a(T)\to\infty$: right, since the alternative keeps $\nu'_a$ and the source
  carries no evidence against it. ✓
- **Boundary $\mu'_a=\mu^\star-L_a$**: $K'_a=\mathcal K_{\inf}(\nu'_a,m(\nu'_a))=0$ (P006 Prop.
  4.2(iii), upper bound $\ln1$; e.g. $\mathrm{kl}(0.45,0.45)=0$); with bounded $x_a$ the bound is
  $1/K_a$, as in K2(i) with $K'=0$. Unbounded: open (`oq:boundary`, roadmap D2). ✓
- **Very large sources** ($x_a(T)\ge1/K'_a$): bound $0$, consistent with K3(i)
  ($\mathbb E[(\ln T-N'_aK')_+]=0$). ✓
- **Simulations** (`sec:examples`, Figure 1, `notebook/simulate.py`, `simulate.txt`): UCB1, kl-UCB,
  KL-UCB-Transfer and MIN-UCB on `ex:bernoulli` with $N'_2=\lfloor c\ln T\rfloor$; see the paper
  for what they show (illustration only). Round 2: the interpretation of the figure was re-read
  against the table of `simulate.txt`, horizon by horizon (several curves are below the asymptotic
  bound at small $T$, as a liminf allows).
- **$K=2$, Bernoulli**: `ex:bernoulli`, numbers from `notebook/constants.py` (`constants.txt`):
  $K_2=\mathrm{kl}(0.5,0.7)\approx0.087177$, $K'_2=\mathrm{kl}(0.3,0.45)\approx0.047174$; bounds
  11.47 ($c=0$), 10.93 ($c=1$), 8.77 ($c=5$), 6.06 ($c=10$), 0 ($c\ge21.2$). The script also checks
  the alternative of `lem:alternative` (Case 2) with Bernoulli $Q,Q'$: the windows and the
  divergences are as claimed for $\varepsilon=10^{-1},10^{-2},10^{-3}$.
- **Ties**: several optimal arms are allowed; the alternative makes $a$ the unique optimal arm, so
  the consistency of the learner under the alternative covers every $k\ne a$. ✓
- **Infinite divergences**: $\kappa=\mathrm{KL}(\nu_a,Q)$ and $\kappa'$ are finite by construction;
  `prop:fixed` holds in $[0,\infty]$; `lem:kl` handles $q\in\{0,1\}$.
- **Explicit instance satisfying all the hypotheses**: `ex:bernoulli`: $(\nu,\nu')$ in the four sets,
  a deterministic size rule ($\mathbb E$ finite), the UCB source-ignoring learner in the four classes
  (`lem:classes`, from P003 Proposition 5.9), arm 2 suboptimal.
- **Consistency with KNOWN**: K2 (`cor:source` equals it), K7(a) (not tight for fluctuating sizes:
  acknowledged), K7(b) (checked above), K3 (same constant for deterministic sizes).

## Weak points

1. `cor:source` vs Theorem 2 of PMRM26: the learners. Our class (P003) has learners that see the
   source data only; PMRM26's see the ordered prior history. On the common learners the statements
   agree, but `cor:source` is not literally Theorem 2 for learners that use the interleaving. This is
   the reading of P003 (accepted), but a referee may want it called "Theorem 2 restricted to transfer
   learners".
2. `lem:window`, Step 3: the integrability bookkeeping ($\int g\,dP$ defined in $[-\infty,\infty)$,
   $\ln f$ integrable from $\mathrm{KL}(P,Q_0)<\infty$ and $\int(\ln f)^-dP\le e^{-1}$). Standard, but
   it is the only measure-theoretic step written by us; Lean will need the convexity of `klDiv` in
   its second argument or this pointwise argument.
3. `thm:main`, Step 3 (item (i)): the order of limits. $T_0$ and $T_1$ depend on $(\varepsilon,\alpha)$ through
   the alternative; the bound $x_a(T)<1/K'_a$ for $T\ge T_1$ uses $c>0$, which does not depend on
   $(\varepsilon,\alpha)$; the $\liminf$ is taken for fixed $(\varepsilon,\alpha)$, then
   $\alpha,\varepsilon\to0$. I believe it is right, and it is the step a referee should check.

## Searches

- "transfer learning bandits historical data lower bound source samples K_inf consistent algorithms
  adaptive prior policy" (2026-11-17): PMRM26 (arXiv 2610.21582), PMM25 (arXiv 2509.19098), Cai et
  al. (contextual transfer, minimax), offline-to-online hyperparameter transfer (2501.02926), latent
  continuity (2102.02472). Nothing beyond PMRM26 on this lower bound.
- "multi-armed bandit offline data biased mean shift bound lower bound regret change of measure warm
  start" (2026-11-17): CL24 (arXiv 2405.02594, lower bound for biased offline data with fixed sizes),
  hybrid MAB (OpenReview), linear-bandit offline-to-online papers, online pricing with offline data
  (1910.08693). None with adaptive source sizes.
- "bandits with side information from a related source distribution discrepancy bound
  problem-dependent lower bound" (2026-11-17): PMRM26; side-observation papers (Degenne et al. UAI
  2018, Atsidakou et al. ICML 2022), CRIMED (corruption). Not the same model.
- "\"Prevost\" \"Maillard\" transfer bandits lower bound 2025 2026" (2026-11-17): PMM25, PMRM26, and
  the Incognita repository. No later version of PMRM26 (arXiv v1 only).
- "Shivaswamy Joachims multi-armed bandit problems with history lower bound" (2026-11-17): SJ12
  (upper bounds only, lower bounds left open), CL24 citing it, Artificial Replay (2210.00025).
- Forward search in the arXiv listing of PMRM26 (the abs page shows v1 only, 15 Oct 2026): no
  citing work found by the queries above.

## Reading notes

- Revision round 1 (2026-11-17), at the request of referee-scope: CL24 §2, §4 (Algorithm 1,
  Theorems 2–3, Definitions 1–3), App. D.1–D.2.1 (new note `literature/notes/CL24.md`); HZT26 §1–§3,
  §5, App. D.1 (new note); YTC25 pp. 1–6 (new note); GMS20 (10) and §7 (folklore); HT10 Lemma 2,
  Theorems 7–8 (re-checked on the page images); PMRM26 §5.1–§5.2 (KL-UCB and Algorithm 1
  KL-UCB-Transfer, $\delta_t=\ln t+\ln\ln t$) and §9 (experiments), PDF text layer, for the
  simulations. No new search queries: the works were those named by the referee.
- Revision round 2 (2026-11-17), at the request of referee-scope (SC2.3): PMRM26 §5.1–§5.2 (the
  KL-UCB-Transfer index, $\delta_t:=\ln t+\ln\ln t$, Algorithm 1 line by line), §6 (the hypotheses
  of Theorem 3: $|\mu_k-\mu'_k|<L_k$ for every $k$, $T\ge3$) and §9 (the setup of its experiments)
  re-read in the arXiv v1 PDF, text layer (`pdftotext -layout`), and recorded in
  `literature/notes/PMRM26.md` and in its row of `literature/index.md`.
- Revision round 3 (2026-11-17), at the request of referee-scope (SC3.1): AJSS23 (arXiv:2306.09048v1
  HTML, through extracts of a fetch tool): §2 (offline data from an unknown adaptive policy, same
  laws), Theorem 2.1 (offline counts through $\mathbb E[N^o_a]$), Appendix B.1, (10) and the
  sentences around it. Recorded in its row of `literature/index.md`.

- PMRM26: arXiv v1 PDF, text layer (`pdftotext`), 2026-11-17: §4.1–§4.2 (Theorem 1, class
  $\mathcal C_L$, Theorem 2 and the paragraphs after it), Appendix E in full (Lemmas 22–24 and their
  proofs, the proof of Theorem 2). Lemmas 23 and 24 and the outline of the proof were added to
  `literature/notes/PMRM26.md`. Also §6 (Theorem 3, Proposition 4) and Appendix D (the proof of
  Proposition 4, the Lipschitz property of the positive part), added to the note.
- GMS19: (6), (10), (11), Lemma 1, Theorem 1 as recorded in `literature/notes/GMS19.md` (not
  re-read this session).
- P003 v1 (`thm:main`, `cor:fundamental`, Definitions 3.1–3.9, 5.1, Lemma 5.3, Proposition 5.9) and
  P006 v1 (Definition 3.2, Proposition 4.2) read in the repository; numbers checked from the
  compiled `.aux` files of P003 and P006.
