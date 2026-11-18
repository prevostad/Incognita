# Writing a paper of the Incognita library

How a paper is written and how its presentation is judged. [AGENTS.md](../AGENTS.md) §5 is the
contract (structure, what never appears in `paper.tex`, cited results, packages, refereeing); this
file holds the writing rules it points to. The owner adopted them on 2026-11-15, from a study of
writing guides, journal and conference reviewing guidelines, leanblueprint projects and a diagnosis
of the first two accepted papers. They are a first version: the owner reads the papers and adjusts
them.

## 1. The reader

The **target reader** is an expert referee of JMLR or COLT who has never heard of Incognita: a
researcher of the field who knows the standard tools (concentration, change of measure, the
Lai–Robbins bound, the usual algorithms) and reads the paper to decide whether its result is true,
new and worth knowing. Write for that reader:

- tell what is proved, why it matters and what is new before anything else;
- do not explain what an expert knows (too much detail hinders an expert as much as too little);
- explain everything that is new, and the hard step more than the easy ones.

The reader pays for what the author does not say: implicit justifications, sentences whose
logical status must be guessed, results to look for far away, objects to keep in mind. A readable
proof is often **longer**: reduce the density of what is left unsaid, not the number of lines.

One source, three documents (AGENTS.md §5.2):

| Document | For | What it holds |
|---|---|---|
| reader build of `paper.tex` (`P<nnn>.pdf`) | the reader | the paper: no `Uses:` lines, labels or Lean names printed |
| blueprint build (`P<nnn>-blueprint.pdf`) | formalisers, the proof referee | the same text, with every `\uses`, `\proves`, `\extends` printed |
| `DOSSIER.md` | the referees, the owner | roadmap correspondence, KNOWN ids, derivation attempts, sanity checks, weak points, searches |

Never hide proof text in the reader build: the published text is the refereed text.

## 2. The structure of a paper: the owner's papers as the model

**The model is the owner's paper arXiv:2610.21582** (Prevost, Mathieu, Radji, Maillard, *Transfer
learning in bandits from unknown adaptive policies: problem-dependent lower and upper bounds*,
2026; `PMRM26` in `literature/bibliography.json`; read its PDF on arXiv before writing a paper). Copy
its organisation of sections, the airiness of its paragraphs around displayed equations, the shape
of its statements and the way its proofs are written (section 2a below). In this order (AGENTS.md
§5.2; the template `templates/paper/paper.tex` has a slot for each):

1. **Introduction** (`sec:intro`): the problem and why it matters, in a few short paragraphs; the
   main result in informal words with its constant, on page 1 or 2; then a run-in paragraph
   `\paragraph{Our contributions}` with an itemized list, each item pointing to a numbered result;
   then `\paragraph{Outline}`, one sentence naming every section with `\autoref`.
2. **Related work and context** (`sec:related`), its own section: run-in paragraphs by theme
   (`\paragraph{Classical multi-armed bandits}`, …), ending with `\paragraph{Closest related work}`
   and `\paragraph{Gap with the literature}`; a **comparison table** when three or more prior results
   are compared; for each closest result, one sentence on why it does not give the main result; the
   techniques credited to where they come from.
3. **Problem formulation** (`sec:setting`): first the classical setting, recalled, then the new
   one (subsections); the model (what is observed when, what the learner knows, the filtration),
   the definitions and assumptions as nodes, run-in paragraphs for conventions
   (`\paragraph{Notational convention}`, …). Standing assumptions of a section are `assumption`
   nodes that later statements `\uses`.
4. **One section per main result**, in the logical order of the paper (for instance: lower bound,
   then algorithm, then upper bound, then extensions). Each section recalls the classical result
   first (a theorem with its reference), then states the new one. `thm:main` carries every
   quantifier, within the first 5 pages when possible, every symbol defined before it. A theorem
   is followed by "(see the proof in Appendix …)" and by discussion paragraphs with run-in titles
   (`\paragraph{Comparison with KL-UCB}`, `\paragraph{Comparison with the lower bound}`,
   `\paragraph{Tightness}`, `\paragraph{Necessary and sufficient condition}`): the nature of the
   constants, the **scope** in plain words (no item ids), an interpretation. An algorithm section
   recalls the classical algorithm, then displays the new index in an `equation` with one sentence
   of intuition, then gives the pseudo-code (`algorithm`, `algpseudocode`), the algorithm's name in
   `\texttt{}`.
5. **How the proofs work** (`sec:overview`), mandatory beyond 10 pages: the decomposition, the key
   lemmas, how they combine, where the difficulty lies, and a map of the appendices.
6. **Numerical experiments** (`sec:examples`; criterion W16: simulations that compare with the published
   algorithms, almost always; a paper without them must say why, for one of the reasons W16 allows): the setup in a paragraph, figures of curves (tables only for summaries),
   then `\paragraph{Interpretation of Figure 1}`; one explicit instance satisfying all the
   hypotheses at once; the degenerate cases.
7. **Conclusion and open questions** (`sec:open`): what is shown, the limitations, then the
   `openquestion` environments, each stated completely (every quantifier, the class, the criterion,
   why the method stops there); the roadmap item goes in `\extends{D8}`, never in the text.
8. `\appendix`: **Useful lemmas** (`sec:cited`): the results from other papers, each a cited node
   titled `[From \cite{KEY}, Proposition 14]`, introduced by one sentence saying what it is for;
   then **one appendix per theorem**, "Proof of Theorem 3", written as in section 2a; then
   **Sources of the techniques** (`sec:attribution`) and **Notation** (`sec:notation`, "Every
   symbol is a link to its definition").

The main text is about 15 pages at most when the paper is longer than 25 pages: only the main
statements (theorems, corollaries) and at most the one lemma that makes the interest of the work;
**every other lemma and every proof goes to the appendices**, one subsection "Proof of Lemma X" per
lemma.

## 2a. The house style (the owner's rules)

These rules come from the owner's papers and notes. They complement section 5–6 (readability of
proofs) and win over them in case of conflict.

**Air and displays.**

- Every formula that matters is **displayed**, in an `equation` environment (numbered when it is
  referred to later, `equation*` otherwise) or in `align` for a chain. Never more than one
  non-trivial relation in running text.
- Short paragraphs of two to five lines, separated by a blank line, alternate with displays. A
  paragraph that contains seven relations or more is rewritten.
- Conditions on parameters are displayed one per line before the statement that uses them, for
  example "for all $\mu^\dagger$ such that" followed by a display of $\mu^\dagger>\mu_a$,
  $\mu^\dagger\le\mu_1$, $\mu^\dagger\le\mu'_1+L_1$.

**Statements.**

- The quantifiers come first, in order: "For all distributions …, for every suboptimal arm $a$ and
  for every $T\ge3$, the algorithm \texttt{KL-UCB-Transfer} satisfies:", then items (i), (ii), each
  with its displayed bound.
- **Bounds are fully explicit** whenever possible: no $o(\cdot)$ and no "for $T$ large enough";
  valid from $T\ge3$. Put a constant in front of $\varepsilon$ rather than a condition on $T$. When
  an asymptotic hypothesis (for example $\log t=o(f(t))$) is replaced by a constant, state and
  prove the link.
- `:=` for a definition, `=` for an equality.

**Proofs of a regret bound** (the appendix "Proof of Theorem X"):

1. "To prove this theorem we will use the following decomposition": a **deterministic
   decomposition lemma**, $N_a(T)\le K+\dots$ as a sum of sums of indicators of events, each term
   named with `\underbrace` ($A$, $B$, …), followed by "(see the proof of Lemma 4 in Subsection
   B.1)".
2. "From this decomposition we will use the following lemmas to control each term": **one lemma
   per term**, in expectation, with an explicit bound, each followed by "(see the proof in
   Subsection B.2)" and one sentence saying whether it is classical ("as in the classical proof of
   KL-UCB [CGMMS13]; no contribution here") or new and why.
3. The proof of the theorem from these lemmas: the choice of $\varepsilon$ (defined with `:=`, with
   the reason of the choice), the sum of the bounds, the conclusion.
4. One subsection "Proof of Lemma X" per lemma.

**Writing a proof.**

- Long **aligned chains** of $\le$ and $=$ on indicators of events written with $\cap$, **one
  transformation per line**, the justification at the end of **every** line that is not a pure
  rewriting (rule B10).
- Short linking sentences between the chains: "Let us look at $A$, we have", "Now using Lemma 7 we
  get", "Then we split according to this event", "Using Lemma 7 and that $\mu_1-\mu^\dagger\ge0$ we
  get", "Finally we have". Each step ends by saying what it obtained.
- Split explicitly on events (`\mathbf 1(G>0\cap\dots)+\mathbf 1(G\le0)`) rather than hiding a case
  in a sentence.
- An "Idea." paragraph before every proof that is not routine; a Setting/Goal block before a long
  one (section 6).

**Conventions for index policies** (unless the roadmap pins others):
$N_k(t):=\sum_{u\le t}\mathbf 1(A_u=k)$ (round $t$ included); the index $U_k(t)$ is computed at the
end of round $t$ from $N_k(t)$, $\hat\nu_k(t)$ and $\delta_t$, and $A_{t+1}\in\arg\max_kU_k(t)$ for
$t\ge K$; the fundamental inequality $\sum_{t}\mathbf 1(A_{t+1}=k,\,N_k(t)=s)\le1$; the exploration
rate $\delta_t:=\ln(t\vee3)+\ln\ln(t\vee3)$.

**Navigation (mandatory).**

- **Every quantity defined in the paper is defined with `:=`** (never `=`), in a sentence of its
  own, and **every later use of it is a hyperlink back to the place where it is defined**: an anchor
  at the definition (`\newcommand{\dt}[1]{\hypertarget{#1}{}}`, then `\dt{s:kinf}` just before the
  `:=`) and one macro per symbol (`\newcommand{\sy}[2]{\hyperlink{#1}{#2}}`, then
  `\newcommand{\Kinf}{\sy{s:kinf}{\mathcal K_{\inf}}}`), used **everywhere** after the definition,
  in statements, proofs, displays and tables alike. The same for defined words (*activated*,
  *rejected*): a macro `\term` that links to their definition. A symbol typed without its macro
  after its definition is a defect (W15).
- **Every lemma, proposition, theorem, definition, assumption or equation used is cited by
  `\ref`/`\eqref`** (a hyperlink to it), at the place where it is used, never as "the previous
  lemma", "the above", "by the same argument" without the link. A reference to a result that is not
  on the same or the previous page also says its name and what it brings ("Lemma 5 (*the IMED phase
  lifts the water level*), which bounds …"), not only its number.
- The algorithm's name is a link to its pseudo-code.
- The appendix **Notation** lists every symbol, each a link to its definition ("Every symbol is a
  link to its definition").

**Citations.** Author–year style, as in the owner's papers: `natbib` with `\bibliographystyle{plainnat}`;
`\citet{KEY}` in running text ("Garivier et al. (2019) show"), `\citep{KEY}` in parentheses, with a
locus when a precise result is used (`\citet[Theorem~3]{HT15}`). Never alpha keys such as
"[GMS19]" in the PDF. The keys of `literature/bibliography.json` are unchanged; every entry of
`refs.bib` has its authors and year so that the label prints correctly.

**Language.** English, plain, "we". No promotional adjectives; "optimal" only for a result paired
with a lower bound in the same class.

## 3. The seventeen presentation criteria

The scope referee applies them to the **reader build** (the PDF's text, `pdftotext paper.pdf -`),
in addition to the source. Each has a yes/no test. **R** marks a criterion whose failure is
usually a readability defect (class R, AGENTS.md §5.4); **P** marks one whose failure is usually a
presentation defect (class P). The class of a given failure is decided by the test of section 4,
whatever the mark: a failure of an R criterion that an expert could fix without anyone re-checking
is P, and a failure of a P criterion that hides or distorts what is claimed is R.

### The frame of the paper

- **W1 (R) An introduction for an expert who does not know Incognita.** It gives the problem and
  its motivation, the main result in informal form on page 1 or 2 with its constant, what is new
  against the closest result, and the organisation. *Test*: after the introduction alone, can the
  referee write the three-sentence summary a report opens with (setting, main result, exact
  difference from the closest prior work)?
- **W2 (R) An explicit comparison with the best known bounds.** They are stated exactly, with the
  differences of assumptions (class, known or unknown horizon, criterion, constants), in a table
  from three competitors on; related work is a comparison, not a list. *Test*: for each main
  result, is the closest published bound for the same problem quoted, and is it said why it does
  not give the result?
- **W3 (R) The main text carries the architecture of the proof.** The decomposition, the key
  lemmas, the new step and the hard step are named, with pointers to the appendices; the appendices
  need not be read to believe the result. *Test*: could the referee explain the central argument
  in a talk after reading the main text only?
- **W4 (P) Title and abstract match the theorems.** Same class, same criterion; no "optimal"
  without both bounds; an abstract of about 200 words, without citations. An abstract that promises
  more than the theorems is R. *Test*: does each claim of the title and abstract correspond to a
  numbered result, with the same class of instances and the same criterion?
- **W5 (P) Each section says first what it is for**; the appendix proofs follow the order of the
  main text, each with a short plan. *Test*: does the first paragraph of each section and appendix
  say what it establishes and for what?

### Statements and notation

- **W6 (R) Every symbol is defined before use, with one meaning in the whole paper.** A notation
  table beyond about 30 symbols. *Test*: draw ten symbols at random from the proofs: is each
  defined before its first use, with a single meaning?
- **W7 (R) Self-contained statements.** The hypotheses are in the statement or named (an
  `assumption` node, A1, A2), the quantifiers explicit and in order, the dependence of every
  constant said, also inside $O(\cdot)$. *Test*: can the statement be read, and formalised, without
  the surrounding text? (A hypothesis used in the proof but absent from the statement is a gap, G.)
- **W8 (P) Each main result is followed by an interpretation**: when it improves on prior work,
  which term dominates, a worked instance (Bernoulli rewards, $K = 2$), why each hypothesis is
  needed (or a counterexample without it). *Test*: is there such a remark after each main result?

### Proofs

- **W9 (R) Detail proportional to difficulty.** No "standard", "clearly" or "it is easy to see" on
  a step the result depends on, and the hard step at least as detailed as the easy ones (the
  typical defect of AI-written text: easy steps detailed, the hard step dispatched). *Test*: is
  every step justified by a numbered result, a precisely cited result or an explicit computation,
  and is the longest justification where the difficulty is? (A load-bearing step justified only
  by "clearly" is a gap, G.)
- **W10 (P) An "Idea." paragraph before every proof longer than half a page**, then named steps;
  the hierarchy follows mathematical importance, not the granularity of the Lean. *Test*: does
  each such proof open with its idea and its plan?
- **W11 (P) Local readability**: the rules B7–B12b below (a Setting/Goal block, one non-trivial
  relation per sentence of running text, chains in `align` with a justification on every line that is not a pure rewriting (B10), a
  sentence of conclusion after each chain). *Test*: pick three proofs: do they follow them? and
  apply the ten-line test of B10.

### Honesty and cleanliness

- **W12 (R) Calibrated claims.** "Optimal", "first", "new", "tight" rest on a theorem (an upper and
  a lower bound in the same sense and class) or on a citation; the limits are said in a Scope
  remark, in words, without roadmap item ids. *Test*: is each such word backed, and is what is not
  proved said?
- **W13 (R) Nothing of the process.** No KNOWN id (`K12`), roadmap id (`D8`) outside `\extends`,
  raw label, "(to be checked)", "we read only its abstract", "this paper serves direction …", web
  query or weak-points list in the PDF: all of that goes to `DOSSIER.md`. *Test*: search the PDF's
  text for them. (CI refuses KNOWN ids and "(to be checked)" in a changed `paper.tex`; a single
  stray id is P by the test of section 4, a printed process section is R.)
- **W14 (P) Cleanliness.** The same notation and numbers in the abstract, the theorems and the text;
  no repetition of the main result; no remnant of the template. *Test*: compare the abstract with
  the theorems, and look for "<", "TODO" and duplicated paragraphs.
- **W15 (P) The house style** (section 2a): the sections of section 2 in their order; formulas that
  matter displayed in `equation`/`align`, short paragraphs between displays; statements with their
  quantifiers first and explicit bounds; regret proofs as a decomposition lemma, one lemma per term,
  then one subsection per lemma, written as aligned chains on indicators with linking sentences;
  every defined quantity defined with `:=` and every later use of it a link to its definition;
  every result used cited by a link at the place where it is used. *Test*: put the PDF next to
  arXiv:2610.21582 and compare the organisation of the sections, one main-text page and one
  appendix proof; in the source, pick ten symbols used in the proofs and check that each is typed
  with its link macro and defined with `:=`; pick five places where a result is used and check the
  `\ref`. A failure that makes a proof hard to follow (a dense paragraph of relations, a chain
  without its steps, a result used without saying which) is R.
- **W16 (R) Numerical experiments, compared with the literature** (owner, 2026-11-16, reinforced
  2026-11-17). Every paper has a section "Numerical experiments" (as in arXiv:2610.21582), not only
  those that propose an algorithm:
  - **Compare with the literature.** The algorithms of the paper (or, for a lower bound or an
    impossibility, the best published algorithms of the setting) against **at least two published
    algorithms** of the same setting, the closest ones (for example KL-UCB, IMED, Thompson sampling,
    the batched algorithms of the literature), implemented from their papers; for a lower bound, plot
    the bound against the regret of these algorithms.
  - **Curves, not tables.** Figures of curves: the regret (or the counts, or the quantity the
    theorem is about) against the time or the horizon, the mean over the runs with a confidence band,
    a logarithmic time axis when the theory is in $\ln T$; one figure per message, a legend that
    names every algorithm. A table only summarises numbers that a figure already shows.
  - **Simulate the algorithm that is proved.** The algorithm of the paper runs exactly as in its
    theorems: the same index, the same rules and parameters inside the range the theorems cover
    (for example the default parameters). Never prove a result with some parameters and simulate
    with others. Large constants in the *bound* are not a reason to change the algorithm: run it
    as stated. A variant outside the theorems (other parameters, a heuristic simplification) may
    only be an *additional* curve, labelled as not covered by the theorems, never in place of the
    proved algorithm; when the proved algorithm cannot be run at all (its definition needs a
    quantity that cannot be computed), say so and why.
  - **Setup and reproduction.** The instances (including at least one hard instance of the
    theorem), the horizon, the number of runs, the seeds, the algorithms and their parameters; the
    scripts and their outputs in `notebook/`, the figures as PDF made by a committed script, and how
    to reproduce them. Runs stay small: the whole campaign takes at most about thirty minutes on four
    cores (fewer runs, a shorter horizon, a coarser grid of horizons otherwise).
  - **Simulations illustrate.** Never present them as evidence for an asymptotic constant or a
    second-order term (a horizon of $10^5$ does not show a $\ln\ln T$ term); say what they show at
    finite horizon, and only that.
  - **Valid reasons for no simulation** (a paragraph in the section says which): a setting paper
    (kind `definitions`); a paper whose setting has no algorithm and no quantity that can be
    computed. "The result is asymptotic", "the remainder terms are astronomical" and "the
    constants are not explicit" are **not** valid reasons.
  *Test*: is there a figure of curves comparing the paper's algorithms (or its bound) with at least
  two published algorithms, with reproducible scripts, the paper's algorithm run with parameters its
  theorems cover, or a paragraph giving one of the valid reasons? A missing section, or a missing comparison, without a valid reason is **R** (major); a
  table where a curve was needed, too few runs or a missing confidence band is P.
- **W17 (P) Economy of notation** (owner, 2026-11-18). Few symbols, each one earning its place:
  - **A symbol must serve.** A quantity gets a symbol only if it is used at least three times after
    its definition; otherwise write it in words or expand the formula where it is used.
  - **Local quantities stay local.** A quantity used in one proof only is defined inside that proof,
    not in the setting and not in the notation table.
  - **No near-homonyms.** Never two symbols for the same object, nor near-identical symbols for
    different objects ($N_a$, $\tilde N_a$, $\bar N_a$, $N_a'$ side by side); at most two decorations
    on a symbol (for example one subscript and one superscript).
  - **Standard notation first**: the notation of the field (Lattimore and Szepesvári's book, the
    owner's model paper arXiv:2610.21582, the cited papers) rather than a new one for a known object.
  This does not weaken section 2a: every symbol that remains is defined with `:=` and linked to its
  definition; there are simply fewer of them. *Test*: list the symbols introduced in the main text
  and count the uses of each; flag those used fewer than three times, those used in one proof only,
  and the near-homonyms; then read the main theorem's statement: can it be read with at most two
  look-ups in the notation table? A few superfluous symbols is P; a main theorem that cannot be read
  without repeated look-ups, or more than a third of the main text's symbols used fewer than three
  times, is R.

## 4. When a presentation defect blocks

A presentation defect is **R** (readability, blocking) when it prevents an expert from
understanding or checking what is proved, or hides or distorts what is claimed. *Test*: **could an
expert of the field fix it without anyone re-checking after him?** If yes, it is **P**. Examples:
no introduction, a statement before its symbols are defined, no proof overview beyond 10 pages, a
notation clash inside a statement, a printed "Closest known" section of derivation attempts: R. A
typo, a missing interpretation remark, a stray KNOWN id: P.

R counts like L for the verdict (`major`), with one limit (AGENTS.md §5.4): a revision round spent
on R defects is enough. When, after a revision, only R defects remain that were raised in an
earlier round and were addressed in part, the referee rates them P (the paper is then accepted if
nothing else blocks), and lists what is left as P defects.

Two operational tests summarise the criteria:

1. **Reader test** (reader build, main text only). An expert reading in one sitting can state the
   main theorem and why it matters after pages 1–2; explain the proof strategy (which
   propositions, where the difficulty lies) after the overview; check every main-text proof with
   the stated results only. No label, roadmap number, KNOWN id or process section is visible.
2. **Formaliser test** (blueprint build). Every statement is complete (quantifiers in order, every
   hypothesis, measurability, nonemptiness and integrability included); every proof uses only the
   nodes of its `\uses` and textbook facts that Mathlib or LML provide; a formaliser can write each
   appendix proof without inventing an argument.

## 5. Rules for proofs: the macro level

Ported from the owner's readability rules (2026-11-04), which rest on the literature on how
mathematicians read proofs and on cognitive load.

- **A1. The target reader is explicit** (section 1). Do not detail what he already knows.
- **A2. Before any proof longer than half a page**, a paragraph "Idea." (3 to 5 lines), **then the
  plan in named steps**.
- **A3. Linear text cut into steps**, each announced by what it establishes ("Step 2: we show that
  …"). No Lamport-style tree proofs (the reader jumps around).
- **A4. The hierarchy follows mathematical importance, not the granularity of the Lean.** Technical
  facts go into separate lemmas (in the appendices), and the main argument stays visible. (Only
  `formalisation.tex` follows the Lean.)
- **A5. Each reference says what it brings**: "by (3.17), which bounds $N_a(t)$ by …", not "by
  (3.17)". A result that is not on the same page or the previous one is recalled on the spot.
- **A6. Few objects to keep in mind**: reintroduce an old notation locally, move routine
  computations to a lemma or an appendix, avoid piling up indices.
- **A6a. A long appendix is written top down**:
  - first the result it proves and the **skeleton of its proof**: the decomposition and what each
    term costs;
  - then the lemmas, **grouped by the question they answer**, under headings in the form of a
    question ("Why is the leader reliable?");
  - under each lemma, a line **"Role."**: where it is used and to show what;
  - a small dependency graph (or table) at the head of the appendix;
  - forward references are allowed when they summarise the lemma in one sentence.
- **A6b. Defined vocabulary is treated like symbols**: each technical word (*activated*,
  *rejected*, *high*) is defined once, linked to its definition at least in statements and in
  Setting/Goal blocks, and listed in the notation appendix.
- **A6c. A lemma of constants or small properties is ordered by use**: what is used often comes
  first, and each item says where it is used ("used in Lemma …").
- **A6d. A reference to a distant lemma carries its name**, not only its number ("Lemma 5 (*the
  exploration phase lifts the water level*)"); a class or an event used far from its definition is
  recalled in a few words.

## 6. Rules for proofs: the micro level

- **B7. A separate opening block**, before any computation: what is fixed and what is assumed,
  then the goal.
  > *Setting.* Fix $\varepsilon \in (0, \varepsilon_0]$ and $L \ge 1$; assume (H1)–(H3).
  > *Goal.* Show that $\mathbb{E}[N_a(t_L)] \le \dots$
- **B8. Every new quantity is introduced alone**, in its own sentence ("Let $T := \dots$"), never in
  the middle of a computation; with `:=`, and a hyperlink anchor when it is used far away.
- **B9. Every non-trivial relation is displayed**; never more than one non-trivial relation in the
  running text of a paragraph.
- **B10. Chains of more than two relations go in `align`**, one step per line, and **every line
  that transforms the expression carries its justification on the line itself, on the right**
  (owner, 2026-11-17, as in his paper P000): the result used, with its link; the hypothesis used;
  or the named computation ("Pinsker", "union bound", "since $x \le e^{x-1}$", "by definition of
  $\tau$"):
  `&\le \dots && \text{(Lemma~3, since } n \ge n_0\text{)}`.
  Only a pure rewriting (the same expression rearranged, expanded or simplified by algebra a reader
  does at a glance) may go without one. The justification says what is applied, not just a label:
  "(Lemma~3)" is enough only when Lemma~3 applies with no further condition. *Test*: pick ten lines
  of `align` at random in the appendix proofs and count those that transform the expression without
  a justification. A few easy lines without one is P; a load-bearing step without one, or more than
  a third of the lines tested, is R.
- **B11. A sentence of purpose before each chain, a sentence of conclusion after it** ("Hence we
  have shown that …"). Each step ends by stating what it obtained.
- **B12. Spacing and typography follow the structure of the formulas**: visual groupings agree with
  the syntax; never two formulas separated only by punctuation; never a sentence that starts with a
  symbol.
- **B12a. A paragraph that checks several facts is a list "claim (reason)"**: the claim first,
  displayed if it contains a fraction, then the reason, with the definition used recalled and the
  intermediate computation written. Rule B9 applies to the "easy" checks too, which are precisely
  the ones left compact.
- **B12b. In statements, hypothesis and conclusion are separated by "Then"** (not "Let … be in E.
  (i) …").

Also: every symbol is defined with `:=` before its first use and keeps one meaning in the whole
paper (W6); macros are defined in the preamble by `\newcommand` only.

## 7. Failure modes of AI-written mathematics

Documented in recent studies of AI-written proofs (First Proof, Proof or Bluff, Agents4Science,
Tao's ICM 2026 lecture). Avoid them as an author; look for them as a referee.

| Failure | What it looks like | Caught by |
|---|---|---|
| Uneven detail | routine parts meticulous, the hard step "by standard arguments" | W9 |
| Premise smuggling | a non-trivial claim presented as background knowledge | W7, W9 |
| Silent reformulation | an easier or modified problem solved, an unneeded hypothesis added | W4, W7, W12 |
| Local-to-global gaps | each step right, the conditions that make them compatible never checked | W3, W9 |
| Wrong citations | the source does not contain the claim, or states a weaker version | AGENTS.md §7 |
| Missing attribution | known results not marked as known, recent results called "standard" | W2, appendix of sources |
| Overclaiming | partial results presented as complete, "optimal" with one bound | W4, W12 |
| Polish hiding errors | flawless typesetting over a wrong argument | section 8 |
| Verbosity without ideas | long, pedantic, the conceptual explanation removed | W3, W10 |
| Notation drift | sections written by different sessions disagree | W6, W14 |
| Structural artefacts | repeated sections, abstract and body that disagree | W14 |
| Generalising from small cases | a pattern seen for $K = 2$ claimed for all $K$ | W7, W12 |
| Formalisation mismatch | the Lean statement is not the LaTeX statement | AGENTS.md §6 |

## 8. For referees: polish is not rigour

Agent reviews check correctness well; readability less so. An agent's `accept` says nothing about
the reading load. Never count length, polish or formatting as evidence of correctness: check the
hardest step first, compare its detail with the routine ones, compare the abstract with the
theorems, and check that every hypothesis used in a proof is in its statement.
