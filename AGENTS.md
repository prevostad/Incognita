# Working in Incognita

This is the contract for every AI agent working here. Your role prompt
(`agents/roles/<role>.md`) says what to do in your session; this file says the rules, and wins over
anything else you read in the repository. [README.md](README.md) gives the overview.

Incognita produces **new** mathematics in three layers:

1. **Roadmaps** (`roadmaps/<Roadmap>/`, approved by the owner, or proposed by agents and approved
   after his veto window): what may be worked on, the pinned conventions and definitions, the open
   directions, the acceptance criteria for papers, `KNOWN.md`, what the owner already knows, and
   `directions.md`, the open questions of accepted papers that became candidate directions.
2. **Papers** (`papers/<P>/`): short notes written by agents, one main result each, refereed by two
   agents. A paper is also the blueprint of its formalisation. Accepted papers form a **library**:
   each one builds on others (`depends_on`), and its certification (section 9) says how far it can
   be trusted.
3. **Formalisation** (Lean 4, Rémy Degenne's `formalize-paper` method): the statements of an
   accepted paper are frozen in `Statements/`, then proved in the library `Incognita/`. Lean is the
   final arbiter.

Lean checks proofs. It does not check that a statement means what it should, that it is new, or
that it matters. Most rules below protect these three things; when a rule slows you down, it is
doing its job.

## 1. Your session

**Read `.agents/task.md` first.** It gives your role, your target (a paper, a pull request, a
roadmap), the pull request number and head SHA if any, the paper id (for `write-paper`, the number
of the new paper: you choose its slug) and its Lean prefix, the roadmap with the path of its
`KNOWN.md` (and of a private file of KNOWN entries, if any), the deadline, the situation (for
example the errata entries to resolve), and the list of context files the script prepared in
`.agents/`:

| File | Content |
|---|---|
| `open-prs.md` | the open pull requests with their role and target: those targets are busy, never work on them |
| `pr.diff` | the diff of the pull request (from its merge base with `main` to the head named in task.md) |
| `pr.txt` | its title and description |
| `reports.md` | previous trusted reports on the pull request (referee reports, reviews, fix rounds), oldest first; for `write-paper` and `referee-scope`, also the referee reports of the roadmap's rejected papers; for `bibliographer` on a paper, the scope referees' reports on the pull request that added it |
| `revision.diff` | for a reviewer who already reported on this pull request: the diff from the head of its last report to the current head (for a paper, its directory only) |
| `papers.md` | for `write-paper`: the papers of the roadmap and the items they serve, on `main`, in open pull requests, and rejected |
| `items.md` | for `write-paper` and `propose-roadmap`: the items of the roadmap (D, F, C) on `main`, open, closed, covered or dropped (`scripts/certify.py items`) |
| `roadmaps.md` | for `propose-roadmap`: every roadmap with its status, domain, KNOWN.md state, extensions and free items, and the domains of the approved roadmaps |
| `known-private.md` | the roadmap's private KNOWN entries, when the owner gives them (never quote them) |
| `ci-log.txt` | the end of the failing CI logs (workflows CI and Papers) |
| `owner-answers.md` | the owner's answers on the pinned issue "Questions for the owner", after the questions they answer: never ask again what is answered there |

Only the files listed in task.md exist. The working tree is a clone of the repository, at `main` or
at the pull request's head. `.agents/` is never committed.

**Tools.** Read, Edit, Write, Glob, Grep, WebSearch, WebFetch; `lake build`, `lake env lean`,
`lake lint`, `lake exe mk_all`, `lake exe audit`, `scripts/check-build.sh`, `scripts/build.sh`;
`latexmk`, `pdflatex` and `bibtex`; `python3` with numpy, scipy and matplotlib (numerical
experiments); `ls`, `grep`, `wc`, `mkdir`; local git `add`, `commit`, `rm`, `mv`, `status`, `diff`,
`log`, `show`; for `fix-pr` and `revise` only, `git rebase origin/main`, `git rebase --continue`,
`git rebase --abort`. You have no `git push`, no `gh` and no shell network command: the script
pushes your commits and opens or updates the pull request. Python never downloads anything. The web
is for reading only: never post, sign up or submit anything.

**Reviewers** (`referee-scope`, `referee-proofs`, `review-statements`, `review-pr`, `review-roadmap`) are read-only:
they change no file of the repository and make no commit (`referee-proofs` may write numerical
experiments in `.agents/scratch/`, never collected), and their final message is their report. Its
first line is the verdict.

**Writing roles** commit early and often: a session is stopped at its deadline, and committed work
is kept as a draft pull request labelled `incomplete`. The script publishes the sum of a session's
commits as **one commit** (on the pull request's head, or on `main` for a new pull request): what a
commit adds and a later one removes is never published, but the sum is checked and published. They end by writing `.agents/summary.md`
(never committed), which becomes the pull request's description. Write it early and update it at the
end. Sections, in this order:

```
## Results
Each result of this pull request as a precise mathematical statement (LaTeX between $...$), with
its paper label (`P001-…, thm:main`) or its Lean name. "None" if there is none.
## Frozen statements
Lean names of the statements added under Statements/, each with its paper label. "None".
## Sources read
[KEY, part] for every part of a source you actually read in this session.
## Not done
What remains, your doubts, and `Ask-owner: <question>` lines (one line each) for what only the
owner can decide.
```

The script writes the first line of the pull request body (`Role: … Target: … Model: …`); do not
write it. It copies every `Ask-owner:` line of a summary or a report to the pinned issue "Questions
for the owner", even when the session made no commit. Anything you write may be posted on GitHub: no `@` mentions, no HTML comments, nothing
secret, and keep a report under 40 000 characters. Stop starting new work 10 minutes before the
deadline of task.md: commit, then finish the summary.

## 2. Paths

What each role may change. The script checks every commit of a session against this table
(`role_allows` in `scripts/lib.sh`, which follows it line for line) and refuses the whole result if
one path is outside it. `<P>` is the paper of the task; "no deletion" means files may be added or
modified only.

| Role | May change |
|---|---|
| `write-paper` | one new directory `papers/<P>/` (number from task.md): `paper.tex`, `refs.bib`, `META.toml`, `notebook/`; `literature/` (no deletion); `Exploration/`, `Exploration.lean` |
| `revise` | its paper's `paper.tex`, `refs.bib`, `META.toml`, `notebook/`, `errata.md` (lines `Revised in …`, §6.6, and entries after a dependency check) and `dependency-checks.md` (§5.6); `literature/` (no deletion); `Exploration/`, `Exploration.lean` |
| `formalize-statements` | `Statements/P<nnn>/*.lean` and `*.lock` (additions only), `Statements.lean` (added imports only); `Incognita/` (no deletion), `Incognita.lean`; `catalogue/definitions/` (no deletion); its paper's `blueprint.md`, `errata.md`, `statement-corrections.md`; `Exploration/`, `Exploration.lean` |
| `prove` | `Incognita/` (no deletion), `Incognita.lean`; `catalogue/results/P<nnn>-<name>.toml` (additions only); its paper's `blueprint.md`, `formalisation.tex`, `errata.md`, `statement-corrections.md`; `Exploration/`, `Exploration.lean` |
| `bibliographer` | `literature/` and `catalogue/attribution/` (no deletion); `refs.bib` of any paper (metadata fields only) |
| `garden` | `Incognita/` (no deletion; lemmas and theorems only), `Incognita.lean`; `catalogue/relations.toml`, `catalogue/garden.md` (rows appended only); `Dropped` lines under existing entries of a `roadmaps/<R>/directions.md` (never a new entry); entries of `papers/*/errata.md` and `papers/*/statement-corrections.md` after a failed re-check (§8); `Exploration/`, `Exploration.lean` |
| `propose-roadmap` | either one new roadmap, `roadmaps/<Name>/ROADMAP.md` and `KNOWN.md` (status `proposed`, first line of KNOWN.md `Reviewed by owner: no`), or one new extension `roadmaps/<Roadmap>/extensions/X<k>.md` of an approved roadmap (status `proposed`); `literature/` (no deletion) |
| `fix-pr` | the paths of the role that opened the pull request; on `main`: `Incognita/` (no deletion), `Incognita.lean`, `Statements.lean` (added imports only), `Exploration/`, `Exploration.lean` |
| reviewers | nothing |

The root files `Incognita.lean`, `Statements.lean`, `Exploration.lean` change only by import lines.
Nothing under `papers/` is ever deleted. An accepted `paper.tex` changes only by a new version after
an erratum (§6.6, case b).

**The owner only** (refused for every role): `README.md`, `AGENTS.md`, `CLAUDE.md` and
`CONTRIBUTING.md` anywhere (so every `README.md` of `catalogue/`, `literature/`, `papers/`…),
`LICENSE`, `agents/`, `templates/`, `docs/`, `scripts/`, `tests/`, `.github/`, `lakefile.toml`,
`lean-toolchain`, `lake-manifest.json`, `roadmaps/` (KNOWN.md included; except a proposal of
`propose-roadmap` and the `Dropped` lines of `garden`; the entries of `directions.md` and the status
`approved` of a proposal are written by the loop itself, §4), `literature/notes/TEMPLATE.md`,
`papers/<P>/withdrawn.md`, `papers/<P>/human-audits.md`. **Generated, never committed**:
`papers/library.bib` (§5.6), `papers/<P>/certification.tex` and `catalogue/certification.md`
(`scripts/certify.py`, §9).

Never: a path component starting with a dot, a symlink, a submodule, a file over 1 MB, something
that looks like a secret (a Claude or GitHub token, a private key), a change under `Statements/`
other than an addition. The script refuses a pull request that breaks these. Append-only files
(CI, `scripts/certify.py check`): `roadmaps/*/directions.md` (entries), `catalogue/garden.md`
(rows), and the entries of `papers/*/errata.md` and `statement-corrections.md` (only the lines
`Revised in …` and `Resolved by …` are added under an existing entry).

## 3. Order of work

The loop (`scripts/loop.sh`) chooses every task; you never choose your role. For reference, it skips
busy targets (`open-prs.md`), targets attempted twice tonight, `needs-human` and `parked` targets,
and pull requests from forks, then takes the first available of:

1. (no agent) at most one merge, then mechanical rebases of agent pull requests that conflict
   with `main`. After the merge of an accepted paper, a pull request of the loop itself (role
   `loop`) adds its accepted open questions to `directions.md` (§4.1, §5.5); a roadmap proposal is
   merged only after the scripted commit that approves it (§4);
2. `fix-pr` on `main` when the CI of `main` is red (then no review and no merge until it is fixed);
3. repairs, oldest pull request first: `revise` for a paper pull request, `fix-pr` for any other,
   when its head has a trusted `major` (papers) or `request_changes` (others), a failed build
   (after one automatic rerun), a conflict the mechanical rebase could not resolve, or it is a draft
   labelled `incomplete`. For a paper, only an answer to a referee's `major` is a revision round;
   the other repairs are fix rounds;
4. reviews of agent pull requests with a green build and no trusted verdict on their head for the
   needed role: paper pull requests get `referee-scope`, then `referee-proofs` once scope accepted
   that head; statements pull requests get `review-statements`; roadmap proposals get
   `review-roadmap`; all others get `review-pr`;
5. every 6 agent tasks, one `garden` (once a proof marker exists) or `bibliographer` task,
   alternately (§8);
6. `prove` for frozen statements still open (not superseded by a correction): first the papers
   that the most library papers depend on, then the oldest (§5.6);
7. `formalize-statements` for an accepted paper without frozen statements, or with entries waiting
   for corrected statements (an erratum revised in a new version, a statement correction; §6.6):
   at most one statements pull request open per roadmap, the roadmap's `definitions` paper first,
   then a paper only once that paper and every paper it depends on have frozen statements;
8. `revise` for a disputed paper (an errata entry neither revised nor resolved): a new version;
   then `revise` for a dependency check: a paper that depends on a library paper revised since it
   cited it (§5.6);
9. `bibliographer` on a paper that waits for it: an external paper without its source note, or a
   verified internal paper without its attribution audit;
10. `propose-roadmap` for an approved roadmap (KNOWN.md reviewed) with no free item left (§4);
11. `write-paper`, in an approved roadmap whose `KNOWN.md` is reviewed and which has a free item,
    while the roadmap has fewer than 3 papers in open pull requests (1 while its `definitions` paper
    is not on `main`) and fewer than 2 accepted papers not yet verified; the roadmap's known results
    to formalise (items F0, F1, …) come first, in order;
12. `propose-roadmap` periodically, only if the owner enables it (`INCOGNITA_PROPOSE_EVERY`; off by
    default), if none is open (§4);
13. fallback: `write-paper` up to 6 papers in open pull requests per roadmap (the limit on accepted
    papers not yet verified still holds), then `garden`, then `bibliographer`; otherwise the loop
    waits and looks again.

Formalising what is accepted always comes before writing more.

## 4. Roadmaps and KNOWN.md

- Papers are written only in a roadmap whose `ROADMAP.md` has status `approved` and whose
  `KNOWN.md` starts with the line `Reviewed by owner: <date>` (a date, not `no`).
- A roadmap numbers its **directions** D1, D2, … (in `ROADMAP.md` and in its approved extensions
  `extensions/X<k>.md`), its **known results to formalise** F0, F1, …, and its **candidate
  directions** C1, C2, … (`directions.md`, §4.1). A paper serves one or more of them (`directions`
  in its `META.toml`). An item marked `pending owner decision`, `on hold` or `closed`, a direction
  of an extension that is not `approved`, and a dropped candidate are not open for papers.
- The roadmap's pinned conventions and Definitions are used as written. A paper that changes one
  says which, and why, in its Setting.
- `KNOWN.md` lists what the owner knows: entries K1, K2, … with a statement (algorithms given by
  their formula), a status (`[Lean]`, `[paper]`, `[sketch]`, `[belief]`), a reason, and possibly the
  flag `private`. Read every entry before writing or refereeing a paper. Entries may also come in
  a private file listed in task.md: they count the same.
- **`private` entries**: never re-derive, propose, formalise or quote them. Refer to them by id only
  (`K12`), in papers, reports and summaries alike. A paper that re-derives a private entry is
  rejected.
- Roadmaps and `KNOWN.md` are never edited by agents (a proposal adds new files, §4.2). If you
  think a direction is answered, ill-posed, or should be reframed, write an `Ask-owner:` line.

### 4.1 Candidate directions (`directions.md`)

The open questions of an accepted paper that the scope referee rated as candidates (§5.4; the
latest rating of each question in its reports) become entries `C1`, `C2`, … of
`roadmaps/<Roadmap>/directions.md`: once the paper is merged, the loop appends them by a pull
request of its own (role `loop`, one scripted commit on top of `main`, merged after CI; never
reviewed or repaired by an agent). Each entry gives the question as stated in the paper, its
source (paper, version, label `oq:…`) and the referee's rating (interest, novelty, fit).
**Append-only**: entries are never edited, renumbered or deleted; `garden` (or the owner) adds a
line `Dropped (<date>, <role>, <model>): <reason>` under a candidate that a paper answers or that
is known. A writer takes a candidate like a direction (`directions = ["C3"]` in META.toml). The
status of an item is computed, never stored: **open**, **taken** (an open pull request serves it),
**done by P<nnn>** (a paper on `main` serves it), **covered** (a rejected paper served it),
**closed** (marked, or in an extension not approved) or **dropped**. The same busy and covered rules
hold for D, F and C items (`scripts/certify.py items`).

### 4.2 Roadmaps proposed by agents

When an approved roadmap (KNOWN.md reviewed) has no free item left, and periodically if the owner
enables it (`INCOGNITA_PROPOSE_EVERY`, off by default), the loop runs `propose-roadmap`. It proposes, in one pull request, either an **extension** of an
approved roadmap (`roadmaps/<Roadmap>/extensions/X<k>.md`: new directions numbered after the
existing ones) or a **new roadmap** (`roadmaps/<Name>/ROADMAP.md` with a `Domain` line, and a
`KNOWN.md` whose first line is `Reviewed by owner: no`), always with the status `proposed`.
`review-roadmap` reviews it (`approve`, `request_changes`: `fix-pr`, `reject`: closed with the label
`rejected`). Approval (the owner's policy):

- **inside an existing domain** (an extension, or a new roadmap whose domain is that of an approved
  roadmap): approved automatically if `review-roadmap` approves and the owner has not vetoed it
  during **2 nights**. The loop announces the veto window in a comment and in the night report;
  the owner vetoes by a comment starting with `veto` (or the label `veto`; a veto also stops a
  proposal already approved but not yet merged), or approves at once by a comment starting with
  `approve` (it counts only after the latest `review-roadmap` report and the last fix round). Once the window has passed, the loop adds a scripted commit
  that sets the status to `approved`, recording the dates, and merges the pull request;
- **a new domain**: only the owner's explicit approval (a comment starting with `approve`, or his
  own merge).

Roadmap pull requests are never merged automatically in any other way. Papers are written in a new
roadmap only after the owner has reviewed its KNOWN.md (first line `Reviewed by owner: <date>`); the
directions of an approved extension are open at once (the roadmap's KNOWN.md is reviewed).

## 5. Papers

### 5.1 The paper directory

`papers/<P>/`, where `<P>` is `P<nnn>-<slug>` (three digits, then lowercase letters, digits and
hyphens, for example `P001-one-batch-lower-bound`); `P<nnn>` alone is the paper's **prefix**, used
in Lean names. The number is given in task.md. [papers/README.md](papers/README.md) lists the files
and how a paper's status is computed. Start from `templates/paper/paper.tex`, `refs.bib` and
`META.toml`.

`META.toml` holds only: `roadmap`, `kind`, `directions` (items D, F or C served), `authors` (the
models that wrote or revised the paper), `version` (§5.6), `depends_on` (§5.6) and, for an external
paper, `source`. Kinds:

- `internal`: a result written by an agent. This includes a paper for a known result of the
  roadmap that is not published (an owner's result stated in the roadmap): its Main result copies
  the roadmap's statement verbatim and cites the roadmap item.
- `external`: a published result to formalise, `source = "[KEY]"`. The paper is the blueprint of
  the published proof: statements copied verbatim from `literature/notes/KEY.md`, proofs following
  the source, every gap the source leaves filled and marked as such.
- `definitions`: a setting paper (for example `P000-setting`): definitions with their basic
  properties, witnesses and exclusions.

### 5.2 Writing rules

- English. At most **12 pages and 25 nodes** (definition, lemma, proposition, theorem and corollary
  environments, cited results included); beyond, split into a lemma paper and an application
  paper. One main result, labelled `thm:main`. A negative result or a counterexample is a main
  result.
- **The paper is the blueprint** (leanblueprint conventions):
  - every definition, lemma, proposition, theorem and corollary is an environment with a `\label`;
  - a statement that uses definitions starts with `\uses{def:…}`; every proof starts with
    `\uses{…}` listing **every** node it uses (definitions included); a proof placed away from its
    statement also has `\proves{<label>}`;
  - labels have the prefixes `def:`, `lem:`, `prop:`, `thm:`, `cor:`, `cite:` (and `sec:` for
    sections); once submitted, a label is never renamed or reused;
  - a **cited result** is a node: a `lemma` or `theorem` labelled `cite:<KEY>-<part>`, with optional
    argument `[{\cite[<part>]{<KEY>}}]`, whose statement is copied verbatim from
    `literature/notes/<KEY>.md`, and no proof. If the note lacks the statement, read the source and
    add it to the note in the same pull request. A result of a **library paper** is a cited node
    too: `cite:INC-P<nnn>-<label>`, its statement copied verbatim from that paper at the version
    recorded in `depends_on` (§5.6); Facts at the level of a textbook that Mathlib or
    LML provide (Markov's inequality, Fubini, the chain rule for KL) may be used by name without a
    node;
  - a proof longer than one page is split into lemmas;
  - no `\lean{…}` in `paper.tex`: the Lean names of its nodes are recorded in `blueprint.md` by
    `formalize-statements`; **never write `\leanok` or `\mathlibok`**: they come from the audit
    (inserted when the paper is built, never committed by an agent) and print the green
    "LEAN APPROVED" box.
- **Mandatory sections**, in the order of the template:
  1. **Main result** (page 1): the complete statement with every quantifier, the class of
     instances, the class of learners or the algorithm, the criterion; the nature of the
     constants (explicit, or existential, and on what they depend); the roadmap items served, and
     what is missing if the result is weaker than the direction asks.
  2. **Setting**: the roadmap's conventions used, the definitions as nodes.
  3. **Closest known**: the nearest KNOWN entries (by id) and published results; for each, the
     difference, and an honest attempt to derive the main result from them, with where it fails.
  4. **Proofs**.
  5. **Sanity checks**: degenerate cases (for example $x = 1$, $K = 2$, Bernoulli rewards,
     $N = 0$, ties, infinite divergences), consistency with every `[Lean]` entry of KNOWN.md and with
     the roadmap's known results, and one explicit example satisfying all hypotheses at once.
  6. **Weak points**: the three steps you are least sure of, each by label and step.
  7. **Open questions**: one to five questions the paper leaves open, each an environment
     `openquestion` labelled `oq:<name>`, precise enough to be the main result of a next paper
     (quantifiers, class, criterion), with why the paper's method stops there and the roadmap item
     it extends. An internal paper has at least one; an external or definitions paper may write
     "None". They are not nodes. The scope referee rates them; the accepted ones become candidate
     directions of the roadmap (§4.1).
  8. **Attribution**: for each technique of the proofs, the earliest source you found
     (`[KEY, part]`) or "source not known", and the web queries you ran.
- No evaluative definitions: "optimal" is never a definition. State upper bounds with explicit
  constants and lower bounds with explicit classes of learners; "optimal" is a corollary pairing
  the two in one class.
- LaTeX: only the packages of the template; macros by `\newcommand` in the preamble; no `\def`, no
  `enumitem`, no TikZ, no Unicode characters except accented letters in names; braces around macro
  subscripts (`x_{\ell}`); `\texorpdfstring` for mathematics in headings.
- **Compile before finishing**, as CI does:
  `python3 scripts/certify.py bib` (it writes `papers/library.bib`, the keys `INC-P<nnn>`), then
  `latexmk -pdf -interaction=nonstopmode -halt-on-error -cd papers/<P>/paper.tex`. The final
  `papers/<P>/paper.log` must have no error, no undefined reference or citation (`undefined`) and
  no duplicate label (`multiply defined`); the PDF at most 12 pages. Then remove the generated files
  with `latexmk -C -cd papers/<P>/paper.tex`, and `git add` your source files by name: never commit
  a PDF, a build file or `papers/library.bib` (generated, never committed). CI compiles every paper
  the same way and fails on the same problems. Before the last commit,
  `python3 scripts/certify.py check` checks META.toml (`roadmap`, an existing roadmap), `depends_on`,
  the citations of library papers and the open questions, as CI does.

### 5.3 The notebook

During a paper's life its authors (`write-paper`, then `revise`) keep `papers/<P>/notebook/`, so
that the next agent starts from what was learned:

- `NOTEBOOK.md`, whose first line is `Not refereed: working notes of the authors of <P>.`, then
  one dated section per session (role, model): attempts, **dead ends with the reason they fail**,
  proof ideas, pointers to Lean drafts in `Exploration/<prefix>/`, the numerical experiments run and
  what they showed, and, after a referee report, the answer to each defect;
- small numerical experiments: `python3` scripts and their outputs (text or CSV under 100 kB each;
  a PNG figure under 200 kB only when it shows what text cannot).

The notebook stays in the repository after acceptance, marked "not refereed", and is never part of
the PDF: nothing in `paper.tex` refers to it. **Referees judge only `paper.tex`** (with `refs.bib`,
KNOWN.md, the roadmap and `literature/notes/`) and never rely on the notebook. Read the notebook
before working on a paper (`revise`, `fix-pr`, `formalize-statements`, `prove`).

### 5.4 Refereeing

- Two referees review the same head, in this order: `referee-scope` (novelty, bibliography,
  roadmap fit, interest, attribution, and a rating of each open question: interest, novelty, fit,
  candidate or not), then, only if scope accepts, `referee-proofs` (every proof, node by node, all
  nodes: a paper has at most 25).
- **Defect classes.** **F** fatal: the main statement is false, already known, a corollary of
  KNOWN.md or of the literature, out of the roadmap, or re-derives a private entry. **G** gap: an
  unjustified step in a labelled proof (or, for scope, a novelty claim left unjustified). **L**
  local error: wrong but fixable without changing any statement. **P** presentation.
- **Verdict, computed:** `reject` if any F; `major` if any G or L; otherwise `accept` (P defects
  only: an accepted paper keeps no error). The report's first line is `Verdict: accept`,
  `Verdict: major` or `Verdict: reject` (the script reads `minor` as `major`); the defect table
  follows:

  ```
  | ID | Class | Node | Step | Defect | Fix |
  |---|---|---|---|---|---|
  | SC1.1 | G | sec:closest | relation to K4 | ... | ... |
  ```

  IDs are `SC<round>.<n>` (scope) or `PF<round>.<n>` (proofs); the round is 1 + the number of the
  referee's previous reports on this paper.
- A paper is accepted when both referees accept the same head and its build is green (checks
  "Build and check" and "Compile papers"); the loop then merges it. On `major` the author revises
  (`revise`), fixing every G and L defect, and the P defects in passing; after 2 revision rounds
  without acceptance the pull request is closed with the label `rejected` (reports kept; only the
  owner reopens it). P defects alone never block acceptance.
- On a revision, referees re-check only the nodes that changed and the nodes that `\uses` them
  (transitively; `.agents/revision.diff` shows what changed since their last report), and rule on
  each previous G and L: resolved or not.
- A direction (D) or candidate direction (C) whose paper was rejected counts as covered: no new
  paper on it unless the owner reopens it. A known result to formalise (F) and the items of a
  `definitions` paper stay open after a rejection: the next writer reads the rejected paper's
  reports (`reports.md`) and answers them. When the owner reopens a rejected pull request (and
  removes the label), its rounds start again.
- A reviewer who needs a decision of the owner (for example a paper that reframes a direction)
  adds lines `Ask-owner: <question>` at the end of the report; the script copies them to the
  pinned issue "Questions for the owner".

### 5.5 After acceptance

Accepted paper (its accepted open questions become candidate directions, §4.1) →
`formalize-statements` (statements pull request, reviewed by `review-statements`, merged by the
owner during the first nights) → statements frozen → `prove` (proof pull requests, reviewed by
`review-pr`) → verified when every frozen statement of the paper is proved → re-verified by
gardening (§8). Its certification (§9) follows these steps.

**An accepted `paper.tex` is never edited**, except by a new version after an erratum (§6.6,
case b). What formalisation adds lives next to it: `blueprint.md` (Lean names, modelling decisions)
and `formalisation.tex` (extra lemmas, §6.6 case c). The owner may veto any paper after the fact
(`withdrawn.md`).

### 5.6 The library: identifiers, versions, citations, dependencies

- **Identifiers.** A paper is `P<nnn>` for good; its **version** is `version` in META.toml: 1 when
  submitted (refereeing rounds do not change it), and +1 with each new `paper.tex` after acceptance
  (an erratum, an affected dependency). CI checks it: a changed `paper.tex` of a paper on `main`
  must come with the next version, and a version changes only with `paper.tex`.
- **Bibliography of the library.** `papers/library.bib` has one entry per paper, key `INC-P<nnn>`,
  with its title and its version (field `version`). It is generated by
  `python3 scripts/certify.py bib` before compiling (by you, and by CI), never edited by hand and
  never committed (`.gitignore`). Papers load it with `\bibliography{refs,../../papers/library}`
  (the template does).
- **Citations.** A paper cites a library paper as `\cite[Theorem~2]{INC-P001}`, and records each
  result it uses, with the exact version it read, in `depends_on = ["P001v2:thm:main", …]`
  (labels `def:`, `lem:`, `prop:`, `thm:`, `cor:`). Every `INC-` key cited is in `depends_on` and
  conversely (CI). Lean docstrings cite `[INC-P001, Theorem 2]`.
- **Conditional results.** A paper is **conditional** while one of its dependencies is not
  Lean-verified; its certification level is capped by its dependencies' (§9).
- **Formalisation priority.** `prove` takes first the papers that the most library papers depend on.
- **Propagation of errata.** When a paper P has an erratum, every paper depending on P is flagged in
  the night report, and its certification is capped while P is disputed. Once P has a new version,
  each dependant gets a `revise` task (a **dependency check**): either it is not affected (a line in
  its `dependency-checks.md`, `depends_on` updated to the new version, `paper.tex` unchanged), or it
  is (an entry in its own `errata.md` and its next version). Either way the referees check the
  pull request.

## 6. Formalisation (Lean)

### 6.1 Method

Rémy Degenne's `formalize-paper` method: the paper is the blueprint; phase 1 freezes the headline
statements (with `sorry`), phase 2 proves them lemma by lemma following the `\uses` graph, one
coherent area per pull request. Prove the general statement first (Mathlib- or LML-shaped), and
derive the paper's statement as a one-line specialisation. `theorem` only for frozen statements and
big classical results, `lemma` for everything else. Drop hypotheses a proof does not use and say so
in the docstring.

### 6.2 Names and files

| What | Where | Lean name |
|---|---|---|
| definition of a roadmap | `Incognita/<Roadmap>/….lean`, plus `catalogue/definitions/<Name>.toml` | `Incognita.<Roadmap>.<Name>` |
| frozen statement of a paper node | `Statements/<prefix>/<name>.lean`, one theorem per file, and its lock `Statements/<prefix>/<name>.lock` | `Incognita.Statements.<prefix>.<name>` |
| its proof, exactly the frozen type | a module under `Incognita/` (paper-specific material in `Incognita/<prefix>/`) | `Incognita.<prefix>.<name>` |
| its refutation | idem | `Incognita.<prefix>.<name>_false : ¬ T` |
| witnesses that the hypotheses of a frozen statement hold together | `Incognita/<prefix>/Witnesses.lean` | `Incognita.<prefix>.<name>_satisfiable` |
| general lemmas | `Incognita/ForMathlib/…`, `Incognita/ForLML/…` (mirroring the upstream layout) or `Incognita/<Roadmap>/…` | by their content |
| proof marker | `catalogue/results/<prefix>-<name>.toml`, named by the frozen statement's Lean name (also for a refutation, with `status = "refuted"`) | — |

`<prefix>` is `P001` for the paper `P001-…`; `<name>` is a snake_case identifier (`lower_bound`).
A frozen name is never reused: a corrected statement gets a new name (`lower_bound_v2`). Proof
markers are additions only; the novelty of a result is not in its marker but in the
bibliographer's attribution audit `catalogue/attribution/<prefix>.md` (§7).

Every Lean file starts like this (the layout of LMLExplore and `formalize-paper`):

```
/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
module

public import Mathlib.Probability.HasLaw

/-! # Title

What the file defines and proves, the main declarations, the conventions. -/

@[expose] public section
```

### 6.3 Rules of the library

- `Incognita/`: no `sorry`, no axioms beyond `propext`, `Classical.choice`, `Quot.sound`, no
  warnings, Mathlib's linters (`lake lint`), every module listed in `Incognita.lean`
  (`lake exe mk_all --lib Incognita`).
- **Forbidden** in `Incognita/`, `Statements/` and `Exploration/`, even in comments and docstrings
  (CI greps for them before building): `#eval`, `run_cmd`, `run_elab`, `run_meta`, `elab`, `macro`,
  `syntax`, `initialize`, `unsafe`, `meta `, `implemented_by`, `extern`, `set_option`, `simproc`,
  `native_decide`, and declaring attributes. Using `@[simp]`, `@[fun_prop]` or
  `@[measurability]` is fine.
- `Statements/`: only theorems in `Incognita.Statements.*` whose proof is `sorry`, using definitions
  of `Incognita/` and of the dependencies; never a definition. Existing files and `.lock` files never
  change: CI accepts only added files under `Statements/` and added `import` lines in
  `Statements.lean`. Lock files are written by `lake exe audit --new-locks` (missing locks only),
  never by hand. In a pull request that changes a statement it added itself (answering
  `review-statements`), `lake exe audit --refresh-new-locks` rewrites the locks that are not on
  `origin/main` and deletes the orphan ones the pull request added; it never touches a lock of
  `main`. The placeholder `Statements/Basic.lean` (from version 1) is tolerated by the audit until
  the owner deletes it.
- **Proof pull requests add only `lemma` and `theorem`**: no `def`, `abbrev`, `structure`, `class`,
  `instance`, `inductive`, `axiom`, `opaque`, `notation`. A new object goes through a statements pull
  request.
- **No theorem lost.** Never delete a theorem of `Incognita/` or change its statement. Proof markers
  `catalogue/results/*.toml` are additions only, and the audit fails if a marked statement is no
  longer proved.
- `Exploration/`: drafts, `sorry` allowed, never imported from outside `Exploration/`; use
  `Exploration/<prefix>/` for a paper.

### 6.4 Definitions

Definitions are where a new library goes wrong silently. Before defining anything, search the
dependencies at their pinned versions (§6.7) and reuse: LMLExplore's `LMLExplore.Bandits` (`dInf`,
`IsConsistent`, its lower bounds), LML (`Algorithm`, `IsAlgEnvSeq`, `trajMeasure`, `pullCount`,
`regret`, `gap`), Mathlib. Follow the roadmap's Definitions section (planned names, conventions).
Write each definition in library generality, with a docstring, and prove in the same pull request:

- **witness**: a non-trivial object satisfying it;
- **known case**: it agrees with the classical notion on a known special case;
- **exclusion**: an object that must not satisfy it, proved not to (catches definitions that are
  trivially true);
- **non-vacuity**: for every frozen statement using it, a Lean witness that its hypotheses hold
  together.

Record them in `catalogue/definitions/<Name>.toml`
([catalogue/definitions/README.md](catalogue/definitions/README.md)).

### 6.5 Lean pitfalls (formalisers and reviewers)

Natural-number subtraction; `x / 0 = 0`; `Real.log 0 = 0` and `log` of negative numbers;
`ENNReal.toReal ∞ = 0`; `Filter.liminf`/`limsup` in `ℝ` of an unbounded sequence (a junk value: use
`EReal`, or write `∀ c < L, ∀ᶠ n in atTop, …`); rounds from 0 in LML against 1 in papers; arms as a
`Fintype α`, never `Fin K`; a learner measurable with respect to too large a σ-algebra (the
information model leaks the future); hypotheses that make a statement vacuous.

### 6.6 When formalisation shows that something must change

Decide which case you are in, and say it in your summary. Never weaken a statement silently.

- **(a) The Lean statement mistranslates the paper** (an implicit hypothesis left out, a junk value
  such as `x / 0 = 0` or a real `liminf` of an unbounded sequence, a convention such as 0-based
  rounds): add an entry `SC<n>` to `papers/<P>/statement-corrections.md` (frozen name, what is
  wrong, the corrected Lean statement in words, relation `closeMatch`). The loop then runs
  `formalize-statements`, whose new statements pull request freezes the corrected statement under a
  new name and adds the line `Resolved by …` under the entry. The paper is unchanged; the old frozen
  statement stays (superseded).
- **(b) The paper is wrong** (a false statement, a real gap, an extra hypothesis that is needed):
  add an entry `E<k>` to `papers/<P>/errata.md` (node, what is wrong, why), with the Lean
  counterexample `Incognita.<prefix>.<name>_false : ¬ T` when the statement is false. The paper is
  then **disputed**: the loop runs `revise`, which writes a new version of `paper.tex` on a new
  pull request and adds the line `Revised in the version of <date>: …` under the entry; the
  referees re-check only the changed nodes and the nodes that `\uses` them. Once that version is
  merged, the loop runs `formalize-statements`, whose statements pull request freezes the corrected
  statements under new names and adds the line `Resolved by …` under the entry (or
  `Resolved by the version of <date>: no frozen statement changes` when none does). The old frozen
  statements stay (the audit marks the refuted ones).
- **(c) The statement is true but its proof needs another decomposition or extra lemmas**: write
  them in `papers/<P>/formalisation.tex` (from `templates/paper/formalisation.tex`): new labelled
  lemmas with `\lean{…}` and exhaustive `\uses{…}`, referring to the nodes of `paper.tex` by their
  labels. It is not refereed, because Lean checks it; `paper.tex` is not edited.

Format of an entry (the loop reads the heading and the three kinds of lines below it; formats in
[papers/README.md](papers/README.md)):

```
## E1 (2026-11-20, prove, claude-opus-5-5)
- Node: thm:main
- Frozen statement: Incognita.Statements.P001.lower_bound
- Problem: the statement is false when the grid has a single batch.
- Evidence: Incognita.P001.lower_bound_false
Revised in the version of 2026-11-22: hypothesis "at least two batches" added to thm:main.
Resolved by Incognita.Statements.P001.lower_bound_v2 (statements pull request).
```

An `E<k>` without a `Revised in` or `Resolved by` line makes the paper disputed; an `E<k>` revised
but not resolved, or an `SC<n>` not resolved, waits for a statements pull request. The line
`- Frozen statement:` names the frozen statement the entry replaces: once the entry is resolved,
that statement is superseded (it no longer counts for `prove` nor for "verified"). Entries are never
renumbered, edited or deleted: later roles only add their line under them.

### 6.7 Building and searching

- Dependencies: `.lake/packages/LMLExplore`, `.lake/packages/LeanMachineLearning` (LML),
  `.lake/packages/TauCeti`, `.lake/packages/mathlib/Mathlib`. Grep ignores `.lake` unless you give
  the path: search with `path` set to one of these directories.
- Iterate with `lake env lean <file>` (one file) and `lake build <Module>`. Run the CI commands once,
  at the end: `scripts/check-build.sh Incognita --no-sorry`, `scripts/check-build.sh Statements`,
  `scripts/build.sh Exploration` (if you touched it), `lake exe audit --check`, `lake lint`,
  `lake exe mk_all --check --lib <Lib>` for each library you touched. In a fresh clone, build before
  running the audit.
- The machine has 8 GB of RAM: one `lake` command at a time, never in parallel.
- Never require Mathlib, LML or Tau Ceti directly: they come from LMLExplore, at its pins.

## 7. Literature and attribution

Lean does not check citations, and models invent plausible references. So:

- **Cite only what was read.** A citation `[KEY, part]` (in LaTeX `\cite[part]{KEY}`) points to an
  entry of `literature/bibliography.json`, whose cited part is marked as read in
  `literature/index.md`; a paper's `refs.bib` uses the same keys. If you need a reference that is
  not there, add it with metadata `unchecked`, mark as read only what you read in the source, and
  write "(to be checked)" after an unread citation. Never fill a field from memory.
- **Credit techniques, not only results.** For each idea of a proof, the earliest source you can
  find (follow references in both directions). A new statement proved with an old technique is new;
  its technique is still credited.
- **Record your searches**: the queries you ran and what they found go in the paper's Attribution
  section or in your report.
- Statements of results are copied exactly in `literature/notes/` and in cited nodes; for the rest,
  quote at most a short phrase and summarise in your own words.
- Novelty is never claimed by the author: the bibliographer's attribution audit
  (`catalogue/attribution/`) decides `new`, `rediscovery of [KEY]` or `known: [KEY]`.

## 8. Gardening

The `garden` role revisits what was validated (accepted papers, verified results), oldest
revisit first, and records each pass in `catalogue/garden.md`:

- **implications**: a result A is subsumed by B only if B implies A with quantitative content at
  least as good (same constants, same order, hypotheses no stronger); then A gets a proof as a
  corollary of B, and A's statement stays;
- **lower against upper bounds** of the same class: if they contradict each other, Lean proves
  `False` from them and a definition is wrong: report it at once (`Ask-owner:`);
- **duplicates**, within the library or with what the dependencies now provide;
- **no theorem lost**: every proof marker is still proved;
- **re-verification** of a Lean-verified paper, independently of its formalisers: a
  `back-translation` of its frozen statements from the Lean alone, a `double-formalisation`
  (stated again and proved equivalent), or `known-cases` (instances proved in Lean). A re-check
  counts for the certification (§9) only if it brings something new: a check type or a model not
  yet used for that paper, or a library changed since its last counted re-check. A failed re-check
  comes with an erratum or a statement correction of the paper (§6.6), and disputes the paper;
- **candidate directions**: a candidate answered by a paper of the library, or known, gets a
  `Dropped` line (§4.1).

Each pass is logged in `catalogue/garden.md`, one row per item, with the check, the outcome and the
commit of `main` (format in [catalogue/README.md](catalogue/README.md)).

## 9. Certification

The certification of a paper is **computed, never written by hand**, by `scripts/certify.py` from
the repository: the audit's statuses (or the proof markers it checks), the referees' verdicts (the
trailers of the loop's merge commits), the gardening log and the human audits. Levels:

| Level | Name | Condition |
|---|---|---|
| 0 | submitted | an open pull request (also: disputed, withdrawn, or capped at 0 by a dependency) |
| 1 | accepted | on `main`, after both referees accepted (or merged by the owner) |
| 2 | Lean-verified | every frozen statement proved (not superseded), audit OK |
| 3 | re-verified | level 2, and at least one counted re-check by gardening (§8) |

- The **level is capped** by the levels of the papers it depends on (§5.6); the paper is
  **conditional** while a dependency is below level 2.
- A **disputed** paper (an erratum not revised, a refuted frozen statement, or a last re-check that
  failed) is at level 0, and so caps every paper built on it.
- A **counter** of the counted re-checks, and two **badges**, independent of the level: **used by
  N** (the Lean-verified papers that depend on it) and **audited by a human** (who, when, which
  version: `papers/<P>/human-audits.md`, the owner's file, lines `- <who>, <YYYY-MM-DD>, v<k>:
  <what was checked>`).
- The PDF of a paper (workflow Papers) shows the green box "LEAN APPROVED" under each node whose
  frozen statement is proved, and its certification line under the title; both come from
  `papers/<P>/certification.tex`, generated by CI, never written by agents.
- `catalogue/certification.md` (generated: CI's summary, the night report) lists every paper with
  its level, re-checks, badges and dependencies.

## 10. Roles

| Role | Model | Does |
|---|---|---|
| `write-paper` | author | writes a paper for an open item of an approved roadmap |
| `referee-scope` | reviewer | novelty and bibliography (technique by technique), KNOWN.md, roadmap fit, interest, attribution |
| `referee-proofs` | reviewer | checks every node and proof line by line |
| `revise` | author | answers referee reports or an erratum: new version of the paper |
| `formalize-statements` | author | phase 1: definitions, frozen statements, witnesses, `blueprint.md` |
| `review-statements` | reviewer | fidelity of phase 1: back-translation, definitions, witnesses |
| `prove` | author | phase 2: proofs of frozen statements, one coherent area per pull request; `formalisation.tex`; errata |
| `review-pr` | reviewer | every other pull request (proofs, garden, literature, exploration, fixes) |
| `fix-pr` | author | rebases, repairs builds, answers `review-pr` and `review-statements`, repairs `main` |
| `bibliographer` | author | source notes, reference metadata, attribution audits |
| `garden` | author | revisits validated results: implications, contradictions, duplicates, re-verification, candidate directions |
| `propose-roadmap` | author | proposes an extension of an approved roadmap or a new roadmap (§4.2) |
| `review-roadmap` | reviewer | reviews a roadmap proposal: form, interest, novelty, precision, domain |
