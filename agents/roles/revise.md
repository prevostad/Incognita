You **revise a paper** of the Incognita repository. Five situations (task.md says which):

- **Referee reports** (a revision round): a submitted paper (an open paper pull request) whose head
  received `Verdict: major`. You work on its branch.
- **Referee reports on a presentation revision** (a revision round too): a pull request of the
  owner (branch `owner/*`, role `revise`) that rewrites an accepted paper for presentation as its
  next version (AGENTS.md §5.6); task.md says so. The mathematical content of every node must stay
  as it is on `main`: answer the reports by changes of presentation only.
- **Repair** (a fix round, not a revision round): an open paper pull request whose build failed
  (checks "Build and check" or "Compile papers": `ci-log.txt`), that conflicts with `main`, or a
  draft labelled `incomplete` (an earlier session stopped before the end: finish the paper as
  `agents/roles/write-paper.md` says, from its notebook and its commits). You work on its branch.
- **Erratum**: an accepted paper with an entry `E<k>` in `papers/<P>/errata.md` that has neither a
  `Revised in` nor a `Resolved by` line (AGENTS.md §6.6, case b): the paper is disputed. You write a
  new version of `paper.tex`, on a new pull request.
- **Dependency check**: an accepted paper that depends on a library paper which has a new version
  since this paper cited it (AGENTS.md §5.6; task.md names `P<nnn>v<k>->v<m>`). You decide whether
  this paper is affected, on a new pull request.

## Inputs

- `.agents/task.md`: paper id, pull request number and head SHA if any, deadline, context files.
- `.agents/reports.md`: the referee reports, latest last; `.agents/pr.diff`; `.agents/ci-log.txt`
  if the build failed.
- `papers/<P>/`: **read `notebook/NOTEBOOK.md` first**, then `paper.tex`, `DOSSIER.md`,
  `refs.bib`, `META.toml`, `errata.md`, `statement-corrections.md`.
- The roadmap, its KNOWN.md (path in task.md), `literature/notes/`; `AGENTS.md` §5, §6.6, §7;
  `docs/writing.md` (the reader, the structure, the criteria W1–W17 behind R and P defects; §2–2a: the house style, modelled on the owner's paper arXiv:2610.21582, which you read).

## Steps

1. **Conflict with `main`**: `git rebase origin/main`; resolve conflicts in favour of `main` outside
   `papers/<P>/`; `git rebase --continue` (or `git rebase --abort`, and say so).
2. **Build failure**: fix it from `ci-log.txt`.
3. **Referee reports**: address every defect of the latest report of each referee, G first, then L
   and R, then P. An accepted paper keeps no error: every G, L and R must be fixed (or disputed
   with an argument), P defects are fixed in passing.
   - G: close the gap (a corrected argument, a new lemma). If the step is false, change the
     statement (an extra hypothesis, a weaker constant) and say so plainly in the main results and
     their Scope remark: a changed statement is a new claim, checked again.
   - R (readability, `docs/writing.md` §4): restructure as the report asks (an introduction, a
     proof overview, definitions before use, the process material moved to `DOSSIER.md`…). One
     round is enough for R defects: do it fully now.
   - L, P: fix them.
   - A defect you believe wrong: do not obey it; answer with a mathematical argument in the notebook
     and in the summary.
   - **On a presentation revision**, never change the mathematical content of a node: the same
     labels, hypotheses and conclusions (a statement may be reworded, never strengthened or
     weakened), no node removed, new nodes only for restated cited results or for lemmas that were
     inline steps; proofs reorganised or expanded, not changed in substance. A defect that needs a
     change of a statement (a G or an F on the mathematics) is not answered there: dispute it, or
     write it under Not done with an `Ask-owner:` line (the version on `main` then needs an
     erratum, §6.6).
4. **Erratum**: for each `E<k>` task.md names, correct the statement, the proof or both, consistently
   with the Lean counterexample if there is one. Under the entry, add the line
   `Revised in the version of <date>: <what changed>` (never edit the entry itself, never write
   `Resolved by`: `formalize-statements` adds it once the corrected statements are frozen, in a new
   statements pull request).
5. **Dependency check**: read the dependency's errata (`papers/<dep>/errata.md`) and compare, node
   by node, what this paper uses of it (the cited nodes `cite:INC-P<nnn>-…`) with the new version.
   - Not affected: `paper.tex` unchanged; in `META.toml`, `depends_on` names the new version (same
     labels, or the new labels of the same results); add a line to
     `papers/<P>/dependency-checks.md`: `- <date>, <model>: P<nnn>v<k> -> v<m>: not affected:
     <reason, node by node>`.
   - Affected: add an entry `E<j>` to this paper's `errata.md` (node, the dependency's change, why
     it breaks), and write the next version as for an erratum (with `Revised in …` under the entry
     and a line `… -> v<m>: affected, see E<j>` in `dependency-checks.md`).
6. **Versions**: a new `paper.tex` of an accepted paper (an erratum, an affected dependency, a
   presentation revision) has `version` = the version on `main` + 1 in `META.toml`; during
   refereeing (a paper pull request), the version stays the one it was submitted with (1 for a new
   paper). After any change of `META.toml` or of a title, run
   `python3 scripts/certify.py bib` (it regenerates `papers/library.bib`, which is never
   committed) and `python3 scripts/certify.py check --base origin/main`.
7. **Labels**: a changed node keeps its label; a new node gets a new label; a removed label is never
   reused. The referees re-check exactly the changed nodes and those that `\uses` them, so change
   nothing else. Stay within 100 pages; update `\uses`, the comparison of the introduction, the
   examples, the open questions and the appendix of sources of the techniques where the changes
   require it, and `DOSSIER.md` (closest known, sanity checks, weak points, searches, and Changes
   for a new version). Nothing of `DOSSIER.md` goes into `paper.tex` (AGENTS.md §5.2): a paper
   written before the rules of 2026-11-15 gets a `DOSSIER.md`, and loses its KNOWN ids and its
   "(to be checked)", in the first pull request that changes its `paper.tex` (CI checks it). Add
   your model to `authors` in `META.toml`. A paper of the owner (`human_authors` in `META.toml`)
   keeps its `human_authors` and its `\author` line (the script refuses any change of them), and its
   text: change only what a defect requires, as targeted edits, never a rewrite.
8. **Notebook**: add a dated section: for each defect ID (or `E<k>`), "fixed" with the nodes changed,
   or "disputed" with the argument; new dead ends with the reason they fail.
9. **Compile** both builds as `write-paper` does (AGENTS.md §5.2: the reader build and the
   blueprint build; no error, no `undefined`, no `multiply defined`; read the reader build with
   `pdftotext papers/<P>/paper.pdf -`; then `latexmk -C` for both), `git add` the source files by
   name, commit `P<nnn>: revision for <IDs>`.

Summary (`.agents/summary.md`, AGENTS.md §1): Results (the main result as now stated, with its
label), Frozen statements (None), Sources read, Not done (each defect ID: fixed, with the nodes
changed, or disputed; anything left).

## Do not

Edit `paper.tex` of an accepted paper except for an erratum, an affected dependency, or in the
pull request of a presentation revision; change the mathematics of a node in a presentation
revision; touch another paper, a roadmap, `directions.md` or KNOWN.md; renumber or delete entries
of `errata.md`; write `\lean`, `\leanok` or `\mathlibok`; change nodes the reports do not concern.
