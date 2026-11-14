You **revise a paper** of the Incognita repository. Two situations (task.md says which):

- **Referee reports**: a submitted paper (an open paper pull request) whose head received
  `Verdict: major`, or whose LaTeX build failed. You work on its branch.
- **Erratum**: an accepted paper with an unresolved entry `E<k>` in `papers/<P>/errata.md`
  (AGENTS.md §6.6, case b). You write a new version of `paper.tex`, on a new pull request.

## Inputs

- `.agents/task.md`: paper id, pull request number and head SHA if any, deadline, context files.
- `.agents/reports.md`: the referee reports, latest last; `.agents/pr.diff`; `.agents/ci-log.txt`
  if the build failed.
- `papers/<P>/`: **read `notebook/NOTEBOOK.md` first**, then `paper.tex`, `refs.bib`,
  `META.toml`, `errata.md`, `statement-corrections.md`.
- The roadmap, its KNOWN.md (path in task.md), `literature/notes/`; `AGENTS.md` §5, §6.6, §7.

## Steps

1. **Conflict with `main`**: `git rebase origin/main`; resolve conflicts in favour of `main` outside
   `papers/<P>/`; `git rebase --continue` (or `git rebase --abort`, and say so).
2. **Build failure**: fix it from `ci-log.txt`.
3. **Referee reports**: address every defect of the latest report of each referee, G first, then L,
   then P.
   - G: close the gap (a corrected argument, a new lemma). If the step is false, change the
     statement (an extra hypothesis, a weaker constant) and say so plainly in Main result: a changed
     statement is a new claim, checked again.
   - L, P: fix them.
   - A defect you believe wrong: do not obey it; answer with a mathematical argument in the notebook
     and in the summary.
4. **Erratum**: for each unresolved `E<k>`, correct the statement, the proof or both, consistently
   with the Lean counterexample if there is one. Under the entry, add the line
   `Resolved by the version of <date>: <what changed>` (never edit the entry itself). The corrected
   statements will be frozen under new names by a new statements pull request.
5. **Labels**: a changed node keeps its label; a new node gets a new label; a removed label is never
   reused. The referees re-check exactly the changed nodes and those that `\uses` them, so change
   nothing else. Stay within 12 pages and 25 nodes; update `\uses`, Closest known, Sanity checks,
   Weak points and Attribution where the changes require it. Add your model to `authors` in
   `META.toml`.
6. **Notebook**: add a dated section: for each defect ID (or `E<k>`), "fixed" with the nodes changed,
   or "disputed" with the argument; new dead ends with the reason they fail.
7. **Compile** as `write-paper` does
   (`latexmk -pdf -interaction=nonstopmode -halt-on-error -cd papers/<P>/paper.tex`; no error, no
   `undefined`, no `multiply defined`; then `latexmk -C -cd papers/<P>/paper.tex`), `git add` the
   source files by name, commit `P<nnn>: revision for <IDs>`.

Summary (`.agents/summary.md`, AGENTS.md §1): Results (the main result as now stated, with its
label), Frozen statements (None), Sources read, Not done (each defect ID: fixed, with the nodes
changed, or disputed; anything left).

## Do not

Edit `paper.tex` of an accepted paper except for an erratum; touch another paper, a roadmap or
KNOWN.md; renumber or delete entries of `errata.md`; write `\lean`, `\leanok` or `\mathlibok`;
change nodes the reports do not concern.
