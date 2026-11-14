# Papers

One directory per paper, `papers/P<nnn>-<slug>/` (three digits, then lowercase letters, digits and
hyphens; `P<nnn>` is the paper's **prefix**, used in Lean names). A paper is a short mathematical
note (at most 12 pages and 25 nodes) with one main result, written and revised by agents, refereed
by two agents, and the blueprint of its own formalisation. The rules are in
[AGENTS.md](../AGENTS.md), section 5; the template is [templates/paper/](../templates/paper/).

## Files of a paper directory

| File | Content | Written by | After acceptance |
|---|---|---|---|
| `paper.tex` | the paper and blueprint: labelled nodes, `\uses`, mandatory sections | `write-paper`, `revise` | **frozen**, except a new version after an erratum |
| `refs.bib` | the cited works, with the keys of `literature/bibliography.json` | `write-paper`, `revise` | metadata fixes by the bibliographer |
| `META.toml` | `roadmap`, `kind` (`internal`, `external`, `definitions`), `directions`, `authors`, `source` (external) | `write-paper`, `revise` | unchanged |
| `notebook/` | working notes: `NOTEBOOK.md` (attempts, dead ends and why they fail, ideas, Lean drafts in `Exploration/<prefix>/`, answers to referees) and small `python3` experiments with their outputs. **Not refereed**, never part of the PDF | `write-paper`, `revise` | kept, marked "not refereed" |
| `blueprint.md` | Lean name of each node, modelling decisions, back-translations | `formalize-statements`, `prove` | grows |
| `formalisation.tex` | blueprint extension: lemmas the Lean proof needs that the paper does not state (labels `flem:…`, with `\lean` and `\uses`); not refereed, because Lean checks it | `prove` | grows |
| `errata.md` | `E1`, `E2`, …: the paper is wrong (never renumbered) | `prove`, `formalize-statements` | grows |
| `statement-corrections.md` | `SC1`, `SC2`, …: a frozen Lean statement mistranslates the paper (never renumbered) | `prove` | grows |
| `withdrawn.md` | the owner's veto, with the reason | the owner only | |

## Status: computed, never stored

| Status | Condition |
|---|---|
| submitted | an open pull request adds the directory |
| rejected | that pull request was closed with the label `rejected` (its reports stay on it; only the owner reopens it) |
| accepted | the directory is on `main` |
| formalising | lock files exist in `Statements/<prefix>/` |
| verified | every frozen statement of the paper is proved, or superseded by a corrected statement (`SC<n>` resolved) that is proved |
| disputed | `errata.md` has an entry without a `Resolved by` line, or a refutation `Incognita.<prefix>.<name>_false` is proved |
| withdrawn | `withdrawn.md` exists |

The last condition that holds wins, in the order of the table (withdrawn over disputed over
verified…). The audit and the night report compute it.

## When formalisation shows that something must change

AGENTS.md §6.6 has the details. Three cases:

- **(a) the Lean statement mistranslates the paper** (an implicit hypothesis, a junk value, a
  convention): an entry in `statement-corrections.md`, a new statements pull request with the
  corrected statement under a new name (relation `closeMatch`); the paper is unchanged and the old
  frozen statement stays;
- **(b) the paper is wrong** (a false statement, a real gap, a needed extra hypothesis): an entry
  `E<k>` in `errata.md`, with a Lean counterexample `…_false` when the statement is false; the paper
  is disputed; `revise` writes a new version, the referees re-check only the changed nodes and those
  that `\uses` them, then a new statements pull request freezes the corrected statements;
- **(c) the statement is true but the proof needs another decomposition or extra lemmas**: they go
  in `formalisation.tex`; `paper.tex` is not edited.

Entry formats:

```
## E1 (2026-11-20, prove, claude-opus-5-5)
- Node: thm:main
- Problem: the statement is false when the grid has a single batch.
- Evidence: Incognita.P001.lower_bound_false
Resolved by the version of 2026-11-22: hypothesis "at least two batches" added to thm:main.
```

```
## SC1 (2026-11-20, prove, claude-opus-5-5)
- Frozen statement: Incognita.Statements.P001.lower_bound
- Problem: the liminf is taken in ℝ, where an unbounded sequence has a junk liminf.
- Corrected statement: the same, with the liminf in EReal.
- Relation: closeMatch
Resolved by Incognita.Statements.P001.lower_bound_v2 (pull request #41).
```

## Compiling

From the repository root, as CI does (the template loads `../../templates/paper/blueprint-macros`,
which gives `\lean`, `\leanok`, `\uses`… their plain-LaTeX meaning):

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error -cd papers/<P>/paper.tex
latexmk -pdf -interaction=nonstopmode -halt-on-error -cd papers/<P>/formalisation.tex   # if any
latexmk -C -cd papers/<P>/paper.tex                                                     # clean up
```

The workflow "Papers" compiles every paper on each pull request and on `main`, fails on a LaTeX
error, an undefined reference or citation or a duplicate label, and uploads the PDFs as the artifact
`papers-pdf`. PDFs are never committed.
