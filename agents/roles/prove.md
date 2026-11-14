You do **phase 2 of the formalisation** of a paper of the Incognita repository: prove its frozen
statements in Lean, lemma by lemma, following the paper's `\uses` graph, one coherent area per pull
request.

## Inputs

- `.agents/task.md`: paper id, the frozen statements or the area to prove, deadline.
- `Statements/<prefix>/`: the frozen statements (never change them).
- `papers/<P>/paper.tex` (the blueprint), `formalisation.tex`, `blueprint.md` (Lean names already
  chosen), `notebook/` (hints, dead ends; read only: your notes go in `blueprint.md`, in
  `formalisation.tex` and in your summary), `errata.md`, `statement-corrections.md`.
- `Incognita/` and the dependencies under `.lake/packages/` (Grep with `path` set there);
  `AGENTS.md` §6.

## Steps

1. **Plan.** From the `\uses` graph of the target, list the lemmas it needs; mark those already in
   `blueprint.md` or in the library; for each standard step, search the dependencies.
2. **Prove**, in modules under `Incognita/`: paper-specific material in `Incognita/<prefix>/`,
   general lemmas in general form in `Incognita/ForMathlib/`, `Incognita/ForLML/` or
   `Incognita/<Roadmap>/`. The final theorem `Incognita.<prefix>.<name>` has **exactly** the frozen
   type: copy it verbatim from the `Statements/` file. Drafts with `sorry` go in
   `Exploration/<prefix>/`.
3. **Only `lemma` and `theorem`**: no `def`, `abbrev`, `structure`, `class`, `instance`, `inductive`,
   `axiom`, `opaque`, `notation`. If you need a new object, stop and say so in the summary: it needs a
   statements pull request.
4. **Iterate** with `lake env lean <file>` and `lake build <Module>`, one command at a time; commit
   each lemma as soon as it compiles without `sorry`; add new modules to the root with
   `lake exe mk_all --lib Incognita`.
5. **Record.** Add a row to `blueprint.md` for each paper lemma you prove (label, Lean name). If the
   Lean proof needs lemmas the paper does not state, or another decomposition (AGENTS.md §6.6,
   case c), write them in `papers/<P>/formalisation.tex` (from `templates/paper/formalisation.tex`):
   labels `flem:…`, with `\lean{…}` and an exhaustive `\uses{…}`. Compile it after the paper
   (`latexmk -pdf -interaction=nonstopmode -halt-on-error -cd papers/<P>/paper.tex`, then the same
   for `formalisation.tex`; no error, no `undefined`), then remove the generated files
   (`latexmk -C -cd` on both).
6. **Proof marker.** When a frozen statement is proved, add
   `catalogue/results/<prefix>-<name>.toml`, named by the frozen statement (fields in
   `catalogue/README.md`; `novelty` is not a field: the bibliographer's attribution audit decides it).
7. **If the statement seems false or mistranslated**, stop proving it and decide the case
   (AGENTS.md §6.6): (a) mistranslated: an entry `SC<n>` in `statement-corrections.md`; (b) the
   paper is wrong: an entry `E<k>` in `errata.md` (with the line
   `- Frozen statement: Incognita.Statements.<prefix>.<name>`), with the proof of
   `Incognita.<prefix>.<name>_false : ¬ T` when the statement is false, and then its marker
   `catalogue/results/<prefix>-<name>.toml` (the frozen statement's name, not `_false`) with the
   line `status = "refuted"`. Entries make the paper disputed: such a pull request is merged by the
   owner.
8. **Checks**, once, at the end: `scripts/check-build.sh Incognita --no-sorry`,
   `lake exe audit --check`, `lake lint`, `lake exe mk_all --check --lib Incognita`, and
   `scripts/build.sh Exploration` if you touched it.

Partial progress is useful: commit the lemmas you proved, and say in the summary which lemma
remains and what blocks it.

Summary (AGENTS.md §1): Results (each statement or lemma proved, in mathematics, with its Lean name),
Frozen statements (None), Sources read, Not done.

## Do not

Change anything under `Statements/` or an existing theorem; use `sorry` or an axiom outside
`Exploration/`; use `set_option`, even for heartbeats (split the proof instead) or any other forbidden
keyword (AGENTS.md §6.3); edit `paper.tex`; prove a weaker statement and call it the frozen one.
