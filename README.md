# Incognita

Mathematical research by AI agents, refereed by AI agents and verified in Lean 4, on top of
[LMLExplore](https://github.com/LeanMachineLearning/LMLExplore), and so of
[LML](https://github.com/LeanMachineLearning/LML), [Tau Ceti](https://github.com/TauCetiProject/TauCeti)
and [Mathlib](https://github.com/leanprover-community/mathlib4).

> **Independent project.** Incognita is not part of, affiliated with, or endorsed by LMLExplore,
> LML or Tau Ceti. It only uses LMLExplore as a Lean dependency, and borrows its build scripts from
> [lml-paper-template](https://github.com/LeanMachineLearning/lml-paper-template) (Apache 2.0).

**Status: version 3, being set up.** The rules, one approved roadmap (BatchedBandits, whose
KNOWN.md the owner has not reviewed yet, so no paper is written yet), three draft roadmaps and the
agent scripts are written.

## Why

LMLExplore has agents formalise *known* results, chosen by humans in roadmaps: the truth and the
interest of each statement come from the literature. Incognita aims at *new* results. Lean settles
whether a proof is correct, but not whether a statement means what it should, whether it is new, nor
whether it matters. These guarantees have to be rebuilt: by refereeing, by a careful bibliography,
and by checks on every definition. The quality bar is at least LMLExplore's, even if research goes
slower.

## How it works

1. **Roadmaps** (owner): the owner approves a roadmap: motivation, pinned conventions, the core
   definitions with their planned Lean names, numbered open directions, known results to formalise,
   acceptance criteria for papers. He also writes its `KNOWN.md`, what he already knows (results,
   dead ends, conjectures), and reviews it once. See [roadmaps/](roadmaps/).
2. **Papers** (agents): an agent writes a paper (at most 100 pages) with one main result in an
   open direction, in LaTeX with leanblueprint macros, so that **the paper is also the blueprint of
   its formalisation**. It keeps a working notebook next to it (attempts, dead ends, numerical
   experiments), which is never refereed. See [papers/](papers/).
3. **Refereeing** (agents): a scope referee checks novelty and the bibliography, technique by
   technique, against the literature and KNOWN.md; then a proof referee checks every proof, node by
   node. Defects are classed fatal, gap, local or presentation; the paper is accepted when both
   referees accept the same version, after at most four revisions.
4. **Formalisation** (agents), following Rémy Degenne's `formalize-paper` method: the statements
   of an accepted paper are frozen in `Statements/` with `sorry` and locked (`lake exe audit`); then
   they are proved in the library `Incognita/`, lemma by lemma, following the paper's dependency
   graph. If formalisation shows that the paper is wrong, an erratum sends it back to revision;
   nothing frozen is ever deleted.
5. **Literature** (agents): only references read in the source are cited; a bibliographer writes
   source notes and audits the attribution of every verified result. See [literature/](literature/).
6. **Gardening** (agents): validated results are revisited regularly, to find implications,
   contradictions between bounds (a wrong definition) and duplicates. See [catalogue/](catalogue/).
7. **A library that builds on itself**: accepted papers cite and use one another (`depends_on`,
   keys `INC-P<nnn>`), their open questions become candidate directions of their roadmap, and
   agents propose new directions and roadmaps when the open ones run out. Each paper carries a
   **certification**, computed from the repository: accepted, Lean-verified, re-verified by
   gardening, capped by its dependencies, with the badges "used by N" and "audited by a human".
8. **The owner** approves roadmaps (agents' proposals inside his domains pass after a veto window),
   reviews KNOWN.md, reads a nightly report, and keeps a veto on everything. See
   [CONTRIBUTING.md](CONTRIBUTING.md).

Agents are Claude Code sessions with one role each, launched by the scripts in `scripts/`; their
rules are in [AGENTS.md](AGENTS.md) and their prompts in [agents/roles/](agents/roles/). The design
rationale, in French, is in [docs/proposal/proposition.pdf](docs/proposal/proposition.pdf) (written
for version 1).

## Layout

| Path | Content | Owner |
|---|---|---|
| `roadmaps/<Name>/` | `ROADMAP.md` and `KNOWN.md` of each research area, its extensions, its candidate directions | the owner; agents propose, the loop appends candidates |
| `papers/<P>/` | one paper: `paper.tex`, `refs.bib`, `META.toml`, notebook, formalisation notes, errata | agents |
| `Statements/` | frozen Lean statements of accepted papers (`sorry` by design), one locked file each | agents, additions only |
| `Incognita/` | the library: definitions and proofs, no `sorry` | agents, under review |
| `Exploration/` | Lean drafts, `sorry` allowed, never imported by the library | agents |
| `catalogue/` | definitions, proof markers, attribution audits, relations between results | agents |
| `literature/` | bibliography, what was read in each source, source notes | agents |
| `templates/` | the paper template and its LaTeX macros | the owner |
| `agents/` | role prompts | the owner |
| `docs/` | design documents | the owner |
| `scripts/`, `tests/`, `.github/`, `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` | build, audit, CI and its canaries, the agent loop | the owner |

## Building

```bash
scripts/build.sh Incognita
latexmk -pdf -cd papers/<P>/paper.tex
```

The first command fetches Mathlib's and Tau Ceti's prebuilt files, then runs `lake build`;
LMLExplore publishes no cache, so the LMLExplore modules that are imported are compiled. CI checks
that the library has no `sorry`, no warning and only the three standard axioms, that frozen
statements only receive additions and match their locks, that each proof has exactly its frozen
type (`lake exe audit`), that the dependencies are pinned at LMLExplore's revisions (workflow
"CI", check "Build and check", required on `main`); the workflow "Papers" (check "Compile papers")
compiles every paper to PDF (artifact `papers-pdf`) when a pull request touches `papers/`.

## License

Apache 2.0, see [LICENSE](LICENSE).
