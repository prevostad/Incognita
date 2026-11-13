# Incognita

Mathematical research by AI agents, verified in Lean 4, on top of
[LMLExplore](https://github.com/LeanMachineLearning/LMLExplore), and so of
[LML](https://github.com/LeanMachineLearning/LML), [Tau Ceti](https://github.com/TauCetiProject/TauCeti)
and [Mathlib](https://github.com/leanprover-community/mathlib4).

> **Independent project.** Incognita is not part of, affiliated with, or endorsed by LMLExplore,
> LML or Tau Ceti. It only uses LMLExplore as a Lean dependency, and borrows its build scripts from
> [lml-paper-template](https://github.com/LeanMachineLearning/lml-paper-template) (Apache 2.0).

**Status: design stage.** The rules and the first programme are written; no agent works here yet.

## Why

LMLExplore has agents formalise *known* results, chosen by humans in roadmaps: the truth and the
interest of each statement come from the literature. Incognita aims at *new* results. Lean settles
whether a proof is correct, but not whether a statement means what it should, nor whether it
matters. These guarantees have to be rebuilt, and the quality bar is at least LMLExplore's, even if
research goes slower.

## How it works

1. **Programmes** (human-owned): a human approves a research programme, a short text with
   motivation, pinned conventions, known results, open directions and criteria for questions.
   See [programmes/](programmes/).
2. **Questions** (agents): agents propose questions inside an approved programme. A question
   reviewer validates them against the programme's criteria. While the project is being
   calibrated, the owner validates every question too.
3. **Frozen statements**: a validated question gets its Lean statement, with `sorry`, in
   `Statements/`. It is frozen: a proof must prove exactly it.
4. **Results**: agents prove the statement, refute it (a formal counterexample is a result), or
   prove a justified variant. Exploratory work lives in `Exploration/`, where `sorry` is allowed.
5. **Library**: a result enters `Incognita/` only under LMLExplore's standard (no `sorry`, standard
   axioms, Mathlib's linters), with a human-readable write-up and an entry in the
   [catalogue](catalogue/).
6. **Gardening**: agents consolidate the library (a general result subsumes special cases only if
   it is quantitatively as good; "optimal" is never a definition; no theorem is ever lost).
7. **Confidence**: a result's confidence level rises with independent checks of different kinds
   and with use, not with time.

The full rules for agents are in [AGENTS.md](AGENTS.md); the human side is in
[CONTRIBUTING.md](CONTRIBUTING.md); the design rationale, in French, is in
[docs/proposal/proposition.pdf](docs/proposal/proposition.pdf).

## Layout

| Path | Content | Owner |
|---|---|---|
| `programmes/<Name>/PROGRAMME.md` | approved research programmes | humans |
| `programmes/<Name>/questions/` | one file per question: status, statement, dead ends, outcome | agents |
| `Statements/` | frozen Lean statements of validated questions (`sorry` by design) | humans approve changes |
| `Exploration/` | drafts, `sorry` allowed, never imported by the library | agents |
| `Incognita/` | the library: results that passed every check | agents, under review |
| `catalogue/` | metadata of the main results, used for gardening | agents |
| `templates/` | templates for questions | humans |
| `docs/` | design documents | humans |
| `scripts/`, `.github/`, `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` | build and CI | humans |

## Building

```bash
scripts/build.sh Incognita
```

The script fetches Mathlib's and Tau Ceti's prebuilt files, then runs `lake build`. LMLExplore
publishes no cache, so the LMLExplore modules that are imported are compiled. CI checks that the
library has no `sorry` and no warnings, that `Statements/` and `Exploration/` build, and that the
dependencies are pinned at LMLExplore's revisions.

## License

Apache 2.0, see [LICENSE](LICENSE).
