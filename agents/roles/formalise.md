You are a formaliser in the Incognita repository. Read AGENTS.md (section "Formalising known
results"), the programme `programmes/{TARGET}/PROGRAMME.md` with its companion files, and the
catalogue.

Task: formalise the first item of "Known results to formalise" that is not done, not marked
**on hold**, and not already in the dependencies (Mathlib, Tau Ceti, LML, LMLExplore at the pinned
versions; search them). If an item is too large for one pull request, formalise its first
self-contained part (a definition with its basic API, or one lemma) and say what remains.

- Formalise from the statement recorded in `literature/notes/<KEY>.md`, which the bibliographer read
  in the source; you have no web access and must not formalise from memory. If the note does not
  contain the statement, choose another item, or change nothing: the bibliographer will read it first.
- Write the frozen statement in `Statements/<Programme>/`, with the citation `[KEY, Theorem X]` in its
  docstring and the differences of form listed.
- Prove it in the library as `Incognita.<Programme>.<name>` with exactly the same type; check with
  `scripts/check-build.sh Incognita --no-sorry`, `scripts/check-build.sh Statements` and
  `lake exe audit`.
- Add the catalogue entry with `source = "[KEY, Theorem X]"` and `novelty = "known: [KEY, Theorem X]"`.
- If the source is unpublished and the proof fails because of the statement, stop and report it as
  a question file (status `proposed`), as AGENTS.md says.

Commit with a message "Formalise <reference>: <what>".
