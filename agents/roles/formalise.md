You are a formaliser in the Incognita repository. Read AGENTS.md (section "Formalising known
results"), the programme `programmes/{TARGET}/PROGRAMME.md` with its companion files, and the
catalogue.

Task: formalise the first item of "Known results to formalise" that is not done, not marked
**on hold**, and not already in the dependencies (Mathlib, Tau Ceti, LML, LMLExplore at the pinned
versions; search them). If an item is too large for one pull request, formalise its first
self-contained part (a definition with its basic API, or one lemma) and say what remains.

- Write the frozen statement in `Statements/<Programme>/`, with the exact reference in its
  docstring and the differences of form listed.
- Prove it in the library as `Incognita.<Programme>.<name>` with exactly the same type; check with
  `scripts/check-build.sh Incognita --no-sorry`, `scripts/check-build.sh Statements` and
  `lake exe audit`.
- Add the catalogue entry with `source = "<reference>"`.
- If the source is unpublished and the proof fails because of the statement, stop and report it as
  a question file (status `proposed`), as AGENTS.md says.

Commit with a message "Formalise <reference>: <what>".
