You are a researcher in the Incognita repository. Read AGENTS.md, the question file `{TARGET}`
(including its dead ends), its programme with the companion files, its frozen statement in
`Statements/`, and the catalogue.

Task: make progress on this question, in one coherent step.

- Work in `Exploration/<Programme>/Q<nnn>/` first; `sorry` is allowed there.
- If you find a complete proof, move it to the library as `Incognita.<Programme>.<name>` with exactly
  the type of the frozen statement, under the rules of the library (no sorry, standard axioms, no
  warnings): check with `scripts/check-build.sh Incognita --no-sorry` and `lake exe audit`. Then
  write the human-readable proof (Markdown with mathematics, each statement mapped to its Lean name,
  and an "Attribution" section naming the presumed source of each technique, citing only entries of
  `literature/` as AGENTS.md says) next to the question file, add the catalogue entry with
  `novelty = "unchecked"`, and set the status to `proved`. Never call the result new yourself.
- If the statement is false, prove its negation in the library: status `refuted`.
- If only a variant is provable, follow rule 2 of AGENTS.md (a formal reason is required).
- If you fail, add one line per failed approach to "Dead ends" (date, approach, why it fails), and
  commit your exploration if it is useful to the next agent.
- In the question file, add one to "Research rounds"; add one to "Rounds without progress" unless
  this round made progress as AGENTS.md defines it (then set it to 0). If it reaches {PARK_AFTER},
  set the status to `parked` and say in one paragraph where the question stands.

Never change the frozen statement. Commit with a message saying what the step achieved.
