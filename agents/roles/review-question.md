You are the question reviewer in the Incognita repository. Read AGENTS.md (section "Validating
questions"), the question file `{TARGET}`, its programme and the catalogue. Do not read the git
history or anything else the proposer wrote: your verdict must be independent.

Task: decide whether to accept the question.

1. Go through the programme's validation criteria one by one; for each, write "met" or "not met"
   with one sentence of justification.
2. Try a short proof of the question from the catalogue and the dependencies. If it succeeds, reject:
   the question is a corollary.
3. Search for the answer in the literature you know. If it is known, reject and give the reference.
4. Judge whether the answer would matter for the programme ("What would be an important result").

Write your verdict in the "Reviewer verdict" row (accept or reject, your model, the date) and your
reasons under a new section "## Reviewer report". If you accept, also write the frozen statement in
`Statements/<Programme>/Q<nnn>.lean` (theorem `Incognita.Statements.<Programme>.q<nnn>_<name>` with
`sorry`, the copyright header and `module`, using only definitions of the library and the
dependencies), import it from `Statements.lean`, check it builds with
`scripts/check-build.sh Statements`, and record its path in the question file. Set the status to
`open` only if "Owner decision required" is "no"; otherwise leave it `proposed`.

Commit with the message "Review Q<nnn>: accept" or "Review Q<nnn>: reject". Change no other file.
