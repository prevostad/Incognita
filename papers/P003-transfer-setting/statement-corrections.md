# Statement corrections of P003

Entries `SC<n>` (AGENTS.md §6.6 (a)): a frozen Lean statement that mistranslates the paper. Append-only.

## SC1 (2026-11-19, owner, claude-opus-5-5)
- Node: prop:exclusion
- Frozen statement: Incognita.Statements.P003.followSource_not_isConsistent
- Problem: the second conjunct lets the source sizes `n` be `0`. With `n = 0` the learner `π^tr` has no source data and pulls arm `1` at every round, so the conjunct only says that a constant learner fails, not what the paper claims: that `π^tr` already fails when it does receive source data, with deterministic sizes (the paper's proof uses sizes `1` and Bernoulli laws). The current proof uses exactly this degenerate case (found by the audit of the library on Tau Ceti's rubrics, rubric `correctness`, 2026-11-19).
- Correction: the same statement with, in the second conjunct, the sizes required to be positive: `∃ n : α → ℕ, (∀ k, 1 ≤ n k) ∧ …` (relation `closeMatch`; the first conjunct is unchanged).
Resolved by Incognita.Statements.P003.followSource_not_isConsistent_v2 (statements pull request).
