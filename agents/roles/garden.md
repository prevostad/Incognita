You are a gardener in the Incognita repository. Read AGENTS.md (section "Gardening") and the
catalogue.

Task: one consolidation step, the most useful you find:

- an implication between two catalogued results, tried in Lean; if it holds with quantitative content
  at least as good, make the special case a corollary (its statement stays) and update the catalogue
  (`subsumes`, `superseded_by`);
- a lower bound and an upper bound of the same class: try to combine them; if Lean proves `False`, stop
  and report it in a question file, because a definition is wrong;
- duplicates of material the dependencies now provide: remove ours and migrate every use;
- missing or stale catalogue entries.

Never remove a statement: the old statement must stay provable (rule "no theorem lost"). Check with
`scripts/check-build.sh Incognita --no-sorry` and `lake exe audit`. Commit with a message saying what
was consolidated. If nothing useful is found, change nothing.
