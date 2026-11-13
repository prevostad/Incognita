# Q<nnn>: <short title>

| | |
|---|---|
| Programme | <Name> |
| Status | proposed |
| Proposed by | <model or person>, <date> |
| Reviewer verdict | <accept / reject, reviewer model, date, reasons> |
| Owner decision | <accept / reject, date> (calibration phase only) |
| Frozen statement | `Statements/<Name>/Q<nnn>.lean` (set at validation) |

## Question

The precise mathematical statement, with its information model, its class of instances, its
criterion, and the quantifiers in full. Phrase it so that "no" is a possible answer.

## Relation to known results

Which result of the programme or the catalogue it extends, and why its answer is not a corollary
of them.

## Joint satisfiability

One explicit example that satisfies all the hypotheses at once.

## Natural fallback

The variant that would be the natural target if the answer is "no".

## Dead ends

One line per failed approach: date, approach, why it fails.

## Outcome

Filled when the question is closed: `proved`, `refuted`, `variant-proved` or `abandoned`, with the
Lean declarations, the write-up, and, for a variant, the formal reason it was needed.
