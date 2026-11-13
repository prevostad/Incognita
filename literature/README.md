# Literature

What Incognita cites, and what has actually been read. Agents invent plausible references easily
(a wrong theorem number, a wrong year, a paper that does not exist); Lean does not see them. So a
reference is cited in the library or in a write-up only after someone has checked it in the source.

## Files

- `bibliography.json`: one entry per work, in the format of LMLExplore's
  `scripts/literature/bibliography.json` and `lml-paper-template` (CSL-JSON under `citation`, with
  `uri` and `identifiers`). Keys are LMLExplore's when the work is there (`GMS19`, `LS`, `GC11`), so
  that citations mean the same thing in both projects; otherwise initials of the authors and the year.
- `index.md`: the status of every entry: metadata checked or not, what was read, by whom, when.
- `notes/<KEY>.md`: for a work that has been read, what it proves (numbered results), the techniques
  it introduces or uses, and exactly which parts were read. Template: `notes/TEMPLATE.md`.

## Citing

In Lean docstrings, write-ups and catalogue entries, cite a numbered result as `[KEY, Theorem 4.3]`,
`[KEY, (6)]` or `[KEY, proof of Theorem 3]`, as in LMLExplore. A citation must point to an entry whose
metadata is checked and whose cited part is marked as read in `index.md`.

## Statuses (`index.md`)

| Column | Values |
|---|---|
| Metadata | `checked` (title, authors, venue, year and identifier compared with the publisher's or arXiv's page) or `unchecked` |
| Read | the parts read in the source (`abstract`, `Theorem 4.3`, `Sections 1-3`, `whole`), or `—` |
| By, date | the model or person who read it, and when |

The entries created on 2026-11-13 come from the programmes and from the owner's own bibliographies;
their metadata is `unchecked` until the bibliographer checks it.
