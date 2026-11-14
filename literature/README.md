# Literature

What Incognita cites, and what has actually been read. Agents invent plausible references easily
(a wrong theorem number, a wrong year, a paper that does not exist), and Lean does not see them. So
a reference is cited in a paper, a docstring or the catalogue only after someone has read the cited
part in the source. Rules: [AGENTS.md](../AGENTS.md), section 7.

## Files

- `bibliography.json`: one entry per work, in the format of LMLExplore's
  `scripts/literature/bibliography.json` and `lml-paper-template` (CSL-JSON under `citation`, with
  `uri` and `identifiers`). Keys are LMLExplore's when the work is there (`GMS19`, `LS`, `GC11`), so
  that citations mean the same thing in both projects; otherwise the authors' initials and the year.
  A paper's `refs.bib` uses the same keys and the same metadata.
- `index.md`: the status of every entry: metadata checked or not, what was read, by whom, when.
- `notes/<KEY>.md`: for a work that has been read, what it proves (numbered results), the
  techniques it introduces or uses, and exactly which parts were read. Template:
  `notes/TEMPLATE.md`.

## Notes are the fixed reference for statements

- A **cited result** in a paper is a node whose statement is copied **verbatim** from
  `notes/<KEY>.md`. If the note lacks it, the writer reads the source and adds it to the note in the
  same pull request.
- An **external paper** (`kind = "external"`, a published result to formalise) is formalised from
  the note of its source, which must exist before its statements pull request and come from another
  session. The bibliographer writes missing notes, and the scope referee checks external papers
  against the source itself.
- In a note, statements are copied exactly (hypotheses, conclusion, constants, the source's
  numbering); everything else is summarised in your own words, with at most short quotations.

## Citing

In papers, `\cite[<part>]{KEY}` (for example `\cite[Theorem~4.3]{GMS19}`); in Lean docstrings,
Markdown and the catalogue, `[KEY, Theorem 4.3]`, `[KEY, (6)]` or `[KEY, proof of Theorem 3]`, as in
LMLExplore. A citation points to an entry whose cited part is marked as read in `index.md`;
otherwise it is followed by "(to be checked)". A new entry is added with metadata `unchecked`.

Papers of the Incognita library are not entries of `bibliography.json`: they are cited by their key
`INC-P<nnn>` (`\cite[Theorem~2]{INC-P001}`, in Lean docstrings `[INC-P001, Theorem 2]`), from
`papers/library.bib`, which `scripts/certify.py bib` generates; the version read goes in
`depends_on` (AGENTS.md, section 5.6).

## Who checks

Any writing role adds entries and notes for what it read. The bibliographer
([agents/roles/bibliographer.md](../agents/roles/bibliographer.md)) checks metadata against the
publisher's page or arXiv, writes missing notes, and audits the attribution of every verified paper
(`catalogue/attribution/`), independently of the scope referee, who searches the earliest source of
each technique when the paper is refereed.

## Statuses (`index.md`)

| Column | Values |
|---|---|
| Metadata | `checked` (title, authors, venue, year and identifier compared with the publisher's or arXiv's page) or `unchecked` |
| Read | the parts read in the source (`abstract`, `Theorem 4.3`, `Sections 1-3`, `whole`), or `—` |
| By, date | the model or person who read it, and when |

The entries created on 2026-11-13 come from the v1 programmes (now `roadmaps/`) and from the owner's
own bibliographies; their metadata is `unchecked` until the bibliographer checks it.
