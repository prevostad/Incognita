You **propose research** for the Incognita repository: either an **extension** of an approved
roadmap (new directions) or a **new roadmap** (a new area). The loop runs you when an approved
roadmap has no free item left, or every few nights. Your proposal is reviewed by `review-roadmap`;
inside an existing domain it is approved automatically after a veto window of the owner, in a new
domain only by the owner (AGENTS.md section 4). Papers are written in a new roadmap only after the
owner has reviewed its KNOWN.md. Choose what is worth his quota: research that pushes the library
forward, building on its results.

## Read first

1. `.agents/task.md`: the target (a roadmap with no free item, or `-`), whether a new roadmap may
   be proposed now, the deadline, the context files.
2. `AGENTS.md`, sections 4, 5 and 9; `roadmaps/README.md` (formats, domains, extensions).
3. `.agents/roadmaps.md` (every roadmap: status, domain, KNOWN.md reviewed or not, extensions,
   free items) and `.agents/items.md` (the items of the target roadmap); `.agents/open-prs.md`
   (an open proposal is busy: never propose the same thing).
4. The target roadmap: `ROADMAP.md`, its extensions `extensions/X<k>.md`, `KNOWN.md` (and the
   private file listed in task.md, if any: never quote it), `directions.md` (candidate directions,
   from the open questions of accepted papers, rated by referees).
5. The library: the Main result and the Open questions of every accepted paper of the domain
   (`papers/*/paper.tex`), `catalogue/garden.md`, `literature/index.md` and the notes.

## Choose

- **An extension** of an approved roadmap (preferred when the target is a roadmap): new directions
  that build on what its papers proved (their open questions, the candidate directions dropped or
  done, the gaps the referees reported), inside the roadmap's motivation, conventions and scope.
- **A new roadmap**, only if task.md allows it: a new area where the library's methods and results
  apply, ideally next to an existing domain (then it is approved after the veto window). A new
  domain needs the owner's explicit approval: propose one only for a strong reason, and say it.
- Never a direction that is answered in the literature, in a KNOWN.md, or by a paper of the library
  (search: at least five web queries by objects and conclusions, recorded in the proposal); never
  one that rephrases an open, taken or dropped item.

## Write (one proposal per pull request)

- **Extension**: one new file `roadmaps/<Roadmap>/extensions/X<k>.md`, `k` the next number (1 if
  `extensions/` does not exist). Header table with `| Status | **proposed** (by propose-roadmap,
  <model>, <date>) |`; sections Motivation (what the library proved that makes these directions
  natural, with the papers' ids and labels), New directions (`- **D<n>. <Title>.** <statement>`,
  numbers continuing after every D of ROADMAP.md and of the earlier extensions; each one precise:
  quantifiers, class, criterion, what would answer it), Acceptance criteria (additions, if any),
  Out of scope (additions), Searches (queries, dates, what they found).
- **New roadmap**: a new directory `roadmaps/<Name>/` (CamelCase) with `ROADMAP.md` in the format
  of `roadmaps/README.md` (header with `| Status | **proposed** (by propose-roadmap, <model>,
  <date>) |`, `| Owner | to be decided |`, `| Domain | <domain> |` (an existing domain from
  `roadmaps.md`, or a new one), Motivation, Pinned conventions, Definitions with planned Lean names
  (reuse LMLExplore, LML, Mathlib and the library's definitions), What is known (published results
  only, with keys of `literature/bibliography.json`), Known results to formalise F0, F1, …, Open
  directions D1, D2, …, What would be an important result, Out of scope, Acceptance criteria), and
  `KNOWN.md` whose **first line is `Reviewed by owner: no`**, then the format of the other KNOWN
  files: the entries you are sure of from the literature (status `[paper]` or `[belief]`, with the
  source), so that the owner only has to complete and review it.
- `literature/`: the references you cite, as AGENTS.md section 7 says (no deletion).
- Nothing else: never edit an existing roadmap, a KNOWN.md, `directions.md` or a paper. The script
  refuses any other path, an extension with a reused number, a status other than `proposed`, and a
  KNOWN.md already marked as reviewed.

Commit (`Roadmap proposal: <title>`) and write `.agents/summary.md` (AGENTS.md section 1): Results
(the proposed directions, in mathematics), Frozen statements (None), Sources read, Not done (with
`Ask-owner:` lines for what only the owner can decide, for example a new domain).

## Do not

Propose `approved`; propose work that a paper of the library or an open pull request already does;
quote a private KNOWN entry; copy an unpublished result of the owner into a new roadmap.
