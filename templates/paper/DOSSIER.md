# Dossier of P<nnn>-<slug>, version <k>

*Template (AGENTS.md, section 5.2): copy to `papers/P<nnn>-<slug>/DOSSIER.md`, replace every
`<...>` and delete this line.*

Refereed and versioned with `paper.tex`, never compiled into the PDF: what the referees and the
owner need and the reader does not. It changes only with a new version of `paper.tex` after
acceptance. Private KNOWN entries are cited by id only, never quoted.

## Roadmap correspondence

- Items served (`directions` of META.toml): <D3: how the paper serves it; for a direction that
  several papers serve, which part>.
- <For an owner's result stated in the roadmap: the roadmap's statement, verbatim, then its
  correspondence with `thm:main`, symbol by symbol.>
- What the items ask that the paper does not give: <...> (the paper says it in words in its Scope
  remark).
- Predicted interest: <n>/10, because <what the result changes in the literature> (D and C items;
  AGENTS.md section 4.1).
- Acceptance criteria of the roadmap, one by one: <criterion: met or not, where in the paper>.
- Conventions of the roadmap changed, if any: <which, and why> (also declared in the Setting).

## Closest known

For each nearest KNOWN entry (by id: `K3`), published result (`[KEY, part]`) and library paper
(`INC-P<nnn>`, label): what it says, the difference with `thm:main`, and an honest attempt to
derive `thm:main` from it, with the step where the attempt fails.

- <K3>: <...>
- <[GMS19, Theorem 1]>: <...>

## Sanity checks

- Degenerate cases: <$x = 1$, $K = 2$, Bernoulli rewards, $N = 0$, ties, infinite divergences: what
  the results give in each, and why it is right>.
- Consistency with every `[Lean]` entry of KNOWN.md and with the roadmap's known results: <entry by
  entry>.
- The explicit example satisfying all the hypotheses at once: <where it is in the paper (Section
  `sec:examples`), and the check>.

## Weak points

The three steps the authors are least sure of, most doubtful first, each by label and step:

1. <`lem:example`, step 2>: <why>.
2. <...>
3. <...>

## Searches

The web queries run, with their dates and what they found:

- "<query>" (<YYYY-MM-DD>): <what it found>.

## Reading notes

<Optional: what was read of each cited source (part), beyond `literature/index.md`.>

## Changes

<For a new version only: what changed since the previous version, node by node (a presentation
revision: "statements unchanged", and how each node was reworded or moved).>
