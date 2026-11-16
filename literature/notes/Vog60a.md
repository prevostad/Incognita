# Vog60a: A sequential design for the two armed bandit

| | |
|---|---|
| Work | W. Vogel, *A Sequential Design for the Two Armed Bandit*, The Annals of Mathematical Statistics 31(2), 430–443, 1960 |
| Identifiers | DOI 10.1214/aoms/1177705906 (Crossref: issued 1960-06) |
| Read | Metadata (Crossref, OpenAlex). "Abstract" reconstructed from the OpenAlex `abstract_inverted_index` (one position, 142, missing): it is the text of Section 1, Introduction. Project Euclid not accessed. Not read: Sections 2 onward |
| By, date | Claude Opus 5.5 (revise, P001), 2026-11-15 |

## Results

- **Section 1 (as indexed).** Two experiments with means $p$, $q$, horizon $n$, maximise the sum of
  outcomes. "The purpose of this paper is to describe a class of strategies, which results from the
  following kind of restriction. In the first 2k steps we perform each of Ex I and Ex II k times. Then
  the rest of the n - 2k steps are made either with Ex I alone or with Ex II alone. The decision
  whether to continue with Ex I or with Ex II will be made with the help of a sequential probability
  ratio test for double dichotomies." "Strategies of this kind are not exceptionally good ones (in
  the sense of the lossfunction defined in Section 3)." "Another justification for treating this
  class of strategies are the results in [8], for which the Theorems 2 and 3 of this paper are
  needed." ([8] is presumably Vog60; not checked.)
- Theorems 1–3: not read. No order of magnitude of the risk appears in the indexed text.

## Techniques

Explore-then-commit with a sequential probability ratio test deciding the commitment (Section 1).
Credits Robbins, Bradt–Johnson–Karlin, Isbell, Bellman for earlier approaches.

## Where Incognita uses it

`papers/P001-minimax-constant/`: thm:bounds, Main result, Closest known, Attribution.
