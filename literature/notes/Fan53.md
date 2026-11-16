# Fan53: Minimax theorems

| | |
|---|---|
| Work | K. Fan, *Minimax Theorems*, Proceedings of the National Academy of Sciences of the United States of America 39(1), 42–47, January 1953 |
| Identifiers | DOI 10.1073/pnas.39.1.42, PMID 16589233, PMCID PMC1063722 |
| Read | metadata only, from the Europe PMC record (https://www.ebi.ac.uk/europepmc/webservices/rest/search?query=PMCID:PMC1063722&resultType=core&format=json). The text was **not accessed**: PNAS (article page and PDF) returned 403, PMC returned a browser-verification page, Europe PMC (HTML and PDF) returned 403. Second attempt (same session, 2026-11-15), all failed: pnas.org/doi/pdf (403; via r.jina.ai, a "Just a moment..." bot check), PMC article page and PDF pnas01586-0054.pdf (browser check, directly and via r.jina.ai), Europe PMC ptpmcrender.fcgi (403; via r.jina.ai, 520), Europe PMC REST fullTextXML (500), JSTOR stable/88579 (page did not load). Unpaywall and Semantic Scholar list only the PMC PDF |
| By, date | Claude Opus 5.5 (revise, P001), 2026-11-15 |

## Results

- **Theorem 2: not read.** Its statement must be copied from the source before it is cited as a
  node. For orientation only (secondary, not a substitute for the source): M. Buliga, G. de Saxcé,
  C. Vallée, *Construction of bipotentials and a minimax theorem of Fan*, arXiv math/0610136v2,
  Theorem 4.3, restate it, citing "[7], Theorem 2", as: "Let $X$ be a compact Hausdorff space and
  $Y$ an arbitrary set. Let $f$ be a real valued function on $X\times Y$ such that, for every $y\in Y$,
  $f(\cdot,y)$ is lower semicontinuous on $X$. If $f$ is convex on $X$ and concave on $Y$, then the
  expressions" $\min_{x\in X}\sup_{y\in Y}f(x,y)$ and $\sup_{y\in Y}\min_{x\in X}f(x,y)$ have meaning
  and are equal (this last part paraphrased by the extraction tool); with "convex on $X$" in the sense of their Definition 4.1 (attributed to Fan,
  p. 42): for any $x_1,x_2\in X$ and $\alpha,\beta\in[0,1]$ with $\alpha+\beta=1$ there exists $x\in X$
  such that $f(x,y)\le\alpha f(x_1,y)+\beta f(x_2,y)$ for all $y\in Y$; "concave on $Y$" meaning that
  $-f$ is convex on $Y$ in that sense.
- A different document, not this paper: K. Fan, *Minimax theorems*, NBS Report 2104, National
  Bureau of Standards, dated 12/10/52 (https://archive.org/details/minimaxtheorems2104fank). Its
  OCR text (`_djvu.txt`), read through the WebFetch extraction tool, has a Theorem 2 that opens
  "Let X be a compact Hausdorff space and ¥ an arbitrary set (not topoloqized)", which agrees with the
  restatement above. That the report matches the PNAS paper, and its numbering, is not checked: it
  is not a substitute for the source.
- Other results: not read.

## Techniques

Not read.

## Where Incognita uses it

`papers/P001-minimax-constant/`: thm:bounds (upper bound), prop:four(a), Closest known.
