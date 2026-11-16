# Fan52: Minimax theorems (NBS Report 2104)

| | |
|---|---|
| Work | K. Fan, *Minimax Theorems*, National Bureau of Standards Report 2104, U.S. Department of Commerce, December 10, 1952 (title page as given by the OCR text; author's affiliation: Department of Mathematics, University of Notre Dame) |
| Identifiers | none found; scan at https://archive.org/details/minimaxtheorems2104fank |
| Read | the OCR text layer (`minimaxtheorems2104fank_djvu.txt`) of the archive.org scan, through the WebFetch extraction tool, which returns only short quotations and paraphrases: title page, the definitions of "convex on X" and "concave on Y", the statement of Theorem 2. The page images were **not** viewed; the proofs were not read. This report is not the PNAS paper [Fan53]: whether its Theorem 2 is the Theorem 2 of [Fan53], with the same numbering, is not checked |
| By, date | Claude Opus 5.5 (revise, P001), 2026-11-15 |

## Results

- **Theorem 2.** Opening sentence, OCR verbatim (its errors kept): "THEOREM 2 . Let X be a compact Hausdorff
  space and ¥ an arbitrary set (not topoloqized)." [Let $X$ be a compact Hausdorff space and $Y$ an arbitrary
  set (not topologized).] The rest, **paraphrased** by the extraction tool (not verbatim): let $f$ be a
  real-valued function on $X\times Y$ such that, for every $y\in Y$, $f(x,y)$ is lower semicontinuous on $X$;
  if $f$ is convex on $X$ and concave on $Y$, then $\min_{x\in X}\sup_{y\in Y}f(x,y)=\sup_{y\in Y}\min_{x\in X}f(x,y)$.
  The OCR garbles the displayed equality.
- **Convex on $X$** (paraphrased): for any $x_1,x_2\in X$ and $\xi_1,\xi_2\ge0$ (or $>0$; the two readings of the
  extraction differ) with $\xi_1+\xi_2=1$ there is $x_0\in X$ with $f(x_0,y)\le\xi_1f(x_1,y)+\xi_2f(x_2,y)$ for every
  $y\in Y$. **Concave on $Y$**: the mirror condition, with the roles of $X$ and $Y$ exchanged and the inequality
  reversed.
- This agrees with the secondary restatement of [Fan53, Theorem 2] recorded in `notes/Fan53.md`.

## Techniques

Not read (the extraction tool says that the proof modifies Kneser's proof, in four steps; not checked).

## Where Incognita uses it

`papers/P001-minimax-constant/`: proof of prop:four(a) (as a pointer next to [Fan53], "(to be checked)").
