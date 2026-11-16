# Ber76: bottom-up computation of recursive programs

| | |
|---|---|
| Work | Gérard Berry, *Bottom-up computation of recursive programs*, Revue française d'automatique, informatique, recherche opérationnelle. Informatique théorique 10 (R1), 47–82, 1976 |
| Identifiers | Numdam ITA_1976__10_1_47_0 (http://www.numdam.org/item/ITA_1976__10_1_47_0/) |
| Read | §II.2 "Stable functions" (pp. 56–57): the definition of stable functions, Proposition II.2.1, the definition of sequential functions (after Vuillemin) with the critical index, Proposition II.2.2 and its proof; through the OCR text layer of the Numdam scan (the page images were not viewed) |
| By, date | Claude Opus 5.5 (revise, P003), 2026-11-16 |

## Results

- Definition (§II.2): a monotone function $b$ from $D^p$ to a discrete domain $D$ is *stable* if
  $b(x\wedge x')=b(x)\wedge b(x')$ for all joinable $x,x'$.
- Proposition II.2.1: $b$ is stable if and only if every $x$ has a unique minimal $m_b(x)\le x$ with
  $b(m_b(x))=b(x)$.
- Definition (after Vuillemin): $b$ is *sequential* if for every $x$ there is an index $i$ (the
  *critical index* of $x$) such that $y\ge x$ and $y_i=x_i$ imply $b(y)=b(x)$. Example: if-then-else.
- Proposition II.2.2: every sequential function is stable; there exist stable functions that are
  not sequential. The proof of the second claim takes $D=\{\bot,0,1\}$ and the least function $b$
  defined by three equations that put the value $0$ on three partial inputs of three arguments,
  each with one $\bot$, in a cyclic pattern, and observes that an input has no critical index.
  The OCR text layer garbles the third equation and the input ("b (1,0, 1) = 0" and "(JL, 1 , 1 )");
  the cyclic form is the one given by Cur03, pp. 5–6:
  $BK(\mathrm{true},\mathrm{false},\bot)=BK(\mathrm{false},\bot,\mathrm{true})=BK(\bot,\mathrm{true},\mathrm{false})=\mathrm{true}$,
  and the input without critical index is then $(\bot,\bot,\bot)$ (each argument is $\bot$ in one
  of the three defining inputs). This is the "Gustave function" (Cur03 credits it to Berry, and a
  variant to Kleene).

## Techniques

- Stability by minimal data, and sequentiality by a critical index: an argument that must be
  evaluated first. The counterexample is a cyclic pattern of minimal data, so that no argument is
  needed on every input.

## Where Incognita uses it

- `papers/P003-transfer-setting/`: `prop:stopped-games`(c) (the cyclic size rule $N^{\rm cyc}$ has
  the same pattern: its observed sets on its first three cases are the minimal inputs of the
  Gustave function), the remark after it, Related work and Appendix D.
