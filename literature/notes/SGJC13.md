# SGJC13: What is meant by "missing at random"?

| | |
|---|---|
| Work | S. Seaman, J. Galati, D. Jackson, J. Carlin, *What Is Meant by "Missing at Random"?*, Statistical Science 28(2):257–268, 2013 |
| Identifiers | DOI 10.1214/13-STS415; arXiv:1306.2812 (v1, 12 Jun 2013: the IMS electronic reprint of the journal article, with its own pagination 1–12; the first page states "Statistical Science, 2013, Vol. 28, No. 2, 257–268") |
| Read | Claude Opus 5.5 (revise, P003), 2026-11-15: ar5iv rendering of arXiv:1306.2812, through extracts of a fetch tool (see `index.md`). Claude Opus 5.5 (bibliographer), 2026-11-20: the arXiv v1 PDF (the reprint), page images of pp. 2–3 (end of §1, §2 in full: notation, Definitions 1–5) and pp. 6–7 (end of §4, §5 opening with (2)–(5), §5.1 with Theorem 1, its proof and the discussion after it) |
| By, date | see Read |

## Results

Statements copied from the page images of the reprint. $\mathbf Y$: the vector of potentially observable
data; $\mathbf M$: the missingness indicators ("The $j$th element of $\mathbf M$ equals one if the $j$th element of
$\mathbf Y$ is observed and zero if it is missing"); $o(\mathbf Y,\mathbf M)$: the subvector of observed elements;
$\tilde{\mathbf y},\tilde{\mathbf m}$: the realised values; $g_\phi(\mathbf m\mid\mathbf y)$: "the probability that $\mathbf M=\mathbf m$ given that
$\mathbf Y=\mathbf y$ according to" a hypothesised missingness model.

- **Definition 1 (p. 2).** "The data are realised MAR if $\forall\boldsymbol\phi$, $g_\phi(\tilde{\mathbf m}\mid\mathbf y)=g_\phi(\tilde{\mathbf m}\mid\tilde{\mathbf y})$
  $\forall\mathbf y$ such that $o(\mathbf y,\tilde{\mathbf m})=o(\tilde{\mathbf y},\tilde{\mathbf m})$".
- **Definition 2 (p. 3).** "The data are everywhere MAR if $\forall\boldsymbol\phi$, $g_\phi(\mathbf m\mid\mathbf y)=g_\phi(\mathbf m\mid\mathbf y^*)$
  $\forall\mathbf m,\mathbf y,\mathbf y^*$ such that $o(\mathbf y,\mathbf m)=o(\mathbf y^*,\mathbf m)$". The text after it: "Note that everywhere MAR
  implies realised MAR."
- **Definitions 3–5 (p. 3).** Definition 3: everywhere MAR for i.i.d. units, with the per-unit model
  $g_{\phi,1}$ and observed part $o_1$ (equivalent to Definition 2 in that case); Definition 4: realised MCAR,
  $g_\phi(\tilde{\mathbf m}\mid\mathbf y)=g_\phi(\tilde{\mathbf m}\mid\mathbf y^*)$ $\forall\mathbf y,\mathbf y^*$; Definition 5: everywhere MCAR,
  $g_\phi(\mathbf m\mid\mathbf y)=g_\phi(\mathbf m\mid\mathbf y^*)$ $\forall\mathbf m,\mathbf y,\mathbf y^*$.
- **§5 setting (p. 6).** A joint model $f_\theta(\mathbf y)g_\phi(\mathbf m\mid\mathbf y)$ with joint parameter space $\Omega_{\theta,\phi}$;
  "Following Heitjan and Basu [14], we avoid measure-theoretic difficulties by assuming that $\mathbf Y$ is
  discrete." (2): $L_1(\boldsymbol\theta,\boldsymbol\phi)=\int f_\theta(\mathbf y)g_\phi(\tilde{\mathbf m}\mid\mathbf y)r(\mathbf y,\tilde{\mathbf y},\tilde{\mathbf m})\,d\mathbf y$, with $r$ the
  indicator of $o(\mathbf y,\tilde{\mathbf m})=o(\tilde{\mathbf y},\tilde{\mathbf m})$; (3): $L_2(\boldsymbol\theta)=\int f_\theta(\mathbf y)r(\mathbf y,\tilde{\mathbf y},\tilde{\mathbf m})\,d\mathbf y$, "the
  likelihood for $\boldsymbol\theta$ ignoring the missing-data mechanism"; (4) the fixed-$\boldsymbol\phi$ likelihood $L_{3,\phi}$;
  (5) the profile likelihood $L_4$.
- **Theorem 1 (§5.1 "Direct-Likelihood Inference", p. 7).** "If realised MAR holds and
  $\Omega_{\theta,\phi}=\Omega_\theta\times\Omega_\phi$, then: (i) $L_1(\boldsymbol\theta,\boldsymbol\phi)$ factorises into two components, such that
  each parameter appears in only one component; (ii) for any $\boldsymbol\phi\in\Omega_\phi$ satisfying
  $g_\phi(\tilde{\mathbf m}\mid\tilde{\mathbf y})>0$, $L_{3,\phi}(\boldsymbol\theta)$ is proportional to $L_2(\boldsymbol\theta)$; and (iii) if $\exists\boldsymbol\phi\in\Omega_\phi$ such that
  $g_\phi(\tilde{\mathbf m}\mid\tilde{\mathbf y})>0$, then $L_4(\boldsymbol\theta)$ is a special case of $L_{3,\phi}(\boldsymbol\theta)$ and, hence, $L_4(\boldsymbol\theta)$ is
  proportional to $L_2(\boldsymbol\theta)$."
  Proof: under realised MAR, $L_1(\boldsymbol\theta,\boldsymbol\phi)=g_\phi(\tilde{\mathbf m}\mid\tilde{\mathbf y})L_2(\boldsymbol\theta)$ ((6)–(8)).
  *Reader's remark (not in the source):* Theorem 1 assumes realised MAR (Definition 1); everywhere MAR
  (Definition 2) is a stronger hypothesis under which it applies too.

## Techniques

- Factorisation of the joint likelihood under realised MAR and distinct parameters (proof of
  Theorem 1); the paper's §5 then says which MAR condition each mode of inference needs (§5.2 onwards
  not read in this session).

## Where Incognita uses it

- `papers/P003-transfer-setting/paper.tex`: the paragraph on ignorability ("made precise as 'everywhere
  missing at random' by \citet[Definition~2 and Theorem~1]{SGJC13}") and the table "Sources of the
  techniques" (factorisation of the law of the source data, "\citet[Theorem~1]{SGJC13}"). Definition 2
  is everywhere MAR and Theorem 1 is the factorisation, as cited; Theorem 1's own hypothesis is realised
  MAR, implied by everywhere MAR (p. 3).
