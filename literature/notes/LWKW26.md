# LWKW26: Multi-armed Bernoulli bandits via minimax single-arm stopping

| | |
|---|---|
| Work | H. Liu, Z. Wang, D. Kuhn, W. Wiesemann, *Multi-Armed Bernoulli Bandits via Minimax Single-Arm Stopping*, arXiv preprint, 2026 |
| Identifiers | arXiv 2609.22690 (v1 only, submitted 2026-09-19, "[cs.LG]"; subjects cs.LG, math.OC, stat.ML); DOI 10.48550/arXiv.2609.22690 (arXiv DOI); arXiv comment: "This work is a preprint and has not been submitted to any conference or journal yet"; no journal reference |
| Read | PDF of arXiv:2609.22690v1 (44 pages), through a PDF reader (text extraction and page images): abstract; §1 (pp. 1–4); §2.2 (p. 6); §3 opening (p. 8, admissible policies); §5 opening, §5.1, §5.2 (pp. 16–19: Theorem 2, the lower-bound paragraph, Remark 1); reference list (pp. 31–34). The rest was seen but not checked (proofs §5.3, Appendix A, experiments). The HTML rendering (arxiv.org/html/2609.22690) was also queried through a summarising tool; that rendering apparently numbers the main theorem "Theorem 5.1" (not checked); the numbering below is the PDF's. Metadata: arXiv abstract page. The PDF's running head reads "Anonymous Authors: Monotone-Adjusted One-Arm Index Policies" (a different title from the arXiv one) |
| By, date | Claude Opus 5.5 (revise, P001), 2026-11-15 |

## Results

Numbering and page numbers are those of the PDF of v1. Mathematics is transcribed into LaTeX from
the PDF text.

- **Model, §5.1, p. 16.** "Consider $K\ge2$ independent Bernoulli arms with fixed unknown mean vector
  $\mathbf p=(p_1,\dots,p_K)\in[0,1]^K$ and integer horizon $T\ge2$. Arm $k$ has an independent reward
  sequence $\tilde z_{k,1},\tilde z_{k,2},\dots\sim\mathrm{Ber}(p_k)$, and these sequences are mutually
  independent across arms. At round $t$, an admissible policy selects $\tilde a_t\in[K]:=\{1,\dots,K\}$
  using past observations. It observes the reward from the selected arm and no rewards from the other
  arms. Let $p^\star:=\max_{k\in[K]}p_k$ and $\Delta_k:=p^\star-p_k$." Then $\tilde n_{k,t}:=\sum_{i=1}^{t-1}\mathbf 1\{\tilde a_i=k\}$,
  "Thus $\tilde n_{k,T+1}$ is its total number of pulls." "The accumulated pseudo-regret is
  $\tilde r_T:=\sum_{t=1}^T\Delta_{\tilde a_t}$, and its expectation is
  $$R_T(\pi,\mathbf p):=\mathbb E_{\mathbf p}[\tilde r_T]=\sum_{k=1}^K\Delta_k\mathbb E_{\mathbf p}[\tilde n_{k,T+1}].\quad(10)$$
  We refer to this expected pseudo-regret simply as regret."
- **Admissible policies, §3, p. 8.** "Probabilities and expectations include both the rewards and any
  independent randomization used by the policy. An admissible policy uses only previously observed
  rewards and its own randomization." The horizon $T$ is known to the policy (the index uses
  $H=\lceil T/K\rceil$).
- **Theorem 2, §5.2, p. 18 (main result).** With (12) "$H:=\lceil T/K\rceil$, $G:=2H$, $b:=\frac14\sqrt G$":
  "Let $T\ge2K$, and choose $H,G,b$ as in (12). Let $\{\pi_{c,G}:c\in[0,1]\}$ be the SAB stopping policy
  family used to construct the adjusted index $j^{\mathrm{adj}}_{G,b}$. Assume that this adjusted index is
  evaluated exactly for the chosen auxiliary family, and that the family satisfies the uniform SAB regret
  bound $\sup_{c,p\in[0,1]}R_{c,G}(\pi_{c,G},p)\le\sqrt{\frac G{8e}}+\frac32$. Then the SAB-based index policy
  satisfies
  $$\sup_{\mathbf p\in[0,1]^K}R_T(\pi^{\mathrm{MAB}}_{G,H,b},\mathbf p)\le4.45\sqrt{KT}+10.75K.\quad(13)$$
  For $T<2K$, every admissible policy $\pi$ satisfies $R_T(\pi,\mathbf p)\le T<\sqrt{2KT}$ for all
  $\mathbf p\in[0,1]^K$."
- **Lower bound attributed to Cesa-Bianchi–Lugosi, §5.2, p. 18 (paragraph after Theorem 2), verbatim.**
  "The order of the bound in Theorem 2 cannot be improved in general. For $K\ge2$, the Bernoulli
  instances used in the lower-bound construction of Cesa-Bianchi et al. (2006, Theorem 6.11) imply
  $\inf_\pi\sup_{\mathbf p\in[0,1]^K}R_T(\pi,\mathbf p)\ge(\sqrt2-1)\sqrt{KT}/\sqrt{32\log(4/3)}>0.1365\sqrt{KT}$.
  Thus, the upper and lower bounds have the same dependence on $K$ and $T$, up to constants."
  - Conditions stated: only $K\ge2$. **No condition on $T$** is stated in this sentence (beyond the
    standing model of §5.1: integer $T\ge2$). No condition relating $T$ (or $n$) and $K$ appears.
  - Reward model: Bernoulli arms, $\mathbf p\in[0,1]^K$. Regret: $R_T$ of (10), the expected
    pseudo-regret. Infimum over admissible (possibly randomised, horizon-aware) policies.
  - Form of the citation: the text does not state Theorem 6.11 itself; it says that the Bernoulli
    instances of its construction "imply" the display. The notation ($K$, $T$, $R_T$) is the paper's own.
  - Bibliography entry, p. 32, verbatim: "Cesa-Bianchi N, Lugosi G, et al. (2006) Prediction,
    learning, and games, volume 1 (Cambridge university press Cambridge)." (The "et al." and
    "volume 1" are as printed; the book has two authors.)
  - The same bound is quoted in the opening of §5, p. 16: "The $\sqrt{KT}$ dependence is
    minimax-order optimal in view of the classical lower bound $0.1365\sqrt{KT}$ of Cesa-Bianchi et
    al. (2006, Theorem 6.11)."
  - Arithmetic (not in the paper; computed here with the natural logarithm):
    $(\sqrt2-1)/\sqrt{32\ln(4/3)}\approx0.41421/3.03411\approx0.13652$.
- **Other attributions of the lower bound in the paper.** §1, p. 3: the bound "has the minimax-optimal
  dependence on the horizon and the number of arms, matching the $\sqrt{KT}$ order in the classical
  lower bound of Auer et al. (2002b)" (Auer, Cesa-Bianchi, Freund, Schapire, SIAM J. Comput. 32(1)).
  §2.2, p. 6: "MOSS achieves the $\sqrt{KT}$ minimax regret order for $T\ge K$, matching the classical
  lower bound up to constants (Audibert and Bubeck 2009, Auer et al. 2002c)."
- **Remark 1, §5.2, p. 18 (summary).** Bounded rewards in $[0,1]$ reduce to Bernoulli rewards by
  feeding $\mathbf 1\{\tilde v_{k,n}<\tilde y_{k,n}\}$, $\tilde v_{k,n}\sim\mathrm{Unif}(0,1)$, to the policy;
  "this construction yields $R_T(\pi^{\mathrm{bin}},(\nu_1,\dots,\nu_K))=R_T(\pi,(p_1,\dots,p_K))$", so
  (13) holds over bounded-reward problems. Credited to Agrawal and Goyal (2012, 2013), Xu and Zeevi
  (2025), Riou and Honda (2020).
- **Remark 2, p. 19 (summary).** Other parameter choices give "a sharper theoretical regret bound
  $1.51\sqrt{KT}+1.9K$" (proof in the appendix, not read).

## Techniques

Index policy built from finite-horizon minimax solutions of single-arm stopping problems (one
unknown Bernoulli arm against a known reward $c$), computed by a semi-infinite linear program
(Theorem 1, §3.1); a shared uniform threshold per arm turns cumulative continuation probabilities
into a stopping rule (Proposition 4, §4.1). The lower bound of §5.2 is not proved in the paper.

## Where Incognita uses it

`papers/P001-minimax-constant/`: raised by a referee as a restatement of [CBL06, Theorem 6.11]; to
be cited only for its §5.2 sentence (as a secondary source for the constant), not for Theorem 6.11
itself.
