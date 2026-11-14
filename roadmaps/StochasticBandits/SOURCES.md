# Sources read for the roadmap StochasticBandits (2026-11-14)

Reader: Claude Opus 5.5 (agent), 2026-11-14. Method: each PDF was fetched from the URL given, its
text extracted with `pdftotext -layout`, and the cited parts read in the extraction; where the
mathematics was garbled, the page itself was read as an image (listed as "page image"). Only the
parts listed below were read; everything else in these works was not. A KNOWN.md entry that relies
on a part not read says `(to be checked)`.

These parts are also marked as read in [literature/index.md](../../literature/index.md) (column
"Read", by "agent (roadmap draft), 2026-11-14"); the works are entries of
`literature/bibliography.json`, whose metadata is `unchecked` until the bibliographer checks it.
This file records the reading of the draft; it is not kept up to date afterwards: `literature/` is
the reference.

## Works read

| Key | Version read (URL) | Parts read | Not read / caveats |
|---|---|---|---|
| GMS19 | arXiv:1602.07182v3 (13 Oct 2018), https://arxiv.org/pdf/1602.07182 | pp. 4–7: definition of $\mathcal K_{\inf}$, (2), §1.3–1.4, §2 inequality (6), (7), Remarks 1–2, (8) and start of its proof; §2.2 Definition 1, Theorem 1 and start of proof; §3.1 Definition 2, Theorem 2 and proof (p. 11, page image); §3.2 Definition 3, Theorem 3 (p. 11, page image); §3.3 Definition 4, Theorem 4 (p. 13, page image), (13); §4.1 Definitions 5–6, (16)–(17), Theorem 5, Remark 3 (p. 17, page image); §4.2 first paragraph and the first lines of Lemmas 3–4; reference list (titles of [9], [11], [14]–[25]) | proofs of Theorems 3–5 in full; Lemmas 3–4 in full; appendices |
| CGMMS13 | arXiv:1210.1136v4, https://arxiv.org/pdf/1210.1136 | introduction (pp. 4–5, contributions); §3 opening (Algorithm 1 description); §4.2 Theorem 1 and (13) (p. 14, page image); §5 empirical KL-UCB, Algorithm 3, Theorem 2 (pp. 14–16); §6.2 Proposition 1 and "Conjectured regret guarantees" paragraph; §8 Conclusion | supplementary proofs; §6.1; §7 |
| KKM12 | arXiv:1205.4217v2, https://arxiv.org/pdf/1205.4217 | §1 (pp. 1–2) including Theorem 1; Theorem 2 statement (§3.1) | proofs |
| AG13 | arXiv:1209.3353v1, https://arxiv.org/pdf/1209.3353 | §1.2–1.3: Algorithm 1, Theorems 1–2, comparison with earlier work | proofs, appendices |
| KKM13 | arXiv:1307.3400v1, https://arxiv.org/pdf/1307.3400 | introduction (Theorem 1); §3 Theorem 2 statement | proofs, Theorem 4 beyond its statement line |
| HT14 | arXiv:1311.1894v1, https://arxiv.org/pdf/1311.1894 | abstract; §2 model, (2)–(3); §2.2 Algorithm 1, prior, (4)–(5); §3 Theorems 1–2, Remarks 1–2 (p. 3, page image); final section (open problem) | proofs (Lemmas 5–10) |
| CHK18 | arXiv:1504.05823v2 (3 Jun 2015, technical report; title longer than the JMLR version), https://arxiv.org/pdf/1504.05823 | abstract; §1 pp. 1–5 (notation, UFC policies, ACF policy, $M_{BK}$ (8), policy BK (9), Conjecture 1, policy CHK (11), Remark 1, related work); Theorems 4–5 statements and proof of Theorem 4; first line of Proposition 6 | proofs of Theorems 3, 5, Proposition 6; the JMLR 2018 version (numbering to be checked) |
| MG17 | arXiv:1702.07211v2, https://arxiv.org/pdf/1702.07211 | abstract; §2 (lower bounds recap); §3 algorithm (2)–(3), Theorems 1–2 and the paragraph after them; end of §5; §6 | §4–§5 proofs |
| GHMS22 | arXiv:1805.05071v3 (1 Jul 2022), https://arxiv.org/pdf/1805.05071 | abstract; §1 and §1.1 literature review (pp. 1–4); §2.1 indices (5)–(8); §2.2 Theorems 1–2 and comments; §2.3 (9)–(14), Theorems 3–4 | §3 onwards, appendices |
| HT15 | JMLR 16 (2015) 3721–3756, https://jmlr.org/papers/volume16/honda15a/honda15a.pdf | abstract; §1 (pp. 3721–3723); §1.3; §2 (notation, Algorithm 1, (2), Proposition 1, (3)); §3 Theorems 2, 3, Corollary 4 with proof, Theorem 5 (p. 3727, page image) and the following paragraph; start of §4.1; §9 (pp. 3742–3743) | §§5–8, appendices (Lemma 18) |
| L18 | JMLR 19 (2018) 1–32, paper 17-513, https://jmlr2020.csail.mit.edu/papers/volume19/17-513/17-513.pdf | abstract; §1 (pp. 1–3); §2 strategy, Table 1, Theorem 1 (pp. 3–5, page images of pp. 3, 4, 5); §5 Theorem 10 (p. 13, page image), Theorem 11 and its proof; §6 paragraph "Alternative noise models and other extensions" | §3–§4 proofs, appendices |
| SA11 | arXiv:1107.4506v2 (25 Jul 2011), "Robustness of anytime bandit policies", https://arxiv.org/pdf/1107.4506 | abstract; §1 (pp. 1–3); §2 Definitions 1–3, Proposition 2.1; §3 Theorem 3.3 (p. 8, page image), Corollary 3.4, Theorems 3.5–3.6 (p. 9, page image); §5 opening and Theorem 5.1 (p. 14, page image), Corollary 5.2 | §4 in full; §7 proofs; the ALT 2011 version "Deviations of stochastic bandit regret" (not read: Springer) |
| FG24 | arXiv:2109.13595v8 (12 Nov 2024), https://arxiv.org/pdf/2109.13595v8 | abstract; §1 (pp. 1–2); §2 Definitions 1–2, (4)–(5); §3.1 Definition 3, Theorem 1, Lemma 1 statement, Corollary 1; Theorem 4 statement and the start of Remark 3 | §3.2–§7, in particular §4.5 (moments) and §6 (robust UCB); proofs |
| LS17 | arXiv:1610.04491v1 (14 Oct 2016), https://arxiv.org/pdf/1610.04491 | abstract; §1; §2 notation; §3 Theorem 1 (p. 2, page image), Corollary 2, (2), Examples 3–4; §4 Lemmas 5–6 statements; Theorem 10 statement; §8 (p. 8, page image); §9 | §5–§7 proofs, Algorithm 1 in detail, appendices; the AISTATS 2017 version |
| CMP17 | arXiv:1711.00400v1, https://arxiv.org/pdf/1711.00400 | abstract; §3 examples (Lipschitz, unimodal, combinatorial); §4 Theorem 1 and its examples; §5 OSSB, Algorithm 1, Assumptions 1–6, Theorem 2 (p. 7, page image); §6 Lemma 1 and the finite-time bound (p. 7); Appendix A opening | proofs beyond Appendix A opening; §7 |
| DSK20 | arXiv:2007.00969v1, https://arxiv.org/pdf/2007.00969 | abstract; §1 (contributions, related work on OSSB and forced exploration); Assumption 1; §2.1 Theorem 1; §2.2 Lemma 1, Theorem 2; Assumption 2; §2.5 Theorem 3; §3 list of compared algorithms; §4 Open Questions | appendices (Assumption 7), proofs |
| CP14 | arXiv:1405.5096v1, https://arxiv.org/pdf/1405.5096 | §3 model and unimodal structure (p. 3, page image); §4.1 Theorem 4.1; §4.2 OSUB (p. 4, page image); §4.3 Theorem 4.2, Lemma 4.3, Corollary 4.4 (p. 5, page image) | §5 non-stationary; proofs |
| JZ20 | arXiv:2006.08754v2, https://arxiv.org/pdf/2006.08754 | abstract; §1 (pp. 1–2, footnotes); §2 opening; §4 Theorem 1 and discussion, "Cheating code" example; §5 Theorem 2 (informal); §6; appendix paragraphs "worst-case regret" and "Future work" | CROP's definition (§3) in detail; formal Theorem 2 and all proofs |
| KLVS21 | arXiv:2011.05944v4 (COLT 2021 version), https://arxiv.org/pdf/2011.05944 | abstract; §1 related work; Theorem 1 (citing GL97, CMP17); (3); Theorem 2 statement; Theorem 5 statement and the remarks after it | Algorithm 1 in detail, proofs |
| AJK21 | arXiv:2102.03734v1 (dated 9 Feb 2021), https://arxiv.org/pdf/2102.03734 | abstract; §1; §2 (3)–(4); §3 Algorithm 1, (5); §3.1 Theorem 1, Corollary 2, Theorem 3; §3.2 Proposition 4 | §3.3–§5, appendices (Lemma 10) |
| RH20 | PMLR 117:1–50 (ALT 2020), https://proceedings.mlr.press/v117/riou20a/riou20a.pdf | abstract; §3 discussion of Non-parametric TS, Remarks 2–3, Algorithm 3; §4 Theorems 4–5, start of Lemma 6 | §2, Algorithms 1–2 in detail, proofs |
| KCG16 | JMLR 17 (2016) 1–42, https://jmlr.org/papers/volume17/kaufman16a/kaufman16a.pdf | §1 contributions paragraph; §2 opening, Lemma 1, start of Remark 2 | everything else |
| BCL13 | arXiv:1209.1727v1 (8 Sep 2012), https://arxiv.org/pdf/1209.1727 | abstract; Theorem 1 (truncated-mean Robust-UCB) and comments; Theorem 2 statement and start of proof | the published IEEE version; Assumption 1 and Proposition 1 in detail; other estimators |
| L17 | arXiv:1703.08937v1 (27 Mar 2017), https://arxiv.org/pdf/1703.08937 | abstract; §1 Table 1, Assumption 1, Theorem 2 (p. 2, page image); Theorem 7, Remark 8; §4 Summary | §2 algorithm, §3 Theorem 9, proofs |
| JXSXG21 | arXiv:2003.01803v3 (1 Oct 2020), https://arxiv.org/pdf/2003.01803 | abstract; §3.2 (2)–(4); §4.1 Theorems 1–3 and comments; §4.2 Algorithm 2, (8), Theorem 4, Remark 2; §7 | proofs; the venue (to be checked) |
| GKL16 | arXiv:1605.08988v2 (NIPS 2016), https://arxiv.org/pdf/1605.08988 | abstract; §1; §2 (p. 3, page image: definitions, table); Theorems 3–4 statements | other theorems, proofs |
| SAE13 | JMLR 14 (2013) 187–207, https://jmlr.org/papers/volume14/salomon13a/salomon13a.pdf | abstract; Definition 5 and the paragraph before it; Theorem 6; Theorem 8 and the following paragraph | §3, definition of UCB($\rho$), Theorem 4, proofs |
| AMS09 | author's version, https://sites.ualberta.ca/~szepesva/papers/ucbtuned-journal.pdf | abstract; §1 overview (pp. ~4–5, including the conjecture on the horizon); Theorem 10 and footnote 5; Theorem 13 statement (Appendix A.1) | everything else; the journal version's page numbers |
| LS | free online edition, https://tor-lattimore.com/downloads/book/book.pdf (states that its page numbers differ from the print edition) | §9.2; §9.3 Notes 1–3; §15.1 Lemma 15.1 statement; §16.1 Definition 16.1, Theorem 16.2 and the start of its proof; §16.2 Lemma 16.3, Theorem 16.4 and the start of its proof; §16.3 Note 3; §16.4; Exercise 16.4; remark after Exercise 19.5; §25.1 Theorem 25.1, Corollary 25.2, Theorem 25.3; §25.2; §25.3 Notes 1–2; §25.4; §36.5 Notes 1–2; §36.6 | everything else |

## Works cited without being read (marked "(to be checked)" in KNOWN.md)

| Key | Why not read | How it is cited |
|---|---|---|
| LR85 | ScienceDirect returned HTTP 403 | only as "original of K1", through [LS, Theorem 16.2] and [GMS19] |
| BK96 | not attempted after LR85's refusal (same publisher) | idem; its condition (A3) only through [CHK18] |
| GL97 | SIAM, not attempted | only as the result [CMP17, Theorem 1] relies on |
| HT10 | not fetched | only through [HT15, Proposition 1] |

Works seen only in other papers' reference lists or in web-search snippets (not cited as sources
of results): Degenne–Perchet 2016, Garivier 2013, Magureanu–Combes–Proutière 2014, Cowan–Katehakis
2015, Lee–Chiang–Sugiyama (AAAI 2024, a follow-up of HT14 found by a search: to be read before
working on D10c).

## Where the metadata of `literature/bibliography.json` comes from (new entries)

- Read from the PDF header: HT15 (JMLR 16, 3721–3756), L18 (JMLR 19, 1–32), KCG16 (JMLR 17, 1–42),
  SAE13 (JMLR 14, 187–207), RH20 (PMLR 117, 1–50, ALT 2020, editors), KLVS21 (PMLR 134, COLT 2021,
  "vol 134:1–42" in the arXiv header), GKL16 (NIPS 2016, footer of arXiv v2), FG24 (Operations
  Research, "to appear", arXiv v8 comment).
- From reference lists of read papers: BCL13 (IEEE Trans. Inf. Theory 59(11):7711–7717, in [AJK21],
  [LS], [L17]); L17 (NeurIPS 2017, pp. 1584–1593, in [AJK21]); KKM13 (NIPS 2013, pp. 1448–1456, in
  [LS]).
- From web-search results (unchecked): GHMS22 (JMLR 23(179):1–66, 2022); CHK18 (JMLR 18(154):1–28,
  2018; DBLP gives 2017); HT14 (PMLR 33:375–383, AISTATS 2014); AJK21 (PMLR 134:26–62); SA11 (ALT
  2011, LNCS 6925, 159–173, DOI 10.1007/978-3-642-24412-4_15); AMS09 (TCS 410(19):1876–1902; DOI from
  LMLExplore's bibliography); FG24 (DOI 10.1287/opre.2023.0283, from a search snippet).
- Keys reused from LMLExplore's `scripts/literature/bibliography.json` (pinned revision `b4e0ab9`):
  KCG16, KKM13, AMS09 (same works); their LMLExplore metadata is copied, with the fields read here
  added.
- Not verified at all: the venue of JXSXG21 (entered as an arXiv preprint).

## Existing keys of `literature/bibliography.json` used, with the parts read

GMS19, CGMMS13, KKM12, AG13, HT15, MG17, LS17, CMP17, DSK20, CP14, SAE13, LS (parts in the table
above); LR85, BK96, GL97, HT10 (not read). Observed identifiers for existing entries that lack them:
CGMMS13 arXiv:1210.1136; KKM12 arXiv:1205.4217; LS17 arXiv:1610.04491; CMP17 arXiv:1711.00400;
DSK20 arXiv:2007.00969; CP14 arXiv:1405.5096; MG17 arXiv:1702.07211 (the arXiv header of MG17 also
prints "Journal of Machine Learning Research 1–15, 2017 / Algorithmic Learning Theory 2017", the PMLR
template of ALT).
