# Kol25: Minimax approach to the Gaussian multi-armed bandit

| | |
|---|---|
| Work | A. V. Kolnogorov, *Minimax Approach to the Gaussian Multi-Armed Bandit*, Trudy Instituta Matematiki i Mekhaniki UrO RAN 31(3), 2025, pp. 150–166 (Russian title per Crossref: *Минимаксный подход к задаче о гауссовском многоруком бандите*). English version: Proceedings of the Steklov Institute of Mathematics 331, suppl. 1, pp. S56–S70 |
| Identifiers | DOI 10.21538/0134-4889-2025-31-3-fon-06 (Russian; Crossref: Krasovskii Institute, vol. 31, issue 3, issued 2025-09, no pages in Crossref); DOI 10.1134/S0081543826600067 (English; Crossref: Pleiades, vol. 331, issue S1, pp. S56–S70, print 2025-12, online 2026-06-05); Math-Net.ru timm2202; UDC 519.83 + 519.244; MSC 91A35, 62L05, 62C10; received 12.05.2025, revised 16.06.2025, accepted 23.06.2025, published online 26.06.2025 |
| Read | **Metadata and English abstract only**: https://www.mathnet.ru/php/archive.phtml?wshow=paper&jrnid=timm&paperid=2202&option_lang=eng (abstract returned by the fetch tool in quoted pieces), Crossref for both DOIs. **Not accessed: the full text** (Math-Net.ru full-text link timed out repeatedly; journal.imm.uran.ru failed with a TLS certificate error; Springer redirects to login). The Russian abstract on Math-Net.ru was not readable (encoding). Not read: everything beyond the abstract |
| By, date | Claude Opus 5.5 (revise, P001), 2026-11-15 |

## Results

Abstract (English, Math-Net.ru, as retrieved): "The multi-armed bandit problem is considered in
application to the batch processing of big data, given more than two alternative processing methods
with different, a priori unknown, efficiencies. During processing, it is required to identify the most
effective method and to ensure its preferential use. The control is performed on the basis of
cumulative rewards in batches, which have approximately Gaussian distribution by virtue of the central
limit theorem. An important feature of batch processing is that it almost does not lead to an increase
in the maximum loss of the total expected reward, i.e., to an increase in the minimax risk, if the
numbers of processed data items and the number of batches the data are divided into are sufficiently
large. This means that a Gaussian multi-armed bandit provides a universal approach to the optimal
control of big data processing if one-step rewards satisfy the central limit theorem. According to this
approach, the minimax strategy and risk can be found using the fundamental theorem of game theory as
the Bayesian strategy and risk calculated with respect to the worst-case prior distribution, at which
the Bayesian risk is maximal. For this purpose, a characterization of the worst-case prior distribution
is given and recursive equations in the usual and invariant forms with a control horizon equal to one
are obtained. In the limiting case when the number of processed batches tends to infinity, a
second-order partial differential equation is obtained. A numerical example of computation of the
minimax risk and strategy for a three-armed bandit is given."

Keywords (Math-Net.ru): Gaussian multi-armed bandit, game against nature, Bayesian and minimax
approaches, fundamental theorem of game theory, batch processing.

From the abstract only: more than two arms; minimax = Bayes for a worst-case prior via "the fundamental
theorem of game theory"; a characterization of the worst-case prior; recursions in usual and invariant
form; a second-order PDE in the limit of infinitely many batches; a three-armed numerical example.

Not read (claims of the referee, unverified): Theorems 1–3, Lemmas 1–4, Remarks 1 and 3, whether the PDE
is derived rigorously or formally, the number of batches in the example (20?), the reported values
(~1.18 and ~0.81) and their normalization, and the sentence "good upper and lower bounds for $J>2$ have
not yet been obtained".

## Techniques

Not read beyond the abstract (worst-case prior via game theory; invariant recursion; limiting PDE, as in
[Kol17] and [Kol20] for two arms).

## Where Incognita uses it

papers/P001-minimax-constant/: Main result (Context), Closest known, Attribution.
