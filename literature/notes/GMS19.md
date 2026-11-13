# GMS19: Explore first, exploit next

| | |
|---|---|
| Work | A. Garivier, P. Ménard, G. Stoltz, *Explore First, Exploit Next: The True Shape of Regret in Bandit Problems*, Mathematics of Operations Research 44(2), 2019 |
| Identifiers | DOI 10.1287/moor.2017.0928, arXiv 1602.07182 |
| Read | abstract and introduction (arXiv v3); inequalities (6) and (11). Not read: Sections 3–4 in full, conclusion |
| By, date | an agent for the owner (inequalities (6), (11)), 2026-10-31; Claude (abstract, introduction), 2026-11-13 |

## Results

- **(6), fundamental inequality.** For every random variable $Z \in [0,1]$ measurable with respect to the
  history up to $T$: $\sum_a \mathbb E_\nu[N_a(T)]\,\mathrm{KL}(\nu_a, \nu'_a) \ge \mathrm{kl}(\mathbb E_\nu Z, \mathbb E_{\nu'} Z)$,
  with kl the Bernoulli divergence. Proof: chain rule (equality) and data processing (inequality).
- **(11).** $\mathrm{kl}(p, q) \ge p \log(1/q) - \log 2$.
- Section 3 (not read in full): lower bounds for small horizons, almost linear regret, under mild
  symmetry assumptions on the strategies.
- Section 4 (not read in full): a non-asymptotic lower bound for large horizons (Theorem 4.3) for
  uniformly super-fast convergent strategies, with a second-order term of order $-\log\log T$
  (Remark 4.4). The exact constants must be read in the paper before any use.

## Techniques

Change of measure written as a single inequality (data processing applied to the law of the
history), valid for any pair of instances on the same history; it also gives the distribution-free
$\sqrt{KT}$ lower bound and the Lai–Robbins bound as corollaries.

## Where Incognita uses it

Programmes RegretShape (known results 1–3) and BatchedBandits (known result 1).
