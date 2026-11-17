# YTC25: Best arm identification with possibly biased offline data

| | |
|---|---|
| Work | L. Yang, V. Y. F. Tan, W. C. Cheung, *Best Arm Identification with Possibly Biased Offline Data*, arXiv preprint, v1 of 29 May 2025 (16 pp.); arXiv comment "Accepted to UAI 2025" (proceedings version not checked) |
| Identifiers | arXiv 2505.23165 (v1) |
| Read | arXiv:2505.23165v1 PDF, page images pp. 1–6: abstract; §1, §1.1; §2 formulation; §3, Proposition 3.1 and the discussion; Algorithm 1 LUCB-H, (4.1)–(4.4), Theorem 4.1 with (4.5); §5, Assumption 5.1, Theorem 5.1, Remark 5.1. Not read: §6 onward, Appendices (proof of Theorem 5.1 is in App. D) |
| By, date | Claude Opus 5.5 (revise, P008), 2026-11-17 |

## Setting (§2)

Fixed-confidence BAI with $k$ arms; warm-start phase with $T_S(i)$ i.i.d. offline samples from
$P^{\mathrm{off}}_i$, then online samples from $P^{\mathrm{on}}_i$; "the DM has access only to $A$ and $\{T_S(i)\}_{i\in A}$ before
the online phase"; "both the online and offline reward distributions, $P^{\mathrm{on}}$ and $P^{\mathrm{off}}$, are normal
distributions with known variance"; $\mu^{\mathrm{on}}(1)>\mu^{\mathrm{on}}(2)\ge\dots$, $\Delta_i=\mu^{\mathrm{on}}(1)-\mu^{\mathrm{on}}(i)$; $\delta$-PAC
policies. Valid bias bound $V(i)\geq|\mu^{\mathrm{off}}(i)-\mu^{\mathrm{on}}(i)|$ (§3), discrepancy
$\eta(i)=V(i)+\mu^{\mathrm{off}}(i)-\mu^{\mathrm{on}}(i)\in[0,2V(i)]$ (§4).

## Results

- **Proposition 3.1** (impossibility without $V$, two arms; analogue of CL24, Theorem 1): read, not copied.
- **Theorem 4.1** (LUCB-H upper bound): $\mathbb E[\tau_\delta]=O\Bigl(\sum_{\Delta_i>0}\Bigl(\frac{1}{\Delta_i^2}\log(\frac1\delta)-\mathrm{Sav}_{\mathrm u}(i)\Bigr)\Bigr)$ (4.5),
  with $\mathrm{Sav}_{\mathrm u}(i)=T_S(i)\cdot\max\Bigl\{1-\frac{4\eta(i)}{\Delta_i},0\Bigr\}$ (as printed: no square).
- **Assumption 5.1.** "For all $v,v'\in\mathcal P^2$ such that $v\neq v'$, for all $a>0$, there exists $v''\in\mathcal P$ such
  that $\mathrm{KL}(v,v')<\mathrm{KL}(v,v'')<\mathrm{KL}(v,v')+a$ and $\mathbb E_{X\sim v''}[X]>\mathbb E_{X\sim v'}[X]$. Furthermore, there exists
  $v'''\in\mathcal P$ such that $\mathrm{KL}(v,v')<\mathrm{KL}(v,v''')<\mathrm{KL}(v,v')+a$ and $\mathbb E_{X\sim v'''}[X]<\mathbb E_{X\sim v'}[X]$."
- **Theorem 5.1.** "Suppose that $\mathcal P$ satisfies Assumption 5.1, any algorithm that is $\delta$-PAC on $\mathcal M$
  satisfies, for $\delta\leq0.15$, the expected stopping time
  $$\mathbb E[\tau_\delta]=\Omega\Biggl(\sum_{\Delta_i>0}\Biggl(\frac{1}{\mathrm{KL}(\mu^{\mathrm{on}}(i),\mu^{\mathrm{on}}(1))}\log\Bigl(\frac1\delta\Bigr)-\mathrm{Sav}_{\mathrm l}(i)\Biggr)\Biggr),$$
  where $\mathrm{Sav}_{\mathrm l}(i)$, the "Saving" term in the lower bound, is
  $$\mathrm{Sav}_{\mathrm l}(i)=T_S(i)\max\Biggl\{\frac{\mu^{\mathrm{off}}(1)-\mu^{\mathrm{off}}(i)}{\Delta_i},0\Biggr\}^2."$$
  As printed: $\mathcal M$ is not defined in the pages read; $\mathrm{Sav}_{\mathrm l}$ involves the offline means of
  arms 1 and $i$, not $V$ or $\eta$; the proof (App. D) was not read, so the alternative instance is not known.
- **Remark 5.1** compares $\mathrm{Sav}_{\mathrm l}$ and $\mathrm{Sav}_{\mathrm u}$ in two special cases (equal $V$'s; $V(1)=\eta(1)$) and
  leaves the general sign of the gap open.

## Techniques

LUCB with the minimum of an online and a pooled confidence bound (the CL24 construction with the bias
correction $\frac{T_S}{N+T_S}V$), lower bound by change of measure (credited to Lai–Robbins 1985 and
Kaufmann et al. 2016 for Assumption 5.1).

## Where Incognita uses it

`papers/P008-transfer-lower-bound/` (revision of 2026-11-17, related work).
