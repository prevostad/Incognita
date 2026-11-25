# Errata of P007-stochastic-setting

## E1 (2026-11-20, prove, claude-opus-5-5)
- Node: thm:main
- Problem: a gap in Step 3 of the proof (`sec:proof-gl`): the claim $\mathcal K_b<\infty$, "the set defining $\mathcal K_b$ contains $\nu'_b$", is false when $\mathrm{KL}(\nu_b,\nu'_b)=\infty$ and every law of $\mathcal D_b$ with mean above $m^\star$ is at infinite divergence from $\nu_b$. Then $w_b=1/\mathcal K_b=0$ and $w_b\,\mathrm{KL}(\nu_b,\nu'_b)=0\cdot\infty=0<1$. Example: $\nu=(\delta_1,\delta_0)$, $\mathcal D_1=\{\delta_1\}$, $\mathcal D_2=\{\delta_0,\delta_2\}$: $\mathcal K_2=\infty$, the weights $w_2=1/\mathcal K_2=0$ violate the constraint of $(\delta_1,\delta_2)$, and the value $S=0$ is an infimum that is not attained. The statement of `thm:main` is still true: the weights $1/\mathcal K_a+\delta$, $\delta\to0$, repair the step.
- Evidence: the remark after `flem:feasible-margin` in `formalisation.tex`; the repaired step is `Incognita.StochasticBandits.feasible_update_inv_dInf_add` and `Incognita.StochasticBandits.gravesLai_productClass_le`, which prove `Incognita.P007.gravesLai_productClass` with the frozen type.
