Scripts for rapport.md section 6 (Python 3, numpy, scipy; no cvxpy).
d8.py    : K_inf on a finite support (dual), primal convex program J(x,c) for TV / W1 / KS / mean, D_c by bisection.
dual.py  : Lagrange dual of Prop. D (weak duality -> certified lower bounds on J).
run1.py  : Example 1 (Bernoulli) and check of the mean closed form.
run2.py  : Example 4 (nu = nu' = (1/4,1/2,1/4)).
run5.py  : certified brackets (primal + dual); helper inst().
run6.py  : Examples 2 and 3 (certified).
run7.py  : Example 2 at c = 10, 20.
Each run takes from a few seconds to a few minutes on a laptop.
sim.py      : Section 9.3 of version 2 (revision round 1): KL-UCB, KL-UCB-Transfer and KL-UCB-TV-Transfer
             on the two-armed instance; the index computations (exact TV projection, bisection on the mean).
test_sim.py : checks of the indices of sim.py against d8.py (about two minutes).
run_sim.py  : the experiment (T = 10^4, c = 5 and 25, 40 runs each, 4 processes, about an hour); writes sim.txt.
sim.txt     : its output (summary, then one line per run: learner, c, seed, N_2(T), time).
fig_dtv.py : Figure 1 of version 2 (no-drift example): D_TV(c) by primal bisection at 26 values of c, checked against the certified values; writes fig_dtv.txt (TikZ coordinates).
