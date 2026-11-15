Scripts for rapport.md section 6 (Python 3, numpy, scipy; no cvxpy).
d8.py    : K_inf on a finite support (dual), primal convex program J(x,c) for TV / W1 / KS / mean, D_c by bisection.
dual.py  : Lagrange dual of Prop. D (weak duality -> certified lower bounds on J).
run1.py  : Example 1 (Bernoulli) and check of the mean closed form.
run2.py  : Example 4 (nu = nu' = (1/4,1/2,1/4)).
run5.py  : certified brackets (primal + dual); helper inst().
run6.py  : Examples 2 and 3 (certified).
run7.py  : Example 2 at c = 10, 20.
Each run takes from a few seconds to a few minutes on a laptop.
