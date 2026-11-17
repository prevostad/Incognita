"""KLinf-UCB on two arms: arm 1 ~ P_{q,pi} = (1-pi) delta_1 + pi Law(-V), V ~ Pareto(q) on [1, inf);
arm 2 = delta_0 (deterministic). Records N_2(n) at checkpoints, as imed_sim.py does.

Index of Panda-Agrawal (arXiv:2604.14876, Section 3): U_a = sup{x : Kinf(hat nu_a, x) <= f_a(t)/N_a},
with f_a(t) = log t + 2 log log t + g(N_a), g(n) = log(1+n) + 1 (the value of C_2 is a choice; any
C_2 > 0 is allowed by Lemma B.6(a) of P004). Kinf is the divergence of P004 (semi-bounded laws).
Each arm is pulled once (arm 1 first); then, at round t (counted from 1), arm 1 is pulled iff
U_1 >= U_2 (ties to arm 1).

Arm 2 is delta_0, so Kinf(delta_0, x) = log(1/(1-x)) for x in [0,1) and U_2 = 1 - exp(-f_2/N_2).
Since x -> Kinf(hat nu_1, x) is nondecreasing, U_1 >= U_2 iff N_1 Kinf(hat nu_1, U_2) <= f_1
(up to the boundary case of equality, of probability 0 here), so one evaluation of Kinf per round
suffices: no inversion is needed in this two-arm instance.

Usage: python klinf_ucb_sim.py q runs nmax seed
"""
import sys, math
import numpy as np


def kinf_emp(n1, vs, x):
    """Kinf(hat nu, x) * n for hat nu with n1 atoms at 1 and negative values -v (v in vs, v >= 1),
    and 0 <= x < 1. Dual (Lemma B.3 / [HT15, Thm 2]) with nu = lambda (1-x) in [0,1]:
    max_nu n1 log(1-nu) + sum log(1 + nu (v+x)/(1-x)). Returns the total (not divided by n)."""
    if len(vs) == 0:
        return 0.0  # every sample equals 1 > x
    w = (vs + x) / (1.0 - x)
    def deriv(nu):
        return -n1 / (1.0 - nu) + float(np.sum(w / (1.0 + nu * w)))
    if deriv(0.0) <= 0.0:
        return 0.0  # empirical mean >= x
    if n1 == 0:
        nu = 1.0
    else:
        lo, hi = 0.0, 1.0 - 1e-15
        if deriv(hi) > 0:
            nu = hi
        else:
            for _ in range(55):
                mid = 0.5 * (lo + hi)
                if deriv(mid) > 0:
                    lo = mid
                else:
                    hi = mid
            nu = 0.5 * (lo + hi)
    val = (n1 * math.log(1.0 - nu) if n1 > 0 else 0.0) + float(np.sum(np.log1p(nu * w)))
    return max(val, 0.0)


def f(t, n):
    return math.log(t) + 2.0 * math.log(max(math.log(t), 1.0)) + math.log(1.0 + n) + 1.0


def run(q, pi, nmax, checkpoints, rng):
    is_neg = rng.random(nmax + 5) < pi
    V = (1.0 - rng.random(nmax + 5)) ** (-1.0 / q)
    out = {}
    negs = np.empty(nmax + 5)
    k = 0      # number of negative samples of arm 1
    n1 = 0     # number of samples of arm 1 equal to 1
    T1, T2 = 0, 0
    cps = sorted(checkpoints)
    ci = 0
    for t in range(1, nmax + 1):   # t = number of the round, from 1
        if t == 1:
            pull1 = True
        elif t == 2:
            pull1 = False
        else:
            U2 = 1.0 - math.exp(-f(t, T2) / T2)
            pull1 = kinf_emp(n1, negs[:k], U2) <= f(t, T1)
        if pull1:
            if is_neg[T1]:
                negs[k] = V[T1]; k += 1
            else:
                n1 += 1
            T1 += 1
        else:
            T2 += 1
        while ci < len(cps) and cps[ci] <= t:
            out[cps[ci]] = T2
            ci += 1
    return out


if __name__ == "__main__":
    q = float(sys.argv[1]); runs = int(sys.argv[2]); nmax = int(sys.argv[3]); seed = int(sys.argv[4])
    pi = 0.1
    mustar = 1 - pi - pi * q / (q - 1)
    d = -math.log(1 - mustar)
    cps = [c for c in [10**3, 10**4, 10**5] if c <= nmax]
    rng = np.random.default_rng(seed)
    res = {c: [] for c in cps}
    for r in range(runs):
        o = run(q, pi, nmax, cps, rng)
        for c in cps:
            res[c].append(o[c])
    print(f"KLinf-UCB q={q} pi={pi} mu*={mustar:.4f} Dinf(delta0,mu*)={d:.4f} runs={runs}")
    for c in cps:
        a = np.array(res[c], dtype=float)
        print(f"n={c:>8d}  log n/D={math.log(c)/d:8.2f}  mean N2={a.mean():10.2f}  se={a.std(ddof=1)/math.sqrt(len(a)):9.2f}"
              f"  median={np.median(a):8.1f}  q90={np.quantile(a,0.9):9.1f}  max={a.max():9.0f}  frac(N2>n/10)={np.mean(a>c/10):.3f}")
