"""IMED on two arms: arm 1 ~ F_q = (1-pi) delta_1 + pi Law(-V), V ~ Pareto(q) on [1, inf);
arm 2 = delta_0 (deterministic). Records N_2(n) at checkpoints.
Light simulation (few runs). Usage: python imed_sim.py q runs nmax seed
"""
import sys, math
import numpy as np

def dinf_frozen(n1, negs, T1):
    """D_inf(Fhat_1, 0) for Fhat_1 with n1 atoms at 1 and negative values -v (v in negs, v>0),
    T1 = n1 + len(negs) (no other values). Dual: max_{0<=nu<=1} (1/T1)[n1 log(1-nu) + sum log(1+nu v)]."""
    vs = np.asarray(negs)
    def deriv(nu):
        return -n1 / (1.0 - nu) + np.sum(vs / (1.0 + nu * vs))
    # deriv decreasing in nu; deriv(0) = -n1 + sum vs > 0 iff mean < 0 (here mean<0 assumed)
    if n1 == 0:
        nu = 1.0
    else:
        lo, hi = 0.0, 1.0 - 1e-15
        if deriv(hi) > 0:
            nu = hi
        else:
            for _ in range(60):
                mid = 0.5 * (lo + hi)
                if deriv(mid) > 0:
                    lo = mid
                else:
                    hi = mid
            nu = 0.5 * (lo + hi)
    val = (n1 * math.log(1.0 - nu) if n1 > 0 else 0.0) + float(np.sum(np.log1p(nu * vs)))
    return max(val, 0.0) / T1

def run(q, pi, nmax, checkpoints, rng):
    # pre-draw arm-1 samples
    is_neg = rng.random(nmax + 5) < pi
    V = (1.0 - rng.random(nmax + 5)) ** (-1.0 / q)  # Pareto(q) on [1, inf)
    X = np.where(is_neg, -V, 1.0)
    out = {}
    # initialization: round 1 arm 1, round 2 arm 2
    T1, T2 = 1, 1
    s1 = X[0]
    n1 = 1 if X[0] == 1.0 else 0
    negs = [] if X[0] == 1.0 else [V[0]]
    l = 2  # rounds done
    cps = sorted(checkpoints)
    ci = 0
    def record(lround):
        nonlocal ci
        while ci < len(cps) and cps[ci] <= lround:
            out[cps[ci]] = None
            ci += 1
    while l < nmax:
        mu1 = s1 / T1
        if mu1 >= 0.0:
            # arm 1 is (weakly) the leader: I1 = log T1; I2 = T2 d(mu1) + log T2
            if mu1 >= 1.0:
                pull2 = False
            else:
                I2 = T2 * (-math.log(1.0 - mu1)) + math.log(T2)
                pull2 = I2 < math.log(T1)
            if pull2:
                T2 += 1; l += 1
            else:
                x = X[T1]
                s1 += x
                if x == 1.0: n1 += 1
                else: negs.append(-x)
                T1 += 1; l += 1
        else:
            # arm 2 leader (mean 0 > mu1): I2 = log T2; I1 = T1 Dinf(F1hat, 0) + log T1, frozen
            I1 = T1 * dinf_frozen(n1, negs, T1) + math.log(T1)
            target = math.exp(min(I1, 700.0))
            k = int(math.ceil(target)) - T2  # pulls of arm 2 while T2 < e^{I1}
            if k > 0:
                k = min(k, nmax - l)
                # record checkpoints crossed with N2 values
                while ci < len(cps) and cps[ci] <= l + k:
                    out[cps[ci]] = T2 + (cps[ci] - l)
                    ci += 1
                T2 += k; l += k
                if l >= nmax:
                    break
            # now pull arm 1 (tie or arm 1 index smaller)
            x = X[T1]
            s1 += x
            if x == 1.0: n1 += 1
            else: negs.append(-x)
            T1 += 1; l += 1
        while ci < len(cps) and cps[ci] <= l:
            out[cps[ci]] = T2
            ci += 1
    while ci < len(cps):
        out[cps[ci]] = T2
        ci += 1
    return out

if __name__ == "__main__":
    q = float(sys.argv[1]); runs = int(sys.argv[2]); nmax = int(sys.argv[3]); seed = int(sys.argv[4])
    pi = 0.1
    mustar = 1 - pi - pi * q / (q - 1)
    d = -math.log(1 - mustar)
    cps = [10**3, 10**4, 10**5, 10**6]
    cps = [c for c in cps if c <= nmax]
    rng = np.random.default_rng(seed)
    res = {c: [] for c in cps}
    for r in range(runs):
        o = run(q, pi, nmax, cps, rng)
        for c in cps:
            res[c].append(o[c])
    print(f"q={q} pi={pi} mu*={mustar:.4f} Dinf(delta0,mu*)={d:.4f} runs={runs}")
    for c in cps:
        a = np.array(res[c], dtype=float)
        print(f"n={c:>8d}  log n/D={math.log(c)/d:8.2f}  mean N2={a.mean():10.2f}  se={a.std(ddof=1)/math.sqrt(len(a)):9.2f}"
              f"  median={np.median(a):8.1f}  q90={np.quantile(a,0.9):9.1f}  max={a.max():9.0f}  frac(N2>n/10)={np.mean(a>c/10):.3f}")
