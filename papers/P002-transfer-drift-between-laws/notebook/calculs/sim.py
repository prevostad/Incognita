"""Simulation of the section "Numerical experiments" of P002 version 2 (W16).

Instance: the two-armed instance of the paper ("A complete instance with two arms"):
S = {0, 1/2, 1}, L_1 = L_2 = 0.11, no drift, nu_1 = nu'_1 = (0, 0.8, 0.2) (mu* = 0.6),
nu_2 = nu'_2 = (0.02, 0.96, 0.02), source sizes N'_k = floor(c log T) for both arms.

Three learners, with the same exploration rate delta_t = log(t v 3) + log log(t v 3)
(eq:rate), the same rule (pull arms 1..K first, then pull an arm maximising the indices
computed at the end of round t, ties broken at random):
  klucb : U = max{m(q) : N_k KL(hat nu_k, q) <= delta_t}                     (no source)
  kltr  : U = max{m(q) : m(q) - m(q') <= L_k,
                         N_k KL(hat nu_k, q) + N'_k KL(hat nu'_k, q') <= delta_t}
          (KL-UCB-Transfer with K_inf computed on S, as in Section 5.2 of the paper)
  tv    : U = max{m(q) : TV(q, q') <= L_k,
                         N_k KL(hat nu_k, q) + N'_k KL(hat nu'_k, q') <= delta_t}
          (KL-UCB-TV-Transfer, Definition 5.1)

How an index is computed (exactly up to the tolerances below, no generic solver):
  G(mu) := min of the budget N KL(r,q) + N' h(q) over the laws q of mean exactly mu, where
  h(q) = min over the admissible q' of KL(r', q'); G is convex in mu, and the index is the
  right end of the interval {G <= delta}, found by bisection from a feasible point.
  * On S = {0,1/2,1}, the laws of mean mu form a segment, q = (1-mu-s/2, s, mu-s/2); the
    minimum over s of the convex function is found on a grid refined three times.
  * kltr: h(q) = K_S(r', m(q) - L), the same segment minimum at level m(q) - L (0 below m(r')).
  * tv: h(q) is the KL projection of r' on the TV ball of radius L around q, in closed form
    (KKT): q'(y) = min(max(q(y), a r'(y)), b r'(y)) on supp r', the mass outside supp r'
    removed first, with a, b solving sum (a r' - q)_+ = L and sum (q - b r')_+ = L
    (piecewise linear equations, solved exactly).
The script test_sim.py checks these indices against independent computations (d8.py).

Usage:  python3 sim.py ALGO C T RUNS SEED   -> one line per run: algo c T seed N_2(T)
"""
import sys
import numpy as np

Y = np.array([0.0, 0.5, 1.0])
M = 3


def rate(t):
    t = max(t, 3)
    return np.log(t) + np.log(np.log(t))


def segment(mu, s):
    """Laws of mean mu on {0,1/2,1}, parametrised by s = q(1/2); s is an array."""
    return np.maximum(np.stack([1 - mu - s / 2, s, mu - s / 2], axis=-1), 0.0)


def kl_rows(r, Q):
    """KL(r, q) for each row q of Q (inf if q(y) = 0 < r(y))."""
    P = r > 0
    with np.errstate(divide='ignore', invalid='ignore'):
        v = np.where(Q[:, P] > 0, r[P] * np.log(r[P] / np.where(Q[:, P] > 0, Q[:, P], 1)), np.inf)
    return v.sum(axis=1)


def h_tv(r2, Q, L):
    """min{KL(r2, q') : TV(q, q') <= L} for each row q of Q (closed form, see the docstring)."""
    G = Q.shape[0]
    out = np.zeros(G)
    tv = 0.5 * np.abs(Q - r2).sum(axis=1)
    act = tv > L
    if not act.any():
        return out
    Qa = Q[act]
    P = r2 > 0
    rp = r2[P]
    QP = Qa[:, P]
    base = Qa[:, ~P].sum(axis=1)                  # mass outside supp r2, removed first
    t = QP / rp                                    # breakpoints
    order = np.argsort(t, axis=1)
    ts = np.take_along_axis(t, order, axis=1)
    rs = rp[order]
    qs = np.take_along_axis(QP, order, axis=1)
    # increase: sum (a r - q)_+ = L
    R = np.cumsum(rs, axis=1)
    C = np.cumsum(qs, axis=1)
    F = ts * R - C                                 # f at the breakpoints, nondecreasing
    j = (F <= L).sum(axis=1) - 1                   # last breakpoint with f <= L (>= 0)
    Rj = np.take_along_axis(R, j[:, None], 1)[:, 0]
    Cj = np.take_along_axis(C, j[:, None], 1)[:, 0]
    a = (L + Cj) / Rj
    # decrease: sum (q - b r)_+ = L - base on supp r2 (b = inf if base >= L)
    Lp = L - base
    Rs = np.cumsum(rs[:, ::-1], axis=1)[:, ::-1]   # suffix sums
    Cs = np.cumsum(qs[:, ::-1], axis=1)[:, ::-1]
    Gk = Cs - ts * Rs                              # g at the breakpoints, nonincreasing
    k = (Gk >= Lp[:, None]).sum(axis=1)            # first index with g < L'
    k = np.minimum(k, rs.shape[1] - 1)
    Rk = np.take_along_axis(Rs, k[:, None], 1)[:, 0]
    Ck = np.take_along_axis(Cs, k[:, None], 1)[:, 0]
    b = np.where(Lp > 0, (Ck - Lp) / Rk, np.inf)
    qp = np.minimum(np.maximum(qs, a[:, None] * rs), b[:, None] * rs)
    with np.errstate(divide='ignore'):
        val = (rs * np.log(rs / qp)).sum(axis=1)
    out[act] = val
    return out


def seg_min(fun, mu, passes=3, grid=201):
    """min over the segment of laws of mean mu of fun(Q) (convex in s)."""
    if mu < 0 or mu > 1:
        return np.inf
    smax = min(2 * mu, 2 - 2 * mu)
    lo, hi = 0.0, smax
    best = np.inf
    for _ in range(passes):
        s = np.linspace(lo, hi, grid)
        v = fun(segment(mu, s))
        i = int(np.argmin(v))
        best = min(best, v[i])
        step = (hi - lo) / (grid - 1)
        lo, hi = max(0.0, s[i] - 2 * step), min(smax, s[i] + 2 * step)
        if hi - lo < 1e-13:
            break
    return best


class Index:
    def __init__(self, kind, L):
        self.kind, self.L = kind, L
        self.prev = None

    def G(self, mu, n, r, n2, r2):
        if self.kind == 'tv' and n2 > 0:
            return seg_min(lambda Q: n * kl_rows(r, Q) + n2 * h_tv(r2, Q, self.L), mu)
        v = seg_min(lambda Q: n * kl_rows(r, Q), mu)
        if self.kind == 'kltr' and n2 > 0 and mu - self.L > r2 @ Y:
            v += n2 * seg_min(lambda Q: kl_rows(r2, Q), mu - self.L)
        return v

    def solve(self, n, r, n2, r2, delta, tol=1e-7):
        G = lambda mu: self.G(mu, n, r, n2, r2)
        feas = None
        if self.prev is not None and G(self.prev) <= delta:
            feas = self.prev
        if feas is None:
            # minimise the convex G on [0, 1] (golden section), then test it
            lo, hi = 0.0, 1.0
            g = (np.sqrt(5) - 1) / 2
            x1, x2 = hi - g * (hi - lo), lo + g * (hi - lo)
            f1, f2 = G(x1), G(x2)
            while hi - lo > 1e-6:
                if f1 <= f2:
                    hi, x2, f2 = x2, x1, f1
                    x1 = hi - g * (hi - lo); f1 = G(x1)
                else:
                    lo, x1, f1 = x1, x2, f2
                    x2 = lo + g * (hi - lo); f2 = G(x2)
                if min(f1, f2) <= delta:
                    break
            x = x1 if f1 <= f2 else x2
            if min(f1, f2) > delta:
                self.prev = None
                return -np.inf
            feas = x
        if G(1.0) <= delta:
            self.prev = 1.0
            return 1.0
        # right end of {G <= delta}: bisection between feas (feasible) and an infeasible point
        step = 1e-3
        hi = min(1.0, feas + step)
        lo = feas
        while G(hi) <= delta:
            lo = hi
            step *= 4
            hi = min(1.0, feas + step)
        while hi - lo > tol:
            mid = 0.5 * (lo + hi)
            if G(mid) <= delta:
                lo = mid
            else:
                hi = mid
        self.prev = lo
        return lo


def run(kind, c, T, seed, L=0.11):
    rng = np.random.default_rng(seed)
    nu = [np.array([0.0, 0.8, 0.2]), np.array([0.02, 0.96, 0.02])]
    K = 2
    n2 = int(np.floor(c * np.log(T)))
    src = [np.bincount(rng.choice(M, size=n2, p=nu[k]), minlength=M) / max(n2, 1)
           for k in range(K)]
    counts = [np.zeros(M) for _ in range(K)]
    N = np.zeros(K, int)
    idx = [Index(kind, L) for _ in range(K)]
    for t in range(1, T + 1):
        if t <= K:
            a = t - 1
        else:
            d = rate(t - 1)
            U = np.array([idx[k].solve(N[k], counts[k] / N[k], n2, src[k], d) for k in range(K)])
            best = np.flatnonzero(U >= U.max() - 1e-9)
            a = int(rng.choice(best))
        counts[a][rng.choice(M, p=nu[a])] += 1
        N[a] += 1
    return N[1]


if __name__ == '__main__':
    kind, c, T, runs, seed = sys.argv[1], float(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
    for i in range(runs):
        print(kind, c, T, seed + i, run(kind, c, T, seed + i), flush=True)
