"""Checks the indices of sim.py against independent computations of d8.py.

For random (n, r, n', r', delta), with U the index of sim.py and g(mu) the minimal budget at the
mean level mu computed by d8.py (K_S by its dual for klucb and kltr, the convex programme J by
SLSQP with several starts for tv), it checks g(U) = delta (up to the solvers' tolerance) and
g(U + 1e-3) > delta, i.e. that U is the right end of the feasible means. It also checks the
closed-form TV projection h_tv against a brute-force minimisation on a fine grid.
Usage: python3 test_sim.py   (about two minutes)
"""
import sys
import os
import time
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sim
import d8

Y = sim.Y
L = 0.11


def level(p, mu):
    """min KL(p, q) over the laws q of mean exactly mu (by the dual of d8; S is symmetric)."""
    return d8.kinf(p, Y, mu)[0] if mu >= p @ Y else d8.kinf(p[::-1], Y, 1 - mu)[0]


rng = np.random.default_rng(1)

# 1. the closed-form TV projection against a grid over the TV ball
err = 0.0
for it in range(200):
    q = rng.dirichlet(np.ones(3)); r2 = rng.dirichlet(np.ones(3))
    if it % 4 == 0:
        r2[rng.integers(3)] = 0; r2 /= r2.sum()
    h = sim.h_tv(r2, q[None, :], L)[0]
    g = np.linspace(0, 1, 801)
    A, B = np.meshgrid(g, g)
    QP = np.stack([A.ravel(), B.ravel(), 1 - A.ravel() - B.ravel()], axis=1)
    QP = QP[(QP[:, 2] >= 0) & (0.5 * np.abs(QP - q).sum(axis=1) <= L)]
    brute = sim.kl_rows(r2, QP).min() if len(QP) else np.inf
    if not (h <= brute + 1e-9):
        print('h_tv above the grid minimum', q, r2, h, brute)
    err = max(err, brute - h)
print('h_tv: largest (grid minimum - closed form) =', err, '(>= 0, small: grid resolution)')

# 2. the indices
worst = {}
times = {}
for it in range(60):
    n = int(rng.integers(1, 3000)); n2 = int(rng.integers(0, 300))
    r = rng.multinomial(n, rng.dirichlet(np.ones(3))) / n
    r2 = rng.multinomial(max(n2, 1), rng.dirichlet(np.ones(3))) / max(n2, 1)
    if it % 3 == 0:  # near the simulated instance
        r = rng.multinomial(n, [0.02, 0.96, 0.02]) / n
        r2 = rng.multinomial(max(n2, 1), [0.02, 0.96, 0.02]) / max(n2, 1)
    if it % 3 == 1:
        r = rng.multinomial(n, [0.0, 0.8, 0.2]) / n
        r2 = rng.multinomial(max(n2, 1), [0.0, 0.8, 0.2]) / max(n2, 1)
    delta = sim.rate(int(rng.integers(3, 20000)))
    for kind in ['klucb', 'kltr', 'tv']:
        ix = sim.Index(kind, L)
        t0 = time.time()
        U = ix.solve(n, r, n2, r2, delta)
        times.setdefault(kind, []).append(time.time() - t0)

        def g(mu):
            if mu > 1:
                return np.inf
            if kind == 'klucb' or n2 == 0:
                return n * d8.kinf(r, Y, mu)[0]
            if kind == 'kltr':
                # the target law has mean exactly mu (the source constraint depends on it)
                return n * level(r, mu) + n2 * d8.kinf(r2, Y, mu - L)[0]
            return n * d8.J(1.0, n2 / n, r, r2, Y, mu, L, 'TV', starts=6)[0]
        if U == -np.inf:
            # empty: the smallest budget over all admissible pairs must exceed delta
            grid = np.linspace(0.001, 0.999, 999)
            if kind == 'kltr':
                gm = min(n * level(r, mu) + n2 * (d8.kinf(r2, Y, mu - L)[0] if mu - L > r2 @ Y else 0)
                         for mu in grid)
            else:
                gm = n * d8.J(1.0, n2 / n, r, r2, Y, 0.0, L, 'TV', starts=6)[0]
            if gm <= delta:
                print('EMPTY?', kind, n, r, n2, r2, delta, gm)
            continue
        if U >= 1 - 1e-9:
            continue
        e1 = g(U) - delta
        e2 = g(U + 1e-3) - delta
        if abs(e1) > 1e-3 * delta or e2 <= 0:
            print('MISMATCH', kind, n, r, n2, r2, delta, U, e1, e2)
        worst[kind] = max(worst.get(kind, 0), abs(e1) / delta)
print('largest |g(U) - delta| / delta:', worst)
print('mean time per index (ms):', {k: round(1000 * np.mean(v), 2) for k, v in times.items()})
