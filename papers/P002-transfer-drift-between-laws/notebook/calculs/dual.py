import numpy as np
from scipy.optimize import minimize
import sys
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from d8 import kinf, make_d, kl

def J_primal(x, c, nu, nup, y, mu, L, kind, extra_starts=()):
    """Primal with better starts: uses d8.J plus explicit candidate pairs."""
    from d8 import J
    best, bz = J(x, c, nu, nup, y, mu, L, kind, starts=4)
    d = make_d(kind, y)
    for (q, qp) in extra_starts:
        if q @ y >= mu - 1e-9 and d(q, qp) <= L + 1e-9:
            v = x * kl(nu, q) + c * kl(nup, qp)
            if v < best:
                best, bz = v, (q, qp)
    return best, bz

def J_dual(x, c, nu, nup, y, mu, L, kind, start=None):
    """Lower bound on J from the Lagrange dual:
    sup x E_nu log A + c E_nu' log B + lam*mu - k + x + c - c L ||B||_d,
    with x A + c B + lam y = k on S, A,B >= 0.  Variables z = (lam, k, B, kap)."""
    y = np.asarray(y, float); m = len(y); dy = np.diff(y)
    nu = np.asarray(nu, float); nup = np.asarray(nup, float)
    eps = 1e-300
    def unpack(z):
        lam, k = z[0], z[1]; B = z[2:2 + m]; kap = z[2 + m]
        A = (k - lam * y - c * B) / x
        return lam, k, A, B, kap
    def negobj(z):
        lam, k, A, B, kap = unpack(z)
        if np.any(A[nu > 0] <= 0) or np.any(B[nup > 0] <= 0):
            return 1e10
        v = x * np.sum(nu[nu > 0] * np.log(A[nu > 0])) + c * np.sum(nup[nup > 0] * np.log(B[nup > 0]))
        v += lam * mu - k + x + c - c * L * kap
        return -v
    cons = [{'type': 'ineq', 'fun': lambda z: unpack(z)[2] - 1e-12},
            {'type': 'ineq', 'fun': lambda z: z[2:2 + m] - 1e-12},
            {'type': 'ineq', 'fun': lambda z: z[0]}]
    if kind == 'TV':
        cons.append({'type': 'ineq', 'fun': lambda z: np.array([z[2 + m] - (z[2 + i] - z[2 + j]) for i in range(m) for j in range(m)])})
    elif kind == 'W1':
        cons.append({'type': 'ineq', 'fun': lambda z: np.concatenate([z[2 + m] - np.diff(z[2:2 + m]) / dy, z[2 + m] + np.diff(z[2:2 + m]) / dy])})
    elif kind == 'KS':
        # KS = sup over f = indicators of [y_j, 1]; dual norm: total variation of increments
        cons.append({'type': 'ineq', 'fun': lambda z: z[2 + m] - np.sum(np.abs(np.diff(z[2:2 + m])))})
    z0 = start
    r = minimize(negobj, z0, method='SLSQP', constraints=cons, options={'ftol': 1e-14, 'maxiter': 3000})
    # re-evaluate exactly with the constraint-satisfying kappa
    lam, k, A, B, kap = unpack(r.x)
    if kind == 'TV':
        kap = B.max() - B.min()
    elif kind == 'W1':
        kap = np.max(np.abs(np.diff(B)) / dy)
    elif kind == 'KS':
        kap = np.sum(np.abs(np.diff(B)))
    if lam < 0 or np.any(A[nu > 0] <= 0) or np.any(A < -1e-12) or np.any(B[nup > 0] <= 0) or np.any(B < -1e-12):
        return -np.inf
    v = x * np.sum(nu[nu > 0] * np.log(A[nu > 0])) + c * np.sum(nup[nup > 0] * np.log(B[nup > 0])) + lam * mu - k + x + c - c * L * kap
    return v

def start_from_primal(x, c, nu, nup, y, q, qp):
    y = np.asarray(y, float); m = len(y)
    A = np.where(nu > 0, nu / np.maximum(q, 1e-300), 1.0)
    B = np.where(nup > 0, nup / np.maximum(qp, 1e-300), 1.0)
    # fit lam, k: x A + c B + lam y = k  (least squares)
    M = np.column_stack([-y, np.ones(m)])
    sol, *_ = np.linalg.lstsq(M, x * A + c * B, rcond=None)
    lam, k = max(sol[0], 0.0), sol[1]
    Bf = (k - lam * y - x * A) / c
    Bf = np.maximum(Bf, 1e-6)
    kap = 10.0
    return np.concatenate([[lam, k + 1e-6], Bf, [kap]])
