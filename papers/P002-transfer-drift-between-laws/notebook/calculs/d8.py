import numpy as np
from scipy.optimize import minimize, brentq

def kl(p, q):
    p = np.asarray(p, float); q = np.asarray(q, float)
    m = p > 0
    if np.any(q[m] <= 0):
        return np.inf
    return float(np.sum(p[m] * np.log(p[m] / q[m])))

def kinf(nu, y, mu):
    """K_inf on support y (closed version m(q) >= mu) via the dual."""
    y = np.asarray(y, float); nu = np.asarray(nu, float)
    if nu @ y >= mu:
        return 0.0, None
    xmax = y.max()
    hi = 1.0 / (xmax - mu)
    f = lambda lam: -np.sum(nu[nu > 0] * np.log(1 - lam * (y[nu > 0] - mu)))
    # maximise concave g(lam) = -f on [0, hi]
    from scipy.optimize import minimize_scalar
    r = minimize_scalar(f, bounds=(0, hi * (1 - 1e-12)), method='bounded',
                        options={'xatol': 1e-14})
    lam = r.x
    q = np.where(nu > 0, nu / (1 - lam * (y - mu)), 0.0)
    rest = 1 - q.sum()
    if rest > 1e-12:
        q[np.argmax(y)] += rest
    return -r.fun, q

def make_d(kind, y):
    y = np.asarray(y, float)
    dy = np.diff(y)
    if kind == 'TV':
        return lambda q, qp: 0.5 * np.sum(np.abs(q - qp))
    if kind == 'W1':
        return lambda q, qp: float(np.sum(np.abs(np.cumsum(q - qp)[:-1]) * dy))
    if kind == 'mean':
        return lambda q, qp: abs(float((q - qp) @ y))
    if kind == 'KS':
        return lambda q, qp: float(np.max(np.abs(np.cumsum(q - qp))))
    raise ValueError

def J(x, c, nu, nup, y, mu, L, kind, starts=6, seed=0):
    """min x KL(nu,q) + c KL(nup,q') s.t. m(q)>=mu, d(q,q')<=L (convex program).
    Smooth reformulation with slack variables for |.|."""
    y = np.asarray(y, float); m = len(y)
    nu = np.asarray(nu, float); nup = np.asarray(nup, float)
    dy = np.diff(y)
    # variables: q (m), qp (m), s (ns) slacks
    if kind == 'TV':
        ns = m
    elif kind == 'W1':
        ns = m - 1
    elif kind == 'KS':
        ns = m - 1
    else:
        ns = 0
    eps = 1e-12
    def obj(z):
        q = z[:m]; qp = z[m:2*m]
        v = 0.0
        mk = nu > 0
        v += x * np.sum(nu[mk] * np.log(nu[mk] / np.maximum(q[mk], eps)))
        mk2 = nup > 0
        if c > 0:
            v += c * np.sum(nup[mk2] * np.log(nup[mk2] / np.maximum(qp[mk2], eps)))
        return v
    def grad(z):
        g = np.zeros_like(z)
        q = z[:m]; qp = z[m:2*m]
        g[:m] = -x * nu / np.maximum(q, eps)
        if c > 0:
            g[m:2*m] = -c * nup / np.maximum(qp, eps)
        return g
    cons = [
        {'type': 'eq', 'fun': lambda z: np.sum(z[:m]) - 1},
        {'type': 'eq', 'fun': lambda z: np.sum(z[m:2*m]) - 1},
        {'type': 'ineq', 'fun': lambda z: z[:m] @ y - mu},
    ]
    if kind == 'TV':
        cons += [{'type': 'ineq', 'fun': lambda z: z[2*m:] - (z[:m] - z[m:2*m])},
                 {'type': 'ineq', 'fun': lambda z: z[2*m:] + (z[:m] - z[m:2*m])},
                 {'type': 'ineq', 'fun': lambda z: 2 * L - np.sum(z[2*m:])}]
    elif kind == 'W1':
        D = lambda z: np.cumsum(z[:m] - z[m:2*m])[:-1]
        cons += [{'type': 'ineq', 'fun': lambda z: z[2*m:] - D(z)},
                 {'type': 'ineq', 'fun': lambda z: z[2*m:] + D(z)},
                 {'type': 'ineq', 'fun': lambda z: L - z[2*m:] @ dy}]
    elif kind == 'KS':
        D = lambda z: np.cumsum(z[:m] - z[m:2*m])[:-1]
        cons += [{'type': 'ineq', 'fun': lambda z: L - D(z)},
                 {'type': 'ineq', 'fun': lambda z: L + D(z)}]
    elif kind == 'mean':
        cons += [{'type': 'ineq', 'fun': lambda z: L - (z[:m] - z[m:2*m]) @ y},
                 {'type': 'ineq', 'fun': lambda z: L + (z[:m] - z[m:2*m]) @ y}]
    bounds = [(1e-10, 1)] * (2 * m) + [(0, 2)] * ns
    rng = np.random.default_rng(seed)
    best = np.inf; bz = None
    for k in range(starts):
        if k == 0:
            _, qs = kinf(nu, y, mu)
            q0 = qs if qs is not None else nu.copy()
            q0 = 0.98 * q0 + 0.02 / m
            qp0 = q0.copy()
        else:
            q0 = rng.dirichlet(np.ones(m)); qp0 = rng.dirichlet(np.ones(m))
        z0 = np.concatenate([q0, qp0, np.ones(ns)])
        r = minimize(obj, z0, jac=grad, method='SLSQP', bounds=bounds,
                     constraints=cons, options={'ftol': 1e-13, 'maxiter': 2000})
        z = r.x
        # feasibility check
        q = z[:m] / z[:m].sum(); qp = z[m:2*m] / z[m:2*m].sum()
        dd = make_d(kind, y)(q, qp)
        if q @ y >= mu - 1e-7 and dd <= L + 1e-7:
            v = obj(np.concatenate([q, qp, z[2*m:]]))
            if v < best:
                best = v; bz = (q, qp)
    return best, bz

def Dc(c, nu, nup, y, mu, L, kind):
    K0, _ = kinf(nu, y, mu)
    if J(0.0, c, nu, nup, y, mu, L, kind)[0] >= 1:
        return 0.0
    f = lambda x: J(x, c, nu, nup, y, mu, L, kind)[0] - 1
    return brentq(f, 0.0, 1.0 / K0 + 1e-9, xtol=1e-7)

def Dmean_closed(c, nu, nup, y, mu, L):
    K0, _ = kinf(nu, y, mu); K0p, _ = kinf(nup, y, mu - L)
    return max(1 - c * K0p, 0) / K0
