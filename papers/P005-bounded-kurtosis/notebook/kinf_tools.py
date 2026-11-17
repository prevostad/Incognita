"""Numerical tools for K_inf over the class H_kappa of laws with kurtosis at most kappa (P005).

Not refereed: working tools of the authors of P005. Everything here is a heuristic evaluation, with no
certificate of accuracy (see Section 5 of the paper):
  * dual value at fixed location c and scale s (Proposition 3.3):
        D(R) = max over lambda in Lambda of sum_i p_i log(1 + lambda1*y_i + lambda2*phi(y_i)),
    computed by nested one-dimensional bounded maximisations, using the exact description
        Lambda = {0 <= lambda2 <= 1/(kappa(kappa-1)), |lambda1| <= L(lambda2)},
        L(lambda2) = min_{y > 0} (1 + lambda2*phi(y))/y, minimiser y^2 = (kappa + sqrt(kappa^2 + 3 kappa + 3/lambda2))/3;
  * profiled value K(P, mu) = inf over c > mu, s > 0 of D(T_{c,s} P): multi-start Nelder-Mead in (log(c - mu), log s),
    plus a one-dimensional search on the boundary c = mu;
  * a direct (non-convex) primal: Q = sum_i w_i delta_{x_i} + two free atoms, mean >= mu, kurtosis <= kappa, by SLSQP
    with random restarts (an upper bound on K, up to the solver's tolerance);
  * the convex primal at fixed (c, s): Q in G with two free atoms (an upper bound on K_G).
Usage: imported by the table scripts of this directory.
"""
import numpy as np
from scipy.optimize import minimize, minimize_scalar


def phi(y, kappa):
    """phi_kappa(y) = (y^2 - kappa)^2 - kappa(kappa - 1) = y^4 - 2 kappa y^2 + kappa."""
    return y ** 4 - 2.0 * kappa * y ** 2 + kappa


def L(l2, kappa):
    """Half-width of the section of Lambda at lambda2 = l2."""
    if l2 <= 0:
        return 0.0
    y2 = (kappa + np.sqrt(kappa ** 2 + 3.0 * kappa + 3.0 / l2)) / 3.0
    y = np.sqrt(y2)
    return max(0.0, (1.0 + l2 * phi(y, kappa)) / y)


def dual_value(y, p, kappa):
    """max over Lambda of sum_i p_i log h_lambda(y_i); returns (value, lambda)."""
    b = kappa * (kappa - 1.0)
    py = phi(y, kappa)

    def best_l1(l2):
        Lm = L(l2, kappa) * (1.0 - 1e-12)

        def f(l1):
            h = 1.0 + l1 * y + l2 * py
            if np.any(h <= 0):
                return 1e300
            return -np.sum(p * np.log(h))

        if Lm <= 1e-15:
            return 0.0, -f(0.0)
        r = minimize_scalar(f, bounds=(-Lm, Lm), method="bounded", options={"xatol": 1e-13})
        return r.x, -r.fun

    r = minimize_scalar(lambda l2: -best_l1(l2)[1], bounds=(0.0, 1.0 / b), method="bounded",
                        options={"xatol": 1e-14})
    l1, val = best_l1(r.x)
    val0 = 0.0  # lambda = 0 is in Lambda and gives the value 0
    return max(val, val0), (l1, r.x)


def K_dual(x, p, mu, kappa, starts=(0.05, 0.5, 2.0), scales=(0.5, 1.0, 3.0)):
    """Profiled dual: inf over c > mu, s > 0 of dual_value((x - c)/s). Returns (value, (c, s))."""
    m = p @ x
    sd = np.sqrt(p @ (x - m) ** 2)
    best, arg = np.inf, None
    for d in starts:
        for sc in scales:
            f = lambda z: dual_value((x - (mu + np.exp(z[0]))) / np.exp(z[1]), p, kappa)[0]
            r = minimize(f, np.array([np.log(d * sd), np.log(sc * sd)]), method="Nelder-Mead",
                         options={"xatol": 1e-8, "fatol": 1e-11, "maxiter": 1500})
            if r.fun < best:
                best, arg = r.fun, (mu + np.exp(r.x[0]), np.exp(r.x[1]))
    # boundary c = mu (the infimum over c > mu equals the infimum over c >= mu, Proposition 3.3(i))
    s0 = arg[1]
    r2 = minimize_scalar(lambda ls: dual_value((x - mu) / np.exp(ls), p, kappa)[0],
                         bounds=(np.log(s0) - 2.0, np.log(s0) + 2.0), method="bounded",
                         options={"xatol": 1e-10})
    if r2.fun < best:
        best, arg = r2.fun, (mu, np.exp(r2.x))
    return best, arg


def KG_primal(y, p, kappa, restarts=30, seed=0):
    """Convex primal at fixed (c, s): min sum_i p_i log(p_i/w_i) over Q = sum w_i delta_{y_i} + 2 free atoms in G."""
    rng = np.random.default_rng(seed)
    k = len(y)
    best = np.inf

    def unpack(z):
        e = np.exp(np.clip(z[:k + 2], -50, 50))
        e = e / e.sum()
        return e[:k], e[k:], z[k + 2:]

    obj = lambda z: np.sum(p * np.log(p / unpack(z)[0]))

    def mom(z):
        w, be, u = unpack(z)
        pts = np.concatenate([y, u])
        ws = np.concatenate([w, be])
        return ws @ pts, ws @ phi(pts, kappa)

    cons = [{"type": "eq", "fun": lambda z: mom(z)[0]}, {"type": "ineq", "fun": lambda z: -mom(z)[1]}]
    for _ in range(restarts):
        z0 = np.concatenate([np.log(p) + rng.normal(scale=0.3, size=k), rng.normal(size=2) - 1.0,
                             rng.normal(scale=2.0, size=2)])
        r = minimize(obj, z0, method="SLSQP", constraints=cons, options={"maxiter": 2000, "ftol": 1e-14})
        m0, m2 = mom(r.x)
        if abs(m0) < 1e-8 and m2 < 1e-8 and r.fun < best:
            best = r.fun
    return best


def K_primal(x, p, mu, kappa, restarts=60, seed=1):
    """Direct non-convex primal: Q = sum w_i delta_{x_i} + 2 free atoms, mean >= mu, kurtosis <= kappa."""
    rng = np.random.default_rng(seed)
    k = len(x)
    best, bz = np.inf, None

    def unpack(z):
        e = np.exp(np.clip(z[:k + 2], -50, 50))
        e = e / e.sum()
        return e[:k], e[k:], z[k + 2:]

    obj = lambda z: np.sum(p * np.log(p / unpack(z)[0]))

    def mom(z):
        w, be, u = unpack(z)
        pts = np.concatenate([x, u])
        ws = np.concatenate([w, be])
        m = ws @ pts
        v = ws @ (pts - m) ** 2
        m4 = ws @ (pts - m) ** 4
        return m, v, m4

    cons = [{"type": "ineq", "fun": lambda z: mom(z)[0] - mu},
            {"type": "ineq", "fun": lambda z: kappa * mom(z)[1] ** 2 - mom(z)[2]}]
    for _ in range(restarts):
        z0 = np.concatenate([np.log(p) + rng.normal(scale=0.3, size=k), rng.normal(size=2) - 2.0,
                             rng.normal(scale=3.0, size=2) + mu])
        r = minimize(obj, z0, method="SLSQP", constraints=cons, options={"maxiter": 2000, "ftol": 1e-14})
        m, v, m4 = mom(r.x)
        if m >= mu - 1e-8 and kappa * v ** 2 - m4 >= -1e-8 and r.fun < best:
            best, bz = r.fun, r.x
    return best, (unpack(bz) if bz is not None else None)


def q_kappa(kappa):
    """Largest atom of a law of kurtosis at most kappa (Proposition 3.4)."""
    return 0.5 * (1.0 + np.sqrt((kappa - 1.0) / (kappa + 3.0)))


def K_infinity(kappa):
    return np.log(1.0 / q_kappa(kappa))
