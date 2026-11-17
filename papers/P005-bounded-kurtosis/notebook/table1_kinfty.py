"""Table 1 of P005: K_infinity(kappa) = log(1/q_kappa), the bounds kappa < 1/K_infinity < kappa + 2, the limit
1/K_infinity - kappa -> 3/2, the comparison with log(kappa/(kappa-1)) (large-gap branch of [L17, Theorem 9]),
and a random search for the largest atom of a 4-point law with kurtosis at most kappa (Proposition 3.4(i)).
Output: table1_out.txt. Not refereed."""
import os
import sys

import numpy as np
from scipy.optimize import minimize

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from kinf_tools import K_infinity, q_kappa  # noqa: E402

print("kappa | q_kappa | K_inf(kappa) | 1/K_inf | 1/K_inf - kappa | kappa < 1/K_inf < kappa+2 | log(kappa/(kappa-1))")
for k in [1.5, 2, 3, 3.5, 5, 9, 20, 100, 1e3, 1e4]:
    Kv = K_infinity(k)
    lat = np.log(k / (k - 1.0))
    print(f"{k:8g} | {q_kappa(k):.6f} | {Kv:.5f} | {1 / Kv:10.4f} | {1 / Kv - k:.5f} | {k < 1 / Kv < k + 2} | {lat:.5f}")

print("\nchecks: q(1-q)(kappa+3) = 1 and two-point kurtosis 1/(q(1-q)) - 3 = kappa")
for k in [1.5, 3, 7]:
    q = q_kappa(k)
    print(f"kappa={k}: q(1-q)(kappa+3)={q * (1 - q) * (k + 3):.12f}, two-point kurtosis={1 / (q * (1 - q)) - 3:.12f}")

print("\nlargest atom of a 4-point law with kurtosis <= kappa (SLSQP, 40 random starts)")
rng = np.random.default_rng(0)


def kurt(x, w):
    m = w @ x
    v = w @ (x - m) ** 2
    return w @ (x - m) ** 4 / v ** 2


for k in [1.5, 2.5, 3, 6]:
    best = 0.0
    for _ in range(40):
        x0 = rng.normal(size=4) * 3
        z0 = np.concatenate([x0, [0.5], rng.random(3) + 0.1])

        def unpack(z):
            a = z[4]
            rest = np.abs(z[5:8])
            rest = rest / rest.sum() * (1 - a)
            return z[:4], np.concatenate([[a], rest])

        def cons(z):
            x, w = unpack(z)
            v = w @ (x - w @ x) ** 2
            if v < 1e-9:
                return -1.0
            return k - kurt(x, w)

        try:
            r = minimize(lambda z: -z[4], z0, method="SLSQP", constraints=[{"type": "ineq", "fun": cons}],
                         bounds=[(-50, 50)] * 4 + [(0.01, 0.999)] + [(1e-3, 10)] * 3, options={"maxiter": 500})
            x, w = unpack(r.x)
            if cons(r.x) > -1e-7 and w[0] > best:
                best = w[0]
        except Exception:
            pass
    print(f"kappa={k}: largest atom found={best:.6f}, q_kappa={q_kappa(k):.6f}")
