import numpy as np, sys
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from d8 import *

y = np.array([0.0, 0.5, 1.0])
print("=== Example A: no drift, nu = nu' = (1/4,1/2,1/4), mu* = 0.6 ===")
nu = np.array([0.25, 0.5, 0.25]); nup = nu.copy(); mu = 0.6
K0, Qs = kinf(nu, y, mu)
print("K0 = %.6f, 1/K0 = %.4f, Q* =" % (K0, 1 / K0), np.round(Qs, 6))
for kind in ['TV', 'W1', 'KS', 'mean']:
    print("  d(Q*, nu') [%s] = %.6f" % (kind, make_d(kind, y)(Qs, nup)))
for L in [0.12, 0.05]:
    K0p, Qps = kinf(nup, y, mu - L)
    print("-- L = %.2f: K'_0 = Kinf(nu', mu*-L) = %.6f, Q'* =" % (L, K0p), None if Qps is None else np.round(Qps, 6))
    if Qps is not None:
        for kind in ['TV', 'W1', 'KS']:
            print("   d(Q*,Q'*) [%s] = %.6f" % (kind, make_d(kind, y)(Qs, Qps)))
    for c in [0.0, 1.0, 2.0, 4.0, 8.0, 16.0]:
        row = [Dmean_closed(c, nu, nup, y, mu, L)]
        for kind in ['W1', 'KS', 'TV']:
            row.append(Dc(c, nu, nup, y, mu, L, kind))
        print("   c=%5.1f  mean=%.4f  W1=%.4f  KS=%.4f  TV=%.4f" % (c, *row))
    # o(log T) thresholds: c such that D_c = 0  -> c0 = 1/J(0,1)
    for kind in ['mean', 'W1', 'KS', 'TV']:
        g = J(0.0, 1.0, nu, nup, y, mu, L, kind)[0]
        print("   G_min[%s] = %.6f  -> threshold c0 = %.4f" % (kind, g, 1 / g if g > 0 else np.inf))
