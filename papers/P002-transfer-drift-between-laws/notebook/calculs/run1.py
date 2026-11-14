import numpy as np, sys
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from d8 import *

print("=== Check 1: mean pseudometric, numeric D vs closed form; Bernoulli: TV, W1 ===")
y = np.array([0.0, 1.0])
nu = np.array([0.6, 0.4]); nup = np.array([0.65, 0.35])
mu, L = 0.7, 0.1
for c in [0.0, 1.0, 3.0, 6.0]:
    out = [Dmean_closed(c, nu, nup, y, mu, L)]
    for kind in ['mean', 'TV', 'W1', 'KS']:
        out.append(Dc(c, nu, nup, y, mu, L, kind))
    print("c=%.1f  closed=%.5f  mean=%.5f  TV=%.5f  W1=%.5f  KS=%.5f" % (c, *out))

print("=== Check 2: three atoms, mean pseudometric numeric vs closed ===")
y = np.array([0.0, 0.5, 1.0])
nu = np.array([0.25, 0.5, 0.25]); nup = np.array([0.35, 0.45, 0.20])
mu, L = 0.6, 0.05
for c in [0.0, 1.0, 3.0]:
    print("c=%.1f closed=%.5f numeric=%.5f" % (c, Dmean_closed(c, nu, nup, y, mu, L), Dc(c, nu, nup, y, mu, L, 'mean')))
