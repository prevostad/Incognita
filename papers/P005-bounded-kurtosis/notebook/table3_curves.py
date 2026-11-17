"""Table 3 of P005: K(P, Delta) = K_inf(P, Delta; H_kappa) for two standardised discretised laws (mean 0, variance 1):
the 41-point quantile discretisation of N(0,1) (kurtosis about 2.69) and the 21-point uniform grid (kurtosis about 1.79),
for kappa in {3, 5}. Columns: K for both laws, K/(Delta^2/2), the regret coefficient Delta/K of an arm with gap Delta
and unit variance, the bracket Delta(kappa - 1 + 1/Delta^2) of [L17, Theorem 2] without its universal constant, and
their ratio. Heuristic evaluation by the profiled dual (kinf_tools.K_dual), no certificate.
Output: table3_out.txt. Not refereed."""
import os
import sys
import time

import numpy as np
from scipy.stats import norm

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from kinf_tools import K_dual, K_infinity  # noqa: E402

n = 41
xg = norm.ppf((np.arange(n) + 0.5) / n)
pg = np.full(n, 1.0 / n)
xg = (xg - pg @ xg) / np.sqrt(pg @ (xg - pg @ xg) ** 2)
xu = np.linspace(-1, 1, 21)
pu = np.full(21, 1.0 / 21)
xu = (xu - pu @ xu) / np.sqrt(pu @ (xu - pu @ xu) ** 2)
print(f"Gaussian, 41 quantiles: kurtosis={pg @ xg ** 4:.4f}; uniform, 21 points: kurtosis={pu @ xu ** 4:.4f}")
for kappa in [3.0, 5.0]:
    print(f"\nkappa={kappa}: K_infinity={K_infinity(kappa):.5f}")
    print("Delta | K(Gauss) | K/(D^2/2) | K(unif) | K/(D^2/2) | Delta/K(Gauss) | Delta(kappa-1+1/D^2) | ratio")
    for D in [0.02, 0.05, 0.1, 0.25, 0.5, 1.0, 2.0, 4.0, 8.0]:
        t0 = time.time()
        kg, _ = K_dual(xg, pg, D, kappa)
        ku, _ = K_dual(xu, pu, D, kappa)
        lat = D * (kappa - 1.0 + 1.0 / D ** 2)
        print(f"{D:5} | {kg:.7f} | {kg / (D * D / 2):.4f} | {ku:.7f} | {ku / (D * D / 2):.4f} | {D / kg:8.3f} | "
              f"{lat:8.3f} | {D / kg / lat:.3f}  [{time.time() - t0:.0f}s]", flush=True)
