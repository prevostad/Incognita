"""Table 2 of P005: checks of the dual formula (Proposition 3.3).
(a) At fixed location and scale: the dual maximum over Lambda against the convex primal over G (two free atoms),
    on four random 4-point laws (Lemma B.5, finite support).
(b) Profiled: K(P, mu) for P uniform on {-1, 0, 1} (kurtosis 3/2) and kappa = 3, by the profiled dual against a direct
    non-convex primal search (two free atoms, mean >= mu, kurtosis <= 3).
(c) The extremal two-point law q_kappa delta_0 + (1 - q_kappa) delta_1 (kurtosis exactly kappa = 3).
Output: table2_out.txt. Not refereed; no certificate of accuracy."""
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from kinf_tools import K_dual, K_infinity, K_primal, KG_primal, dual_value, q_kappa  # noqa: E402

kappa = 3.0
print(f"kappa={kappa}, K_infinity={K_infinity(kappa):.6f}")
rng = np.random.default_rng(5)
print("\n(a) fixed (c,s): dual max over Lambda vs convex primal over G")
for trial in range(4):
    yy = np.sort(rng.normal(size=4) * 1.5 + rng.normal())
    pp = rng.dirichlet(np.ones(4))
    dv, lam = dual_value(yy, pp, kappa)
    pv = KG_primal(yy, pp, kappa)
    print(f"  law {trial}: atoms={np.round(yy, 3)}, weights={np.round(pp, 3)}: dual={dv:.7f}, primal={pv:.7f}")

print("\n(b) P uniform on {-1,0,1}: profiled dual vs direct primal")
x = np.array([-1.0, 0.0, 1.0])
p = np.ones(3) / 3
for mu in [0.1, 0.3, 0.6, 1.0, 2.0]:
    d, arg = K_dual(x, p, mu, kappa)
    pr, sol = K_primal(x, p, mu, kappa)
    line = f"  mu={mu}: dual={d:.6f} at (c,s)=({arg[0]:.4f},{arg[1]:.4f}), primal={pr:.6f}"
    if sol is not None:
        w, be, u = sol
        line += f"; primal extra atoms: masses {np.round(be, 4)} at {np.round(u, 3)}"
    print(line, flush=True)

print("\n(c) extremal two-point law (atom q_kappa at 0), kurtosis exactly kappa")
q = q_kappa(kappa)
x2 = np.array([0.0, 1.0])
p2 = np.array([q, 1 - q])
m2 = p2 @ x2
v2 = p2 @ (x2 - m2) ** 2
print(f"  kurtosis={(p2 @ (x2 - m2) ** 4) / v2 ** 2:.6f}, mean={m2:.5f}, variance={v2:.5f}")
for D in [0.001, 0.01, 0.05, 0.2, 1.0, 5.0]:
    d, arg = K_dual(x2, p2, m2 + D, kappa)
    pr, _ = K_primal(x2, p2, m2 + D, kappa, restarts=40)
    print(f"  Delta={D}: dual={d:.6f}, primal={pr:.6f}, ratio to Delta^2/(2 sigma^2)={d / (D * D / (2 * v2)):.4f}",
          flush=True)
