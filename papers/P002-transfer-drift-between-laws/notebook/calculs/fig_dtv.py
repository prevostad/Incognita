"""Data of the figure of the no-drift example (paper: Example ex:no-drift, Figure fig:no-drift).

S = {0, 1/2, 1}, nu_a = nu'_a = (0.02, 0.96, 0.02), mu* = 0.6, L_a = 0.11.
Computes c -> D^TV_a(c) by primal bisection (d8.Dc), checks the values against the certified
values of the paper's table (run6.py, run7.py) and against two properties that every D_a has
(nonincreasing and convex in c, as a supremum of nonincreasing affine functions of c, by the
supremum form of Lemma lem:D), and prints the TikZ coordinates drawn in paper.tex
(`\\draw plot coordinates {...}`). PDFs under papers/ are never committed, so the figure is
drawn by TikZ from these numbers. Output: fig_dtv.txt (this directory). About a minute.

Usage: python fig_dtv.py
"""
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from d8 import Dc, kinf  # noqa: E402

Y = np.array([0.0, 0.5, 1.0])
NU = np.array([0.02, 0.96, 0.02])
MU, L = 0.6, 0.11
CERTIFIED = {1: 5.7289, 2: 5.4322, 5: 4.5595, 10: 3.1692, 20: 0.6940}
THRESHOLD = 23.505  # 1/G^TV, analytic (Example ex:no-drift)


def main():
    k0, _ = kinf(NU, Y, MU)
    grid = sorted(set(float(c) for c in np.linspace(0, 23, 24)) | {22.5, 23.25})
    vals = []
    lines = []
    for c in grid:
        d = 1.0 / k0 if c == 0 else Dc(c, NU, NU, Y, MU, L, 'TV')
        vals.append(d)
        lines.append("c=%7.3f  D_TV=%.4f" % (c, d))
        print(lines[-1], flush=True)
    vals = np.array(vals)
    g = np.array(grid)
    ok = True
    for c, v in CERTIFIED.items():
        got = vals[np.argmin(np.abs(g - c))]
        flag = abs(got - v) < 2e-3
        ok = ok and flag
        lines.append("check c=%d: computed %.4f, certified %.4f %s" % (c, got, v, "ok" if flag else "MISMATCH"))
    mono = bool(np.all(np.diff(vals) <= 1e-6))
    slopes = np.diff(vals) / np.diff(g)
    conv = bool(np.all(np.diff(slopes) >= -1e-3))
    lines.append("nonincreasing: %s, convex: %s, 1/K_0 = %.4f" % (mono, conv, 1 / k0))
    ok = ok and mono and conv
    coords = " ".join("(%.4g,%.4f)" % (c, v) for c, v in zip(g, vals)) + " (%.3f,0)" % THRESHOLD
    lines.append("checks: %s" % ("passed" if ok else "FAILED"))
    lines.append("TikZ coordinates (c, D^TV_a(c)):")
    lines.append(coords)
    text = "\n".join(lines) + "\n"
    print(text)
    with open(os.path.join(HERE, "fig_dtv.txt"), "w") as f:
        f.write(text)
    if not ok:
        sys.exit(1)


if __name__ == "__main__":
    main()
