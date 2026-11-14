import numpy as np, sys
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from run5 import inst, J_both
from d8 import J, kinf

y = [0, .5, 1]
inst("Ex2 no drift, nu=nu'=(.02,.96,.02), L=0.11", y, [0.02, 0.96, 0.02], [0.02, 0.96, 0.02], 0.6, 0.11, [1, 2, 5, 10], ['TV', 'W1'])
# o(log T) thresholds c0 = 1/G_min, G_min = J(0,1)
nu = np.array([0.02, 0.96, 0.02])
for kind in ['TV', 'W1', 'mean']:
    g = J(0.0, 1.0, nu, nu, np.array(y, float), 0.6, 0.11, kind, starts=8)[0]
    print("  G_min[%s]=%.6f c0=%s" % (kind, g, ('%.3f' % (1 / g)) if g > 1e-9 else 'inf'))
inst("Ex3 W1 gain with drift", y, [0.1, 0.3, 0.6], [0.02, 0.96, 0.02], 0.85, 0.35, [2, 5, 10], ['W1'])
