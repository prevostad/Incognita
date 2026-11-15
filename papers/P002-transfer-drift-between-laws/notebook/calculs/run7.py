import numpy as np, sys
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from d8 import Dc, J, kinf, make_d
from dual import J_dual, start_from_primal
y = np.array([0, .5, 1.]); nu = np.array([0.02, 0.96, 0.02])
for c in [10.0, 20.0]:
    D = Dc(c, nu, nu, y, 0.6, 0.11, 'TV')
    p, (q, qp) = J(D, c, nu, nu, y, 0.6, 0.11, 'TV', starts=8)
    best = -np.inf
    for kap in [0.5, 2, 10, 50]:
        z0 = start_from_primal(D, c, nu, nu, y, q, qp); z0[-1] = kap
        best = max(best, J_dual(D, c, nu, nu, y, 0.6, 0.11, 'TV', start=z0))
    print("c=%.1f  D_TV(primal bisection)=%.4f  J at D: primal=%.6f dual=%.6f" % (c, D, p, best))
    print("   optimal pair q=%s q'=%s TV=%.4f" % (q.round(4), qp.round(4), make_d('TV', y)(q, qp)))
