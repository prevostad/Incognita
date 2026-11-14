import numpy as np, sys
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from d8 import kinf, make_d, Dmean_closed, kl
from dual import J_primal, J_dual, start_from_primal

def candidates(nu, nup, y, mu, L):
    K0, Qs = kinf(nu, y, mu); K0p, Qps = kinf(nup, y, mu - L)
    Q2 = Qps if Qps is not None else nup
    return [(Qs, Q2), (Qs, nup)]

def J_both(x, c, nu, nup, y, mu, L, kind):
    p, (q, qp) = J_primal(x, c, nu, nup, y, mu, L, kind, extra_starts=candidates(nu, nup, y, mu, L))
    z0 = start_from_primal(x, c, nu, nup, y, q, qp)
    d = J_dual(x, c, nu, nup, y, mu, L, kind, start=z0)
    return p, d, q, qp

def D_bracket(c, nu, nup, y, mu, L, kind, iters=22):
    K0, _ = kinf(nu, y, mu)
    lo, hi = 0.0, 1.0 / K0     # J(1/K0) >= 1 always
    for _ in range(iters):
        mid = 0.5 * (lo + hi)
        p, d, _, _ = J_both(mid, c, nu, nup, y, mu, L, kind)
        if d >= 1:
            hi = mid          # certified J(mid) >= 1
        elif p < 1:
            lo = mid          # certified J(mid) < 1
        else:
            return lo, hi, 'uncertified gap at x=%.5f p=%.6f d=%.6f' % (mid, p, d)
    return lo, hi, 'ok'

def inst(name, y, nu, nup, mu, L, cs, kinds):
    y = np.array(y, float); nu = np.array(nu, float); nup = np.array(nup, float)
    print("=== %s ===" % name)
    print(" S=%s nu=%s nu'=%s mu*=%.3f L=%.3f  mu_a=%.4f mu'_a=%.4f" % (y, nu, nup, mu, L, nu @ y, nup @ y))
    for kind in kinds:
        print("  d(nu,nu')[%s]=%.4f" % (kind, make_d(kind, y)(nu, nup)))
    K0, Qs = kinf(nu, y, mu); K0p, Qps = kinf(nup, y, mu - L)
    Q2 = Qps if Qps is not None else nup
    print("  K0=%.5f 1/K0=%.4f K'0=%.5f Q*=%s Q'*=%s" % (K0, 1 / K0, K0p, Qs.round(4), np.round(Q2, 4)))
    for kind in kinds:
        print("  d(Q*,Q'*)[%s]=%.4f   d(Q*,nu')[%s]=%.4f" % (kind, make_d(kind, y)(Qs, Q2), kind, make_d(kind, y)(Qs, nup)))
    for c in cs:
        Dm = Dmean_closed(c, nu, nup, y, mu, L)
        line = "  c=%6.2f  D_mean=%.4f" % (c, Dm)
        for kind in kinds:
            p, d, _, _ = J_both(Dm, c, nu, nup, y, mu, L, kind) if c > 0 else (np.nan, np.nan, 0, 0)
            if c > 0:
                lo, hi, st = D_bracket(c, nu, nup, y, mu, L, kind)
                line += " | %s: J(Dm) in [%.4f,%.4f], D in [%.4f,%.4f] %s" % (kind, d, p, lo, hi, '' if st == 'ok' else st)
        print(line)

if __name__ == '__main__':
    inst("W1-a (random #57)", [0, .5, 1], [0.084, 0.276, 0.64], [0.008, 0.991, 0.001], 0.861, 0.366, [5, 20, 118.62], ['W1'])
    inst("W1-b (random #12, primal failure check)", [0, .5, 1], [0.063, 0.56, 0.377], [0.08, 0.001, 0.919], 0.815, 0.286, [30.56], ['W1'])
