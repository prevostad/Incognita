"""Numerical experiments of P000 (Section "Numerical experiments" of paper.tex).

Not refereed: a script of the notebook of P000. It simulates the algorithm HY of the paper with its
default parameters (Definition def:hy, Theorems thm:upper and thm:main(b)) and four published
algorithms on imposed grids of batch ends, and, on the static grid of BABA (Jin et al., 2021), also
BABA itself; writes one CSV per configuration in notebook/results/ and draws the figures
notebook/fig*.pdf included by paper.tex.

Reproduce (about 5 minutes on a slow laptop, one core; the log is results/log.txt):
    python experiments.py            # simulations, then figures
    python experiments.py --figures  # figures only, from the CSV files

Dependencies: numpy, matplotlib. Seeds are fixed (SEED below); the results are deterministic.

Implementation notes.
- Rewards take finitely many values (atoms in [0,1]); a policy only uses the rewards observed at the
  ends of the batches, so the rewards of the pulls made during a batch are drawn at its end, as
  multinomial counts over the atoms (same law as drawing them round by round, by the stack
  construction of Definition def:stacks). Every empirical distribution is then a vector of counts
  over the atoms, and K_inf is computed exactly (up to 1e-12) by bisection on its dual variable.
- All runs of a configuration are simulated together (arrays of shape (R, K)).
- In every run the arms are labelled by an independent uniform random permutation, so that no tie
  rule and no initial arm (BABA's c_0) favours the optimal arm.
- BABA uses the means of the first s pulls of an arm (its mu_{i,s}): it reads its rewards from
  explicit reward stacks (Definition def:stacks), drawn at the start of each run.
- The horizon T truncates the last batch: no policy below uses the end of the current batch,
  except BaSE, which receives the grid and T as input, as in its paper.
"""

import argparse
import csv
import math
import os
import time

import numpy as np

T = 20_000          # horizon
R = 64              # runs per configuration
SEED = 20261117     # base seed
HERE = os.path.dirname(os.path.abspath(__file__))
RESULTS = os.path.join(HERE, "results")

# ----------------------------------------------------------------------------- instances

def bernoulli(means):
    atoms = np.array([0.0, 1.0])
    probs = np.array([[1.0 - m, m] for m in means])
    return atoms, probs


def binomial10(ps):
    """X = Bin(10, p)/10: a law on {0, 0.1, ..., 1} of mean p."""
    atoms = np.arange(11) / 10.0
    probs = np.array([[math.comb(10, j) * p ** j * (1 - p) ** (10 - j) for j in range(11)]
                      for p in ps])
    return atoms, probs


INSTANCES = {
    "A": ("Bernoulli, means (0.5, 0.4, 0.3, 0.2)", bernoulli([0.5, 0.4, 0.3, 0.2])),
    "B": ("Bernoulli, means (0.5, 0.48, 0.46, 0.44)", bernoulli([0.5, 0.48, 0.46, 0.44])),
    "C": ("Bin(10,p)/10, means (0.5, 0.4, 0.3, 0.2)", binomial10([0.5, 0.4, 0.3, 0.2])),
}

# ----------------------------------------------------------------------------- grids
# Each grid is the list of its batch ends t_1 < t_2 < ... that are smaller than T; B_1 = t_1 >= K.

def grid_constant():          # B_l = 100: bounded batch sizes, x = 1
    return list(range(100, T, 100))


def grid_polynomial():        # t_l = 4 l^3: batch sizes of order l^2, x = 1
    return [4 * l ** 3 for l in range(1, 100) if 4 * l ** 3 < T]


def grid_geometric():         # t_l = 2^(l+1): x_l = (l+1)/l -> 1
    return [2 ** (l + 1) for l in range(1, 40) if 2 ** (l + 1) < T]


def grid_irregular():         # short batches and two long ones (a prefix of grids with x = 1)
    return list(range(8, 201, 8)) + [6000] + list(range(6100, 8001, 100))


def grid_dexp2():             # t_l = 2^(2^l): x_l = 2
    return [2 ** (2 ** l) for l in range(1, 10) if 2 ** (2 ** l) < T]


def grid_dexp15():            # t_l = ceil(2^(3 * 1.5^(l-1))): x_l -> 1.5
    ends = []
    for l in range(1, 30):
        t = math.ceil(2 ** (3 * 1.5 ** (l - 1)))
        if t >= T:
            break
        ends.append(t)
    return ends


# BABA (Jin et al., 2021, Algorithm 1 and Section 3.1), with the parameters of their Section 6:
# alpha = 3, I_1 = 2000. f(x) = max{ceil(x^(1 + 1/(1 + ilog^alpha x))), 2x}, g(x) = ceil(log x/log log x),
# I_r = f(I_{r-1}); epoch r has the five checkpoints t_{1..5,r} of Section 3.1. Readings (the paper
# assumes log I_r integer "for ease of presentation"): log^2 I_r is rounded up, LOG2(I) below; and
# I_0 := 0 (the first epoch starts at t = 0).
BABA_ALPHA, BABA_I1, BABA_K = 3, 2000, 4


def ilog(x, m):
    for _ in range(m):
        x = max(math.log(x), 0.0) if x > 0 else 0.0
    return x


def baba_f(x):
    return max(math.ceil(x ** (1.0 + 1.0 / (1.0 + ilog(x, BABA_ALPHA)))), 2 * x)


def baba_g(x):
    return math.ceil(math.log(x) / math.log(math.log(x)))


def LOG2(x):
    return math.ceil(math.log(x) ** 2)


def baba_epochs():
    """List of (I_{r-1}, I_r) for the epochs that start before T."""
    out, prev, cur = [], 0, BABA_I1
    assert BABA_K * baba_g(BABA_I1) + (2 * BABA_K + 1) * math.log(BABA_I1) ** 2 < BABA_I1  # (6)
    while prev < T:
        out.append((prev, cur))
        prev, cur = cur, baba_f(cur)
    return out


def grid_baba():
    ends = []
    for prev, cur in baba_epochs():
        g, l2, K = baba_g(cur), LOG2(cur), BABA_K
        t1 = prev + K * g
        for t in (t1, t1 + l2, t1 + (K + 1) * l2, t1 + (2 * K + 1) * l2, cur):
            if t < T:
                ends.append(t)
    return ends


GRIDS = {
    "const": ("constant batches $B_\\ell=100$", grid_constant, 1.0),
    "poly": ("polynomial $t_\\ell=4\\ell^3$", grid_polynomial, 1.0),
    "geom": ("geometric $t_\\ell=2^{\\ell+1}$", grid_geometric, 1.0),
    "irr": ("irregular (two long batches)", grid_irregular, 1.0),
    "dexp2": ("doubly exponential $t_\\ell=2^{2^\\ell}$ ($x=2$)", grid_dexp2, 2.0),
    "dexp15": ("doubly exponential $t_\\ell=\\lceil 2^{3\\cdot 1.5^{\\ell-1}}\\rceil$ ($x=1.5$)",
               grid_dexp15, 1.5),
    "baba": ("static grid of BABA", grid_baba, 1.0),
}

CONFIGS = [("A", g) for g in ["const", "poly", "geom", "irr", "dexp2", "dexp15"]] + \
          [("B", "geom"), ("B", "dexp2"), ("C", "geom"), ("C", "dexp2")] + \
          [("A", "baba"), ("B", "baba"), ("C", "baba")]

# ----------------------------------------------------------------------------- divergences

def kinf(counts, mu, atoms):
    """K_inf(G, mu) = sup_{0 <= lam < 1/(1-mu)} E_G[log(1 - lam (X - mu))] (Definition def:kinf).

    counts: (..., J) non-negative weights of the atoms (G is their normalisation);
    mu: (...) levels in [0, 1]. Returns (...). K_inf(G, 1) = 0 if E_G[X] = 1, +inf otherwise.
    The function of lam is concave; its maximiser is found by bisection on the derivative.
    """
    g = counts / counts.sum(axis=-1, keepdims=True)
    mu = np.broadcast_to(mu, g.shape[:-1]).astype(float)
    mean = g @ atoms
    out = np.zeros(g.shape[:-1])
    at_one = mu >= 1.0
    out[at_one & (mean < 1.0)] = np.inf
    todo = (~at_one) & (mean < mu)
    if not todo.any():
        return out
    gg, mm = g[todo], mu[todo]
    d = atoms[None, :] - mm[:, None]                       # X - mu, shape (n, J)
    lam_max = 1.0 / (1.0 - mm)

    def dphi(lam):
        return -(gg * d / (1.0 - lam[:, None] * d)).sum(axis=1)

    lo = np.zeros_like(mm)
    hi = lam_max * (1.0 - 1e-12)
    boundary = dphi(hi) >= 0.0                              # no mass at 1: maximum at the boundary
    for _ in range(60):
        mid = 0.5 * (lo + hi)
        pos = dphi(mid) > 0.0
        lo = np.where(pos, mid, lo)
        hi = np.where(pos, hi, mid)
    lam = np.where(boundary, lam_max * (1.0 - 1e-12), 0.5 * (lo + hi))
    arg = np.maximum(1.0 - lam[:, None] * d, 1e-300)
    val = np.where(gg > 0, gg * np.log(arg), 0.0).sum(axis=1)
    out[todo] = np.maximum(val, 0.0)
    return out


def kl_bern(p, q):
    p = np.clip(p, 0.0, 1.0)
    q = np.clip(q, 1e-15, 1 - 1e-15)
    with np.errstate(divide="ignore", invalid="ignore"):
        a = np.where(p > 0, p * np.log(p / q), 0.0)
        b = np.where(p < 1, (1 - p) * np.log((1 - p) / (1 - q)), 0.0)
    return a + b

# ----------------------------------------------------------------------------- algorithms
# Interface: end_batch(ell, ends, N, C) at the end t_ell of batch ell (N: counts N_c(t_ell), all
# observed; C: counts of the atoms observed for each arm), and act(t, N) at round t with
# N = N_c(t-1), returning the arms pulled in the R runs. Ties: smallest index unless stated.

class HY:
    """HY(w0, beta, omega^dy, theta, gamma) of Definition def:hy and Algorithm alg:hy, default
    parameters (w0 = 1, beta = 2 unless given; omega, theta, gamma as in the box of def:hy)."""

    name = "HY"

    def __init__(self, K, atoms, rng, grid, w0=1.0, beta=2.0):
        self.K, self.atoms, self.w0, self.beta = K, atoms, w0, beta
        self.ell = 0
        self.y = 1.0                  # y_0 := 1
        self.U_next = 1               # U_1 := 1
        self.cols = np.arange(K)[None, :]
        self.activated = []           # batch ends t_ell whose next batch has paced rounds

    def end_batch(self, ell, ends, N, C):
        K, w0, Rr = self.K, self.w0, N.shape[0]
        rows = np.arange(Rr)
        t_l = ends[-1]
        L = math.log(t_l)
        x = 1.0 if ell == 1 else L / math.log(ends[-2])
        y_prev, self.y = self.y, x * x                        # y_{ell-1}, y_ell = x_ell^2
        U_l, self.U_next = self.U_next, math.ceil(L ** self.beta)   # U_ell, U_{ell+1}
        theta = 1.0 / math.log(math.log(t_l)) if t_l >= math.e ** math.e else 1.0
        self.s = math.floor(t_l ** (1.0 + theta))              # s_ell
        k = math.floor(0.25 * math.log2(max(L, 1.0)))
        self.omega = 2.0 ** (-k)                               # omega^dy_ell
        gamma = min(0.5, max(L, 1.0) ** (-0.25))               # gamma_ell
        # (1) pseudo-observation 0 of weight w0
        Ct = C.astype(float)
        Ct[:, :, 0] += w0                                      # atoms[0] == 0
        Nf = N.astype(float)
        mt = (C @ self.atoms) / (Nf + w0)
        # (2) leader and IMED divergences
        leader = np.argmax(mt, axis=1)
        mstar = mt[rows, leader]
        self.Kt = kinf(Ct, mstar[:, None], self.atoms)
        # (3) reference, test level, test divergences
        W = Nf >= 0.5 * U_l
        mtW = np.where(W, mt, -np.inf)
        ref = np.where(W.any(axis=1), np.argmax(mtW, axis=1), leader)
        mhat = mt[rows, ref]
        Kh = kinf(Ct, mhat[:, None], self.atoms)
        # (4) consistency threshold (data up to t_ell only)
        if ell == 1:
            Lam = np.full(Rr, L)
        else:
            Q = (~W) & (self.cols != self.leader[:, None])
            with np.errstate(invalid="ignore"):
                val = Nf * self.Kh / y_prev + np.log(Nf)
            val = np.where(Q, val, np.inf)
            Lam = np.minimum(L, val.min(axis=1))
        h = (1.0 - gamma) * y_prev * Lam
        # (5) verdicts
        notleader = self.cols != leader[:, None]
        with np.errstate(invalid="ignore"):
            self.rejected = notleader & (Kh > 0) & (Nf * Kh >= h[:, None])
        self.leader, self.Kh, self.ell, self.t_l = leader, Kh, ell, t_l
        self.notleader = notleader

    def act(self, t, N):
        Rr = N.shape[0]
        if self.ell == 0:                                      # batch 1: the arms in turn
            return np.full(Rr, (t - 1) % self.K)
        rows = np.arange(Rr)
        if t <= self.s:                                        # IMED phase
            with np.errstate(invalid="ignore"):
                J = np.where(np.isinf(self.Kt), np.inf, N * self.Kt) + self.y * np.log(N)
            jmin = J.min(axis=1)
            return np.where(J[rows, self.leader] <= jmin, self.leader, np.argmin(J, axis=1))
        if t == self.s + 1 and (not self.activated or self.activated[-1] != self.t_l):
            self.activated.append(self.t_l)
        # paced phase: (6) targets and (7) rule
        with np.errstate(divide="ignore", invalid="ignore"):
            plan = np.where(self.Kh > 0,
                            np.ceil((1.0 + self.omega) * self.y * math.log(t) / self.Kh), 0.0)
        plan = np.where(np.isinf(self.Kh), 0.0, plan)
        target = self.K - 1 + np.where(self.rejected, np.minimum(self.U_next, plan), self.U_next)
        need = self.notleader & (N < target)
        return np.where(need.any(axis=1), np.argmax(need, axis=1), self.leader)


class IMEDFrozen:
    """IMED of Honda and Takemura (2015, Algorithm 1), with the empirical distributions frozen at
    the last batch end and the current counts: pull argmin N_c(t-1) K_inf(F_c, m*) + log N_c(t-1)."""

    name = "IMED (frozen statistics)"

    def __init__(self, K, atoms, rng, grid):
        self.K, self.atoms, self.ell = K, atoms, 0

    def end_batch(self, ell, ends, N, C):
        m = (C @ self.atoms) / N
        mstar = m.max(axis=1)
        self.Kd = kinf(C.astype(float), mstar[:, None], self.atoms)
        self.ell = ell

    def act(self, t, N):
        if self.ell == 0:
            return np.full(N.shape[0], (t - 1) % self.K)
        with np.errstate(invalid="ignore"):
            J = np.where(np.isinf(self.Kd), np.inf, N * self.Kd) + np.log(N)
        return np.argmin(J, axis=1)


class KLUCBFrozen:
    """kl-UCB of Cappe et al. (2013, Algorithm 1 and Corollary 1: Bernoulli divergence, valid on
    [0,1]), f(t) = log t + 3 log log t, with the empirical means frozen at the last batch end and the
    current counts: pull argmax max{q : N_c(t-1) kl(m_c, q) <= f(t-1)}."""

    name = "kl-UCB (frozen statistics)"

    def __init__(self, K, atoms, rng, grid):
        self.K, self.atoms, self.ell = K, atoms, 0

    def end_batch(self, ell, ends, N, C):
        self.m = (C @ self.atoms) / N
        self.ell = ell

    def act(self, t, N):
        if self.ell == 0:
            return np.full(N.shape[0], (t - 1) % self.K)
        s = max(t - 1, 3)
        f = math.log(s) + 3.0 * math.log(math.log(s))
        lo, hi = self.m.copy(), np.ones_like(self.m)
        bound = f / N
        for _ in range(22):
            mid = 0.5 * (lo + hi)
            ok = kl_bern(self.m, mid) <= bound
            lo = np.where(ok, mid, lo)
            hi = np.where(ok, hi, mid)
        return np.argmax(lo, axis=1)


class BatchedTS:
    """Thompson sampling of Kalkanli and Ozgur (2021, Algorithm 1): Gaussian prior N(0,1), posterior
    N(mu_c, 1/(1+N_c)) with mu_c = (sum of observed rewards)/(1+N_c), updated at the batch ends only;
    at every round one sample per arm, pull the argmax."""

    name = "Thompson sampling (batched)"

    def __init__(self, K, atoms, rng, grid):
        self.K, self.atoms, self.rng = K, atoms, rng
        self.mu, self.sd = None, None

    def end_batch(self, ell, ends, N, C):
        self.mu = (C @ self.atoms) / (1.0 + N)
        self.sd = 1.0 / np.sqrt(1.0 + N)

    def act(self, t, N):
        z = self.rng.standard_normal(N.shape)
        if self.mu is None:
            return np.argmax(z, axis=1)
        return np.argmax(self.mu + self.sd * z, axis=1)


class BaSE:
    """Batched successive elimination of Gao et al. (2019, Algorithm 1), with the imposed grid and the
    horizon T as its input grid (t_M := T) and gamma = 1 (their experiments): active arms in turn;
    at every end t_m < T, eliminate i if max_j Y_j - Y_i >= sqrt(gamma log(TK)/tau_m); in the last
    batch, the active arm of largest mean. tau_m: the smallest count among the active arms; the means
    use all the observed pulls."""

    name = "BaSE (knows the grid and $T$)"

    def __init__(self, K, atoms, rng, grid, gamma=1.0):
        self.K, self.atoms, self.gamma = K, atoms, gamma
        self.last_end = grid[-1]
        self.active = None
        self.commit = None

    def end_batch(self, ell, ends, N, C):
        if self.active is None:
            self.active = np.ones(N.shape, dtype=bool)
        m = (C @ self.atoms) / N
        mA = np.where(self.active, m, -np.inf)
        best = mA.max(axis=1)
        tau = np.where(self.active, N, np.iinfo(np.int64).max).min(axis=1)
        thr = np.sqrt(self.gamma * math.log(T * self.K) / tau)
        self.active &= ~((best[:, None] - m) >= thr[:, None])
        if ends[-1] == self.last_end:
            self.commit = np.argmax(np.where(self.active, m, -np.inf), axis=1)

    def act(self, t, N):
        if self.commit is not None:
            return self.commit
        if self.active is None:
            return np.full(N.shape[0], (t - 1) % self.K)
        big = np.where(self.active, N, np.iinfo(np.int64).max)
        return np.argmin(big, axis=1)


class BABA:
    """BABA of Jin et al. (2021, Algorithms 1-6), alpha = 3, I_1 = 2000, Bernoulli kl, c_0 = arm 0.
    Run only on its own grid (grid_baba): its batch k of epoch r is Step k. Each step is a plan for
    the next batch: target counts per arm (pull the first arm, in label order, below its target) and
    a filler arm. Readings: log^2 I_r rounded up; Step I/III/IV loops "while T <= m" read as "until
    T = m" (the text: "till reaching"); in (7) kl is kl_+ (delta = +inf when the shifted means are
    in the wrong order); the shifted means are clipped to [0, 1]; the test (8) is evaluated at the
    end of the batch of Step III, when the rewards it uses are observed."""

    name = "BABA (on its own grid)"

    def __init__(self, K, atoms, rng, grid):
        self.K, self.atoms, self.rng = K, atoms, rng
        self.epochs = baba_epochs()

    def set_env(self, probs_perm):
        R_, K = probs_perm.shape[:2]
        cdf = np.cumsum(probs_perm, axis=2)
        U = self.rng.random((R_, K, T))
        idx = np.zeros((R_, K, T), dtype=np.int64)
        for j in range(cdf.shape[2] - 1):
            idx += U > cdf[:, :, j][:, :, None]
        vals = self.atoms[idx]
        self.cum = np.concatenate([np.zeros((R_, K, 1)), np.cumsum(vals, axis=2)], axis=2)
        self.rows = np.arange(R_)
        self.c = np.zeros(R_, dtype=np.int64)          # c_0
        self.r, self.step = 0, 0
        self._plan(np.zeros((R_, K), dtype=np.int64))

    def mean_first(self, arm, s):
        s = np.maximum(s, 1)
        return self.cum[self.rows, arm, s] / s

    def _plan(self, N):
        """Plan of the batch that starts now (step self.step of epoch self.r)."""
        prev, cur = self.epochs[self.r]
        g, l2, K, rows = baba_g(cur), LOG2(cur), self.K, self.rows
        lim = math.log(cur * l2)
        arms = np.arange(K)[None, :]
        if self.step == 0:      # Step I: every arm up to g pulls, then c_{r-1}
            self.target = np.maximum(N, g)
            self.filler = self.c.copy()
        elif self.step == 1:    # Step II: a_1 = argmax of the means of the first g pulls; l2 pulls
            m = np.stack([self.mean_first(np.full(len(rows), i), np.full(len(rows), g))
                          for i in range(K)], axis=1)
            self.a1 = np.argmax(m, axis=1)
            self.target = np.zeros_like(N)
            self.filler = self.a1.copy()
        elif self.step == 2:    # Step III: a_i up to min(delta_i, l2), then c_{r-1}
            self.s1 = N[rows, self.a1].copy()
            eps = 1.0 / math.log(math.log(cur))
            q = np.clip(self.mean_first(self.a1, self.s1) - eps, 0.0, 1.0)
            tgt = np.zeros_like(N)
            for i in range(K):
                p = np.clip(self.mean_first(np.full(len(rows), i), np.full(len(rows), g)) + eps,
                            0.0, 1.0)
                klp = np.where(p <= q, kl_bern(p, q), 0.0)
                with np.errstate(divide="ignore"):
                    delta = np.where(klp > 0, lim / np.maximum(klp, 1e-300), np.inf)
                tgt[:, i] = np.ceil(np.minimum(delta, l2)).astype(np.int64)
            self.target = np.where(arms == self.a1[:, None], 0, np.maximum(tgt, 0))
            self.filler = self.c.copy()
        elif self.step == 3:    # test (8), then Step IV
            m1 = self.mean_first(self.a1, self.s1)
            F = np.zeros(len(rows), dtype=bool)
            for i in range(K):
                si = np.minimum(l2, N[:, i])
                mi = self.mean_first(np.full(len(rows), i), si)
                klp = np.where(mi <= m1, kl_bern(mi, m1), 0.0)
                F |= (i != self.a1) & (klp < lim / np.maximum(si, 1))
            self.F = F
            self.target = np.where(F[:, None], N + l2, 0)
            self.filler = np.where(F, self.c, self.a1)
            self.c = np.where(F, self.c, self.a1)          # c_r = a_1 if F is false
        else:                   # Step V: c_r (argmax of all the means if F), until I_r
            full = np.stack([self.mean_first(np.full(len(rows), i), N[:, i]) for i in range(K)],
                            axis=1)
            self.c = np.where(self.F, np.argmax(full, axis=1), self.c)
            self.target = np.zeros_like(N)
            self.filler = self.c.copy()

    def end_batch(self, ell, ends, N, C):
        self.step += 1
        if self.step == 5:
            self.step, self.r = 0, self.r + 1
        self._plan(N)

    def act(self, t, N):
        need = N < self.target
        return np.where(need.any(axis=1), np.argmax(need, axis=1), self.filler)


ALGOS = [HY, IMEDFrozen, KLUCBFrozen, BatchedTS, BaSE]

# ----------------------------------------------------------------------------- simulation

def checkpoints(ends):
    pts = set(np.unique(np.round(np.logspace(0, math.log10(T), 160)).astype(int)).tolist())
    pts |= set(ends)
    pts.add(T)
    return sorted(p for p in pts if 1 <= p <= T)


def simulate(alg_cls, ends, atoms, probs, seed):
    rng = np.random.default_rng(seed)
    K = probs.shape[0]
    means = probs @ atoms
    # arm labels: an independent uniform permutation in each run
    perm = np.argsort(rng.random((R, K)), axis=1)
    probs_r = probs[perm]                                    # (R, K, J)
    gaps_r = (means.max() - means)[perm]                     # (R, K)
    alg = alg_cls(K, atoms, rng, ends)
    if hasattr(alg, "set_env"):
        alg.set_env(probs_r)
    N = np.zeros((R, K), dtype=np.int64)
    Nobs = np.zeros_like(N)
    C = np.zeros((R, K, len(atoms)), dtype=np.int64)
    reg = np.zeros(R)
    pts = checkpoints(ends)
    pset = set(pts)
    rec = []
    ends_set = set(ends)
    seen = []
    rows = np.arange(R)
    for t in range(1, T + 1):
        a = alg.act(t, N)
        N[rows, a] += 1
        reg += gaps_r[rows, a]
        if t in pset:
            rec.append(reg.copy())
        if t in ends_set:
            C += rng.multinomial(N - Nobs, probs_r)
            Nobs = N.copy()
            seen.append(t)
            alg.end_batch(len(seen), list(seen), N.copy(), C.copy())
    extra = getattr(alg, "activated", None)
    return np.array(pts), np.array(rec), extra


def constant_Cx(atoms, probs, x):
    means = probs @ atoms
    mstar = means.max()
    tot = 0.0
    for c in range(len(means)):
        if means[c] < mstar:
            d = kinf(probs[c][None, :], np.array([mstar]), atoms)[0]
            tot += (mstar - means[c]) / d
    return x * x * tot


def run_all():
    os.makedirs(RESULTS, exist_ok=True)
    log = []
    t0 = time.time()
    for ci, (inst, gname) in enumerate(CONFIGS):
        _, (atoms, probs) = INSTANCES[inst]
        _, gfun, x = GRIDS[gname]
        ends = gfun()
        cols = {}
        if gname == "baba":
            log.append(f"grid of BABA below T: {ends}; epochs (I_(r-1), I_r): {baba_epochs()}")
            print(log[-1], flush=True)
        algos = ALGOS + ([BABA] if gname == "baba" else [])   # BABA runs on its own grid only
        for ai, alg in enumerate(algos):
            t1 = time.time()
            pts, rec, act = simulate(alg, ends, atoms, probs, [SEED, ci, ai])
            cols[alg.name] = rec
            msg = f"{inst}-{gname} {alg.name}: final mean regret {rec[-1].mean():.1f} " \
                  f"({time.time() - t1:.1f} s)"
            if act is not None:
                msg += f"; HY activated after the ends {act}"
            print(msg, flush=True)
            log.append(msg)
        path = os.path.join(RESULTS, f"{inst}-{gname}.csv")
        with open(path, "w", newline="") as fh:
            w = csv.writer(fh)
            head = ["t"]
            for name in cols:
                head += [f"{name}|mean", f"{name}|lo", f"{name}|hi", f"{name}|median"]
            w.writerow(head)
            for i, t in enumerate(pts):
                row = [int(t)]
                for name, rec in cols.items():
                    v = rec[i]
                    m, se = v.mean(), v.std(ddof=1) / math.sqrt(len(v))
                    row += [f"{m:.3f}", f"{m - 1.96 * se:.3f}", f"{m + 1.96 * se:.3f}",
                            f"{np.median(v):.3f}"]
                w.writerow(row)
    total = time.time() - t0
    log.append(f"total {total:.0f} s, T = {T}, R = {R}, seed {SEED}")
    print(log[-1])
    with open(os.path.join(RESULTS, "log.txt"), "w") as fh:
        fh.write("\n".join(log) + "\n")

# ----------------------------------------------------------------------------- figures

STYLE = {  # categorical palette, fixed order; line styles as a second encoding
    "HY": ("#2a78d6", "-", 2.0),
    "IMED (frozen statistics)": ("#eb6834", "--", 1.4),
    "kl-UCB (frozen statistics)": ("#1baf7a", "-.", 1.4),
    "Thompson sampling (batched)": ("#eda100", ":", 1.6),
    "BaSE (knows the grid and $T$)": ("#e87ba4", (0, (5, 1.5, 1, 1.5)), 1.4),
    "BABA (on its own grid)": ("#008300", (0, (3, 1, 1, 1, 1, 1)), 1.4),
}


def shown(name):
    """Legend label of an algorithm: the spelling of paper.tex (KL-UCB); the CSV keys keep the
    names of the classes, so that the saved results stay readable."""
    return name.replace("kl-UCB", "KL-UCB")


def read(inst, gname):
    with open(os.path.join(RESULTS, f"{inst}-{gname}.csv")) as fh:
        rows = list(csv.reader(fh))
    head, data = rows[0], np.array(rows[1:], dtype=float)
    out = {"t": data[:, 0]}
    for j, h in enumerate(head[1:], start=1):
        name, stat = h.split("|")
        out.setdefault(name, {})[stat] = data[:, j]
    return out


def panel(ax, inst, gname, title, ends, stat="mean", logy=False, xlabel=True):
    """One panel: the mean regret with its 95% band (stat="mean") or the median regret
    (stat="median") against the round t; light vertical lines at the batch ends in `ends`."""
    import matplotlib.ticker as mt
    d = read(inst, gname)
    t = d["t"]
    _, (atoms, probs) = INSTANCES[inst]
    _, gfun, x = GRIDS[gname]
    for e in ends:
        ax.axvline(e, color="#c9c8c2", lw=0.6, zorder=0)
    for name, (col, ls, lw) in STYLE.items():
        if name not in d:
            continue
        s = d[name]
        if stat == "mean":
            ax.fill_between(t, s["lo"], s["hi"], color=col, alpha=0.18, lw=0)
        ax.plot(t, s[stat], color=col, ls=ls, lw=lw, label=shown(name))
    cx = constant_Cx(atoms, probs, x)
    ax.plot(t, cx * np.log(t), color="#52514e", lw=0.9, ls=(0, (1, 2)),
            label="$C_x\\log t$ (first-order term)")
    ax.set_xscale("log")
    if logy:
        ax.set_yscale("log")
    ax.set_xlim(10, T)
    if title:
        ax.set_title(title, fontsize=8)
    if xlabel:
        ax.set_xlabel("round $t$", fontsize=8)
    ax.tick_params(labelsize=7)
    ax.grid(True, which="major", color="#ecebe7", lw=0.5)
    ax.xaxis.set_minor_formatter(mt.NullFormatter())


def figure(fname, panels, logy=False, median_row=False):
    """panels: (instance, grid, title, batch ends to mark). With median_row, a second row shows
    the median regret over the runs."""
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    matplotlib.rcParams["pdf.fonttype"] = 42
    n, rows = len(panels), (2 if median_row else 1)
    height = 1.95 * rows + 0.5
    fig, axes = plt.subplots(rows, n, figsize=(2.45 * n + 0.4, height), squeeze=False)
    for j, (inst, gname, title, ends) in enumerate(panels):
        panel(axes[0][j], inst, gname, title, ends, "mean", logy, xlabel=not median_row)
        if median_row:
            panel(axes[1][j], inst, gname, None, ends, "median", logy)
    axes[0][0].set_ylabel("mean regret", fontsize=8)
    if median_row:
        axes[1][0].set_ylabel("median regret", fontsize=8)
    h, lab = axes[0][0].get_legend_handles_labels()
    fig.legend(h, lab, loc="lower center", ncol=3, fontsize=7, frameon=False,
               bbox_to_anchor=(0.5, 0.0))
    fig.tight_layout(rect=(0, 0.48 / height, 1, 1))
    path = os.path.join(HERE, fname)
    fig.savefig(path)
    plt.close(fig)
    print(f"{fname}: {os.path.getsize(path) // 1024} kB")


def normalised_figure(fname):
    """R(t_ell)/log t_ell at the batch ends, against the batch index ell."""
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    matplotlib.rcParams["pdf.fonttype"] = 42
    fig, axes = plt.subplots(1, 2, figsize=(5.6, 2.35), squeeze=False)
    for ax, (inst, gname, title) in zip(axes[0], [
            ("A", "geom", "instance A, geometric grid ($x=1$)"),
            ("A", "poly", "instance A, polynomial grid ($x=1$)")]):
        d = read(inst, gname)
        ends = np.array(GRIDS[gname][1]())
        idx = np.searchsorted(d["t"], ends)
        _, (atoms, probs) = INSTANCES[inst]
        for name, (col, ls, lw) in STYLE.items():
            if name not in d:
                continue
            s = d[name]
            lt = np.log(ends)
            ax.fill_between(np.arange(1, len(ends) + 1), s["lo"][idx] / lt, s["hi"][idx] / lt,
                            color=col, alpha=0.18, lw=0)
            ax.plot(np.arange(1, len(ends) + 1), s["mean"][idx] / lt, color=col, ls=ls, lw=lw,
                    label=shown(name), marker="o", ms=2.5)
        ax.axhline(constant_Cx(atoms, probs, 1.0), color="#52514e", lw=0.9, ls=(0, (1, 2)),
                   label="$C_1$ (first-order constant)")
        ax.set_title(title, fontsize=8)
        ax.set_xlabel("batch index $\\ell$", fontsize=8)
        ax.tick_params(labelsize=7)
        ax.grid(True, color="#ecebe7", lw=0.5)
    axes[0][0].set_ylabel("$\\mathfrak{R}(t_\\ell)/\\log t_\\ell$", fontsize=8)
    h, lab = axes[0][0].get_legend_handles_labels()
    fig.legend(h, lab, loc="lower center", ncol=3, fontsize=7, frameon=False,
               bbox_to_anchor=(0.5, 0.0))
    fig.tight_layout(rect=(0, 0.2, 1, 1))
    path = os.path.join(HERE, fname)
    fig.savefig(path)
    plt.close(fig)
    print(f"{fname}: {os.path.getsize(path) // 1024} kB")


def make_figures():
    none = []
    figure("fig1_x1_grids.pdf", [
        ("A", "const", "constant batches $B_\\ell=100$", none),
        ("A", "poly", "polynomial $t_\\ell=4\\ell^3$", none),
        ("A", "geom", "geometric $t_\\ell=2^{\\ell+1}$", none)])
    normalised_figure("fig2_batch_ends.pdf")
    figure("fig3_long_batches.pdf", [
        ("A", "dexp2", "$t_\\ell=2^{2^\\ell}$ ($x=2$)", grid_dexp2()),
        ("A", "dexp15", "$t_\\ell=\\lceil2^{3\\cdot1.5^{\\ell-1}}\\rceil$ ($x=1.5$)",
         grid_dexp15()),
        ("A", "irr", "irregular (long batches marked)", [200, 6000, 8000])], median_row=True)
    figure("fig4_hard_instance.pdf", [
        ("B", "geom", "instance B, $t_\\ell=2^{\\ell+1}$", none),
        ("B", "dexp2", "instance B, $t_\\ell=2^{2^\\ell}$", grid_dexp2())])
    figure("fig5_binomial_law.pdf", [
        ("C", "geom", "instance C, $t_\\ell=2^{\\ell+1}$", none),
        ("C", "dexp2", "instance C, $t_\\ell=2^{2^\\ell}$", grid_dexp2())], logy=True)
    figure("fig6_baba_grid.pdf", [
        ("A", "baba", "instance A, grid of BABA", grid_baba()),
        ("B", "baba", "instance B, grid of BABA", grid_baba()),
        ("C", "baba", "instance C, grid of BABA", grid_baba())], median_row=True)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--figures", action="store_true", help="figures only, from the CSV files")
    args = ap.parse_args()
    if not args.figures:
        run_all()
    make_figures()
