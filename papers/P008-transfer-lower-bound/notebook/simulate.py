"""Numerical experiments of P008 (Section sec:examples, Figure fig:counts).

Instance: Example ex:bernoulli of the paper. K = 2, target nu = (Ber(0.7), Ber(0.5)), source
nu' = (Ber(0.6), Ber(0.3)), drift bounds L = (0.2, 0.25); arm 2 is suboptimal and informative
(mu'_2 = 0.3 < 0.45 = mu* - L_2). Source strategy: N'^{(T)} = (0, floor(c ln T)), deterministic,
for c in C_VALUES. Lower bound of Theorem thm:main (i): (1 - c K'_2)_+ / K_2 with
K_2 = kl(0.5, 0.7), K'_2 = kl(0.3, 0.45).

Learners (each as in its paper, with the parameters of its theorem):
  ucb1    : UCB1 of Auer, Cesa-Bianchi, Fischer (2002), Figure 1: play each arm once, then the arm
            maximising xbar_j + sqrt(2 ln n / n_j), n the number of plays so far. Ignores the source.
  klucb   : kl-UCB of Cappe et al. (2013), Algorithm 1 with d_BER and f(t) = ln t + 3 ln ln t
            (t >= 3), f(1) = f(2) = f(3) (their Corollary 1): at step t+1 > K, the arm maximising
            max{mu : N_a(t) d_BER(muhat_a(t), mu) <= f(t)}. Ignores the source.
  kltr    : KL-UCB-Transfer of Prevost, Mathieu, Radji, Maillard (2026), Algorithm 1: pull each
            arm once, then at time t > K the arm maximising
            U_a(t) = sup{mu : N_a(t) K_inf(nuhat_a(t), mu) + N'_a K_inf(nuhat'_a, mu - L_a) <= delta_t},
            delta_t = ln t + ln ln t, ties broken uniformly at random, N'_a K_inf := 0 if N'_a = 0.
  minucb  : MIN-UCB of Cheung and Lyu (2024), Algorithm 1 with V = L and delta_t = 1/(2Kt^2)
            (their Theorem 2): see min_ucb_index below. Uses the source, with a two-sided bias
            bound (valid here).
On Bernoulli data the empirical laws are Bernoulli, and K_inf(Ber(p), mu) = kl(p, mu) for
p <= mu < 1, = 0 for mu < p, = infinity for mu >= 1 (setting paper of batched bandits,
Proposition 4.2), so the indices are computed exactly up to the bisection tolerance (2^-40).

Counts: N_a(t) and the empirical means are those after t - 1 rounds when the arm of round t is
chosen. Every horizon T of HORIZONS is a separate experiment (the source size depends on T), with
RUNS runs, the runs of one (learner, c, T) vectorised; seeds are fixed (numpy
generator seeded with [SEED, learner, c, T]).

Usage: python3 simulate.py            -> writes simulate.txt and fig_counts.pdf (about 10 minutes on
                                         4 cores)
       python3 simulate.py --plot     -> redraws fig_counts.pdf from simulate.txt
"""
import math
import sys
from multiprocessing import Pool

import numpy as np

MU = np.array([0.7, 0.5])
MUP = np.array([0.6, 0.3])
L = np.array([0.2, 0.25])
C_VALUES = [0, 5, 10, 25]
HORIZONS = [100, 300, 1000, 3000, 10000, 30000, 100000]
RUNS = 100
SEED = 20261117
LEARNERS = ["ucb1", "klucb", "kltr", "minucb"]
NAMES = {"ucb1": "UCB1", "klucb": "kl-UCB", "kltr": "KL-UCB-Transfer", "minucb": "MIN-UCB"}
ITERS = 40


def kl(p, q):
    """Bernoulli kl(p, q), vectorised, for p in [0,1], q in (0,1)."""
    p = np.clip(p, 0.0, 1.0)
    with np.errstate(divide="ignore", invalid="ignore"):
        a = np.where(p > 0, p * np.log(np.where(p > 0, p, 1.0) / q), 0.0)
        b = np.where(p < 1, (1 - p) * np.log(np.where(p < 1, 1 - p, 1.0) / (1 - q)), 0.0)
    return a + b


def kinf(p, mu):
    """K_inf(Ber(p), mu) on laws on [0,1], for mu < 1: kl(p, mu) if p <= mu, 0 otherwise."""
    m = np.clip(mu, 1e-300, 1 - 1e-16)
    return np.where(mu >= p, kl(p, m), 0.0)


def sup_index(budget, thr):
    """sup{mu in [0,1) : budget(mu) <= thr} for a nondecreasing budget, by bisection on [0, 1].
    The answer is at least the online empirical mean (where the online term vanishes), and the
    bisection keeps lo feasible: budget(0) = 0 <= thr, since K_inf(P, mu) = 0 for mu < m(P) and the
    online term at mu = 0 is N kl(0, 0) = 0 when the empirical mean is 0."""
    lo = np.zeros_like(thr)
    hi = np.ones_like(thr)
    for _ in range(ITERS):
        mid = 0.5 * (lo + hi)
        ok = budget(mid) <= thr
        lo = np.where(ok, mid, lo)
        hi = np.where(ok, hi, mid)
    return lo


def min_ucb_index(S, N, pp, npr, t):
    """MIN-UCB of Cheung and Lyu (arXiv:2405.02594v2), Algorithm 1, (7)-(9), with the valid bias
    bound V = L (two-sided: |mu_k - mu'_k| <= L_k holds on the instance) and delta_t = 1/(2Kt^2)
    (their Theorem 2). Laws on [0,1] are 1/4-sub-Gaussian, hence 1-sub-Gaussian as they assume.
    N, S/N: count and online mean of each arm after t-1 rounds (N_t(a), hat R_t(a));
    npr, pp: offline sizes T_S(a) and offline means hat X(a) (T_S(a) hat X(a) := 0 if T_S(a) = 0)."""
    K = N.shape[1]
    delta = 1.0 / (2 * K * t * t)
    lg = 2 * math.log(2 * t / delta)
    rh = S / N
    ucb = rh + np.sqrt(lg / N)
    ts = npr[None, :].astype(float)
    tot = N + ts
    ucbs = (N * rh + ts * pp) / tot + np.sqrt(lg / tot) + ts / tot * L[None, :]
    return np.minimum(ucb, ucbs)


def run(args):
    learner, c, T = args
    rng = np.random.default_rng([SEED, LEARNERS.index(learner), c, T])
    R, K = RUNS, 2
    npr = np.array([0, int(math.floor(c * math.log(T)))])          # source sizes
    Sp = rng.binomial(npr[None, :], MUP[None, :], size=(R, K)).astype(float)
    pp = np.where(npr > 0, Sp / np.maximum(npr, 1), 0.0)            # source empirical means
    S = np.zeros((R, K))
    N = np.zeros((R, K))
    rows = np.arange(R)
    for t in range(1, T + 1):
        if t <= K:
            arm = np.full(R, t - 1)
        else:
            ph = S / N
            if learner == "ucb1":
                idx = ph + np.sqrt(2 * math.log(t - 1) / N)
            elif learner == "klucb":
                s = max(t - 1, 3)
                f = math.log(s) + 3 * math.log(math.log(s))
                thr = np.full((R, K), f)
                idx = sup_index(lambda m: N * kinf(ph, m), thr)
            elif learner == "kltr":
                d = math.log(t) + math.log(math.log(t))
                thr = np.full((R, K), d)
                idx = sup_index(lambda m: N * kinf(ph, m)
                                + npr[None, :] * kinf(pp, m - L[None, :]), thr)
            else:
                idx = min_ucb_index(S, N, pp, npr, t)
            best = idx.max(axis=1, keepdims=True)
            ties = idx >= best
            u = rng.random((R, K)) * ties
            arm = u.argmax(axis=1)
        y = rng.random(R) < MU[arm]
        S[rows, arm] += y
        N[rows, arm] += 1
    return learner, c, T, N[:, 1].copy()


def bound(c):
    K2 = float(kl(np.array(0.5), np.array(0.7)))
    Kp2 = float(kl(np.array(0.3), np.array(0.45)))
    return max(1 - c * Kp2, 0.0) / K2


def simulate():
    jobs = [(lr, c, T) for lr in LEARNERS for c in C_VALUES for T in HORIZONS]
    jobs.sort(key=lambda j: -j[2])
    with Pool(4) as pool:
        res = [r for r in pool.imap_unordered(run, jobs) if r is not None]
    res.sort(key=lambda r: (LEARNERS.index(r[0]), r[1], r[2]))
    with open("simulate.txt", "w") as f:
        f.write("# learner c T runs mean(N_2(T)) sd(N_2(T)) mean/lnT halfwidth95/lnT bound\n")
        for lr, c, T, n2 in res:
            m, sd = n2.mean(), n2.std(ddof=1)
            f.write("%s %d %d %d %.3f %.3f %.4f %.4f %.4f\n"
                    % (lr, c, T, len(n2), m, sd, m / math.log(T),
                       1.96 * sd / math.sqrt(len(n2)) / math.log(T), bound(c)))
        f.write("# raw: learner c T N_2(T) of each run\n")
        for lr, c, T, n2 in res:
            f.write("raw %s %d %d %s\n" % (lr, c, T, " ".join("%d" % v for v in n2)))


def plot():
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    data = {}
    for line in open("simulate.txt"):
        if line.startswith("#") or line.startswith("raw"):
            continue
        lr, c, T, _, _, _, r, h, _ = line.split()
        data.setdefault((lr, int(c)), []).append((int(T), float(r), float(h)))
    fig, axes = plt.subplots(1, len(C_VALUES), figsize=(13, 3.4), sharey=True)
    styles = {"ucb1": ("tab:gray", "s"), "klucb": ("tab:blue", "o"),
              "kltr": ("tab:red", "^"), "minucb": ("tab:green", "D")}
    for ax, c in zip(axes, C_VALUES):
        for lr in LEARNERS:
            if (lr, c) not in data:
                continue
            pts = sorted(data[(lr, c)])
            T = np.array([p[0] for p in pts])
            r = np.array([p[1] for p in pts])
            h = np.array([p[2] for p in pts])
            col, mk = styles[lr]
            ax.plot(T, r, marker=mk, color=col, label=NAMES[lr], ms=4)
            ax.fill_between(T, r - h, r + h, color=col, alpha=0.2)
        if bound(c) > 0:
            ax.axhline(bound(c), color="k", ls="--", label="asymptotic lower bound")
        else:
            ax.text(0.97, 0.03, "lower bound: 0", transform=ax.transAxes, ha="right",
                    va="bottom", fontsize=8)
        ax.set_xscale("log")
        ax.set_yscale("log")
        ax.set_title("$c=%d$" % c)
        ax.set_xlabel("horizon $T$")
    axes[0].set_ylabel(r"$\mathbb{E}[N_2(T)]/\ln T$")
    h, lab = axes[0].get_legend_handles_labels()
    fig.legend(h, lab, loc="lower center", ncol=len(lab), fontsize=9, frameon=False)
    fig.tight_layout(rect=(0, 0.08, 1, 1))
    fig.savefig("fig_counts.pdf")


if __name__ == "__main__":
    if "--plot" not in sys.argv:
        simulate()
    plot()
