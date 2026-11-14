"""Figure des experiences (3 panneaux) + enveloppe bayesienne de E2 (limite de diffusion, K = 10).
Palette : six premieres teintes de la palette de reference (ordre fixe, une couleur par algorithme)."""
import json, sys
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

def V_K(a, K, n=60_000, dl=2e-3, seed=12345):
    """Risque de Bayes optimal (limite T -> inf) du prior a une aiguille, /sqrt(KT) : copie de scripts/aiguille_K.py
    (representation par niveaux, subordinateurs inverses gaussiens)."""
    rng = np.random.default_rng(seed)
    mu = a / 2
    M = rng.exponential(1.0, n) / a
    S = np.zeros(n); sJ = np.zeros(n); reg = np.full(n, np.nan); l = 0.0
    alive = np.ones(n, bool)
    while alive.any():
        l += dl
        idx = np.nonzero(alive)[0]
        step = np.minimum(dl, np.maximum(M[idx] - (l - dl), 0))
        pos = step > 0
        dS = np.zeros(idx.size); dJ = np.zeros(idx.size)
        dS[pos] = rng.wald((K - 1) * step[pos] / mu, ((K - 1) * step[pos]) ** 2)
        dJ[pos] = rng.wald(step[pos] / mu, step[pos] ** 2)
        S0, J0 = S[idx].copy(), sJ[idx].copy()
        S[idx] += dS; sJ[idx] += dJ
        over = S[idx] + sJ[idx] >= K
        frac = np.where(over, (K - S0 - J0) / np.maximum(dS + dJ, 1e-300), 1.0)
        Send = S0 + frac * dS
        done = over | (M[idx] <= l)
        reg[idx[done]] = np.where(over[done], Send[done], S[idx[done]])
        alive[idx[done]] = False
    r = a * reg / K
    return r.mean(), r.std() / np.sqrt(n)

COL = {"OPT": "#2a78d6", "MOSS": "#eb6834", "KL-UCB++": "#1baf7a", "KL-UCB": "#eda100", "TS": "#e87ba4", "IMED": "#008300"}
LAB = {"OPT": r"Opt$_2$ (ours)", "MOSS": "MOSS", "KL-UCB++": "KL-UCB++", "KL-UCB": "KL-UCB", "TS": "Thompson", "IMED": "IMED"}
MK = {"OPT": "o", "MOSS": "s", "KL-UCB++": "^", "KL-UCB": "v", "TS": "D", "IMED": "P"}
INK, INK2, GRID = "#0b0b0b", "#52514e", "#e4e3df"

d = json.load(open("resultats.json"))
plt.rcParams.update({"font.size": 8, "axes.edgecolor": INK2, "axes.labelcolor": INK, "xtick.color": INK2,
                     "ytick.color": INK2, "axes.linewidth": 0.6, "legend.frameon": False})
fig, ax = plt.subplots(1, 3, figsize=(10.5, 3.3))

# (a) K = 2, pire cas local
for a, rows in d["E1"]["res"].items():
    v, m, s = map(np.array, zip(*rows))
    ax[0].plot(2 * v, m, color=COL[a], marker=MK[a], ms=3.5, lw=1.4, label=LAB[a])
    ax[0].fill_between(2 * v, m - 2 * s, m + 2 * s, color=COL[a], alpha=0.12, lw=0)
ax[0].axhline(0.6373, color=INK2, ls="--", lw=0.9)
ax[0].text(0.52, 1.04, r"dashed: $V_2\approx0.637$ (optimal, $T\to\infty$)", color=INK2, ha="left", fontsize=7)
ax[0].set_xscale("log"); ax[0].set_xlabel(r"gap $\times\sqrt{T}$"); ax[0].set_ylabel(r"regret$/\sqrt{T}$")
ax[0].set_title(r"(a) $K=2$, $T=10^4$: worst case", color=INK)

# (b) K = 10, aiguille
aa = np.array([0.5, 0.75, 1.0, 1.25, 1.5, 1.75, 2.0, 2.5, 3.0, 4.0, 5.0, 6.0])
env = np.array([V_K(x, 10, n=30_000)[0] for x in aa])
for a, rows in d["E2"]["res"].items():
    x, m, s = map(np.array, zip(*rows))
    ax[1].plot(x, m, color=COL[a], marker=MK[a], ms=3.5, lw=1.4, label=LAB[a])
    ax[1].fill_between(x, m - 2 * s, m + 2 * s, color=COL[a], alpha=0.12, lw=0)
ax[1].plot(aa, env, color=INK, ls="--", lw=1.1)
ax[1].text(3.6, 0.80, "myopic Bayes policy\n(optimal if Rodman applies)", color=INK, fontsize=7)
Kb = 10
hb = -(1 / Kb) * np.log(1 / Kb) - (1 - 1 / Kb) * np.log(1 - 1 / Kb)
lam = np.exp(-Kb * hb / (Kb - 1))
af = np.linspace(0.3, 6.2, 200)
beta = af ** 2 * Kb / (2 * (Kb - 1))
ax[1].plot(af, af * lam * (1 - np.exp(-beta)) / beta, color=INK2, ls="-", lw=0.9)
ax[1].text(4.1, 0.44, "proved lower bound\nfor this prior", color=INK2, fontsize=7)
ax[1].set_xlabel(r"needle height $a$ (gap $a\sqrt{K/T}$)"); ax[1].set_ylabel(r"regret$/\sqrt{KT}$")
ax[1].set_title(r"(b) $K=10$, one good arm", color=INK)

# (c) ecart fixe
for a, rows in d["E3"]["res"].items():
    T, m, s = map(np.array, zip(*rows))
    ax[2].errorbar(T, m, yerr=2 * s, color=COL[a], marker=MK[a], ms=3.5, lw=1.4, capsize=0, label=LAB[a])
TT = np.logspace(3, 5, 50)
ax[2].plot(TT, 2 * np.log(TT) / 0.2, color=INK2, ls="-.", lw=0.9)
ax[2].text(1.2e3, 2 * np.log(1.2e3) / 0.2 + 6, r"$2\log T/\Delta$", color=INK2, fontsize=7)
ax[2].set_xscale("log"); ax[2].set_xlabel(r"horizon $T$"); ax[2].set_ylabel("regret")
ax[2].set_title(r"(c) $K=2$, fixed gap $\Delta=0.2$", color=INK)

for x in ax:
    x.grid(True, color=GRID, lw=0.5); x.set_axisbelow(True)
    for sp in ("top", "right"):
        x.spines[sp].set_visible(False)
h, l = ax[0].get_legend_handles_labels()
fig.legend(h, l, loc="upper center", ncol=6, bbox_to_anchor=(0.5, 1.02))
fig.tight_layout(rect=(0, 0, 1, 0.93))
fig.savefig("../figures/experiences.pdf")
json.dump({"a": aa.tolist(), "env": env.tolist()}, open("enveloppe_K10.json", "w"))
print("enveloppe V_10(a):", np.round(env, 3).tolist(), " max", round(env.max(), 3))
