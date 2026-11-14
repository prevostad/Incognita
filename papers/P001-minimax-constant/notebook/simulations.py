"""Simulations du papier (legeres : PC lent). Recompenses gaussiennes de variance sigma^2 = 1 (connue).

E1 : K = 2, T = 10^4, pire cas local : moyennes +-v/sqrt(T) (ecart 2v/sqrt(T)), regret / sqrt(T).
E2 : K = 10, T = 10^4, instances a une aiguille (ecart a sqrt(K/T)), regret / sqrt(KT), contre l'enveloppe bayesienne.
E3 : K = 2, ecart fixe 0.2, T in {10^3, 10^4, 10^5} : comportement probleme-dependant.

Algorithmes : OPT (K = 2 : politique de Bayes du prior le moins favorable, table de seuils HJB, plus un test
d'elimination pour les grands ecarts), MOSS, KL-UCB++ (minimax en ordre), KL-UCB, Thompson, IMED (optimaux
probleme-dependants). Sortie : resultats.json.
"""
import json, time, sys
import numpy as np

SIG = 1.0
TAB = np.load("seuils_K2.npz")
THR, EPS = TAB["thr"], float(TAB["eps"])
NGRID = int(round(1 / EPS))


def logp(x):
    return np.log(np.maximum(x, 1.0))


def choose(alg, S, N, t, T, K, rng, st):
    R = S.shape[0]
    if t < K and alg != "OPT":
        return np.full(R, t)
    mu = S / np.maximum(N, 1)
    if alg == "MOSS":
        idx = mu + SIG * np.sqrt(4.0 / N * logp(T / (K * N)))
    elif alg == "KL-UCB++":
        y = T / (K * N)
        g = logp(y * (1.0 + logp(y) ** 2))
        idx = mu + SIG * np.sqrt(2.0 * g / N)
    elif alg == "KL-UCB":
        tt = max(t, 3)
        idx = mu + SIG * np.sqrt(2.0 * (np.log(tt) + np.log(np.log(tt))) / N)
    elif alg == "TS":
        idx = mu + SIG * rng.standard_normal(mu.shape) / np.sqrt(N)
    elif alg == "IMED":
        best = mu.max(1, keepdims=True)
        idx = -(N * (best - mu) ** 2 / (2 * SIG ** 2) + np.log(N))
    elif alg == "OPT":
        return choose_opt(S, N, T, st)
    idx = idx + 1e-12 * rng.random(idx.shape)          # departage aleatoire
    return idx.argmax(1)


def choose_opt(S, N, T, st):
    """K = 2. Phase 1 : alternance jusqu'a ceil(eps T) tirages par bras. Phase 2 : tirer 1 ssi U >= u*(tau1, tau2).
    Test d'elimination (rayons de type MOSS, niveau A) actif tout le temps ; un bras elimine ne l'est plus jamais."""
    R = S.shape[0]
    N1, N2 = N[:, 0], N[:, 1]
    mu = S / np.maximum(N, 1)
    rad = SIG * np.sqrt(2.0 / np.maximum(N, 1) * (st["A"] + 2 * logp(T / (2 * np.maximum(N, 1)))))
    ok = N.min(1) >= 1
    st["elim"] = np.where(ok & (mu[:, 0] - rad[:, 0] > mu[:, 1] + rad[:, 1]), 1, st["elim"])   # bras 1 (indice 1) elimine
    st["elim"] = np.where(ok & (mu[:, 1] - rad[:, 1] > mu[:, 0] + rad[:, 0]), 0, st["elim"])
    m0 = int(np.ceil(EPS * T))
    phase1 = N.min(1) < m0
    a1 = np.where(N1 <= N2, 0, 1)
    k = np.clip(np.rint((N1 + N2) / (EPS * T)).astype(int), 2, NGRID - 1)
    i = np.clip(np.rint(N1 / (EPS * T)).astype(int), 1, k - 1)
    thr = THR[k, i]
    with np.errstate(invalid="ignore", divide="ignore"):
        U = (S[:, 0] * N2 - S[:, 1] * N1) / ((N1 + N2) * SIG * np.sqrt(T))
    a2 = np.where(U >= thr, 0, 1)
    a = np.where(phase1, a1, a2)
    a = np.where(st["elim"] == 1, 0, a)
    a = np.where(st["elim"] == 0, 1, a)
    return a


def run(alg, means, T, runs, seed):
    rng = np.random.default_rng(seed)
    K = len(means)
    M = np.tile(np.asarray(means, float), (runs, 1))
    for r in range(runs):                                   # position aleatoire des bras
        rng.shuffle(M[r])
    S = np.zeros((runs, K)); N = np.zeros((runs, K))
    st = {"elim": np.full(runs, -1), "A": 4.0}
    rr = np.arange(runs)
    for t in range(T):
        a = choose(alg, S, N, t, T, K, rng, st)
        S[rr, a] += M[rr, a] + SIG * rng.standard_normal(runs)
        N[rr, a] += 1
    gaps = M.max(1, keepdims=True) - M
    reg = (gaps * N).sum(1)
    return reg


def main():
    out = {}
    t0 = time.time()
    # ---------------- E1
    T, runs = 10_000, 600
    vs = [0.25, 0.5, 0.75, 1.0, 1.25, 1.5, 1.75, 2.0, 2.5, 3.0, 4.0, 6.0, 10.0]
    algs = ["OPT", "MOSS", "KL-UCB++", "KL-UCB", "TS", "IMED"]
    E1 = {a: [] for a in algs}
    for a in algs:
        for j, v in enumerate(vs):
            reg = run(a, [v / np.sqrt(T), -v / np.sqrt(T)], T, runs, seed=100 + j) / np.sqrt(T)
            E1[a].append((v, float(reg.mean()), float(reg.std() / np.sqrt(runs))))
        w = max(E1[a], key=lambda x: x[1])
        print(f"E1 {a:9s} pire cas {w[1]:.3f} +- {w[2]:.3f} en v = {w[0]}  ({time.time()-t0:.0f} s)", flush=True)
    out["E1"] = {"T": T, "runs": runs, "res": E1}
    # ---------------- E2
    K, T, runs = 10, 10_000, 200
    As = [0.5, 1.0, 1.5, 2.0, 2.5, 3.0, 4.0, 6.0]
    E2 = {a: [] for a in algs[1:]}
    for a in algs[1:]:
        for j, aa in enumerate(As):
            means = [aa * np.sqrt(K / T)] + [0.0] * (K - 1)
            reg = run(a, means, T, runs, seed=200 + j) / np.sqrt(K * T)
            E2[a].append((aa, float(reg.mean()), float(reg.std() / np.sqrt(runs))))
        w = max(E2[a], key=lambda x: x[1])
        print(f"E2 {a:9s} pire cas aiguille {w[1]:.3f} +- {w[2]:.3f} en a = {w[0]}  ({time.time()-t0:.0f} s)", flush=True)
    out["E2"] = {"K": K, "T": T, "runs": runs, "res": E2}
    # ---------------- E3
    gap, Ts, runs = 0.2, [1_000, 10_000, 100_000], 100
    E3 = {a: [] for a in algs}
    for a in algs:
        for j, T in enumerate(Ts):
            reg = run(a, [gap / 2, -gap / 2], T, runs, seed=300 + j)
            E3[a].append((T, float(reg.mean()), float(reg.std() / np.sqrt(runs))))
        print(f"E3 {a:9s} " + "  ".join(f"T={T}: {m:.1f}+-{s:.1f}" for T, m, s in E3[a]) + f"  ({time.time()-t0:.0f} s)", flush=True)
    out["E3"] = {"gap": gap, "runs": runs, "res": E3}
    json.dump(out, open("resultats.json", "w"), indent=1)
    print(f"total {time.time()-t0:.0f} s")


if __name__ == "__main__":
    main()
