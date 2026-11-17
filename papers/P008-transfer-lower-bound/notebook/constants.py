"""Constants of the lower bound of P008 on an explicit Bernoulli instance (Section sec:examples).

On laws on [0,1], K_inf(Ber(p), mu) = kl(p, mu) for p <= mu < 1 (setting paper of batched bandits,
Proposition 4.2(iv)). The lower bound of Theorem thm:main for deterministic sizes
N'_a(T) = floor(c ln T) is (1 - c K'_a)_+ / K_a.

The script also checks the construction of the alternative (Lemma lem:alternative) for Bernoulli
alternatives: the means of Q and Q' fall in the windows of the proof.

Run: python3 constants.py > constants.txt
"""
import math


def kl(p, q):
    """Bernoulli divergence kl(p, q) for p in [0,1], q in (0,1)."""
    out = 0.0
    if p > 0:
        out += p * math.log(p / q)
    if p < 1:
        out += (1 - p) * math.log((1 - p) / (1 - q))
    return out


def main():
    mu = [0.7, 0.5]        # target means, Bernoulli laws
    mup = [0.6, 0.3]       # source means, Bernoulli laws
    L = [0.2, 0.25]        # drift bounds
    a = 1                  # the suboptimal arm (arm 2 in the paper's numbering)
    mustar = max(mu)
    print("Instance: target Ber(%.2f), Ber(%.2f); source Ber(%.2f), Ber(%.2f); L = (%.2f, %.2f)"
          % (mu[0], mu[1], mup[0], mup[1], L[0], L[1]))
    for k in range(2):
        print("  arm %d: |mu - mu'| = %.2f < L = %.2f: %s; mu - mu' = %.2f < L: %s"
              % (k + 1, abs(mu[k] - mup[k]), L[k], abs(mu[k] - mup[k]) < L[k],
                 mu[k] - mup[k], mu[k] - mup[k] < L[k]))
    level = mustar - L[a]
    K = kl(mu[a], mustar)
    Kp = kl(mup[a], level) if mup[a] <= level else 0.0
    print("mu* - L_2 = %.2f, mu'_2 = %.2f (improvement case: %s)" % (level, mup[a], mup[a] < level))
    print("K_2  = kl(%.2f, %.2f) = %.6f, 1/K_2 = %.6f" % (mu[a], mustar, K, 1 / K))
    print("K'_2 = kl(%.2f, %.2f) = %.6f, 1/K'_2 = %.6f" % (mup[a], level, Kp, 1 / Kp))
    print()
    print("Deterministic sizes N'_2(T) = floor(c ln T): lower bound (1 - c K'_2)_+ / K_2")
    print("%8s %14s %14s" % ("c", "(1-cK')_+", "bound"))
    for c in [0.0, 1.0, 2.0, 5.0, 10.0, 1 / Kp, 20.0]:
        v = max(0.0, 1 - c * Kp)
        print("%8.4f %14.6f %14.6f" % (c, v, v / K))
    print()
    print("Randomised sizes: N'_2 = floor(c ln T) w.p. 1/2, 0 otherwise; E N'_2 / ln T -> c/2:")
    for c in [2.0, 1 / Kp, 2 / Kp]:
        v = max(0.0, 1 - c / 2 * Kp)
        print("  c = %.4f: bound (1 - (c/2) K')_+ / K = %.6f" % (c, v / K))
    print()
    # Alternative of Lemma lem:alternative, case mu'_a <= mu* - L_a, with Bernoulli laws:
    # Q' = Ber(level + eta'), Q = Ber(mu* + eta), eta < m(Q') + L_a - mu*.
    for eps in [1e-1, 1e-2, 1e-3]:
        # choose Bernoulli alternatives whose divergences are within eps of the K_inf
        e1 = 1e-1
        while kl(mup[a], level + e1) > Kp + eps:
            e1 /= 2
        qp = level + min(e1, L[a] / 2)
        e2 = (qp + L[a] - mustar) / 2
        while kl(mu[a], mustar + e2) > K + eps:
            e2 /= 2
        q = mustar + e2
        ok = (q > mustar and abs(q - qp) < L[a] and q - qp < L[a]
              and kl(mup[a], qp) <= Kp + eps and kl(mu[a], q) <= K + eps)
        print("eps = %g: m(Q') = %.6f, m(Q) = %.6f, |m(Q) - m(Q')| = %.6f < L_2: %s; "
              "KL' - K' = %.2e, KL - K = %.2e; all conditions: %s"
              % (eps, qp, q, abs(q - qp), abs(q - qp) < L[a], kl(mup[a], qp) - Kp, kl(mu[a], q) - K, ok))
    print()
    # Boundary instance: mu'_2 = mu* - L_2.
    mup_b = level
    print("Boundary instance mu'_2 = %.2f = mu* - L_2: K'_2 = kl(mu'_2, mu'_2) = %.1f" % (mup_b, kl(mup_b, level)))


if __name__ == "__main__":
    main()
