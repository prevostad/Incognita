"""Constants of the examples of P007 (Section sec:examples). Run: python constants.py > constants.txt

Bernoulli divergence kl, the product-class identity C = sum_a Delta_a / Kinf on explicit instances,
and the bounds of Lemma lem:kinf-unit on a three-point law. Plain Python, no dependency.
"""
import math


def kl(p, q):
    """Bernoulli divergence, conventions 0 log 0 = 0, kl(p, 1) = inf for p < 1."""
    def term(a, b):
        if a == 0:
            return 0.0
        if b == 0:
            return math.inf
        return a * math.log(a / b)
    return term(p, q) + term(1 - p, 1 - q)


def gl_bernoulli(means):
    m = max(means)
    return sum((m - x) / kl(x, m) for x in means if x < m)


print("Bernoulli instance (0.7, 0.5, 0.3)")
for x in (0.5, 0.3):
    print("  arm mean %.1f: Delta = %.1f, kl = %.6f, Delta/kl = %.6f" % (x, 0.7 - x, kl(x, 0.7), (0.7 - x) / kl(x, 0.7)))
print("  C = %.6f" % gl_bernoulli([0.7, 0.5, 0.3]))

print("Gaussian instance N(0,1), N(-1,1)")
k_unknown = 0.5 * math.log(1 + 1.0)
k_known = 1.0 / 2
print("  unknown variance: Kinf = %.6f, C = %.6f" % (k_unknown, 1 / k_unknown))
print("  known variance:   Kinf = %.6f, C = %.6f" % (k_known, 1 / k_known))

print("Three-point law P = (0.2 d_0 + 0.5 d_0.5 + 0.3 d_1), mean m(P) = 0.55, mu = 0.8")
mP, mu = 0.2 * 0 + 0.5 * 0.5 + 0.3 * 1, 0.8
print("  lower bound kl(m(P), mu) = %.6f" % kl(mP, mu))
print("  upper bound log((1-m(P))/(1-mu)) = %.6f" % math.log((1 - mP) / (1 - mu)))

print("UCB bound 13 log T / Delta^2 versus log T / kl, Bernoulli (0.7, 0.5)")
print("  13/Delta^2 = %.1f, 1/kl = %.3f" % (13 / 0.04, 1 / kl(0.5, 0.7)))
print("check 13/4 <= 5 log 2:", 13 / 4, 5 * math.log(2))
print("zeta(3) - 1 =", sum(1 / (t + 1) ** 3 for t in range(1, 200000)))
