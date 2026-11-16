"""Exact check of the source-phase divergence identity (P003, notebook; not refereed).

Bernoulli source laws, K = 2 arms. The source data D = (N', first N'_k values of each stack).
We enumerate all stack prefixes of length <= T' (values in {0,1}) and compute the law of D exactly
under nu' and under an alternative nu~', then compare KL(P^D, P~^D) with
sum_k E[N'_k] kl(nu'_k, nu~'_k).

Rules checked:
  * "greedy": a prior bandit game over T' rounds that pulls arm 1 first, then at each round the
    arm with the larger empirical mean (ties: arm 1), with one forced pull of arm 2 at round 2:
    a size rule (Lemma lem:prior-game of the paper), so the identity must hold;
  * "stop_on_one": a prior game on arm 1 only that stops at the first 1 (or after T' rounds):
    a stopping time, so a size rule;
  * "lookahead": N'_1 = 1 if X'_{1,2} = 1, else 2 (not a size rule): the identity fails,
    KL = 2 kl(p, q) while sum E N' kl = (2 - p) kl(p, q).
"""

import itertools
import math


def kl(p, q):
    s = 0.0
    if p > 0:
        s += p * math.log(p / q)
    if p < 1:
        s += (1 - p) * math.log((1 - p) / (1 - q))
    return s


def law_of_D(rule, p, depth):
    """p = (p_1, p_2): Bernoulli parameters of the two source stacks. Returns dict D -> prob."""
    law = {}
    for x1 in itertools.product((0, 1), repeat=depth):
        for x2 in itertools.product((0, 1), repeat=depth):
            w = 1.0
            for v in x1:
                w *= p[0] if v else 1 - p[0]
            for v in x2:
                w *= p[1] if v else 1 - p[1]
            n = rule(x1, x2)
            d = (n, x1[: n[0]], x2[: n[1]])
            law[d] = law.get(d, 0.0) + w
    return law


def greedy(Tp):
    def rule(x1, x2):
        c = [0, 0]
        s = [0, 0]
        for t in range(Tp):
            if t == 0:
                a = 0
            elif t == 1:
                a = 1
            else:
                m = [s[i] / c[i] for i in range(2)]
                a = 0 if m[0] >= m[1] else 1
            v = (x1, x2)[a][c[a]]
            c[a] += 1
            s[a] += v
        return tuple(c)

    return rule


def stop_on_one(Tp):
    def rule(x1, x2):
        for j in range(Tp):
            if x1[j] == 1:
                return (j + 1, 0)
        return (Tp, 0)

    return rule


def lookahead(x1, x2):
    return (1, 0) if x1[1] == 1 else (2, 0)


def check(name, rule, depth, p, q):
    P = law_of_D(rule, p, depth)
    Q = law_of_D(rule, q, depth)
    kl_D = sum(w * math.log(w / Q[d]) for d, w in P.items() if w > 0)
    EN = [sum(w * d[0][k] for d, w in P.items()) for k in range(2)]
    rhs = EN[0] * kl(p[0], q[0]) + EN[1] * kl(p[1], q[1])
    print(f"{name:12s} p={p} q={q}: KL(P^D,Q^D)={kl_D:.12f}  sum E[N'_k] kl={rhs:.12f}  "
          f"E N'={EN[0]:.6f},{EN[1]:.6f}  diff={kl_D - rhs:+.2e}")


if __name__ == "__main__":
    for p, q in [((0.3, 0.6), (0.5, 0.4)), ((0.8, 0.2), (0.7, 0.9))]:
        check("greedy T'=5", greedy(5), 5, p, q)
        check("stop_on_one", stop_on_one(5), 5, p, q)
        check("lookahead", lookahead, 2, p, q)
        print(f"{'':12s} lookahead prediction: 2 kl(p1,q1)={2 * kl(p[0], q[0]):.12f}, "
              f"(2-p1) kl(p1,q1)={(2 - p[0]) * kl(p[0], q[0]):.12f}")
