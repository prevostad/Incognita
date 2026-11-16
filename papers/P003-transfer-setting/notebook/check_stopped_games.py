"""Exhaustive check of Proposition prop:stopped-games on binary stacks (not refereed).

Stacks take values in {0,1} (all points of the finite data space, i.e. pointwise statements), no
randomisation U'. A size rule bounded by `top` is a map N' from the data space {0,1}^{B(top)} to
the boxes n <= top with {N'=n} measurable for the values in B(n). We generate random size rules
(processing the boxes n in a random order and giving each a random union of the still free atoms
of the values in B(n); the remaining points go to `top`) and test, by a recursive search, whether
a sequential policy (choose the next arm from the values seen, stop when the event {N'=m} holds)
reaches N' at every point.

Prediction: for K=2 every generated rule is sequential (part (b)); for K=3 the cyclic rule of
part (c) is not, and neither are some random rules.
Run: python3 check_stopped_games.py > check_stopped_games.txt
"""
import itertools
import random


def boxes(top):
    return list(itertools.product(*[range(t + 1) for t in top]))


def cells(n):
    return [(k, j) for k in range(len(n)) for j in range(n[k])]


def random_rule(top, rng):
    allcells = cells(top)
    points = list(itertools.product([0, 1], repeat=len(allcells)))
    idx = {c: i for i, c in enumerate(allcells)}
    rule = {}
    order = boxes(top)
    rng.shuffle(order)
    for n in order:
        if n == tuple(top):
            continue
        cn = cells(n)
        atoms = {}
        for x in points:
            atoms.setdefault(tuple(x[idx[c]] for c in cn), []).append(x)
        for key, pts in atoms.items():
            if all(x not in rule for x in pts) and rng.random() < 0.3:
                for x in pts:
                    rule[x] = n
    for x in points:
        rule.setdefault(x, tuple(top))
    return rule, allcells, idx


def is_size_rule(rule, allcells, idx, top):
    for n in boxes(top):
        cn = cells(n)
        atoms = {}
        for x, v in rule.items():
            atoms.setdefault(tuple(x[idx[c]] for c in cn), set()).add(v == n)
        if any(len(s) > 1 for s in atoms.values()):
            return False
    return True


def sequential(rule, allcells, idx, top):
    K = len(top)

    def ok(m, pts):
        # every point of pts agrees on B(m) and has N' >= m
        vals = {rule[x] == m for x in pts}
        if vals == {True}:
            return True
        if True in vals:
            return False  # cannot happen for a size rule
        for k in range(K):
            if m[k] >= top[k]:
                continue
            m2 = tuple(m[i] + (i == k) for i in range(K))
            if any(any(rule[x][i] < m2[i] for i in range(K)) for x in pts):
                continue
            c = (k, m[k])
            groups = {}
            for x in pts:
                groups.setdefault(x[idx[c]], []).append(x)
            if all(ok(m2, g) for g in groups.values()):
                return True
        return False

    return ok(tuple(0 for _ in top), list(rule))


def cyclic_rule():
    top = (1, 1, 1)
    allcells = cells(top)
    idx = {c: i for i, c in enumerate(allcells)}
    rule = {}
    for x in itertools.product([0, 1], repeat=3):
        b1, b2, b3 = x
        if b1 == 1 and b2 == 0:
            v = (1, 1, 0)
        elif b2 == 1 and b3 == 0:
            v = (0, 1, 1)
        elif b3 == 1 and b1 == 0:
            v = (1, 0, 1)
        else:
            v = (1, 1, 1)
        rule[x] = v
    return rule, allcells, idx, top


def main():
    rng = random.Random(20261116)
    for top, trials in [((2, 2), 3000), ((3, 2), 1000), ((1, 1, 1), 3000), ((2, 1, 1), 1000)]:
        bad = seq = 0
        for _ in range(trials):
            rule, allcells, idx = random_rule(top, rng)
            if not is_size_rule(rule, allcells, idx, top):
                bad += 1
                continue
            seq += sequential(rule, allcells, idx, top)
        print("K=%d, top=%s: %d random size rules, %d sequential, %d not sequential (%d generation errors)"
              % (len(top), top, trials - bad, seq, trials - bad - seq, bad))
    rule, allcells, idx, top = cyclic_rule()
    print("cyclic rule of part (c): size rule %s, sequential %s"
          % (is_size_rule(rule, allcells, idx, top), sequential(rule, allcells, idx, top)))


if __name__ == "__main__":
    main()
