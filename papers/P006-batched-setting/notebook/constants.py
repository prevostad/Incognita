"""Numbers of Section sec:examples of P006 (the batched setting).

Not refereed: working notes of the authors of P006-batched-setting.
Run: python constants.py  (writes constants.txt next to this file; no randomness, no download).

1. The Bernoulli instance nu = (Ber(0.7), Ber(0.5)): K_a = kl(0.5, 0.7) and the two bounds of
   Proposition prop:kinf, 2 Delta^2 <= K_a <= log((1 - m_a)/(1 - m*)).
2. The ratios x_l = log t_l / log t_{l-1} of the three example grids with s = 2:
   sequential t_l = s + l - 1, geometric t_l = s 2^(l-1), doubly exponential t_l = s^(2^(l-1)).
"""
import math
import os


def kl(p, q):
    """Bernoulli relative entropy, with 0 log 0 = 0."""
    out = 0.0
    if p > 0:
        out += p * math.log(p / q)
    if p < 1:
        out += (1 - p) * math.log((1 - p) / (1 - q))
    return out


def grids(s, L):
    seq = [0] + [s + l - 1 for l in range(1, L + 1)]
    geo = [0] + [s * 2 ** (l - 1) for l in range(1, L + 1)]
    dbl = [0] + [s ** (2 ** (l - 1)) for l in range(1, L + 1)]
    return {"sequential": seq, "geometric": geo, "doubly exponential": dbl}


def ratios(t):
    # x_1 := 1; x_l := log t_l / log t_{l-1} for l >= 2 (exact integers, float logs)
    return [None, 1.0] + [math.log(t[l]) / math.log(t[l - 1]) for l in range(2, len(t))]


def main():
    lines = []
    ms, ma = 0.7, 0.5
    d = ms - ma
    lines.append("Bernoulli instance (Ber(0.7), Ber(0.5)), suboptimal arm a = 2:")
    lines.append("  2 Delta^2              = %.4f" % (2 * d * d))
    lines.append("  K_a = kl(0.5, 0.7)     = %.4f" % kl(ma, ms))
    lines.append("  log((1-m_a)/(1-m*))    = %.4f" % math.log((1 - ma) / (1 - ms)))
    lines.append("  1 / K_a                = %.4f" % (1 / kl(ma, ms)))
    lines.append("")
    lines.append("Ratios x_l of the example grids, s = 2 (l = 1, ..., 6):")
    for name, t in grids(2, 6).items():
        x = ratios(t)
        lines.append("  %-19s t = %s" % (name, t[1:]))
        lines.append("  %-19s x = %s" % ("", ", ".join("%.4f" % v for v in x[1:])))
    text = "\n".join(lines) + "\n"
    print(text, end="")
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "constants.txt"), "w") as f:
        f.write(text)


if __name__ == "__main__":
    main()
