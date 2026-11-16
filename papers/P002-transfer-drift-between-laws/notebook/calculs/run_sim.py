"""Driver of the experiment of the section "Numerical experiments" (Table 3 of version 2).

Runs sim.run for the three learners on the two-armed instance, horizon T = 10^4, source rates
c = 5 and c = 25 (N'_k = floor(c log T)), RUNS independent runs per configuration (seeds
1..RUNS, the same seeds for every configuration), on 4 processes, and writes sim.txt: one line
per run, then the mean of N_2(T), its standard error, and D_2(c) log T for comparison.
Usage: python3 run_sim.py [RUNS]   (RUNS = 40: about an hour on 4 cores)
"""
import os
import sys
import time
import numpy as np
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sim

T = 10_000
RUNS = int(sys.argv[1]) if len(sys.argv) > 1 else 40
CONFIGS = [('klucb', 0.0), ('kltr', 5.0), ('tv', 5.0), ('kltr', 25.0), ('tv', 25.0)]
# first-order constants D_2(c) of the paper (Example ex:no-drift, Table tab:no-drift)
D = {('klucb', 0.0): 6.0285, ('kltr', 5.0): 6.0285, ('tv', 5.0): 4.5595,
     ('kltr', 25.0): 6.0285, ('tv', 25.0): 0.0}


def job(args):
    kind, c, seed = args
    t0 = time.time()
    n2 = sim.run(kind, c, T, seed)
    return kind, c, seed, int(n2), time.time() - t0


if __name__ == '__main__':
    jobs = [(k, c, s) for (k, c) in CONFIGS for s in range(1, RUNS + 1)]
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'sim.txt')
    res = {}
    with Pool(4) as pool, open(out + '.partial', 'w') as f:
        for kind, c, seed, n2, dt in pool.imap_unordered(job, jobs):
            res.setdefault((kind, c), []).append(n2)
            f.write(f'{kind} {c} {seed} {n2} {dt:.1f}s\n')
            f.flush()
    lines = [f'T = {T}, log T = {np.log(T):.4f}, runs per configuration = {RUNS}',
             'learner  c  N2_prime  mean N_2(T)  std.err.  min  max  D_2(c) log T']
    for (kind, c) in CONFIGS:
        v = np.array(res[(kind, c)])
        lines.append(f'{kind:6s} {c:4.0f} {int(np.floor(c * np.log(T))):4d} '
                     f'{v.mean():9.2f} {v.std(ddof=1) / np.sqrt(len(v)):7.2f} '
                     f'{v.min():4d} {v.max():4d} {D[(kind, c)] * np.log(T):9.2f}')
    with open(out, 'w') as f:
        f.write('\n'.join(lines) + '\n')
        f.write(open(out + '.partial').read())
    os.remove(out + '.partial')
    print('\n'.join(lines))
