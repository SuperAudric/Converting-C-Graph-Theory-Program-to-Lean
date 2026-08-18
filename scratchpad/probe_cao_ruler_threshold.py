"""probe_cao_ruler_threshold.py -- is the s=5 threshold real, or one lucky ruler?

probe_cao_ruler_curve2.py, m=10 multipede base (rigid, ten size-2 MIXED foot pairs), leak-free
families closed under prod_{i in S} Sym(cell_i):

    control (1 copy, not closed)  -> SPLIT + whole graph discrete   [harness works]
    s = 1,2,3,4                   -> merged
    s = 5,6                       -> SPLIT + whole graph discrete

A threshold in `s` is surprising -- MORE symmetrisation should not help -- so before it goes in the
record it has to survive: independent rulers, independent subsets `S` of the same size, independent
multipede bases, and independent WL hash seeds.

⚠ DIRECTION OF THE HASHING ERROR, and it matters here.  `wl2_diag` hashes the round's multiset, so
collisions can only MERGE colour classes: the computed colouring is COARSER than true 2-WL.  Hence
  SPLIT  is sound  (true 2-WL splits at least as much),
  merged is not    (it could be a collision artefact) -- which is why every `merged` row is re-run
                    with several seeds below.
"""

import random
import sys

import networkx as nx
import numpy as np

from probe_cao_multipede_small import gf2_rank, multipede_adj, wl2_diag, cell_sizes
from probe_cao_ruler_curve import partial_steiner, hypergraph_rigid, rigid_ruler
from probe_cao_ruler_curve2 import find_base, build_subset


def run(nb, Ab, pairs, S, R, seeds=(7,)):
    """True iff every attached pair splits, under every WL hash seed."""
    n, A = build_subset(nb, Ab, pairs, S, R, closed=True)
    ok = True
    for sd in seeds:
        d = wl2_diag(n, A, seed=sd)
        sz = {}
        for i in S:
            for v in pairs[i]:
                sz[d[v]] = sz.get(d[v], 0) + 1
        if any(x > 1 for x in sz.values()):
            ok = False
    return ok, n


if __name__ == '__main__':
    smax = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    nbases = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    m = 10
    print(f'=== is the ruler threshold real?  m={m}, {nbases} bases, '
          f'3 rulers x 3 subsets per (base, s) ===', flush=True)
    print('  a row reads:  s -> (#split / #trials)   [SPLIT is sound; merged re-checked '
          'over 3 WL seeds]\n', flush=True)

    for b in range(nbases):
        rng = random.Random(1000 + 137 * b)
        got = find_base(m, rng)
        if got is None:
            print(f'  base {b}: none found'); continue
        cons, nb, Ab, pairs = got
        print(f'  base {b}: n={nb} c={len(cons)} pairs={len(pairs)}', flush=True)
        for s in range(1, smax + 1):
            k = 2 * s
            tot = 0
            hit = 0
            nn = 0
            for r in range(3):
                R = rigid_ruler(max(k, 7), rng)
                for t in range(3):
                    S = rng.sample(range(len(pairs)), s)
                    ok, nn = run(nb, Ab, pairs, S, R, seeds=(7, 11, 13))
                    tot += 1
                    hit += int(ok)
            print(f'     s={s}  n={nn:5d}  copies={1 << s:4d}   split {hit}/{tot}', flush=True)


# ---------------------------------------------------------------- the control
# Is the split caused by the ruler's INJECTIVE READING (RulerLemma hypothesis (ii)), or just by
# adding vertices?  Re-run with a ruler whose marks are NOT pairwise distinguishable -- a cycle.
# Hypothesis (ii) predicts: rigid ruler splits, symmetric ruler does not.

def cycle_ruler(k):
    A = np.zeros((k, k), dtype=bool)
    for i in range(k):
        A[i, (i + 1) % k] = A[(i + 1) % k, i] = True
    return A


def control_main():
    m = 10
    rng = random.Random(4242)
    got = find_base(m, rng)
    cons, nb, Ab, pairs = got
    print(f'\n=== CONTROL: does the split need an INJECTIVE reading?  base n={nb} ===', flush=True)
    print('  s   rigid ruler (1-WL discrete)      symmetric ruler (cycle, marks indistinguishable)',
          flush=True)
    for s in (4, 5, 6):
        k = 2 * s
        rg = 0
        cy = 0
        for t in range(4):
            S = rng.sample(range(len(pairs)), s)
            ok1, _ = run(nb, Ab, pairs, S, rigid_ruler(max(k, 7), rng), seeds=(7, 11))
            ok2, _ = run(nb, Ab, pairs, S, cycle_ruler(max(k, 7)), seeds=(7, 11))
            rg += int(ok1)
            cy += int(ok2)
        print(f'  {s}   split {rg}/4                        split {cy}/4', flush=True)


if __name__ == '__main__' and len(sys.argv) > 3 and sys.argv[3] == 'control':
    control_main()
