"""probe_cao_multipede3.py -- larger / better-expanding multipedes, with a DIRECT mixedness check.

Reports, per instance: 2-WL cell sizes, |Aut|, and whether any cell is MIXED (meets two Aut-orbits).
Constraint systems are partial Steiner (no two constraints share two legs), which is the expansion
the multipede papers rely on, and are required to have full GF(2) column rank (= no flip automorphism).
"""

import itertools
import math
import random
import sys

import networkx as nx
import numpy as np

from probe_cao_multipede2 import wl2_diag, gf2_rank, multipede_adj, sizes_of


def orbits_of(n, A, cap=200000):
    G = nx.from_numpy_array(A.astype(int))
    par = list(range(n))

    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    gm = nx.algorithms.isomorphism.GraphMatcher(G, G)
    c = 0
    for mp in gm.isomorphisms_iter():
        c += 1
        for a, b in mp.items():
            ra, rb = find(a), find(b)
            if ra != rb:
                par[ra] = rb
        if c >= cap:
            break
    return [find(v) for v in range(n)], c


def mixed_cells(n, diag, orb):
    d = {}
    for v in range(n):
        d.setdefault(diag[v], []).append(v)
    return [c for c in d.values() if len({orb[v] for v in c}) > 1]


def partial_steiner(m, c, deg, rng, tries=8000):
    cons, pairs = [], set()
    for _ in range(tries):
        if len(cons) >= c:
            break
        N = tuple(sorted(rng.sample(range(m), deg)))
        ps = set(itertools.combinations(N, 2))
        if ps & pairs:
            continue
        cons.append(N)
        pairs |= ps
    return cons if len(cons) == c else None


if __name__ == '__main__':
    rng = random.Random(20260818)
    print('=== partial-Steiner multipedes: cells, Aut, and MIXEDNESS ===', flush=True)
    best = None
    for deg in (3, 4):
        for m in (12, 16, 20, 24, 30, 36, 44):
            for ratio in (1.0, 1.2, 1.4):
                c = int(ratio * m)
                for _ in range(25):
                    cons = partial_steiner(m, c, deg, rng)
                    if cons is None:
                        continue
                    rows = [sum(1 << v for v in N) for N in cons]
                    if gf2_rank(rows, m) != m:
                        continue
                    n, A = multipede_adj(m, cons)
                    if n > 420:
                        continue
                    diag = wl2_diag(n, A)
                    sz = sizes_of(diag)
                    if sz[0] == 1:
                        continue
                    orb, naut = orbits_of(n, A)
                    mx = mixed_cells(n, diag, orb)
                    cost = 1
                    for s in sz:
                        cost *= math.factorial(s)
                    print(f'  deg={deg} m={m:2d} c={c:2d} n={n:3d} |Aut|={naut:5d}'
                          f' cells={sz[:8]} cost={cost}'
                          f'  MIXED={[len(x) for x in mx] if mx else "none"}', flush=True)
                    if mx and (best is None or cost < best[0]):
                        best = (cost, deg, m, c, n, sz, [len(x) for x in mx])
                    break
    print('\ncheapest MIXED carrier found:', best)
