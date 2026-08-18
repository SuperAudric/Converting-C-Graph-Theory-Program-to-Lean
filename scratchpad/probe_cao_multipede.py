"""probe_cao_multipede.py -- do CFI/multipede objects give SMALL cells?

The reader's test costs prod |cell|!, so a big graph with many size-2 cells beats a small graph with
one giant cell.  Multipedes (Gurevich-Shelah; Neuen-Schweitzer) are built to be ASYMMETRIC, and that
is exactly what is wanted here:

  * Aut = 1  ==>  every orbit is a singleton  ==>  EVERY non-singleton 2-WL cell is MIXED;
  * Aut = 1  ==>  individualizing any vertices breaks no symmetry at all, so shrinking the cells by
    individualization is free and non-circular  (the reader's second point).

Construction.  Bipartite (V, W): |V| = m legs, each leg v a pair of feet v^0, v^1; each constraint
w in W has N(w) subset V of size 3 and contributes one gadget vertex per EVEN 0/1 assignment on
N(w), joined to the corresponding feet.  Flipping a set X of legs is an automorphism iff M chi_X = 0
over GF(2), where M is the constraint-by-leg incidence matrix -- so the multipede has no flip
automorphism iff M has full column rank.
"""

import itertools
import math
import random
import sys

import networkx as nx
import numpy as np


def wl2_cells(n, adj, rounds=60):
    col = [[0 if u == v else (1 if adj[u][v] else 2) for v in range(n)] for u in range(n)]
    ncls = len({col[u][v] for u in range(n) for v in range(n)})
    for _ in range(rounds):
        cand = [[(col[u][v], tuple(sorted((col[u][z], col[z][v]) for z in range(n))))
                 for v in range(n)] for u in range(n)]
        keys = sorted({cand[u][v] for u in range(n) for v in range(n)}, key=repr)
        tab = {k: i for i, k in enumerate(keys)}
        col = [[tab[cand[u][v]] for v in range(n)] for u in range(n)]
        if len(keys) == ncls:
            break
        ncls = len(keys)
    return [col[v][v] for v in range(n)]


def parts(labels):
    d = {}
    for v, c in enumerate(labels):
        d.setdefault(c, []).append(v)
    return sorted(tuple(sorted(g)) for g in d.values())


def gf2_rank(rows, m):
    piv = []
    rows = [r for r in rows]
    r = 0
    for c in range(m):
        p = None
        for i in range(r, len(rows)):
            if (rows[i] >> c) & 1:
                p = i
                break
        if p is None:
            continue
        rows[r], rows[p] = rows[p], rows[r]
        for i in range(len(rows)):
            if i != r and ((rows[i] >> c) & 1):
                rows[i] ^= rows[r]
        r += 1
    return r


def multipede(m, cons):
    """feet 2*v, 2*v+1 for leg v; then one gadget vertex per even assignment per constraint."""
    G = nx.Graph()
    for v in range(m):
        G.add_node(2 * v); G.add_node(2 * v + 1)
    nxt = 2 * m
    for N in cons:
        k = len(N)
        for bits in itertools.product([0, 1], repeat=k):
            if sum(bits) % 2:
                continue
            G.add_node(nxt)
            for v, b in zip(N, bits):
                G.add_edge(nxt, 2 * v + b)
            nxt += 1
    return G


def analyse(G, name, quiet=False):
    n = G.number_of_nodes()
    idx = {v: i for i, v in enumerate(sorted(G.nodes()))}
    adj = [[False] * n for _ in range(n)]
    for u, v in G.edges():
        adj[idx[u]][idx[v]] = adj[idx[v]][idx[u]] = True
    cells = parts(wl2_cells(n, adj))
    # rigidity: count automorphisms (cheap when Aut is trivial)
    gm = nx.algorithms.isomorphism.GraphMatcher(G, G)
    naut = 0
    for _ in gm.isomorphisms_iter():
        naut += 1
        if naut > 4:
            break
    cost = 1
    for c in cells:
        cost *= math.factorial(len(c))
    sizes = sorted((len(c) for c in cells), reverse=True)
    if not quiet:
        print(f'  {name:26s} n={n:4d} |Aut|{">4" if naut > 4 else f"={naut}"}'
              f'  cell sizes={sizes[:8]}{"..." if len(sizes) > 8 else ""}'
              f'  #non-singleton={sum(1 for c in cells if len(c) > 1)}'
              f'  prod|cell|!={cost}', flush=True)
    return cells, naut, cost


if __name__ == '__main__':
    rng = random.Random(20260818)
    print('=== multipedes from random 3-uniform constraint systems (full GF(2) column rank) ===')
    for m in (4, 5, 6, 7, 8, 10, 12):
        for c_extra in (1, 2, 3):
            c = m + c_extra
            got = None
            for _ in range(400):
                cons = [tuple(sorted(rng.sample(range(m), 3))) for _ in range(c)]
                if len(set(cons)) != c:
                    continue
                rows = [sum(1 << v for v in N) for N in cons]
                if gf2_rank(rows, m) != m:
                    continue
                got = cons
                break
            if got is None:
                continue
            G = multipede(m, got)
            if not nx.is_connected(G):
                continue
            analyse(G, f'multipede m={m} c={c}')
