"""probe_cao_fullclosure.py -- "it preserves all symmetries so can detect none".  Tested.

THE READER'S CLAIM (2026-08-16, sharpest form).  A ruler works only if the ruler set is closed under
the symmetry you want to preserve (agreed -- their mirrored-ruler repair showed exactly that).  In
the full ensemble the set is closed under EVERYTHING, so it preserves all symmetries and can
therefore detect none.

WHAT THIS BUILDS.  The same object as their C6 construction, but with the copy set closed under the
FULL symmetric group S_L instead of a rotation subgroup: for each base graph, EVERY distinct
relabelling is present.  So Aut contains all of S_L -- the maximal-symmetry point of the family, and
the exact situation the claim is about.  Frame types are distinguished (ground state individualized),
no centrals, payload cliques, as before.

WHAT IS MEASURED.  Cells that plain 2-WL (no orbit partition handed to it, no individualization)
puts the payload vertices into, versus the true orbits, which under full closure are exactly the
ISOMORPHISM CLASSES of marked graphs (copy, vertex) -- computed independently by canonical form.

THE POINT AT ISSUE.  Full closure does make every LABELLING undetectable.  The question is whether
it also makes the orbits undetectable.  It cannot make the orbits trivial: S_L does not act
transitively on marked graphs, so several orbits survive closure, and they are what CAO is about.

Usage:  python3 probe_cao_fullclosure.py
"""

import time
from itertools import combinations, permutations

import numpy as np

import probe_cao_c6_ablate as A


def wl2_hash(n, adj, start, seed):
    """exact 2-WL with an O(n^2)-memory round.

    The straightforward round materializes the n^2 x (n+1) array of sorted neighbour-colour rows,
    which is 1.9 GB at n = 620.  Instead each round's multiset {(col[u][z], col[z][v]) : z} is folded
    to a uint64 by summing a random hash of the colour pair -- summation is commutative, so it is a
    multiset invariant.  A collision would MERGE two colours (report a cell that is not there), so
    the run is repeated under two independent seeds and the partitions compared; agreement makes a
    collision-driven answer ~ (n^2 / 2^64)^2 unlikely."""
    rng = np.random.default_rng(seed)
    eye = np.eye(n, dtype=bool)
    s = np.asarray(start, dtype=np.int64)
    col = (((s[:, None] * (s.max() + 1) + s[None, :]) * 2 + eye) * 2 + adj).astype(np.int64)
    _, col = np.unique(col, return_inverse=True)
    col = col.reshape(n, n).astype(np.int64)

    prev = -1
    for _ in range(n):
        C = int(col.max()) + 1
        H = rng.integers(1, 2 ** 63, size=C * C, dtype=np.uint64)
        acc = np.zeros((n, n), dtype=np.uint64)
        b = max(1, 4_000_000 // (n * n) or 1)
        for lo in range(0, n, b):
            hi = min(lo + b, n)
            pair = col[lo:hi, :, None] * C + col[None, :, :]        # (b, n, n): (col[u,z], col[z,v])
            acc[lo:hi] = H[pair].sum(axis=1)
        keyed = np.stack([col.astype(np.uint64).ravel(), acc.ravel()], axis=1)
        v = np.ascontiguousarray(keyed).view([('', np.uint64)] * 2).ravel()
        tab = np.unique(v)
        col = np.searchsorted(tab, v).reshape(n, n).astype(np.int64)
        if len(tab) == prev:
            break
        prev = len(tab)
    return col[np.arange(n), np.arange(n)]


def canon_marked(L, edges, v, pairs, slot):
    """canonical form of the marked graph (G, v) -- the S_L-orbit invariant, computed directly."""
    best = None
    for p in permutations(range(L)):
        code = tuple(sorted(slot[(p[i], p[j])] for (i, j) in edges))
        cand = (code, p[v])
        best = cand if best is None else min(best, cand)
    return best


def build(L, bases):
    """frame + the FULL S_L-orbit of every base graph, as copies sharing one frame."""
    import networkx as nx
    pairs = list(combinations(range(L), 2))
    slot = {}
    for k, (i, j) in enumerate(pairs):
        slot[(i, j)] = slot[(j, i)] = k

    G = nx.Graph()
    for k in range(len(pairs)):
        for t in (0, 1):
            G.add_node(('f', k, t), kind=f'f{t}')
        G.add_edge(('f', k, 0), ('f', k, 1))

    copies = {}                                   # edge-set -> (base name, a representative perm)
    for name, edges in bases:
        for p in permutations(range(L)):
            es = frozenset(frozenset((p[i], p[j])) for (i, j) in edges)
            copies.setdefault(es, (name, p))

    orb_of = {}
    for cid, (es, (name, p)) in enumerate(sorted(copies.items(), key=lambda kv: sorted(map(sorted, kv[0])))):
        for x in range(L):
            G.add_node(('p', cid, x), kind='payload')
        for x, y in combinations(range(L), 2):
            G.add_edge(('p', cid, x), ('p', cid, y))
        for x in range(L):
            for y in range(L):
                if x == y:
                    continue
                k = slot[(x, y)]
                t = 1 if frozenset((x, y)) in es else 0
                G.add_edge(('p', cid, x), ('f', k, t))
        el = [tuple(sorted(e)) for e in es]
        for x in range(L):
            orb_of[('p', cid, x)] = canon_marked(L, el, x, pairs, slot)
    return G, orb_of, len(copies)


def run(L, bases, label):
    t0 = time.time()
    G, orb_of, ncopies = build(L, bases)
    nodes = sorted(G.nodes(), key=repr)
    n = len(nodes)
    idx = {v: i for i, v in enumerate(nodes)}
    adj = np.zeros((n, n), dtype=bool)
    for u, v in G.edges():
        adj[idx[u], idx[v]] = adj[idx[v], idx[u]] = True
    kinds = {}
    start = [kinds.setdefault(G.nodes[v]['kind'], len(kinds)) for v in nodes]
    cells = wl2_hash(n, adj, start, seed=11)
    check = wl2_hash(n, adj, start, seed=977)
    agree = (len({(int(a), int(b)) for a, b in zip(cells, check)}) == len(set(map(int, cells))))

    sel = [i for i, v in enumerate(nodes) if v[0] == 'p']
    ncell = len({int(cells[i]) for i in sel})
    norb = len({orb_of[nodes[i]] for i in sel})
    mix = {}
    for i in sel:
        mix.setdefault(int(cells[i]), set()).add(orb_of[nodes[i]])
    nmix = sum(1 for s in mix.values() if len(s) > 1)
    print(f'  {label:<34} |V|={n:>5}  copies={ncopies:>4}  payload={len(sel):>5}  '
          f'cells={ncell:>3}  orbits={norb:>3}  MIXED={nmix}'
          f"{'   <-- WASHOUT' if nmix else '   cells = orbits'}"
          f"{'' if agree else '  [SEED DISAGREE]'}   ({time.time() - t0:.0f}s)")


P5 = [(0, 1), (1, 2), (2, 3), (3, 4)]
CHAIR = [(0, 1), (1, 2), (2, 3), (1, 4)]                     # 4 vertex orbits, |Aut| = 2
C5 = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]
C6 = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0)]
TWOC3 = [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3)]
PRISM = [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (0, 3), (1, 4), (2, 5)]
K33 = [(0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5)]

if __name__ == '__main__':
    print('FULL S_L closure -- every relabelling of every base graph is present\n')
    print('L=5:')
    run(5, [('P5', P5)], 'P5 alone (3 vertex orbits)')
    run(5, [('chair', CHAIR)], 'chair alone (4 vertex orbits)')
    run(5, [('P5', P5), ('chair', CHAIR), ('C5', C5)], 'P5 + chair + C5 (8 orbits)')
    print('\nL=6:   1-WL-EQUIVALENT non-isomorphic pairs, both fully closed:')
    run(6, [('C6', C6), ('2C3', TWOC3)], 'C6 + 2C3 (2-regular pair)')
    run(6, [('prism', PRISM), ('K33', K33)], 'prism + K33 (3-regular pair)')
