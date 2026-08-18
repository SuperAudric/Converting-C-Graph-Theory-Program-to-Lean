"""probe_cao_ruler_curve2.py -- the prod|cell|! ruler test as an HONEST curve.

⚠ WHAT v1 GOT WRONG, and it is worth keeping.  probe_cao_ruler_curve.py built the family by attaching
the ruler to ALL feet and closing over only the first j pairs, holding the rest FIXED across copies.
A fixed attachment INDIVIDUALISES those feet -- and a multipede's collapse under individualization is
a cliff (doc §8 row 10a), so every j < m row came out fully discrete and told us nothing.  Measured:
j = 0..4 on the m=12 base, all discrete, zero non-singleton cells.

THE FIX.  Attach the ruler to the feet of a SUBSET S of the pairs and leave the others untouched, then
close under prod_{i in S} Sym(cell_i).  Now every row is a leak-free test in its own right:
permutations of an unattached cell act trivially on the family, permutations of an attached cell
permute it.  Nothing is individualised at any row.

    cost at |S| = s :   2^s copies of a 2s-vertex ruler  =  n + s * 2^(s+1)  vertices
    s = 1  ->      4        s = 6  ->    768        s = 9  ->   9,216
    s = 4  ->    128        s = 8  ->  4,096        s = 10 ->  20,480

★ s = 1 is four extra vertices.  If the pair does not split there, the mechanism is already in
trouble; if it splits all the way to s = 8 that is strong evidence for the full row.

The control row `s=1, closed=False` uses a single copy (a bare individualization) and MUST split --
that is the harness check that this setup can see a split at all.
"""

import itertools
import math
import random
import sys

import networkx as nx
import numpy as np

from probe_cao_multipede_small import gf2_rank, multipede_adj, wl2_diag, cell_sizes
from probe_cao_ruler_curve import partial_steiner, hypergraph_rigid, rigid_ruler


def find_base(m, rng, ctries=3000):
    """Partial-Steiner multipede: full GF(2) rank + asymmetric design + 2-WL cells of size 2."""
    for c in range(m, 2 * m):
        for _ in range(ctries):
            cons = partial_steiner(m, c, rng)
            if cons is None:
                continue
            rows = [sum(1 << v for v in N) for N in cons]
            if gf2_rank(rows, m) != m:
                continue
            if not hypergraph_rigid(m, cons):
                continue
            n, A = multipede_adj(m, cons)
            if not nx.is_connected(nx.from_numpy_array(A.astype(int))):
                continue
            diag = wl2_diag(n, A)
            if cell_sizes(diag)[0] == 1:
                continue
            fd = {}
            for v in range(2 * m):
                fd.setdefault(diag[v], []).append(v)
            if len(fd) == m and all(len(g) == 2 for g in fd.values()):
                return cons, n, A, [tuple(sorted(g)) for g in fd.values()]
    return None


def build_subset(nb, Ab, pairs, S, R, closed=True):
    """Attach a rigid ruler to the feet of the pairs in S; close under prod_{i in S} Sym(pair).

    ⚠ `R` must be a ruler for THIS `k` -- a 1-WL-discrete graph on `>= k` vertices, whose first `k`
    vertices are the marks.  Slicing a bigger ruler's top-left k x k block does NOT work: a small
    induced subgraph of a rigid graph is not rigid (for k=2 it is a single edge, whose two ends are
    interchangeable), and that silently turns the control row into a non-test."""
    att = [v for i in S for v in pairs[i]]      # 2|S| attachment points
    k = len(att)
    kr = R.shape[0]
    assert kr >= k
    ncop = (1 << len(S)) if closed else 1
    n = nb + ncop * kr
    A = np.zeros((n, n), dtype=bool)
    A[:nb, :nb] = Ab
    for cidx in range(ncop):
        off = nb + cidx * kr
        A[off:off + kr, off:off + kr] = R
        for t, i in enumerate(S):
            a, b = pairs[i]
            if (cidx >> t) & 1:
                a, b = b, a
            A[off + 2 * t, a] = A[a, off + 2 * t] = True
            A[off + 2 * t + 1, b] = A[b, off + 2 * t + 1] = True
    return n, A


if __name__ == '__main__':
    smax = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    m = int(sys.argv[2]) if len(sys.argv) > 2 else 10
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 20260818
    rng = random.Random(seed)

    print(f'=== HONEST ruler-closure curve, multipede base m={m} ===', flush=True)
    got = find_base(m, rng)
    if got is None:
        print('no rigid + non-discrete base with all-size-2 foot cells'); sys.exit(1)
    cons, nb, Ab, pairs = got
    print(f'  base n={nb}, c={len(cons)}, {len(pairs)} mixed foot pairs (Aut=1 so every pair is '
          f'2 orbits)\n  cons={cons}\n  pairs={pairs}', flush=True)

    rulers = {k: rigid_ruler(max(k, 7), rng) for k in range(2, 2 * m + 2, 2)}
    print(f'  rulers: a fresh 1-WL-discrete graph per mark-count k '
          f'(>= 7 vertices, so k=2 is a real ruler)\n', flush=True)

    print('  s  copies      n   attached-pair cell sizes   #non-singleton cells (whole graph)',
          flush=True)
    # control: one copy, no closure -- a bare individualization, must split
    n, A = build_subset(nb, Ab, pairs, [0], rulers[2], closed=False)
    d = wl2_diag(n, A)
    sizes = {}
    for v in pairs[0]:
        sizes[d[v]] = sizes.get(d[v], 0) + 1
    nons = [x for x in cell_sizes(d) if x > 1]
    print(f'  CONTROL (1 copy, NOT closed): n={n}  pair0 cells={sorted(sizes.values())}  '
          f'non-singleton={nons if nons else "none (discrete)"}', flush=True)

    for s in range(1, smax + 1):
        S = list(range(s))
        n, A = build_subset(nb, Ab, pairs, S, rulers[2 * s], closed=True)
        if n > 4400:
            print(f'  {s:2d}  {1 << s:6d}  {n:5d}   -- skipped (too large for this harness)',
                  flush=True)
            continue
        d = wl2_diag(n, A)
        att_sizes = {}
        for i in S:
            for v in pairs[i]:
                att_sizes[d[v]] = att_sizes.get(d[v], 0) + 1
        nons = [x for x in cell_sizes(d) if x > 1]
        split = all(x == 1 for x in att_sizes.values())
        print(f'  {s:2d}  {1 << s:6d}  {n:5d}   {sorted(att_sizes.values(), reverse=True)[:10]}'
              f'   {len(nons)} cells, sizes {nons[:8]}{"..." if len(nons) > 8 else ""}'
              f'   {"SPLIT" if split else "merged"}', flush=True)
