"""probe_cao_multipede_small2.py -- the smallest multipede with SMALL MIXED foot cells.

v1 (probe_cao_multipede_small.py) found the missing ingredient by failing.  Full GF(2) column rank
kills only the FLIP automorphisms (leg v's two feet swapped).  It says nothing about automorphisms
that PERMUTE THE LEGS, and at small m the partial-Steiner systems with c >= m are forced to be the
maximum packings, which are highly symmetric designs.  Result: m=8 and m=9 came out with |Aut| > 3
and one foot cell of size 16 / three of size 6 -- useless, since the ruler test costs prod|foot|!.

So the carrier needs BOTH:
  (a) full GF(2) column rank            -- no flip automorphism   -> every leg pair is 2 orbits;
  (b) an ASYMMETRIC constraint hypergraph -- no leg permutation   -> legs are pairwise distinguishable,
                                                                     so each foot cell has size 2.
Together they give Aut = 1 and foot cells of size exactly 2, i.e. the reader's test at 2^m copies.

This probe adds (b) and reports, for each m, the cheapest carrier and the exact ruler-test cost
    copies  = prod |foot cell|!   (2^m when all foot cells are pairs)
    verts   = copies * 2m         (a rigid ruler needs one mark per foot)
"""

import itertools
import math
import sys

import networkx as nx
import numpy as np

from probe_cao_multipede_small import (enumerate_ps, gf2_rank, multipede_adj, wl2_diag,
                                       cell_sizes)


def hypergraph_rigid(m, cons):
    """Aut of the legs/blocks incidence bipartite graph -- trivial on the leg side?"""
    B = nx.Graph()
    for v in range(m):
        B.add_node(('v', v), bip=0)
    for j, N in enumerate(cons):
        B.add_node(('b', j), bip=1)
        for v in N:
            B.add_edge(('v', v), ('b', j))
    gm = nx.algorithms.isomorphism.GraphMatcher(
        B, B, node_match=lambda a, b: a['bip'] == b['bip'])
    k = 0
    for _ in gm.isomorphisms_iter():
        k += 1
        if k > 1:
            return False
    return True


def orbits_of(n, A, cap=200000):
    G = nx.from_numpy_array(A.astype(int))
    gm = nx.algorithms.isomorphism.GraphMatcher(G, G)
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    k = 0
    for iso in gm.isomorphisms_iter():
        k += 1
        for a, b in iso.items():
            ra, rb = find(a), find(b)
            if ra != rb:
                parent[ra] = rb
        if k > cap:
            break
    return [find(v) for v in range(n)], k


if __name__ == '__main__':
    ms = [int(x) for x in sys.argv[1:]] or [8, 9, 10, 11]
    print('=== smallest multipede with SMALL MIXED foot cells (rank + asymmetric design) ===',
          flush=True)
    overall = None
    for m in ms:
        cmax = (m * ((m - 1) // 2)) // 3
        print(f'\n-- m={m}  (c_max={cmax}, need c>={m})', flush=True)
        if cmax < m:
            print('   IMPOSSIBLE: c_max < m', flush=True)
            continue
        for c in range(m, min(cmax, m + 4) + 1):
            systems = enumerate_ps(m, c, 3, cap=120000)
            cand = []
            for cons in systems:
                rows = [sum(1 << v for v in N) for N in cons]
                if gf2_rank(rows, m) != m:
                    continue
                if not hypergraph_rigid(m, cons):
                    continue
                cand.append(cons)
            print(f'   c={c}: {len(systems)} PS systems -> {len(cand)} full-rank AND asymmetric',
                  flush=True)
            shown = 0
            for cons in cand:
                n, A = multipede_adj(m, cons)
                if not nx.is_connected(nx.from_numpy_array(A.astype(int))):
                    continue
                diag = wl2_diag(n, A)
                sz = cell_sizes(diag)
                if sz[0] == 1:
                    continue                                   # 2-WL discretised it
                orb, naut = orbits_of(n, A)
                fd = {}
                for v in range(2 * m):
                    fd.setdefault(diag[v], []).append(v)
                foot_sizes = sorted((len(g) for g in fd.values()), reverse=True)
                mixed = [g for g in fd.values() if len({orb[v] for v in g}) > 1]
                copies = 1
                for s in foot_sizes:
                    copies *= math.factorial(s)
                print(f'      n={n:3d} |Aut|={naut} cells={sz[:10]} FOOT={foot_sizes}'
                      f'  mixed_foot_cells={len(mixed)}'
                      f'  copies={copies} ruler_verts={copies * 2 * m}', flush=True)
                if mixed and (overall is None or copies * 2 * m < overall[0]):
                    overall = (copies * 2 * m, copies, m, c, n, foot_sizes, cons)
                shown += 1
                if shown >= 3:
                    break
    print('\n=== cheapest carrier for the prod|cell|! ruler test ===')
    if overall is None:
        print('  none found')
    else:
        print(f'  ruler_verts={overall[0]}  copies={overall[1]}  m={overall[2]} c={overall[3]} '
              f'n={overall[4]}  foot cells={overall[5]}')
        print(f'  constraints={overall[6]}')
