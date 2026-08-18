"""probe_cao_ruler_curve.py -- the reader's prod|cell|! ruler test, as a CURVE in the closure size.

THE TEST (reader, 2026-08-16d).  Take a graph `G` whose 2-WL cells are strictly coarser than its
orbits.  Bolt a RIGID ruler onto it -- one ruler vertex per attachment point, bijectively, so the
ruler's reading of the attachment set is injective -- and then close the family of attachments under
prod Sym(cell), so that no orbit information leaks.  Two predictions:

  (A) the ruler is present in the graph, so it must reveal the orbits  -> the cells split;
  (B) the family preserves every symmetry, so it can detect none       -> the cells stay put.

WHY A CURVE, AND WHY IT IS CHEAP.  The full closure costs prod|cell|! copies, which is the wall.  But
the same experiment run at PARTIAL closure is cheap and strictly more informative: close under only
the first `j` foot pairs (2^j copies, the other pairs held fixed across all copies) and watch the
cells as `j` grows.

  j = 0   one copy, every foot individualised  -> must discretise (sanity check on the harness)
  j = m   the honest test, zero leakage
  in between: exactly how much symmetrisation the ruler survives.

★ If the pairs already re-merge at j = 1 -- two copies, one leg pair symmetrised -- the mechanism is
dead on arrival and the 2^m experiment is unnecessary.  That costs `n + 2*2m` vertices.

⚠ For a RIGID base (Aut = 1) every family preserves the orbits, so partial closure is not "cheating"
in the symmetry sense; what it leaks is orbit *information*.  The j = m row is the honest test and the
rest is diagnosis.

Usage:  python3 probe_cao_ruler_curve.py [jmax] [m] [seed]
"""

import itertools
import math
import random
import sys

import networkx as nx
import numpy as np

from probe_cao_multipede_small import gf2_rank, multipede_adj, wl2_diag, cell_sizes


# ------------------------------------------------------- a rigid multipede base

def partial_steiner(m, c, rng, tries=20000):
    cons, pairs = [], set()
    for _ in range(tries):
        if len(cons) >= c:
            break
        N = tuple(sorted(rng.sample(range(m), 3)))
        ps = set(itertools.combinations(N, 2))
        if ps & pairs or N in cons:
            continue
        cons.append(N)
        pairs |= ps
    return cons if len(cons) == c else None


def hypergraph_rigid(m, cons):
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


def find_base(m, rng, ctries=400):
    """A partial-Steiner multipede that is rigid (full rank + asymmetric) and 2-WL-non-discrete."""
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
            fs = sorted(len(g) for g in fd.values())
            if fs and max(fs) == 2 and len(fd) == m:
                return cons, n, A, diag
    return None


# ------------------------------------------------------------------ the ruler

def rigid_ruler(k, rng):
    """A graph on k vertices whose 1-WL colouring is discrete (hence rigid, all marks distinct)."""
    for _ in range(4000):
        A = np.zeros((k, k), dtype=bool)
        for i in range(k):
            for j in range(i + 1, k):
                if rng.random() < 0.5:
                    A[i, j] = A[j, i] = True
        col = A.sum(axis=1).astype(np.int64)
        for _ in range(k + 2):
            key = [(col[v], tuple(sorted(col[u] for u in range(k) if A[v, u]))) for v in range(k)]
            tab = {kk: i for i, kk in enumerate(sorted(set(key)))}
            col = np.array([tab[kk] for kk in key])
        if len(set(col.tolist())) == k:
            return A
    raise RuntimeError('no discrete ruler found')


def build(nb, Ab, feet, pairs, R, j):
    """Base + 2^j ruler copies; copy eps swaps the first j foot pairs."""
    k = len(feet)
    ncop = 1 << j
    n = nb + ncop * k
    A = np.zeros((n, n), dtype=bool)
    A[:nb, :nb] = Ab
    for c in range(ncop):
        off = nb + c * k
        A[off:off + k, off:off + k] = R
        # attachment: mark i -> foot feet[i], with the first j pairs flipped per the bits of c
        perm = list(range(k))
        for t in range(j):
            a, b = pairs[t]
            if (c >> t) & 1:
                ia, ib = feet.index(a), feet.index(b)
                perm[ia], perm[ib] = perm[ib], perm[ia]
        for i in range(k):
            f = feet[perm[i]]
            A[off + i, f] = A[f, off + i] = True
    return n, A


if __name__ == '__main__':
    jmax = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    m = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 20260818
    rng = random.Random(seed)

    print(f'=== ruler closure curve, multipede base m={m} ===', flush=True)
    got = find_base(m, rng)
    if got is None:
        print('no rigid + non-discrete base found'); sys.exit(1)
    cons, nb, Ab, diag = got
    fd = {}
    for v in range(2 * m):
        fd.setdefault(diag[v], []).append(v)
    pairs = [tuple(g) for g in fd.values()]
    feet = sorted(v for g in fd.values() for v in g)
    print(f'  base: n={nb}, c={len(cons)}, foot cells={sorted(len(p) for p in pairs)}, '
          f'{len(pairs)} pairs -> full test would need 2^{len(pairs)} copies', flush=True)
    print(f'  cons={cons}', flush=True)

    R = rigid_ruler(len(feet), rng)
    print(f'  ruler: {len(feet)} vertices, 1-WL discrete', flush=True)

    print('\n   j  copies    n    foot cells (sizes)          non-singleton cells (whole graph)',
          flush=True)
    for j in range(0, jmax + 1):
        n, A = build(nb, Ab, feet, pairs, R, j)
        if n > 4200:
            print(f'   {j:2d}  {1 << j:6d}  {n:5d}   -- skipped, too large for 2-WL', flush=True)
            continue
        d = wl2_diag(n, A)
        fsz = {}
        for v in feet:
            fsz[d[v]] = fsz.get(d[v], 0) + 1
        allsz = cell_sizes(d)
        nons = [s for s in allsz if s > 1]
        print(f'   {j:2d}  {1 << j:6d}  {n:5d}   {sorted(fsz.values(), reverse=True)[:12]}'
              f'   {nons[:12]}{"..." if len(nons) > 12 else ""}', flush=True)
