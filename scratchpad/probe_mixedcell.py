#!/usr/bin/env python3
"""
THE USER'S WITNESS (2026-08-06): a MIXED cell — a genuine 2-orbit plus one rigid vertex
that a refinement invariant CAN see.  This is the shape probe_goodorisolated.py never had.

Hubs: two attached to 4 disjoint C3's, one attached to 3 disjoint C4's.
Degrees match by construction (4*3 = 3*4 = 12) and every block vertex has degree 3,
so 1-WL is STABLE with two cells and cannot separate C3-blocks from C4-blocks.
Aut: hub1 <-> hub2 swappable (one orbit of size 2); hub3 is its own orbit.

Question: is the C4-hub ISOLATED by an equivariant vertex invariant while the two
C3-hubs are GOOD anchors?  If so GoodOrIsolated is OPEN where CertifiedG is SHUT --
the strict win the earlier sweep found 0 of.
"""
import sys
from collections import defaultdict
sys.setrecursionlimit(100000)
from probe_polyloop import adjlist, refine, indiv, target_cell
from probe_certkey import true_orbit_partition, descend_cert

def build():
    edges, nxt = [], 0
    def fresh():
        nonlocal nxt; v = nxt; nxt += 1; return v
    hubs = []
    for spec in [(3, 4), (3, 4), (4, 3)]:          # (cycle length, #copies)
        L, k = spec
        h = fresh(); hubs.append(h)
        for _ in range(k):
            blk = [fresh() for _ in range(L)]
            for i in range(L):
                edges.append((blk[i], blk[(i + 1) % L]))
            for b in blk:
                edges.append((h, b))
    n = nxt
    adj = [[0] * n for _ in range(n)]
    for a, b in edges:
        adj[a][b] = adj[b][a] = 1
    return n, adj, hubs

def step_sum(n, adjl, col, u):  return sum(indiv(n, adjl, col, u))
def step_mset(n, adjl, col, u): return tuple(sorted(indiv(n, adjl, col, u)))

if __name__ == "__main__":
    n, adj, hubs = build()
    adjl = adjlist(n, adj)
    col = refine(n, adjl, [0] * n)
    print(f"n={n} hubs={hubs}  1-WL cells={len(set(col))}")
    cid, C = target_cell(n, col)
    print(f"branch cell size={len(C)}  contains hubs? {[h in C for h in hubs]}")
    orb = true_orbit_partition(n, adj, col)
    print(f"orbits inside branch cell: {len({orb[v] for v in C})}")
    bs = defaultdict(int)
    for v in range(n): bs[orb[v]] += 1
    rigid = [v for v in C if bs[orb[v]] == 1]
    good  = [v for v in C if descend_cert(n, adj, adjl, col, v)[1]]
    for nm, f in (("stepSum", step_sum), ("mset", step_mset)):
        sig = {v: f(n, adjl, col, v) for v in C}
        cnt = defaultdict(int)
        for v in C: cnt[sig[v]] += 1
        isol = [v for v in C if cnt[sig[v]] == 1]
        prim = len(good) == len(C)
        sec  = all((v in good) or (v in isol) for v in C)
        bad_isol = [v for v in isol if bs[orb[v]] != 1]
        print(f"  inv={nm:8s} good={len(good):3d}/{len(C)} isol={len(isol):3d} rigid={len(rigid):3d}"
              f"  PRIM(CertifiedG)={'open' if prim else 'SHUT'}"
              f"  SEC(GoodOrIsolated)={'open' if sec else 'SHUT'}"
              f"{'  *** STRICT WIN ***' if sec and not prim else ''}"
              f"{'  !!UNSOUND:' + str(bad_isol) if bad_isol else ''}")
