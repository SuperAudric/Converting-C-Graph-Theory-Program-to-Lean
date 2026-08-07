#!/usr/bin/env python3
"""Q2, reading (b): shared-vertex info used to REFINE the colouring (finer cells),
not to SELECT within a canonical cell.

Refining changes WHICH cell is targeted -- unlike a selector, which cannot.  The
cheapest faithful proxy for "joint colouring of the two descents" is individualizing
BOTH compared vertices and refining (the joint colouring is coarser than or equal to
this, so this is an UPPER bound on what the mechanism can deliver).

For every anchor whose min-index descent hits a multi-orbit cell, ask: is there a
partner b in the root cell such that the descent from {a,b} has all single-orbit cells?
If even the upper bound fails, reading (b) is dead on this witness too.
"""
import sys
sys.setrecursionlimit(10000)
from probe_dualdeepen import rand_incidence, build_mp, build_cfi_base, cubic
from probe_polyloop import adjlist, refine, indiv, target_cell
from probe_certkey import true_orbit_partition

def minindex_ok(n, adj, adjl, cur):
    for _ in range(n + 2):
        cid, C = target_cell(n, cur)
        if cid is None: return True
        orb = true_orbit_partition(n, adj, cur)
        if len({orb[v] for v in C}) > 1: return False
        cur = indiv(n, adjl, cur, min(C))
    return False

def analyse(name, n, adj):
    adjl = adjlist(n, adj); col = refine(n, adjl, [0]*n)
    cid, C = target_cell(n, col)
    bad = [a for a in C if not minindex_ok(n, adj, adjl, indiv(n, adjl, col, a))]
    if not bad:
        print(f"{name:28s} no bad anchors"); return
    fixed = 0
    for a in bad:
        ca = indiv(n, adjl, col, a)
        if any(minindex_ok(n, adj, adjl, indiv(n, adjl, ca, b)) for b in C if b != a):
            fixed += 1
    print(f"{name:28s} bad={len(bad):3d}  repaired-by-pair-refinement={fixed:3d}"
          f"  => reading (b) {'LIVE' if fixed else 'DEAD'} here")

if __name__ == "__main__":
    n, adj = build_mp(rand_incidence(12, 8, 3, 4)); analyse("rand multipede V=12 W=8", n, adj)
    n, adj = build_cfi_base(cubic(10, 21), 10, False); analyse("CFI cubic m=10", n, adj)
