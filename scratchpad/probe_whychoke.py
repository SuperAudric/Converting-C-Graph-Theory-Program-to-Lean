#!/usr/bin/env python3
"""Why does the C3/C4 witness's descent from a twin hub FAIL?
Trace which cell chooseIdK actually selects at each level, and its orbit count."""
import sys
from collections import defaultdict
sys.setrecursionlimit(100000)
from probe_polyloop import adjlist, refine, indiv, target_cell
from probe_certkey import true_orbit_partition
from probe_mixedcell import build

n, adj, hubs = build()
adjl = adjlist(n, adj); col = refine(n, adjl, [0]*n)
h1, h2, h3 = hubs
for start, name in ((h1, "h1 (C3-hub, twin)"), (h3, "h3 (C4-hub, rigid)")):
    print(f"\n=== descent from {name} = {start} ===")
    cur = indiv(n, adjl, col, start)
    for lvl in range(6):
        cid, C = target_cell(n, cur)
        if cid is None:
            print(f"  level {lvl}: DISCRETE"); break
        orb = true_orbit_partition(n, adj, cur)
        norb = len({orb[v] for v in C})
        kind = "HUBS" if set(C) <= set(hubs) else ("blocks" if not (set(C) & set(hubs)) else "mixed")
        print(f"  level {lvl}: picks {kind} cell size={len(C)} orbits={norb}"
              f"  {'<-- MIXED, descent FAILS here' if norb > 1 else ''}")
        if norb > 1: break
        cur = indiv(n, adjl, cur, min(C))
