"""Does consume RESOLVE the mixed hub cell, and is the graph outside TinhoferGraph?"""
import sys
from collections import defaultdict
sys.setrecursionlimit(100000)
from probe_polyloop import adjlist, refine, indiv, target_cell
from probe_certkey import true_orbit_partition
from probe_c8witness import build

n, adj = build()
adjl = adjlist(n, adj); col = refine(n, adjl, [0]*n)
orb = true_orbit_partition(n, adj, col)
cells = defaultdict(list)
for v in range(n): cells[col[v]].append(v)

print("cells and their TRUE orbit split (SchurianAt = every cell is ONE orbit):")
schurian = True
for c, C in sorted(cells.items()):
    ids = {orb[v] for v in C}
    if len(ids) > 1: schurian = False
    print(f"  colour {c}: size {len(C)} -> {len(ids)} orbit(s) {'MIXED' if len(ids)>1 else ''}")
print(f"\nroot colouring SchurianAt? {schurian}   => TinhoferGraph? {schurian}")

hub = cells[1]
print(f"\nhub cell {hub}: orbit ids {[orb[v] for v in hub]}")
byorb = defaultdict(list)
for v in hub: byorb[orb[v]].append(v)
print("what consume must do: merge each orbit-block, keep blocks apart ->",
      f"{len(byorb)} reps from {len(hub)} branches:", dict(byorb))
