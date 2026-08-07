import sys
from collections import defaultdict
sys.setrecursionlimit(100000)
from probe_polyloop import adjlist, refine, indiv, target_cell
from probe_certkey import true_orbit_partition
from probe_mixedcell import build
from probe_mixedcell2 import descend_cert_from

n, adj, hubs = build()
adjl = adjlist(n, adj); col = refine(n, adjl, [0]*n)
orb = true_orbit_partition(n, adj, col)
cid, C = target_cell(n, col)
good = set(v for v in C if descend_cert_from(n, adj, adjl, col, v))
byorb = defaultdict(list)
for v in C: byorb[orb[v]].append(v)
print(f"ROOT branch cell size {len(C)}; orbits inside:")
for o, vs in byorb.items():
    g = sum(1 for v in vs if v in good)
    print(f"  orbit {o}: size {len(vs)}  good {g}/{len(vs)}"
          f"   -> {'ALL BAD (BAD-BIG!)' if g==0 and len(vs)>1 else 'ok'}")
# triangle count as a structural invariant on the hub cell
def triAt(v): return sum(1 for i in range(n) for j in range(i+1,n)
                         if adj[v][i] and adj[v][j] and adj[i][j])
print("triAt at hubs:", {h: triAt(h) for h in hubs})
