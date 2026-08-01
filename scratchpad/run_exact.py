"""Is the |C|=16 cell at root/id1/id9 (CFI m=8 twisted) a single Aut_chi-orbit?
Settles whether run_forced.out's uniform '✗' is a CORRECT failure (mixed cells, force's domain,
per cao-propagation §13.6(b)) or a genuine consume-supply gap."""
import time
import probe_readsupply as P
from probe_cao_cleanroom import cfi, all_isos, orbits

t0 = time.time()
es = P.cubic(8, 19)
n, adj, _, _ = cfi(es, 8, twisted_nodes=(0,))
nbrs = P.nbrs_of(n, adj)
col = P.wl(n, nbrs, [0] * n)
d = P.cells_of(col); col = P.step(n, nbrs, col, d[1][0])
d = P.cells_of(col); col = P.step(n, nbrs, col, d[9][0])
auts = all_isos(n, adj, col, col)
orb = orbits(n, auts)
print(f"|Aut_chi| = {len(auts)}   wall {time.time()-t0:.1f}s")
d = P.cells_of(col)
for cid in sorted(d):
    cell = d[cid]
    if len(cell) < 2:
        continue
    reps = {}
    for v in cell:
        reps.setdefault(orb[v], []).append(v)
    print(f"  id={cid:<3} |C|={len(cell):<3} orbits inside = {len(reps)}  "
          f"profile={sorted(len(x) for x in reps.values())}  "
          f"{'SINGLE ORBIT' if len(reps) == 1 else 'MIXED'}")
