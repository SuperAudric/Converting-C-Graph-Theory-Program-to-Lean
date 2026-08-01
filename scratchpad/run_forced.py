"""Variant C at the RECORDED obstruction: CFI cubic m=8 TWISTED, node root/id1/id9.
harvest (replay) vs read (greedy leaves) vs read-FORCED (force-narrowed per-level pick)."""
import time
import probe_readsupply as P
from probe_cao_cleanroom import cfi

t0 = time.time()
es = P.cubic(8, 19)
n, adj, _, _ = cfi(es, 8, twisted_nodes=(0,))
nbrs = P.nbrs_of(n, adj)
P.nbrs_cache[id(adj)] = nbrs
col = P.wl(n, nbrs, [0] * n)
# reproduce root/id1/id9
d = P.cells_of(col); col = P.step(n, nbrs, col, d[1][0])
d = P.cells_of(col); col = P.step(n, nbrs, col, d[9][0])
d = P.cells_of(col)
ns = [(c, d[c]) for c in sorted(d) if len(d[c]) >= 2]
print(f"node root/id1/id9  non-singleton cells = {[(c, len(x)) for c, x in ns]}")
for cid, cell in ns:
    firsts = [(r, P.step(n, nbrs, col, r)) for r in cell]
    hg = P.deepen_gens(n, nbrs, adj, col, cell, firsts)
    hok = P.transitive_on(hg, cell)
    rg, _ = P.read_gens(n, nbrs, adj, col, cell, firsts)
    rok = P.transitive_on(rg, cell)
    fg, nleaf, ties, lvls = P.read_gens_forced(n, nbrs, adj, col, cell, firsts)
    fok = P.transitive_on(fg, cell)
    print(f"  id={cid:<3} |C|={len(cell):<3} "
          f"harvest[{len(hg):<4}{'✓' if hok else '✗'}] "
          f"read[{len(rg):<4}{'✓' if rok else '✗'}] "
          f"read-FORCED[{len(fg):<4}{'✓' if fok else '✗'} leaves={nleaf}/{len(cell)} "
          f"levels-with-ties={ties}/{lvls}]"
          + ("   ★★★ FORCED FIXES IT" if fok and not (hok or rok) else ""))
print(f"bad self-check: {len(P.BAD_SELF_CHECK)}   wall {time.time()-t0:.1f}s")
