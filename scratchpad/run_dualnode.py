"""Reproduce DUAL_resolver_scoping.md §2.1's second falsifier node — "one equivariant force-key
refinement below the root" of CFI cubic m=8 — and test all three supplies there against the EXACT
orbits.  This is cao-propagation §13.6(b)'s recorded outstanding S4 target.

The gap the 'force inside the descent' route is meant to patch = a cell that IS one orbit (so force
provably cannot fire on it) which the consume supply nonetheless fails to certify."""
import time
import probe_readsupply as P
from probe_cao_cleanroom import cfi, all_isos, orbits

def force_narrow(n, nbrs, adj, col, cell):
    keys = [(P.force_key(n, nbrs, adj, col, v), v) for v in cell]
    best = min(k for k, _ in keys)
    return [v for k, v in keys if k == best]

def report(name, tw):
    t0 = time.time()
    es = P.cubic(8, 19)
    n, adj, _, _ = cfi(es, 8, twisted_nodes=(0,) if tw else ())
    nbrs = P.nbrs_of(n, adj)
    P.nbrs_cache[id(adj)] = nbrs
    root = P.wl(n, nbrs, [0] * n)
    d = P.cells_of(root)
    cid0 = min(c for c in d if len(d[c]) >= 2)
    cell0 = d[cid0]
    kept = force_narrow(n, nbrs, adj, root, cell0)
    print(f"\n=== {name}  n={n}")
    print(f"  root: cells {[(c, len(d[c])) for c in sorted(d)]}; branch cell id={cid0} |C|={len(cell0)}"
          f"  -> force key keeps {len(kept)}/{len(cell0)}")
    col = P.step(n, nbrs, root, kept[0])
    auts = all_isos(n, adj, col, col)
    orb = orbits(n, auts)
    d = P.cells_of(col)
    ns = [(c, d[c]) for c in sorted(d) if len(d[c]) >= 2]
    print(f"  child node (one force-key refinement below root): |Aut_chi| = {len(auts)}, "
          f"non-singleton cells = {[(c, len(x)) for c, x in ns]}")
    for cid, cell in ns:
        reps = {}
        for v in cell:
            reps.setdefault(orb[v], []).append(v)
        single = len(reps) == 1
        firsts = [(r, P.step(n, nbrs, col, r)) for r in cell]
        hg = P.deepen_gens(n, nbrs, adj, col, cell, firsts)
        hok = P.transitive_on(hg, cell)
        rg, _ = P.read_gens(n, nbrs, adj, col, cell, firsts)
        rok = P.transitive_on(rg, cell)
        fg, nleaf, ties, lvls = P.read_gens_forced(n, nbrs, adj, col, cell, firsts)
        fok = P.transitive_on(fg, cell)
        flag = ""
        if single and not hok:
            flag = "   ★★★ THE GAP: one orbit, harvest blind" + (
                "  -> READ-FORCED FIXES IT" if fok else ("  -> read fixes it" if rok else "  -> all three blind"))
        print(f"    id={cid:<3} |C|={len(cell):<3} truth[{len(reps)} orbit(s) "
              f"{sorted(len(x) for x in reps.values())} {'SINGLE' if single else 'MIXED'}]  "
              f"harvest[{len(hg):<4}{'✓' if hok else '✗'}] read[{len(rg):<4}{'✓' if rok else '✗'}] "
              f"read-FORCED[{len(fg):<4}{'✓' if fok else '✗'} ties={ties}/{lvls}]{flag}")
    print(f"  wall {time.time()-t0:.1f}s")

report("CFI cubic m=8 TWISTED", True)
report("CFI cubic m=8 plain", False)
print(f"\nself-check (read-equal pairs failing IsColAut): {len(P.BAD_SELF_CHECK)}")
