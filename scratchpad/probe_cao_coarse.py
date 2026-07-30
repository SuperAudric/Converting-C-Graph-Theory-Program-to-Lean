#!/usr/bin/env python3
"""IS THE "non-schurity only at depth 0" LAW REAL, OR JUST DISCRETIZATION SPEED? (2026-07-30)

`probe_cao_induction.py` found: 16k descent nodes, fibre-schurian everywhere, FULL schurity
failing only at the root.  But those descents hit discreteness by depth 4-6 on n = 16-28, and
a near-discrete configuration is trivially schurian -- so the law may be measuring nothing.

The conditional test: among nodes of depth >= 1, how COARSE does the colouring still get?
Report, per object, the largest non-singleton cell seen at each depth, and whether any
depth >= 1 node that is still genuinely coarse fails full schurity.

  * if depth >= 1 nodes are all nearly discrete  -> the law is an artifact, discount it
  * if coarse depth >= 1 nodes exist and are all fully schurian -> the law has content
"""
import sys, time
from collections import defaultdict
from itertools import combinations
sys.path.insert(0, "/workspace/scratchpad")
from probe_cao_cleanroom import wl, individualize, cells, all_isos, orbits
from probe_cao_net import net
from probe_cao_induction import (twowl_pairs, orbital_partition, same_partition, stab,
                                 from_edges, rook, shrikhande, T8, chang, paley)

sys.setrecursionlimit(100000)


def descend(n, adj, auts, col, depth, rec, maxdepth=12):
    H = stab(auts, col, n)
    p2 = twowl_pairs(n, adj, col)
    diag = [p2[v * n + v] for v in range(n)]
    orb = orbits(n, H)
    fibre_ok = same_partition(diag, orb)
    full_ok = same_partition(p2, orbital_partition(n, H))
    d = defaultdict(list)
    for v, c in enumerate(diag):
        d[c].append(v)
    big = [c for c in d.values() if len(c) > 1]
    coarse = max((len(c) for c in big), default=1)
    rec.append((depth, coarse, len(big), fibre_ok, full_ok, len(H)))
    if not big or depth >= maxdepth:
        return
    for cell in big:
        descend(n, adj, auts, individualize(n, diag, cell[0]), depth + 1, rec, maxdepth)


def run(lab, n, adj):
    t0 = time.time()
    A = all_isos(n, adj, wl(n, adj, [0] * n), wl(n, adj, [0] * n), limit=3_000_000)
    orb0 = orbits(n, A)
    m = {}
    oc = [m.setdefault(orb0[v], len(m)) for v in range(n)]
    rec = []
    descend(n, adj, A, oc, 0, rec)
    deep = [r for r in rec if r[0] >= 1]
    coarse_deep = [r for r in deep if r[1] >= 3]           # still a cell of >= 3
    bad_deep = [r for r in deep if not r[4]]
    root = [r for r in rec if r[0] == 0][0]
    per_depth = defaultdict(int)
    for dpt, coarse, nb, fo, uo, h in rec:
        per_depth[dpt] = max(per_depth[dpt], coarse)
    print(f"  {lab:22s} n={n:3d} nodes={len(rec):5d} | root coarse={root[1]:2d} "
          f"full-schur@root={str(root[4]):5s} | max cell by depth "
          f"{dict(sorted(per_depth.items()))}")
    print(f"      depth>=1 nodes: {len(deep):5d}   of which STILL COARSE (cell>=3): "
          f"{len(coarse_deep):5d}   full-schurity failures among them: {len(bad_deep)}"
          f"   ({time.time()-t0:.0f}s)")
    return len(coarse_deep), len(bad_deep)


print("=== is 'non-schurity only at depth 0' real, or just fast discretization? ===")
tot_coarse = tot_bad = 0
for lab, (n, adj) in [("Shrikhande", shrikhande()), ("rook 4x4", rook(4)),
                      ("net(Z4)", net((4,))[:2]), ("net(Z2xZ2)", net((2, 2))[:2]),
                      ("T(8)", T8()),
                      ("Chang-1", chang([(0,1),(2,3),(4,5),(6,7)])),
                      ("Chang-2", chang([(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,0)])),
                      ("Chang-3", chang([(0,1),(0,2),(1,2)]
                                        + [(a,b) for a in range(3,8) for b in range(a+1,8)])),
                      ("Paley(17)", paley(17))]:
    c, b = run(lab, n, adj)
    tot_coarse += c
    tot_bad += b
print(f"\n  TOTAL still-coarse depth>=1 nodes: {tot_coarse}  full-schurity failures: {tot_bad}")
print("  (a small first number means the law is an ARTIFACT of fast discretization)")
