#!/usr/bin/env python3
"""HUNT (habitat 2): the 122 imprimitive VT voltage covers, analysed DEEP.

`probe_cao_vtcover.py` checked only depth 1.  T2 (= every cell mixed at a reachable node)
typically lives DEEPER: the stabiliser shrinks by exactly the picked cell size at each legal
step, so it can hit 1 while the colouring is still non-discrete.  This walks the whole
descent tree and also reports the NEAR-MISS census: per graph, the reachable node with the
highest fraction of mixed cells, and the smallest stabiliser reached.
"""
import sys
from itertools import product
from collections import defaultdict
sys.path.insert(0, "/workspace/scratchpad")
from probe_cao_cleanroom import wl, individualize, cells, all_isos, orbits
from probe_cao_vtcover import iso_exists, cover, spanning_tree, K, CUBE, PET, K33, circ

sys.setrecursionlimit(100000)


def walk(n, adj, col, memo, stats, budget=300000):
    key = tuple(col)
    if key in memo:
        return memo[key]
    d = cells(col)
    ns = [c for c in sorted(d) if len(d[c]) > 1]
    if not ns:
        memo[key] = True
        return True
    try:
        A = all_isos(n, adj, col, col, limit=budget)
    except RuntimeError:
        memo[key] = True
        return True
    o = orbits(n, A)
    nmixed = sum(1 for c in ns if len({o[v] for v in d[c]}) > 1)
    stats.append((len(A), len(ns), nmixed))
    ex = False
    for c in ns:
        cell = d[c]
        if len({o[v] for v in cell}) > 1:
            continue
        if walk(n, adj, wl(n, adj, individualize(n, col, cell[0])), memo, stats, budget):
            ex = True
    memo[key] = ex
    return ex


def analyse_vt(n, adj):
    root = wl(n, adj, [0] * n)
    if len(set(root)) != 1:
        return None
    for v in range(1, n):
        if iso_exists(n, adj, individualize(n, root, 0),
                      individualize(n, root, v)) is not True:
            return None                                   # not VT
    stats, memo = [], {}
    ex = walk(n, adj, wl(n, adj, individualize(n, root, 0)), memo, stats)
    if not stats:
        return ("discrete", 0, 0.0, 1)
    worst = max(s[2] / s[1] for s in stats)
    minstab = min(s[0] for s in stats)
    return (ex, len(stats), worst, minstab)


CASES = []
for lab, nb, es in [("K4", 4, K(4)), ("K5", 5, K(5)), ("K33", 6, K33),
                    ("C6", 6, circ(6, (1,))[1] and [(i, (i + 1) % 6) for i in range(6)]),
                    ("cube", 8, CUBE), ("K6", 6, K(6)), ("Petersen", 10, PET)]:
    tree, cot = spanning_tree(nb, es)
    for k in (2, 3):
        if k ** len(cot) > 300:      # bound the sweep; skipped combos are reported below
            print(f"  [skip] {lab}/Z{k}: {k}^{len(cot)} voltage assignments exceeds the cap")
            continue
        for vals in product(range(k), repeat=len(cot)):
            volt = [0] * len(es)
            for i, t in zip(cot, vals):
                volt[i] = t
            n, adj = cover(nb, es, volt, k)
            if n <= 30:
                CASES.append((f"{lab}/Z{k}{vals}", n, adj))

print(f"candidate covers: {len(CASES)}")
res = defaultdict(int)
hits = []
near = []
for lab, n, adj in CASES:
    r = analyse_vt(n, adj)
    if r is None:
        res["not-VT"] += 1
        continue
    ex, nodes, worst, minstab = r
    if ex == "discrete":
        res["depth-1 discrete"] += 1
        continue
    res["VT analysed"] += 1
    if ex is False:
        hits.append((lab, n, nodes, worst, minstab))
    if worst > 0:
        near.append((lab, n, nodes, round(worst, 2), minstab))
print(dict(res))
print(f"\n  T2 hits (EXISTS-Tinhofer False): {len(hits)}")
for h in hits[:20]:
    print(f"     ** {h}")
print(f"\n  NEAR MISSES (some reachable node has a mixed cell): {len(near)}")
for h in near[:20]:
    print(f"     {h[0]:22s} n={h[1]} nodes={h[2]} worst-mixed-fraction={h[3]} "
          f"min|Aut_chi|={h[4]}")
