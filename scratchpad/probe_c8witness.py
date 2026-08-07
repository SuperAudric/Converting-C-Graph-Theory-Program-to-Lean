#!/usr/bin/env python3
"""
User's second construction (2026-08-06): link the twins through a SHARED structure so that
individualizing one pins the other, instead of leaving a mixed cell below.

  C8 on 0..7; h1=8 joined to the even vertices, h2=9 joined to the odd ones;
  C4 on 10..13; h3=14 joined to all of it.
Degrees: hubs 4/4/4, all cycle vertices 3 -> 1-WL stable at two cells.
Aut: rotation-by-1 swaps h1<->h2 (one orbit), h3 is its own orbit.

Reports, at BOTH 1-WL cells: orbits, good anchors, and the two guard verdicts.
A STRICT WIN needs: every anchor good-or-isolated, but NOT every anchor good.
"""
import sys
from collections import defaultdict
sys.setrecursionlimit(100000)
from probe_polyloop import adjlist, refine, indiv, target_cell
from probe_certkey import true_orbit_partition
from probe_mixedcell2 import descend_cert_from

def build():
    n = 15
    adj = [[0]*n for _ in range(n)]
    def e(a,b): adj[a][b] = adj[b][a] = 1
    for i in range(8): e(i, (i+1) % 8)
    for i in range(0, 8, 2): e(8, i)
    for i in range(1, 8, 2): e(9, i)
    for i in range(4): e(10+i, 10+(i+1) % 4)
    for i in range(4): e(14, 10+i)
    return n, adj

n, adj = build()
adjl = adjlist(n, adj); col = refine(n, adjl, [0]*n)
print("degrees:", [sum(r) for r in adj])
print("1-WL cells:", sorted(defaultdict(int, {c: col.count(c) for c in set(col)}).items()))
orb = true_orbit_partition(n, adj, col)
bs = defaultdict(int)
for v in range(n): bs[orb[v]] += 1

cells = defaultdict(list)
for v in range(n): cells[col[v]].append(v)
cid, branch = target_cell(n, col)
for c, C in sorted(cells.items()):
    if len(C) < 2: continue
    tag = " (ROOT BRANCH CELL)" if C == branch else ""
    good = [v for v in C if descend_cert_from(n, adj, adjl, col, v)]
    rigid = [v for v in C if bs[orb[v]] == 1]
    norb = len({orb[v] for v in C})
    print(f"\ncell colour {c}: {C}{tag}\n  orbits={norb} good={good} Aut-rigid={rigid}")
    for nm, f in (("stepSum", lambda u: sum(indiv(n, adjl, col, u))),
                  ("mset",    lambda u: tuple(sorted(indiv(n, adjl, col, u))))):
        sig = {v: f(v) for v in C}
        cnt = defaultdict(int)
        for v in C: cnt[sig[v]] += 1
        isol = [v for v in C if cnt[sig[v]] == 1]
        prim = len(good) == len(C)
        sec = all((v in good) or (v in isol) for v in C)
        bad = [v for v in isol if bs[orb[v]] != 1]
        print(f"  inv={nm:8s} isol={isol}  CertifiedG={'open' if prim else 'SHUT'}"
              f"  GoodOrIsolated={'open' if sec else 'SHUT'}"
              f"{'   *** STRICT WIN ***' if sec and not prim else ''}"
              f"{'  !!UNSOUND ' + str(bad) if bad else ''}")
