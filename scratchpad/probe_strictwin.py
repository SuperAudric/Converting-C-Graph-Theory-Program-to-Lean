#!/usr/bin/env python3
"""
HUNT FOR THE STRICT WIN, now that the two failed attempts say exactly where it must live.

  C3/C4 witness : bad anchors were the TWINS -- not rigid, so not soundly isolable. No win.
  C8 witness    : no bad anchors at all.                                            No win.

So a strict win needs a cell whose BAD anchors are all Aut-RIGID and inv-isolable.
The cleanest source: a RIGID graph (|Aut| = 1) that 1-WL does not discretize.  Then every
cell member is Aut-rigid, so any non-singleton cell has all-singleton orbits ->
CellSingleOrbit FAILS -> every anchor is bad -> CertifiedG SHUT; while OrbitTrivial holds
for everyone, so GoodOrIsolated is OPEN as soon as inv separates the cell.

(The rigid multipedes in the earlier sweep are exactly this shape but isol = 0 -- they are
built to defeat WL-computable invariants.  A generic rigid regular graph should not be.)
"""
import sys, random
from collections import defaultdict
sys.setrecursionlimit(100000)
from probe_polyloop import adjlist, refine, indiv, target_cell
from probe_certkey import true_orbit_partition
from probe_mixedcell2 import descend_cert_from

def rand_reg(n, d, rng):
    for _ in range(400):
        stubs = [v for v in range(n) for _ in range(d)]
        rng.shuffle(stubs)
        adj = [[0]*n for _ in range(n)]
        ok = True
        for i in range(0, len(stubs), 2):
            a, b = stubs[i], stubs[i+1]
            if a == b or adj[a][b]: ok = False; break
            adj[a][b] = adj[b][a] = 1
        if ok: return adj
    return None

def check(n, adj):
    adjl = adjlist(n, adj); col = refine(n, adjl, [0]*n)
    cid, C = target_cell(n, col)
    if cid is None or len(C) < 2: return None
    orb = true_orbit_partition(n, adj, col)
    bs = defaultdict(int)
    for v in range(n): bs[orb[v]] += 1
    rigid = [v for v in C if bs[orb[v]] == 1]
    good  = [v for v in C if descend_cert_from(n, adj, adjl, col, v)]
    res = {}
    for nm, f in (("stepSum", lambda u: sum(indiv(n, adjl, col, u))),
                  ("mset",    lambda u: tuple(sorted(indiv(n, adjl, col, u))))):
        sig = {v: f(v) for v in C}
        cnt = defaultdict(int)
        for v in C: cnt[sig[v]] += 1
        isol = [v for v in C if cnt[sig[v]] == 1]
        prim = len(good) == len(C)
        sec  = all((v in good) or (v in isol) for v in C)
        unsound = [v for v in isol if bs[orb[v]] != 1]
        res[nm] = (prim, sec, len(isol), unsound)
    return len(C), len(rigid), len(good), res

if __name__ == "__main__":
    rng = random.Random(20260806)
    wins = 0; tested = 0
    for trial in range(60):
        n = rng.choice([10, 12, 14]); d = 3
        adj = rand_reg(n, d, rng)
        if adj is None: continue
        r = check(n, adj)
        if r is None: continue
        tested += 1
        cell, rigid, good, res = r
        prim, sec, nisol, unsound = res["stepSum"]
        if unsound: print(f"  !!UNSOUND at trial {trial}: {unsound}")
        if sec and not prim:
            wins += 1
            if wins <= 3:
                print(f"*** STRICT WIN  n={n} cell={cell} rigid={rigid} good={good} isol={nisol}")
                print(f"    adj rows = {[''.join(map(str,row)) for row in adj]}")
    print(f"\ntested={tested}  STRICT WINS={wins}")
