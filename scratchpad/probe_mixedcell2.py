#!/usr/bin/env python3
"""Same witness, measured at the HUB cell (the mixed one): orbits {h1,h2} and {h3}."""
import sys
from collections import defaultdict
sys.setrecursionlimit(100000)
from probe_polyloop import adjlist, refine, indiv, target_cell
from probe_certkey import true_orbit_partition
from probe_mixedcell import build

def descend_cert_from(n, adj, adjl, col, a):
    """all chosen cells single true-orbit along the greedy path from a"""
    cur = indiv(n, adjl, col, a)
    for _ in range(n + 2):
        cid, C = target_cell(n, cur)
        if cid is None: return True
        orb = true_orbit_partition(n, adj, cur)
        if len({orb[v] for v in C}) > 1: return False
        cur = indiv(n, adjl, cur, min(C))
    return False

n, adj, hubs = build()
adjl = adjlist(n, adj); col = refine(n, adjl, [0]*n)
orb = true_orbit_partition(n, adj, col)
bs = defaultdict(int)
for v in range(n): bs[orb[v]] += 1
C = hubs
print(f"hub cell {C}  orbit ids {[orb[v] for v in C]}  block sizes {[bs[orb[v]] for v in C]}")
good = [v for v in C if descend_cert_from(n, adj, adjl, col, v)]
rigid = [v for v in C if bs[orb[v]] == 1]
print(f"good anchors: {good}   Aut-rigid: {rigid}")
for nm, f in (("stepSum", lambda u: sum(indiv(n, adjl, col, u))),
              ("mset",    lambda u: tuple(sorted(indiv(n, adjl, col, u))))):
    sig = {v: f(v) for v in C}
    cnt = defaultdict(int)
    for v in C: cnt[sig[v]] += 1
    isol = [v for v in C if cnt[sig[v]] == 1]
    prim = len(good) == len(C)
    sec  = all((v in good) or (v in isol) for v in C)
    bad  = [v for v in isol if bs[orb[v]] != 1]
    print(f"  inv={nm:8s} isol={isol}  PRIM(CertifiedG)={'open' if prim else 'SHUT'}"
          f"  SEC(GoodOrIsolated)={'open' if sec else 'SHUT'}"
          f"{'   *** STRICT WIN ***' if sec and not prim else ''}"
          f"{'  !!UNSOUND ' + str(bad) if bad else ''}")
