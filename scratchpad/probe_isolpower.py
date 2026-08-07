#!/usr/bin/env python3
"""Is `isol = 0` an artefact of stepSum being a SUM, or structural?

Escalate the equivariant vertex invariant and re-ask whether it isolates the
Aut-rigid members of the root cell (the vertices IsolatedBy must catch for
GoodOrIsolated to beat CertifiedG):

  sum   : sum of refined colour ranks after individualizing u   (Lean `stepSum`)
  mset  : sorted MULTISET of those ranks -- strictly finer than sum
  pair  : mset, plus for each w the sorted multiset of ranks after individualizing
          {u,w} -- a 2-step refinement, still poly, still equivariant
All three are relabelling-equivariant (they read only VALUES of a colouring, and
transportColouring permutes positions).
"""
import sys, random
from collections import defaultdict
sys.setrecursionlimit(10000)
from probe_dualdeepen import (circ, FANO, MIXED, rand_incidence, build_mp,
                              build_cfi_base, cubic)
from probe_polyloop import adjlist, refine, indiv, target_cell
from probe_certkey import true_orbit_partition

def inv_sum(n, adjl, col, u):  return sum(indiv(n, adjl, col, u))
def inv_mset(n, adjl, col, u): return tuple(sorted(indiv(n, adjl, col, u)))
def inv_pair(n, adjl, col, u):
    c1 = indiv(n, adjl, col, u)
    return (tuple(sorted(c1)),
            tuple(sorted(tuple(sorted(indiv(n, adjl, c1, w))) for w in range(n))))

def isolated(n, adjl, col, C, f):
    sig = {v: f(n, adjl, col, v) for v in C}
    cnt = defaultdict(int)
    for v in C: cnt[sig[v]] += 1
    return [v for v in C if cnt[sig[v]] == 1]

def analyse(name, n, adj):
    adjl = adjlist(n, adj); col = refine(n, adjl, [0]*n)
    cid, C = target_cell(n, col)
    if cid is None: return
    orb = true_orbit_partition(n, adj, col)
    bs = defaultdict(int)
    for v in range(n): bs[orb[v]] += 1
    rigid = {v for v in C if bs[orb[v]] == 1}
    out = []
    for nm, f in (("sum", inv_sum), ("mset", inv_mset), ("pair", inv_pair)):
        I = set(isolated(n, adjl, col, C, f))
        bad = [v for v in I if v not in rigid]
        out.append(f"{nm}={len(I):3d}{'!UNSOUND' if bad else ''}"
                   f"{'/' + str(len(rigid & I)) + 'r' if I else ''}")
    print(f"{name:30s} cell={len(C):3d} rigid={len(rigid):3d}  " + "  ".join(out))

if __name__ == "__main__":
    for (V,W,d,s) in [(6,5,3,1),(8,6,3,2),(10,7,3,3),(12,8,3,4)]:
        n,adj = build_mp(rand_incidence(V,W,d,s)); analyse(f"rand multipede V={V} W={W}", n, adj)
    for nm,g in [("MIXED",MIXED),("circ(5)",circ(5)),("mp7 Fano",FANO)]:
        n,adj = build_mp(g); analyse(nm+" multipede", n, adj)
    for m in (8,10):
        for tw in (False,True):
            n,adj = build_cfi_base(cubic(m,11+m), m, tw); analyse(f"CFI cubic m={m} tw={tw}", n, adj)
