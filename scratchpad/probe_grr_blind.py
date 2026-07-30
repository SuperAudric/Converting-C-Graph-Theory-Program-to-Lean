#!/usr/bin/env python3
"""
PROBE 4 (the user's GRR reduction, 2026-07-29):

  "VT -> Tinhofer can be traced to finding a graphical regular representation whose 1-WL
   refinement does not discretize after individualizing one vertex."

That reduction is CORRECT: a GRR has Aut acting regularly => TRIVIAL vertex stabiliser =>
after individualizing v every orbit is a singleton, so `CellSingleOrbit` on any chosen
(non-singleton) cell is automatically FALSE.  Hence

    for a GRR:   Tinhofer  <=>  1-WL discretizes after ONE individualization.

So one GRR that stays non-discrete refutes `VT => Tinhofer`.

Habitat: Cay(Z2^k, S).  Aut(Cay(Z2^k,S)) >= Z2^k :| Stab_{GL(k,2)}(S), and 1-WL on it sees
only weight-profile data -- the Cayley/code-equivalence corner, where blindness is
plausible.  n=16 (k=4) is likely too small; k=5 gives n=32.

Two-stage, cheap filter first:
  stage 1 (free)  -- individualize vertex 0, 1-WL: does it discretize?
  stage 2 (costly) -- for survivors, exact stabiliser orbits: is some cell MIXED?
"""
import sys, random
from collections import defaultdict
from itertools import product

sys.path.insert(0, "/workspace/scratchpad")
from probe_dualdeepen import refine, indiv
from probe_orbit_oracle import orbit_partition

def cayley_z2k(k, S):
    els = list(product(range(2), repeat=k))
    idx = {e: i for i, e in enumerate(els)}
    n = len(els)
    adj = [[0] * n for _ in range(n)]
    for e in els:
        for s in S:
            f = tuple((a + b) % 2 for a, b in zip(e, s))
            adj[idx[e]][idx[f]] = adj[idx[f]][idx[e]] = 1
    return n, adj

def cells(col):
    d = defaultdict(list)
    for v, c in enumerate(col):
        d[c].append(v)
    return list(d.values())

random.seed(20260729)
print(f"{'k':>2s} {'|S|':>4s} {'n':>3s}  stage1: colours after indiv(0)   stage2")
print("-" * 76)

cands = 0
tested = 0
hits = []
for k in (4, 5):
    els = [e for e in product(range(2), repeat=k) if any(e)]
    n = 2 ** k
    seen = set()
    for trial in range(400 if k == 5 else 200):
        sz = random.randint(3, max(3, k + 3))
        S = tuple(sorted(random.sample(els, min(sz, len(els)))))
        if S in seen:
            continue
        seen.add(S)
        n_, adj = cayley_z2k(k, list(S))
        root = refine(n_, adj, [0] * n_)
        if len(set(root)) != 1:
            continue                                  # 1-WL already splits => not VT
        c1 = refine(n_, adj, indiv(n_, root, 0))
        ncol = len(set(c1))
        tested += 1
        if ncol == n_:
            continue                                  # discretized: Tinhofer-compatible
        cands += 1
        # stage 2: is any surviving cell MIXED under the true stabiliser?
        part = orbit_partition(n_, adj, c1, list(range(n_)))
        if part is None:
            print(f"{k:2d} {len(S):4d} {n_:3d}  non-discrete ({ncol} colours)        oracle BLOWN")
            continue
        mixed = [c for c in cells(c1) if len({part[v] for v in c}) > 1]
        stab_sizes = sorted({sum(1 for u in range(n_) if part[u] == part[v])
                             for v in range(n_)})
        if mixed:
            hits.append((k, S, n_, ncol, [len(c) for c in mixed]))
            print(f"{k:2d} {len(S):4d} {n_:3d}  non-discrete ({ncol} colours)  "
                  f"★★★ MIXED CELLS {[len(c) for c in mixed]}  orbit sizes {stab_sizes}")
        else:
            print(f"{k:2d} {len(S):4d} {n_:3d}  non-discrete ({ncol} colours)  "
                  f"cells ARE orbits (stab orbit sizes {stab_sizes}) -> Tinhofer-ok")

print("-" * 76)
print(f"VT Cay(Z2^k,S) tested: {tested}")
print(f"  non-discretizing after one individualization: {cands}")
print(f"  of those, carrying a MIXED cell (= refutes VT=>Tinhofer): {len(hits)}")
if hits:
    print()
    for k, S, n_, ncol, ms in hits:
        print(f"  ★ k={k} n={n_} S={list(S)} colours={ncol} mixed cell sizes={ms}")
