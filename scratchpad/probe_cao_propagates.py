#!/usr/bin/env python3
"""
PROBE 5 — the user's CORRECTED question (2026-07-29):

  "1-WL does not provide CAO on the root of CFI, but the argument does not require this.
   Provide some pre-processing step (i.e. a single closure of k-WL with k=n) that causes
   CellsAreOrbits; the orbit refinement should still apply even if it could not be
   initially found."

Right -- the hypothesis is "the starting partition IS the orbit partition", HOWEVER
obtained.  So the correct probe SUPPLIES the orbit partition as the initial colouring
instead of filtering on 1-WL reachability.  This puts CFI over RIGID bases back in scope,
which my earlier narrowing wrongly excluded.

    DOES CAO PROPAGATE?   start from the orbit partition, individualize one vertex,
                          take the 1-WL closure -- are the cells again exactly the orbits?

Equivalently (my framing last turn): do cells refine at least as fast as orbits?

Bonus: the reverse direction.  `Tinhofer`'s recursion starts at `step adj chi r`, one
individualization DOWN, so it never constrains chi's own branch cell => `Tinhofer => CAO`
should FAIL on a graph whose root cell is mixed but whose every branch is clean.  G8 is the
candidate (regular, non-VT: 1-WL gives one cell of 8 that is not an orbit).
"""
import sys
from collections import defaultdict
from itertools import product

sys.path.insert(0, "/workspace/scratchpad")
from probe_dualdeepen import (refine, indiv, build_mp, build_cfi, build_cfi_base,
                              cubic, rand_incidence, circ, FANO, MIXED)
from probe_orbit_oracle import orbit_partition

def cells(col):
    d = defaultdict(list)
    for v, c in enumerate(col):
        d[c].append(v)
    return list(d.values())

def orbit_colouring(n, adj, col):
    """Replace `col` by the exact Aut(adj,col)-orbit partition (the k-WL preprocessing)."""
    part = orbit_partition(n, adj, col, list(range(n)))
    if part is None:
        return None
    reps = sorted({part[v] for v in range(n)})
    rank = {r: i for i, r in enumerate(reps)}
    return [rank[part[v]] for v in range(n)]

def cao(n, adj, col):
    """Is every cell of `col` a single Aut(adj,col)-orbit?"""
    part = orbit_partition(n, adj, col, list(range(n)))
    if part is None:
        return None, None
    bad = [c for c in cells(col) if len({part[v] for v in c}) > 1]
    return (len(bad) == 0), bad

def propagates(name, n, adj, out):
    """Start from the ORBIT PARTITION; individualize each v; does CAO survive?"""
    base = refine(n, adj, [0] * n)
    oc = orbit_colouring(n, adj, base)
    if oc is None:
        return "blown"
    # sanity: CAO holds by construction at the start
    ok0, _ = cao(n, adj, oc)
    if ok0 is None:
        return "blown"
    if not ok0:
        return "sanity-fail"
    for v in range(n):
        c1 = refine(n, adj, indiv(n, oc, v))
        ok1, bad1 = cao(n, adj, c1)
        if ok1 is None:
            return "blown"
        if not ok1:
            part = orbit_partition(n, adj, c1, list(range(n)))
            sizes = [sorted(sum(1 for u in c if part[u] == o)
                            for o in {part[x] for x in c}) for c in bad1]
            out.append((name, n, v, sizes))
            return "COUNTEREXAMPLE"
    return "ok"

CASES = []
for m in range(3, 7):
    for tw in (False, True):
        CASES.append((f"CFI[C{m}]{'-tw' if tw else ''}", *build_cfi(m, twist=tw)))
BASES = {"K4": [(i,j) for i in range(4) for j in range(i+1,4)],
         "K33": [(i,3+j) for i in range(3) for j in range(3)],
         "prism": [(0,1),(1,2),(2,0),(3,4),(4,5),(5,3),(0,3),(1,4),(2,5)]}
for bn, be in BASES.items():
    mm = 1 + max(max(e) for e in be)
    for tw in (False, True):
        CASES.append((f"CFI[{bn}]{'-tw' if tw else ''}", *build_cfi_base(be, mm, twist=tw)))
for seed in range(4):
    CASES.append((f"CFI[cubic6.{seed}]", *build_cfi_base(cubic(6, seed), 6)))
for A in (FANO, MIXED):
    CASES.append((f"multipede[{len(A)}x{len(A[0])}]", *build_mp(A)))
for seed in range(4):
    CASES.append((f"mp[4x4d3.{seed}]", *build_mp(rand_incidence(4, 4, 3, seed))))
for m in (5, 7, 9, 10, 12):
    for offs in ((1,), (1, 2)):
        CASES.append((f"circ({m},{offs})", m, circ(m, offs)))
G8 = [[0]*8 for _ in range(8)]
for (a,b) in [(0,1),(1,2),(2,0),(3,4),(4,5),(5,3),(0,6),(3,6),(6,7),(1,7),(4,7),(2,5)]:
    G8[a][b] = G8[b][a] = 1
CASES.append(("G8", 8, G8))

print("DOES CAO PROPAGATE?  (start from the exact orbit partition, individualize, 1-WL)")
print("-" * 80)
tally = defaultdict(int)
found = []
for name, n, adj in CASES:
    if n > 30:
        tally["too-big"] += 1
        continue
    try:
        r = propagates(name, n, adj, found)
    except Exception as ex:
        r = f"err"
    tally[r] += 1
    mark = "★★★ " if r == "COUNTEREXAMPLE" else "    "
    print(f"{mark}{name:24s} n={n:3d}  {r}")
    if r == "COUNTEREXAMPLE":
        nm, nn, v, sizes = found[-1]
        print(f"      individualizing {v} leaves mixed cells, orbit sizes {sizes}")
print("-" * 80)
for k, v in sorted(tally.items()):
    print(f"  {k:18s} {v}")

# ── reverse direction: Tinhofer => CAO ?  (G8: mixed root cell) ────────────────
print()
print("[reverse] is the ROOT cell a single orbit?  (Tinhofer never checks it)")
for name, n, adj in [("G8", 8, G8), ("circ(5,(1,))", 5, circ(5, (1,)))]:
    root = refine(n, adj, [0] * n)
    ok, bad = cao(n, adj, root)
    part = orbit_partition(n, adj, root, list(range(n)))
    sizes = sorted({sum(1 for u in range(n) if part[u] == part[v]) for v in range(n)})
    print(f"  {name:16s} cells={len(cells(root))} CAO={ok} orbit-size-profile={sizes}")
