#!/usr/bin/env python3
"""
PROBE 3 (user, 2026-07-29): does `CellsAreOrbits` imply `Tinhofer`?

  "Take some graph such that every cell contains only one orbit.  Individualize one
   vertex.  ... For two vertices to be in the same cell but different orbit, they must be
   connected to another mixed cell, but for that to arise it would have had to already
   have existed (contradicts starting conditions) or be structurally different to the
   original vertex without being structurally different to the vertex's own neighbours,
   which does not make sense."

Formally the claim is: **schurianity is preserved by one-point individualization +
1-WL closure.**  This probe searches for a counterexample:

    CellsAreOrbits(adj, WL-root)  AND  NOT CellsAreOrbits(adj, WL(indiv(root, v)))

Search space is much larger than probe 1/2 (no VT restriction), so the interesting
sources are the WL-blind constructions: CFI over many bases, multipedes, plus the VT
families as a control.

ALSO (part A): the GRR vacuity check on probes 1+2 — how many of the 498 VT graphs had a
TRIVIAL vertex stabiliser?  If none did, 498/498 never tested the user's sharp case.
"""
import sys, random
from collections import defaultdict
from itertools import combinations, product

sys.path.insert(0, "/workspace/scratchpad")
from probe_dualdeepen import (refine, indiv, build_mp, build_cfi, build_cfi_base,
                              cubic, rand_incidence, circ, FANO, MIXED)
from probe_orbit_oracle import orbit_partition

def cells(col):
    d = defaultdict(list)
    for v, c in enumerate(col):
        d[c].append(v)
    return list(d.values())

def cells_are_orbits(n, adj, col):
    """Every 1-WL cell is a single orbit of Aut(adj, col).  None = oracle blew up."""
    part = orbit_partition(n, adj, col, list(range(n)))
    if part is None:
        return None, None
    bad = [c for c in cells(col) if len({part[v] for v in c}) > 1]
    return (len(bad) == 0), bad

def stabilizer_trivial(n, adj, col):
    part = orbit_partition(n, adj, col, list(range(n)))
    if part is None:
        return None
    return all(sum(1 for u in range(n) if part[u] == part[v]) == 1 for v in range(n))

# ───────────────────────────────────────────── part A: GRR vacuity check on probes 1+2
def grr_audit(cases, label):
    triv = nontriv = blown = 0
    disc_fail = []
    for name, n, adj in cases:
        root = refine(n, adj, [0] * n)
        if len(set(root)) != 1:
            continue                                   # not VT
        # individualize vertex 0, refine, ask whether the STABILISER is trivial
        c1 = refine(n, adj, indiv(n, root, 0))
        t = stabilizer_trivial(n, adj, c1)
        if t is None:
            blown += 1
            continue
        if t:
            triv += 1
            if len(set(c1)) != n:                      # trivial stabiliser but NOT discrete
                disc_fail.append((name, n, len(set(c1))))
        else:
            nontriv += 1
    print(f"[A] {label}: VT graphs with TRIVIAL vertex stabiliser (GRR-like): {triv}")
    print(f"[A] {label}: with NON-trivial stabiliser: {nontriv}   (oracle blown: {blown})")
    if disc_fail:
        print(f"[A] ★★★ GRR-like AND 1-WL does NOT discretize after one individualization:")
        for nm, n, k in disc_fail:
            print(f"        {nm} (n={n}, {k} colours)")
    elif triv:
        print(f"[A] all {triv} GRR-like cases DO discretize after one individualization")
    else:
        print(f"[A] ⚠⚠ ZERO GRR-like cases — the sharp direction was NEVER TESTED (vacuous)")

# ───────────────────────────────────────────── part B: CellsAreOrbits => Tinhofer?
def check(name, n, adj, out):
    root = refine(n, adj, [0] * n)
    ok, bad = cells_are_orbits(n, adj, root)
    if ok is None:
        return "blown"
    if not ok:
        return "root-not-CAO"
    # CellsAreOrbits holds at the root.  Now individualize EVERY vertex.
    for v in range(n):
        c1 = refine(n, adj, indiv(n, root, v))
        ok1, bad1 = cells_are_orbits(n, adj, c1)
        if ok1 is None:
            return "blown"
        if not ok1:
            part = orbit_partition(n, adj, c1, list(range(n)))
            sizes = [sorted(sum(1 for u in c if part[u] == o) for o in {part[x] for x in c})
                     for c in bad1]
            out.append((name, n, v, sizes))
            return "COUNTEREXAMPLE"
    return "ok"

CASES = []
# CFI over many bases (the WL-blind habitat)
for m in range(3, 8):
    for tw in (False, True):
        try:
            CASES.append((f"CFI[C{m}]{'-tw' if tw else ''}", *build_cfi(m, twist=tw)))
        except Exception:
            pass
BASES = {
    "K4": [(i, j) for i in range(4) for j in range(i + 1, 4)],
    "K33": [(i, 3 + j) for i in range(3) for j in range(3)],
    "K5": [(i, j) for i in range(5) for j in range(i + 1, 5)],
    "prism": [(0,1),(1,2),(2,0),(3,4),(4,5),(5,3),(0,3),(1,4),(2,5)],
}
for bn, be in BASES.items():
    mm = 1 + max(max(e) for e in be)
    for tw in (False, True):
        try:
            CASES.append((f"CFI[{bn}]{'-tw' if tw else ''}", *build_cfi_base(be, mm, twist=tw)))
        except Exception:
            pass
for seed in range(6):
    for m in (6, 8):
        try:
            CASES.append((f"CFI[cubic{m}.{seed}]", *build_cfi_base(cubic(m, seed), m)))
        except Exception:
            pass
# multipedes
for A in (FANO, MIXED):
    try:
        CASES.append((f"multipede[{len(A)}x{len(A[0])}]", *build_mp(A)))
    except Exception:
        pass
for seed in range(8):
    for (V, W, deg) in ((4, 4, 3), (5, 4, 3), (5, 5, 3)):
        try:
            CASES.append((f"mp[{V}x{W}d{deg}.{seed}]", *build_mp(rand_incidence(V, W, deg, seed))))
        except Exception:
            pass
# VT controls
for m in range(5, 13):
    for offs in ((1,), (1, 2), (1, 3), (1, 2, 3)):
        if max(offs) * 2 <= m:
            CASES.append((f"circ({m},{offs})", m, circ(m, offs)))

print(f"cases: {len(CASES)}\n")
grr_audit([(a, b, c) for a, b, c in CASES], "probe-1/2 families")
print()

print("[B] CellsAreOrbits(root) AND NOT CellsAreOrbits(after one individualization)?")
print("-" * 78)
tally = defaultdict(int)
found = []
for name, n, adj in CASES:
    if n > 34:
        tally["too-big"] += 1
        continue
    try:
        r = check(name, n, adj, found)
    except Exception as ex:
        r = "err"
    tally[r] += 1
    if r == "COUNTEREXAMPLE":
        nm, nn, v, sizes = found[-1]
        print(f"★★★ {nm} (n={nn}): CAO at root, BROKEN by individualizing {v}; "
              f"mixed cells orbit-sizes {sizes}")
print("-" * 78)
for k, v in sorted(tally.items()):
    print(f"  {k:18s} {v}")
print(f"\ncounterexamples: {len(found)}")
