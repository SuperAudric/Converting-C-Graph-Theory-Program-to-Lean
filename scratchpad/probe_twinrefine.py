#!/usr/bin/env python3
"""
The TWIN-REFINEMENT mechanism, measured against its ceiling.

User's clarification (2026-08-06): the coupling is a modification to the **1-WL**, not
to the selector.  Two branches are two colourings of the SAME vertex set; a vertex's
"twin" is the vertex of the same index in the other branch.  Whether a vertex's twin
followed it into a new cell this round is structurally visible, and -- unlike
intersecting two STABLE colourings -- the signal PROPAGATES to neighbours.

Three objects, increasing strength:
  (i)   MEET   : intersect the two stable 1-WL colourings.  No propagation.
  (ii)  TWIN   : 1-WL run on the JOINT colouring (c_A(v), c_B(v)).  Propagates.
                 = the user's mechanism.
  (iii) BOTH   : refine after individualizing a AND b.  Proved ceiling for (ii):
                 BOTH refines each of chi_a, chi_b, so it determines the joint colour,
                 so it refines TWIN.

Reported: are the partitions equal?  If TWIN == BOTH the cheap signal reaches the
ceiling; if TWIN < BOTH the mechanism is strictly weaker than just individualizing both.
"""
import sys
from collections import defaultdict
sys.setrecursionlimit(10000)
from probe_dualdeepen import rand_incidence, build_mp, build_cfi_base, cubic
from probe_polyloop import adjlist, refine, indiv, target_cell
from probe_certkey import true_orbit_partition

def part(col):
    d = defaultdict(list)
    for v, c in enumerate(col): d[c].append(v)
    return frozenset(frozenset(g) for g in d.values())

def joint_refine(n, adjl, ca, cb):
    """1-WL on the joint colouring (ca(v), cb(v)) -- the TWIN object."""
    key = {}
    init = []
    for v in range(n):
        k = (ca[v], cb[v])
        if k not in key: key[k] = len(key)
        init.append(key[k])
    return refine(n, adjl, init)

def analyse(name, n, adj):
    adjl = adjlist(n, adj); col = refine(n, adjl, [0]*n)
    cid, C = target_cell(n, col)
    eq = lt = 0
    repaired_twin = 0
    bad = []
    for a in C:
        ca = indiv(n, adjl, col, a)
        # is a a bad anchor under plain 1-WL?
        cur, ok = ca, True
        for _ in range(n + 2):
            c2, C2 = target_cell(n, cur)
            if c2 is None: break
            orb = true_orbit_partition(n, adj, cur)
            if len({orb[v] for v in C2}) > 1: ok = False; break
            cur = indiv(n, adjl, cur, min(C2))
        if ok: continue
        bad.append(a)
        fixed = False
        for b in C:
            if b == a: continue
            cb = indiv(n, adjl, col, b)
            twin = joint_refine(n, adjl, ca, cb)
            both = indiv(n, adjl, ca, b)
            if part(twin) == part(both): eq += 1
            else: lt += 1
            # does TWIN alone repair a's descent?
            cur2, ok2 = twin, True
            for _ in range(n + 2):
                c3, C3 = target_cell(n, cur2)
                if c3 is None: break
                orb = true_orbit_partition(n, adj, cur2)
                if len({orb[v] for v in C3}) > 1: ok2 = False; break
                cur2 = indiv(n, adjl, cur2, min(C3))
            if ok2: fixed = True
        if fixed: repaired_twin += 1
    print(f"{name:26s} bad={len(bad):3d} TWIN==BOTH:{eq:4d}  TWIN<BOTH:{lt:4d}"
          f"  repaired-by-TWIN={repaired_twin:3d}")

if __name__ == "__main__":
    n, adj = build_mp(rand_incidence(12, 8, 3, 4)); analyse("rand multipede V=12 W=8", n, adj)
    n, adj = build_cfi_base(cubic(10, 21), 10, False); analyse("CFI cubic m=10", n, adj)
