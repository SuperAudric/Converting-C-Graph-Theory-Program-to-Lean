#!/usr/bin/env python3
"""
Q2 CEILING TEST — how much can a BETTER WITHIN-CELL SELECTOR possibly buy?

`Deepen.Tinhofer` is defined along the path deepen actually walks, and deepen breaks
ties by vertex INDEX (`w :: _` = min of the chosen cell).  Memory already records that
Tinhofer is therefore a **(graph, SELECTOR)** property, not a graph property.  So a
smarter selector -- e.g. the user's "prefer a vertex SHARED with the partner descent's
cell" -- changes the class.

Before designing any selector, measure the CEILING:

    for each anchor whose MIN-INDEX path hits a multi-orbit cell,
    does ANY path (any within-cell pick at every level) have all single-orbit cells?

  * If NO path works, no selector rescues that anchor -- the obstruction is the cell
    structure itself and Q2's mechanism cannot help, however it is chosen.
  * If SOME path works, a selector is worth designing, and the ceiling is how many
    anchors it could recover.

Reported per witness:
  bad      anchors whose min-index path hits a multi-orbit cell
  rescued  of those, how many have SOME all-single-orbit path
  ceiling  rescued/bad -- the most any selector could gain here
"""
import sys
from collections import defaultdict
sys.setrecursionlimit(10000)
from probe_dualdeepen import (circ, FANO, MIXED, rand_incidence, build_mp,
                              build_cfi_base, cubic)
from probe_polyloop import adjlist, refine, indiv, target_cell
from probe_certkey import true_orbit_partition

NODE_CAP = 4000


def path_exists(n, adj, adjl, cur, budget):
    """DFS over EVERY within-cell pick.  True if some complete path has every chosen
    cell a single true Aut-orbit.  budget is a mutable [int] node counter."""
    cid, C = target_cell(n, cur)
    if cid is None:
        return True                       # reached discreteness with no violation
    budget[0] -= 1
    if budget[0] <= 0:
        return None                       # unknown -- ran out of search
    orb = true_orbit_partition(n, adj, cur)
    if len({orb[v] for v in C}) > 1:
        return False                      # this cell is multi-orbit for EVERY pick
    unknown = False
    for w in C:
        r = path_exists(n, adj, adjl, indiv(n, adjl, cur, w), budget)
        if r is True:
            return True
        if r is None:
            unknown = True
    return None if unknown else False


def minindex_ok(n, adj, adjl, cur):
    """Does the MIN-INDEX path have all single-orbit cells?  (= GoodAnchor)"""
    for _ in range(n + 1):
        cid, C = target_cell(n, cur)
        if cid is None:
            return True
        orb = true_orbit_partition(n, adj, cur)
        if len({orb[v] for v in C}) > 1:
            return False
        cur = indiv(n, adjl, cur, min(C))
    return False


def analyse(name, n, adj):
    adjl = adjlist(n, adj)
    col = refine(n, adjl, [0] * n)
    cid, C = target_cell(n, col)
    if cid is None:
        print(f"{name:30s}  discrete root")
        return
    bad, rescued, unknown = [], 0, 0
    for a in C:
        start = indiv(n, adjl, col, a)
        if minindex_ok(n, adj, adjl, start):
            continue
        bad.append(a)
        r = path_exists(n, adj, adjl, start, [NODE_CAP])
        if r is True:
            rescued += 1
        elif r is None:
            unknown += 1
    if not bad:
        print(f"{name:30s} cell={len(C):3d}  bad=0  (min-index path already good everywhere)")
    else:
        print(f"{name:30s} cell={len(C):3d}  bad={len(bad):3d}  rescued={rescued:3d}"
              f"  unknown={unknown:3d}  CEILING={'SOME PATH EXISTS' if rescued else 'NO PATH HELPS'}")


if __name__ == "__main__":
    print("Ceiling on any within-cell selector (incl. the shared-vertex rule)\n")
    for (V, W, d, s) in [(6, 5, 3, 1), (8, 6, 3, 2), (10, 7, 3, 3), (12, 8, 3, 4)]:
        n, adj = build_mp(rand_incidence(V, W, d, s))
        analyse(f"rand multipede V={V} W={W}", n, adj)
    for nm, g in [("MIXED", MIXED), ("circ(5)", circ(5))]:
        n, adj = build_mp(g)
        analyse(nm + " multipede", n, adj)
    for m in (8, 10):
        n, adj = build_cfi_base(cubic(m, 11 + m), m, False)
        analyse(f"CFI cubic m={m}", n, adj)
