#!/usr/bin/env python3
"""
MECHANISM of the E-A repair: at the CFI-cubic m=8 node whose |C|=16 branch cell is ONE true orbit
(so `forceBy_no_narrowing_on_orbit` FORBIDS the outer force resolver from acting), today's greedy
harvest certifies nothing and the interleaved harvest certifies the cell.  WHY?

Prediction (DUAL §2's mechanism): the anchor descent and the replay stay aligned through every
single-orbit cell and diverge at the first MIXED cell.  The interleaved version should show an
equivariant key FIRING at exactly that cell, so no pick is ever made from a mixed cell.

Printed per (anchor, rep) pair: the level at which the greedy pair first individualizes vertices in
different Aut-orbits (the divergence), and whether the key fires on that same cell.
"""
import sys, time
from collections import Counter, defaultdict
sys.setrecursionlimit(20000)
sys.path.insert(0, "/workspace/scratchpad")

from probe_dualdeepen import build_cfi_base, cubic, Ctx, canon
from probe_polyloop import adjlist, refine, indiv, target_cell, twist, transitive_on
from probe_inner_force import (K1, K2, K3, KEYS, force_fires, apply_split, true_orbits,
                               greedy_deepen, greedy_replay, harvest, interleaved_deepen)

def node_of_interest(n, adj):
    """Root -> 1-WL -> force-split while a key fires -> the first cell no key splits."""
    adjl = adjlist(n, adj)
    col = refine(n, adjl, [0] * n)
    while True:
        cid, C = target_cell(n, col)
        if cid is None:
            return None, None, None
        hit = None
        for nm, kf in KEYS:
            ks = force_fires(n, adj, adjl, col, C, kf)
            if ks is not None:
                hit = ks; break
        if hit is None:
            return col, cid, C
        col = apply_split(n, adjl, col, hit)

def orbit_id(n, adj, adjl, col, C):
    """map vertex -> its true Aut(adj,col)-orbit index inside C"""
    orb = true_orbits(n, adj, adjl, col, C)
    if orb is None:
        return None
    m = {}
    for i, blk in enumerate(orb):
        for v in blk:
            m[v] = i
    return m

def trace_greedy(n, adj, adjl, col_a, col_j, maxlev=60):
    """Run the two descents in lockstep; report the first level whose chosen cell is MIXED, and
    whether the key ladder fires there."""
    for lev in range(maxlev):
        cid_a, Ca = target_cell(n, col_a)
        cid_j, Cj = target_cell(n, col_j)
        if cid_a is None or cid_j is None:
            return ('discrete', lev, None, None)
        if cid_a != cid_j:
            return ('id-mismatch', lev, cid_a, cid_j)
        # is the anchor-side chosen cell a single orbit of the CURRENT stabilizer?
        om = orbit_id(n, adj, adjl, col_a, Ca)
        norb = None if om is None else len(set(om.values()))
        if norb is not None and norb > 1:
            fired = [nm for nm, kf in KEYS if force_fires(n, adj, adjl, col_a, Ca, kf) is not None]
            return ('mixed-cell', lev, (len(Ca), norb), fired)
        col_a = indiv(n, adjl, col_a, min(Ca))
        col_j = indiv(n, adjl, col_j, min(Cj))
    return ('fuel', maxlev, None, None)

if __name__ == "__main__":
    m = 8
    for tw in (False, True):
        es = cubic(m, 11 + m)
        n, adj = build_cfi_base(es, m, tw)
        adjl = adjlist(n, adj)
        col, cid, C = node_of_interest(n, adj)
        if col is None:
            print(f"CFI m={m} {'tw' if tw else 'pl'}: no stalled cell"); continue
        om = orbit_id(n, adj, adjl, col, C)
        norb = None if om is None else len(set(om.values()))
        print(f"\n=== CFI cubic m={m} {'tw' if tw else 'pl'}  n={n}: node cell |C|={len(C)}, "
              f"true-orbits={norb}  (outer force {'FORBIDDEN' if norb == 1 else 'allowed'})")
        g = harvest(n, adj, adjl, col, C, 'greedy')
        print(f"  greedy   harvest: {len(g)} verified gens, transitive={transitive_on(C, g)}")
        for nm, kf in KEYS:
            t = time.time()
            gi = harvest(n, adj, adjl, col, C, 'inner', kf)
            print(f"  inner@{nm:<14}: {len(gi)} verified gens, transitive={transitive_on(C, gi)}"
                  f"  [{time.time()-t:.0f}s]")
        # where does the greedy pair first meet a mixed cell?
        a = min(C)
        for rj in C:
            if rj == a:
                continue
            res = trace_greedy(n, adj, adjl, indiv(n, adjl, col, a), indiv(n, adjl, col, rj))
            print(f"    pair ({a},{rj}): first mixed cell -> {res}")
            break
