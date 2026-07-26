#!/usr/bin/env python3
"""
THE DECISIVE TEST for "consume's failure can be handed straight to force".

Deepen on a cell is poly.  Its verdict partitions the cell: reps linked by a VERIFIED
twist vs reps not linked.  The proposal is to hand the "not linked" verdict to force.

Force may only act on an EQUIVARIANT key (`Force.KeyEquivariant`); otherwise
`forceBy` can narrow away part of a genuine orbit and ① dies (not a cost problem —
a correctness problem).  So the question is exactly:

    is the ALL-ANCHOR deepen harvest's orbit partition of the branch cell
    iso-invariant?     P(sigma . G)  ==  sigma(P(G))  ?

(§1.1 measured this FALSE for ONE anchor on G8 and TRUE for all anchors on G8.
 Here: all anchors, 18 witnesses, looking for a falsifier.)

Also reported per witness: does the harvest partition equal the TRUE Aut-orbit
partition?  (harvest == true  =>  the verdict is exact;  harvest finer  =>  the
verdict over-splits, and over-splitting an orbit is precisely what force must not do.)
"""
import sys, random
from collections import defaultdict
sys.setrecursionlimit(10000)

from probe_dualdeepen import (circ, FANO, MIXED, rand_incidence, build_mp,
                              build_cfi_base, cubic, relabel, Ctx, canon)
from probe_polyloop import (adjlist, refine, indiv, target_cell,
                            deepen_harvest, greedy_deepen, replay, twist)

def harvest_partition(n, adj, col, C):
    """Orbit partition of C under the ALL-ANCHOR deepen harvest (today's deepenGens)."""
    adjl = adjlist(n, adj)
    gens = deepen_harvest(n, adj, adjl, col, C, anchors=len(C))
    par = {v: v for v in C}
    def f(x):
        while par[x] != x: par[x] = par[par[x]]; x = par[x]
        return x
    for g in gens:
        for v in C:
            if g[v] in par:
                a, b = f(v), f(g[v])
                if a != b: par[a] = b
    cl = defaultdict(set)
    for v in C: cl[f(v)].add(v)
    return frozenset(frozenset(s) for s in cl.values())

def true_partition(n, adj, col, C):
    """TRUE Aut(adj,col)-orbit partition of C (min-over-cell cert classes)."""
    ctx = Ctx(n, adj, prune=True, leafcap=200000)
    canon(ctx, list(col), [], root=True)
    Cr, percert, expl = ctx.root
    cl = defaultdict(set)
    for v, c in percert.items(): cl[c].add(v)
    # EVERY discovered gen fixes its own path pointwise, and those path vertices are
    # singletons of the ROOT colouring, so every gen is an automorphism of (adj, col).
    gens = [g for (g, p) in ctx.gens]
    par = {v: v for v in Cr}
    def f(x):
        while par[x] != x: par[x] = par[par[x]]; x = par[x]
        return x
    for g in gens:
        for v in Cr:
            if g[v] in par:
                a, b = f(v), f(g[v])
                if a != b: par[a] = b
    cl2 = defaultdict(set)
    for v in Cr: cl2[f(v)].add(v)
    return frozenset(frozenset(s) for s in cl2.values())

def check(name, n, adj, trials=4):
    adjl = adjlist(n, adj)
    col = refine(n, adjl, [0] * n)
    cid, C = target_cell(n, col)
    if cid is None:
        print(f"  {name:<32} n={n:<4} (discrete after 1-WL — no branch cell)"); return
    P = harvest_partition(n, adj, col, C)
    T = true_partition(n, adj, col, C)
    rnd = random.Random(101)
    bad = 0
    for _ in range(trials):
        s = list(range(n)); rnd.shuffle(s)
        a2 = relabel(n, adj, s)
        col2 = refine(n, adjlist(n, a2), [0] * n)
        cid2, C2 = target_cell(n, col2)
        P2 = harvest_partition(n, a2, col2, C2)
        Pimg = frozenset(frozenset(s[v] for v in blk) for blk in P)
        if P2 != Pimg: bad += 1
    print(f"  {name:<32} n={n:<4} |C|={len(C):<3} harvest-blocks={len(P):<3} "
          f"true-blocks={len(T):<3} exact={'YES' if P == T else 'NO '} "
          f"①(partition transports)={'OK' if bad == 0 else f'FAILS {bad}/{trials}'}")


if __name__ == "__main__":
    print("Is the ALL-ANCHOR deepen verdict on the branch cell an EQUIVARIANT partition?\n")
    print("### gauge / symmetric")
    check("mp7 Fano multipede", *build_mp(FANO))
    check("circ(5) multipede", *build_mp(circ(5)))
    check("MIXED multipede", *build_mp(MIXED))
    print("\n### CFI over random cubic bases")
    for m in (8, 10, 12, 14):
        es = cubic(m, 11 + m)
        for tw in (False, True):
            n, adj = build_cfi_base(es, m, tw)
            check(f"CFI cubic m={m} {'tw' if tw else 'pl'}", n, adj)
    print("\n### rigid multipedes")
    for (V, W, deg, seed) in [(6, 5, 3, 1), (8, 6, 3, 2), (10, 7, 3, 3),
                              (12, 8, 3, 4), (14, 9, 3, 5), (16, 10, 3, 6)]:
        n, adj = build_mp(rand_incidence(V, W, deg, seed))
        check(f"rand multipede V={V} W={W}", n, adj)
