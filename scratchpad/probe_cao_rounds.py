#!/usr/bin/env python3
"""HOW does the extension separate fused orbitals?  (2026-07-30, for the proof plan)

The live target's crux step is: if `Aut_v` splits `C`, the 2-WL extension separates the `D-C`
orbitals.  A proof needs to know WHERE the separating information comes from.  Note the naive
first-round answer is NO information at all:

  the round-1 refinement of the pair (v,u) is the multiset over x of (col(v,x), col(x,u)),
  and by COHERENCE that count is the intersection number p^k_{ij} with k = X-class(v,u)
  -- identical for every u in the same X-class.  So the pair (v,u) learns nothing directly.

The marking must therefore travel: a FAR pair (a,b) learns its "triangle type"
(X-class(a,v), X-class(v,b)), those splits refine the far classes, and only then does the
feedback reach (v,u).  So the separation is intrinsically NON-LOCAL, and the question a proof
must answer is: how many rounds, and is it bounded?

Measured here: for each fused class at a deficient root, the round at which the extension
first gives different colours to (v,u) and (v,w) for u,w in the two orbital fibres.
"""
import sys
from collections import defaultdict
sys.path.insert(0, "/workspace/scratchpad")
from probe_cao_cleanroom import wl, individualize, cells, all_isos, orbits
from probe_cao_induction import (orbital_partition, same_partition, shrikhande, chang, T8,
                                 rook, paley)
from probe_cao_net import net

sys.setrecursionlimit(100000)


def twowl_rounds(n, adj, vcol, cap=30):
    """Yield the pair colouring after each refinement round."""
    col = [0] * (n * n)
    init = {}
    for u in range(n):
        for v in range(n):
            k = (0 if u == v else 1, adj[u][v], vcol[u], vcol[v])
            col[u * n + v] = init.setdefault(k, len(init))
    yield 0, col
    for r in range(1, cap + 1):
        rank, new = {}, [0] * (n * n)
        for u in range(n):
            un = u * n
            for v in range(n):
                s = sorted((col[un + w], col[w * n + v]) for w in range(n))
                key = (col[un + v], tuple(s))
                q = rank.get(key)
                if q is None:
                    q = rank[key] = len(rank)
                new[un + v] = q
        stable = len(rank) == len(set(col))
        col = new
        yield r, col
        if stable:
            return


def analyse(lab, n, adj):
    A = all_isos(n, adj, wl(n, adj, [0] * n), wl(n, adj, [0] * n), limit=3_000_000)
    orb = orbits(n, A)
    m = {}
    oc = [m.setdefault(orb[v], len(m)) for v in range(n)]
    # root closure X and the orbitals
    Xcol = None
    for r, c in twowl_rounds(n, adj, oc):
        Xcol = c
    orbl = orbital_partition(n, A)
    byclass = defaultdict(set)
    for i in range(n * n):
        byclass[Xcol[i]].add(orbl[i])
    fused = {c: o for c, o in byclass.items() if len(o) > 1}
    print(f"\n=== {lab} (n={n}) ===")
    print(f"  root: X-classes {len(set(Xcol))} vs orbitals {len(set(orbl))}; "
          f"fused classes {len(fused)}")
    if not fused:
        print("  (schurian root -- the target is trivially satisfied here)")
        return
    v = 0
    col1 = individualize(n, oc, v)
    # which u are in which orbital fibre over v, inside a fused class
    targets = []
    for c, os_ in fused.items():
        fib = defaultdict(list)
        for u in range(n):
            if Xcol[v * n + u] == c:
                fib[orbl[v * n + u]].append(u)
        if len(fib) > 1:
            targets.append((c, {k: vs for k, vs in fib.items()}))
    if not targets:
        print(f"  the fused classes do not meet the row of v={v} in >1 orbital "
              f"(no split to detect from this base point)")
        return
    print(f"  fused classes meeting v's row in >1 orbital: {len(targets)}")
    hist = {}
    for r, col in twowl_rounds(n, adj, col1):
        for c, fib in targets:
            if c in hist:
                continue
            reps = [vs[0] for vs in fib.values()]
            cols = {col[v * n + u] for u in reps}
            if len(cols) == len(reps):
                hist[c] = r
        if len(hist) == len(targets):
            break
    for c, fib in targets:
        sizes = sorted(len(x) for x in fib.values())
        print(f"    class {c}: orbital fibres over v of sizes {sizes} -> separated at "
              f"round {hist.get(c, 'NEVER (within cap)')}")


analyse("Shrikhande", *shrikhande())
analyse("net(Z4)", *net((4,))[:2])
analyse("Chang-2", *chang([(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,0)]))
analyse("rook 4x4 (control, schurian)", *rook(4))
analyse("T(8) (control, schurian)", *T8())
