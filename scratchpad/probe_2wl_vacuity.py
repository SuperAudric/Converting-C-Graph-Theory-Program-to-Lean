#!/usr/bin/env python3
"""VACUITY CHECK on the "2-WL always repairs it" sweep (2026-07-30).

`probe_cao_2wl.py` found 0 counterexamples at 2-WL.  But almost every object in it is
GROUP-DERIVED (nets over abelian groups, Cayley graphs, Johnson/Kneser/Paley, rook), and
for those the coherent closure tends to BE the orbital configuration -- in which case the
sweep could not possibly have exhibited a 2-WL failure.  That is the project's recurring
vacuity trap, so measure it directly:

  SCHURIAN (root)      : 2-WL pair colouring == orbitals of Aut            (rank equal)
  SCHURIAN (extension) : after individualizing v, 2-WL pair colouring == orbitals of Aut_v

A 2-WL vertex-level counterexample REQUIRES a non-schurian one-point extension.  So:
  - if every object has a schurian extension, the sweep NEVER TESTED the sharp case;
  - objects with a non-schurian ROOT but a schurian EXTENSION are the real evidence.
"""
import sys
from collections import defaultdict
sys.path.insert(0, "/workspace/scratchpad")
from probe_cao_cleanroom import wl, individualize, cells, all_isos, orbits
from probe_cao_net import net
from probe_cao_2wl import (twowl_fast, from_edges, K, circ, cayley, johnson, kneser,
                           paley, rook, shrikhande, clebsch, Q3, PETB)
from probe_cao_cleanroom import cfi


def twowl_pairs(n, adj, vcol):
    """Oblivious 2-WL to fixpoint; returns the PAIR colouring as a flat list."""
    col = [0] * (n * n)
    init = {}
    for u in range(n):
        for v in range(n):
            k = (0 if u == v else 1, adj[u][v], vcol[u], vcol[v])
            col[u * n + v] = init.setdefault(k, len(init))
    while True:
        rank, new = {}, [0] * (n * n)
        for u in range(n):
            un = u * n
            for v in range(n):
                s = sorted((col[un + w], col[w * n + v]) for w in range(n))
                key = (col[un + v], tuple(s))
                r = rank.get(key)
                if r is None:
                    r = rank[key] = len(rank)
                new[un + v] = r
        if len(rank) == len(set(col)):
            return col
        col = new


def orbital_partition(n, auts):
    """Orbits of the group on ORDERED pairs (the orbital configuration)."""
    par = list(range(n * n))

    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for g in auts:
        for u in range(n):
            for v in range(n):
                a, b = f(u * n + v), f(g[u] * n + g[v])
                if a != b:
                    par[a] = b
    return [f(i) for i in range(n * n)]


def same_partition(a, b):
    ma, mb = {}, {}
    for i, (x, y) in enumerate(zip(a, b)):
        if ma.setdefault(x, y) != y or mb.setdefault(y, x) != x:
            return False
    return True


def report(lab, n, adj):
    root = wl(n, adj, [0] * n)
    A = all_isos(n, adj, root, root)
    orb = orbits(n, A)
    rootcells = list(cells(root).values())
    cao = all(len({orb[v] for v in c}) == 1 for c in rootcells)
    p2 = twowl_pairs(n, adj, root)
    orbl = orbital_partition(n, A)
    sch_root = same_partition(p2, orbl)
    # one-point extension at a representative of each root orbit
    exts = []
    for c in rootcells:
        v0 = c[0]
        col1 = individualize(n, root, v0)
        A1 = [g for g in A if g[v0] == v0]
        p2e = twowl_pairs(n, adj, col1)
        sch = same_partition(p2e, orbital_partition(n, A1))
        exts.append(sch)
    print(f"  {lab:22s} n={n:4d} |Aut|={len(A):6d} CAO={str(cao):5s} "
          f"rank(2-WL)={len(set(p2)):3d} rank(orbitals)={len(set(orbl)):3d} "
          f"schurian(root)={str(sch_root):5s} schurian(1-pt ext)={exts}")
    return sch_root, all(exts)


CASES = [("net(Z4)=CFI[K4]tw", *net((4,))[:2]), ("net(Z2xZ2)", *net((2, 2))[:2]),
         ("net(Z6)", *net((6,))[:2]),
         ("Petersen", *from_edges(10, PETB)), ("rook4x4", *rook(4)),
         ("Shrikhande", *shrikhande()), ("Clebsch", *clebsch()),
         ("Paley(13)", *paley(13)), ("Paley(17)", *paley(17)),
         ("J(5,2)", *johnson(5, 2)), ("J(6,2)=T(6)", *johnson(6, 2)),
         ("J(8,2)=T(8)", *johnson(8, 2)), ("Kneser(7,2)", *kneser(7, 2)),
         ("Q3 cube", *from_edges(8, Q3)), ("rook3x3", *rook(3)),
         ("Cay(Z4xZ4,{+-e})", *cayley((4, 4), [(1,0),(3,0),(0,1),(0,3)])),
         ("Cay(Z4xZ2^2)", *cayley((4, 2, 2), [(1,0,0),(3,0,0),(0,1,0),(0,0,1)])),
         ("circ(16,{1,2,7})", *circ(16, (1, 2, 7))),
         ("circ(13,{1,3,9})", *circ(13, (1, 3, 9)))]
print("=== is the 2-WL sweep vacuous?  (a 2-WL failure NEEDS a non-schurian extension) ===")
ns_root = ns_ext = 0
for lab, n, adj in CASES:
    sr, se = report(lab, n, adj)
    ns_root += (not sr)
    ns_ext += (not se)
print(f"\n  objects with a NON-schurian root 2-WL closure       : {ns_root}/{len(CASES)}")
print(f"  objects with a NON-schurian ONE-POINT EXTENSION     : {ns_ext}/{len(CASES)}")
print("  (the second number is the one that matters: it counts the cases in which a")
print("   2-WL vertex-level counterexample was even POSSIBLE.)")
