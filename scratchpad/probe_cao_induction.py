#!/usr/bin/env python3
"""PROOF-STRATEGY INSTRUMENTATION (2026-07-30).  Target:

  T:  fibres = Aut-orbits  ==>  after individualizing one point and taking the 2-WL
      closure, fibres = Aut_v-orbits.        ("fibre-schurian CCs are closed under
                                               one-point extension")

Two things a proof must know, and both are measurable:

E1  THE INDUCTION STEP ON A RICHER INPUT CLASS.  Every earlier sweep tested depth 1 only,
    from orbit partitions of PLAIN graphs.  But a proof of T is an induction along the
    descent, and its step is applied at every node -- where the input is a configuration
    that AROSE from individualization, a strictly wider class.  So descend to discreteness,
    checking fibre-schurity at EVERY node.  A depth-2 failure IS a depth-1 counterexample
    for the theorem as stated, just with an input no plain-graph sweep can produce.
    (One representative per cell suffices: under CAO the cell is one orbit, so different
    representatives give conjugate children.)

E2  WHICH HYPOTHESIS DOES THE WORK -- fibres, or the whole configuration?
    At every node record BOTH
        fibre-schurian : diagonal classes of the 2-WL closure == Aut_chi-orbits
        FULL-schurian  : pair classes of the 2-WL closure     == Aut_chi-ORBITALS
    If full schurity is ever LOST while fibre-schurity survives, then T cannot be proved by
    proving the stronger "extensions preserve schurity" -- the fibre hypothesis is doing
    real work and the proof must use it.  If full schurity is never lost in this class, the
    stronger statement is the better target (and a much more standard one).
"""
import sys, time
from collections import defaultdict
from itertools import combinations
sys.path.insert(0, "/workspace/scratchpad")
from probe_cao_cleanroom import wl, individualize, cells, all_isos, orbits, is_perm_aut
from probe_cao_net import net
from probe_2wl_sring import (g_cyclic, g_direct, g_semidirect_cyclic, g_dicyclic,
                             cayley_adj, sring, check_group)

sys.setrecursionlimit(100000)


def twowl_pairs(n, adj, vcol, cap=40):
    col = [0] * (n * n)
    init = {}
    for u in range(n):
        for v in range(n):
            k = (0 if u == v else 1, adj[u][v], vcol[u], vcol[v])
            col[u * n + v] = init.setdefault(k, len(init))
    for _ in range(cap):
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
            break
        col = new
    return col


def orbital_partition(n, auts):
    par = list(range(n * n))

    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for g in auts:
        for u in range(n):
            gu = g[u] * n
            un = u * n
            for v in range(n):
                a, b = f(un + v), f(gu + g[v])
                if a != b:
                    par[a] = b
    return [f(i) for i in range(n * n)]


def same_partition(a, b):
    ma, mb = {}, {}
    for x, y in zip(a, b):
        if ma.setdefault(x, y) != y or mb.setdefault(y, x) != x:
            return False
    return True


def stab(auts, col, n):
    return [g for g in auts if all(col[g[v]] == col[v] for v in range(n))]


def descend(n, adj, auts, col, depth, stats, maxdepth=12):
    """Check fibre- and full-schurity at this node, then recurse on one rep per cell."""
    H = stab(auts, col, n)
    p2 = twowl_pairs(n, adj, col)
    diag = [p2[v * n + v] for v in range(n)]
    orb = orbits(n, H)
    fibre_ok = same_partition(diag, orb)
    full_ok = same_partition(p2, orbital_partition(n, H))
    stats["nodes"] += 1
    stats["depth"] = max(stats["depth"], depth)
    if not fibre_ok:
        stats["fibre_fail"].append((depth, len(H)))
    if not full_ok:
        stats["full_fail"].append((depth, len(H)))
    if fibre_ok and not full_ok:
        stats["fibre_ok_full_fail"] += 1
    d = defaultdict(list)
    for v, c in enumerate(diag):
        d[c].append(v)
    big = [c for c in d.values() if len(c) > 1]
    if not big or depth >= maxdepth:
        return
    # CAO holds here (fibre_ok) => one representative per cell suffices
    for cell in big:
        descend(n, adj, auts, individualize(n, diag, cell[0]), depth + 1, stats, maxdepth)


def run(lab, n, adj, autcap=3_000_000):
    t0 = time.time()
    try:
        A = all_isos(n, adj, wl(n, adj, [0] * n), wl(n, adj, [0] * n), limit=autcap)
    except RuntimeError:
        print(f"  {lab:26s} n={n:3d}  Aut budget blown -- skipped")
        return
    orb0 = orbits(n, A)
    m = {}
    oc = [m.setdefault(orb0[v], len(m)) for v in range(n)]
    stats = {"nodes": 0, "depth": 0, "fibre_fail": [], "full_fail": [],
             "fibre_ok_full_fail": 0}
    descend(n, adj, A, oc, 0, stats)
    ff, uf = stats["fibre_fail"], stats["full_fail"]
    print(f"  {lab:26s} n={n:3d} |Aut|={len(A):6d} nodes={stats['nodes']:4d} "
          f"maxdepth={stats['depth']:2d} | fibre-schurian everywhere: "
          f"{'YES' if not ff else 'NO ' + str(ff[:3])} | full-schurian: "
          f"{'YES' if not uf else 'NO at ' + str(uf[:3])}"
          f" | fibre-ok-but-full-fail nodes: {stats['fibre_ok_full_fail']}"
          f"  ({time.time()-t0:.0f}s)")


def from_edges(nv, es):
    adj = [[0] * nv for _ in range(nv)]
    for a, b in es:
        adj[a][b] = adj[b][a] = 1
    return nv, adj


def rook(m):
    V = [(i, j) for i in range(m) for j in range(m)]
    return from_edges(len(V), [(a, b) for a in range(len(V)) for b in range(a + 1, len(V))
                               if (V[a][0] == V[b][0]) != (V[a][1] == V[b][1])])


def shrikhande():
    V = [(i, j) for i in range(4) for j in range(4)]
    S = {(0,1),(0,3),(1,0),(3,0),(1,1),(3,3)}
    return from_edges(16, [(a, b) for a in range(16) for b in range(a + 1, 16)
                           if ((V[b][0]-V[a][0]) % 4, (V[b][1]-V[a][1]) % 4) in S
                           or ((V[a][0]-V[b][0]) % 4, (V[a][1]-V[b][1]) % 4) in S])


PAIRS = list(combinations(range(8), 2))
IXP = {p: i for i, p in enumerate(PAIRS)}


def T8():
    n = 28
    adj = [[0] * n for _ in range(n)]
    for a in range(n):
        for b in range(a + 1, n):
            if set(PAIRS[a]) & set(PAIRS[b]):
                adj[a][b] = adj[b][a] = 1
    return n, adj


def chang(es):
    n, adj = T8()
    X = {IXP[(min(a, b), max(a, b))] for a, b in es}
    out = [r[:] for r in adj]
    for a in range(n):
        for b in range(a + 1, n):
            if (a in X) != (b in X):
                out[a][b] = out[b][a] = 1 - out[a][b]
    return n, out


def paley(q):
    sq = {(i * i) % q for i in range(1, q)}
    return from_edges(q, [(i, j) for i in range(q) for j in range(i + 1, q)
                          if (j - i) % q in sq])


if __name__ == "__main__":
    print("=== E1/E2: fibre- and full-schurity at EVERY node of the descent ===")
    print("(one representative per cell; CAO makes the other choices conjugate)")
    run("Shrikhande", *shrikhande())
    run("rook 4x4", *rook(4))
    run("net(Z4) = CFI[K4]-tw", *net((4,))[:2])
    run("net(Z2xZ2)", *net((2, 2))[:2])
    run("T(8)", *T8())
    run("Chang-1 (4K2)", *chang([(0,1),(2,3),(4,5),(6,7)]))
    run("Chang-2 (C8)", *chang([(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,0)]))
    run("Chang-3 (K3+K5)", *chang([(0,1),(0,2),(1,2)]
                                  + [(a, b) for a in range(3, 8) for b in range(a + 1, 8)]))
    run("Petersen", *from_edges(10, [(0,1),(1,2),(2,3),(3,4),(4,0),(5,7),(7,9),(9,6),(6,8),
                                     (8,5),(0,5),(1,6),(2,7),(3,8),(4,9)]))
    run("Paley(13)", *paley(13))
    run("Paley(17)", *paley(17))

    # the non-schurian S-ring Cayley graphs found by the hunt (the sharp inputs)
    print("\n=== Cayley graphs whose ROOT S-ring is non-schurian (the sharp inputs) ===")
    G16 = {"Z4^2": g_direct(g_cyclic(4), g_cyclic(4)),
           "Z8xZ2": g_direct(g_cyclic(8), g_cyclic(2)),
           "Z4xZ2^2": g_direct(g_cyclic(4), g_direct(g_cyclic(2), g_cyclic(2))),
           "D16": g_semidirect_cyclic(8, 7), "SD16": g_semidirect_cyclic(8, 3),
           "M16": g_semidirect_cyclic(8, 5), "Q16": g_dicyclic(4),
           "D8xZ2": g_direct(g_semidirect_cyclic(4, 3), g_cyclic(2))}
    seen = 0
    for gname, mul in G16.items():
        check_group(mul, gname)
        n = len(mul)
        inv = [next(y for y in range(n) if mul[x][y] == 0) for x in range(n)]
        classes, sq = [], set()
        for x in range(1, n):
            if x in sq:
                continue
            c = {x, inv[x]}
            sq |= c
            classes.append(sorted(c))
        hits = 0
        for mask in range(1, 2 ** len(classes)):
            S = frozenset(e for i, c in enumerate(classes) if mask >> i & 1 for e in c)
            p = sring(mul, inv, S)
            szs = defaultdict(int)
            for c in p:
                szs[c] += 1
            if max(szs.values()) == 1:
                continue
            nn, adj = cayley_adj(mul, S)
            try:
                A = all_isos(nn, adj, wl(nn, adj, [0] * nn), wl(nn, adj, [0] * nn),
                             limit=2_000_000)
            except RuntimeError:
                continue
            # non-schurian ROOT S-ring  <=>  basic sets != Aut_e-orbits
            A0 = [g for g in A if g[0] == 0]
            o0 = orbits(nn, A0)
            if same_partition(p, o0):
                continue
            hits += 1
            if hits > 3:
                break
            run(f"Cay({gname},{sorted(S)[:4]}..)", nn, adj)
        seen += hits
    print(f"(sharp Cayley inputs exercised: {seen})")
