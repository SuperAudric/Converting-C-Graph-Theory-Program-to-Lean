#!/usr/bin/env python3
"""
CLEAN-ROOM independent verification of the CFI[K4] "CAO does not propagate" claim.

Nothing imported from /workspace/scratchpad.  Own CFI construction (odd-parity twist
formulation), own 1-WL, own individualization-refinement automorphism enumeration.

Question:  start from the EXACT Aut(adj)-orbit partition (so CellsAreOrbits holds by
construction), individualize one vertex, take the 1-WL closure -- is every cell still a
single Aut(adj, col)-orbit?
"""
import sys
from collections import defaultdict
from itertools import combinations

sys.setrecursionlimit(100000)


# ---------------------------------------------------------------- CFI construction
def cfi(base_edges, m, twisted_nodes=()):
    """CFI over base graph on m nodes.  Node i uses ODD-parity gadgets iff i in twisted_nodes.

    Vertices:
      ('E', e, b)  for each base edge e and b in {0,1}
      ('V', i, S)  for each node i and S subset of inc(i) of the right parity;
                   ('V',i,S) ~ ('E',e, 1 if e in S else 0) for e in inc(i)
    """
    names = []
    for e in base_edges:
        names += [('E', e, 0), ('E', e, 1)]
    for i in range(m):
        inc = tuple(e for e in base_edges if i in e)
        par = 1 if i in twisted_nodes else 0
        for k in range(len(inc) + 1):
            if k % 2 != par:
                continue
            for S in combinations(inc, k):
                names.append(('V', i, frozenset(S)))
    idx = {nm: k for k, nm in enumerate(names)}
    n = len(names)
    adj = [[0] * n for _ in range(n)]
    for nm in names:
        if nm[0] != 'V':
            continue
        _, i, S = nm
        inc = [e for e in base_edges if i in e]
        for e in inc:
            w = idx[('E', e, 1 if e in S else 0)]
            g = idx[nm]
            adj[g][w] = adj[w][g] = 1
    return n, adj, names, idx


# ---------------------------------------------------------------- 1-WL
def wl(n, adj, col):
    col = list(col)
    while True:
        sig = [(col[v], tuple(sorted(col[u] for u in range(n) if adj[v][u]))) for v in range(n)]
        rank = {s: i for i, s in enumerate(sorted(set(sig)))}
        new = [rank[sig[v]] for v in range(n)]
        if new == col:
            return col
        col = new


def individualize(n, col, v):
    sig = [(col[u], u != v) for u in range(n)]
    rank = {s: i for i, s in enumerate(sorted(set(sig)))}
    return [rank[sig[u]] for u in range(n)]


def cells(col):
    d = defaultdict(list)
    for v, c in enumerate(col):
        d[c].append(v)
    return d


def is_perm_aut(n, adj, sigma):
    if sorted(sigma) != list(range(n)):
        return False
    for i in range(n):
        for j in range(n):
            if adj[i][j] != adj[sigma[i]][sigma[j]]:
                return False
    return True


# ------------------------------------- I-R search: ALL colour-preserving isos cA -> cB
def all_isos(n, adj, cA, cB, limit=10 ** 7, counter=None):
    """Every automorphism sigma of adj with cB[sigma[v]] == cA[v] (both refined first).
    Complete enumeration (no automorphism pruning), returns list of tuples."""
    if counter is None:
        counter = [limit]
    out = []

    def rec(cA, cB):
        counter[0] -= 1
        if counter[0] <= 0:
            raise RuntimeError('budget exhausted')
        cA = wl(n, adj, cA)
        cB = wl(n, adj, cB)
        pa = sorted((c, len(vs)) for c, vs in cells(cA).items())
        pb = sorted((c, len(vs)) for c, vs in cells(cB).items())
        if pa != pb:
            return
        dA, dB = cells(cA), cells(cB)
        big = [c for c in sorted(dA) if len(dA[c]) > 1]
        if not big:
            sigma = [None] * n
            posB = {cB[v]: v for v in range(n)}
            for v in range(n):
                sigma[v] = posB[cA[v]]
            if is_perm_aut(n, adj, sigma):
                out.append(tuple(sigma))
            return
        c0 = big[0]
        x = dA[c0][0]
        for y in dB[c0]:
            rec(individualize(n, cA, x), individualize(n, cB, y))

    rec(list(cA), list(cB))
    return out


def orbits(n, auts):
    par = list(range(n))

    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for g in auts:
        for i in range(n):
            a, b = f(i), f(g[i])
            if a != b:
                par[a] = b
    return [f(i) for i in range(n)]


def orbit_colouring(n, orb):
    reps = sorted(set(orb))
    rank = {r: i for i, r in enumerate(reps)}
    return [rank[orb[v]] for v in range(n)]


# ---------------------------------------------------------------- the experiment
def report(label, base_edges, m, twisted_nodes):
    n, adj, names, idx = cfi(base_edges, m, twisted_nodes)
    print(f"\n=== {label}: n = {n} ===")
    root = wl(n, adj, [0] * n)
    print(f"  1-WL root cells (sizes): {sorted(len(v) for v in cells(root).values())}")
    A = all_isos(n, adj, root, root)
    print(f"  |Aut(adj)| = {len(A)}")
    orb = orbits(n, A)
    ob = defaultdict(list)
    for v in range(n):
        ob[orb[v]].append(v)
    print(f"  root orbit sizes: {sorted(len(b) for b in ob.values())}")
    oc = orbit_colouring(n, orb)
    cao_root = all(len({orb[v] for v in c}) == 1 for c in cells(root).values())
    print(f"  CAO at the 1-WL root: {cao_root}")

    hits = []
    for v0 in range(n):
        c1 = wl(n, adj, individualize(n, oc, v0))
        A1 = all_isos(n, adj, c1, c1)
        o1 = orbits(n, A1)
        mixed = [c for c in cells(c1).values() if len({o1[x] for x in c}) > 1]
        if mixed:
            hits.append((v0, len(A1), c1, o1, mixed, names))
    if not hits:
        print("  CAO PROPAGATES for every individualization")
        return None
    print(f"  ★ CAO BROKEN for {len(hits)}/{n} individualized vertices")
    v0, sz, c1, o1, mixed, nms = hits[0]
    print(f"  first witness: v0 = {v0} = {nms[v0]}, |Aut(adj,col1)| = {sz}")
    print(f"    1-WL cells after: {sorted(len(v) for v in cells(c1).values())}")
    for c in mixed:
        prof = defaultdict(list)
        for x in c:
            prof[o1[x]].append(x)
        print(f"    mixed cell {sorted(c)} -> orbits {[sorted(g) for g in prof.values()]}")
        for x in sorted(c):
            print(f"        {x}: {nms[x]}  orbit-rep {o1[x]}")
    return hits


K4 = [(i, j) for i in range(4) for j in range(i + 1, 4)]

if __name__ == "__main__":
    report("CFI[K4] untwisted", K4, 4, ())
    report("CFI[K4] twisted", K4, 4, (0,))
