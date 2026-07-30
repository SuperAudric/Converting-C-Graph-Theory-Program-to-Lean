#!/usr/bin/env python3
"""HUNT #1b — the OTHER capable habitat: objects whose 2-WL closure is PARAMETER-DETERMINED
while Aut is small.  (2026-07-30)

For a strongly regular graph the 2-WL root closure is the rank-3 scheme {I, A, A-bar} --
fixed by the parameters alone.  So any SRG whose automorphism group has rank > 3 is
NON-SCHURIAN at the root, and the more `Aut` shrinks the wider the deficiency.  The extreme
small case is the SRG(28,12,6,4) family: T(8) has |Aut| = 8! = 40320, the three CHANG graphs
(Seidel switchings of T(8) w.r.t. 4K2, C8, K3+K5) have tiny groups -- same parameters, so
the same rank-3 closure.  This is `net(Z4)`'s mechanism one level up: identical closure,
different group.

Methodology unchanged: start = the EXACT orbit partition (CAO by construction, "however
obtained"), individualize one representative per root orbit, take the 2-WL closure, and ask
whether any cell fails to be a single Aut_v-orbit.  1-WL reported alongside for contrast.
"""
import sys
from collections import defaultdict
from itertools import combinations
sys.path.insert(0, "/workspace/scratchpad")
from probe_cao_cleanroom import wl, individualize, cells, all_isos, orbits, orbit_colouring
from probe_cao_vtcover import iso_exists
from probe_2wl_sring import twowl_vertex

sys.setrecursionlimit(100000)

PAIRS = list(combinations(range(8), 2))
IX = {p: i for i, p in enumerate(PAIRS)}


def T8():
    n = 28
    adj = [[0] * n for _ in range(n)]
    for a in range(n):
        for b in range(a + 1, n):
            if set(PAIRS[a]) & set(PAIRS[b]):
                adj[a][b] = adj[b][a] = 1
    return n, adj


def switch(n, adj, X):
    """Seidel switching with respect to the vertex subset X."""
    out = [row[:] for row in adj]
    inX = [v in X for v in range(n)]
    for a in range(n):
        for b in range(a + 1, n):
            if inX[a] != inX[b]:
                out[a][b] = out[b][a] = 1 - out[a][b]
    return n, out


def edges_to_vertices(es):
    return {IX[(min(a, b), max(a, b))] for a, b in es}


CHANG_SETS = {
    "Chang-1 (4K2)": [(0, 1), (2, 3), (4, 5), (6, 7)],
    "Chang-2 (C8)": [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 0)],
    "Chang-3 (K3+K5)": ([(0, 1), (0, 2), (1, 2)]
                        + [(a, b) for a in range(3, 8) for b in range(a + 1, 8)]),
}


def paley(q):
    sq = {(i * i) % q for i in range(1, q)}
    adj = [[0] * q for _ in range(q)]
    for i in range(q):
        for j in range(i + 1, q):
            if (j - i) % q in sq:
                adj[i][j] = adj[j][i] = 1
    return q, adj


def latin_square_graph(mods):
    """L3(q): vertices = the q^2 cells of the Cayley table of prod Z_mods; adjacent iff
    same row, same column, or same symbol."""
    from itertools import product as pr
    els = list(pr(*[range(m) for m in mods]))
    q = len(els)
    add = lambda a, b: tuple((x + y) % m for x, y, m in zip(a, b, mods))
    V = [(a, b) for a in els for b in els]
    n = len(V)
    adj = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            (a1, b1), (a2, b2) = V[i], V[j]
            if a1 == a2 or b1 == b2 or add(a1, b1) == add(a2, b2):
                adj[i][j] = adj[j][i] = 1
    return n, adj


def analyse(lab, n, adj, budget_leaves=6_000_000):
    root = wl(n, adj, [0] * n)
    try:
        A = all_isos(n, adj, root, root, limit=budget_leaves)
    except RuntimeError:
        print(f"  {lab:20s} n={n:3d}  Aut enumeration budget exhausted -- skipped")
        return
    orb = orbits(n, A)
    ob = defaultdict(list)
    for v in range(n):
        ob[orb[v]].append(v)
    vt = len(ob) == 1
    oc = orbit_colouring(n, orb)
    print(f"  {lab:20s} n={n:3d} |Aut|={len(A):6d} VT={str(vt):5s} "
          f"root orbits {sorted(len(b) for b in ob.values())} "
          f"(1-WL root cells {sorted(len(c) for c in cells(root).values())})")
    for cell in cells(oc).values():
        v0 = cell[0]
        col1 = individualize(n, oc, v0)
        c1 = wl(n, adj, col1)
        d2 = twowl_vertex(n, adj, col1)
        A1 = [g for g in A if g[v0] == v0]
        o1 = orbits(n, A1)
        part2 = defaultdict(list)
        for v, c in enumerate(d2):
            part2[c].append(v)
        m1 = [c for c in cells(c1).values() if len({o1[x] for x in c}) > 1]
        m2 = [c for c in part2.values() if len({o1[x] for x in c}) > 1]
        tag = ""
        if m2:
            tag = ("   <<<<<< 2-WL COUNTEREXAMPLE "
                   + str([(len(c), sorted(defaultdict(int, {o: sum(1 for x in c if o1[x] == o)
                                                            for o in {o1[y] for y in c}}).values()))
                          for c in m2]))
        print(f"      v0={v0:3d}: |Aut_v|={len(A1):5d} stab-orbits "
              f"{sorted(len(g) for g in defaultdict(list, {o: [x for x in range(n) if o1[x] == o] for o in set(o1)}).values())}"
              f" | 1-WL cells={len(set(c1))} mixed={len(m1)}"
              f" | 2-WL cells={len(part2)} mixed={len(m2)}{tag}")


print("=== SRG(28,12,6,4): T(8) and the three CHANG graphs (identical rank-3 2-WL closure) ===")
n, adj = T8()
analyse("T(8) = J(8,2)", n, adj)
for lab, es in CHANG_SETS.items():
    nn, a2 = switch(n, adj, edges_to_vertices(es))
    analyse(lab, nn, a2)

print("\n=== other parameter-determined families ===")
analyse("Paley(25)", *paley(25))
analyse("L3(5) (Z5 table)", *latin_square_graph((5,)))
analyse("Paley(29)", *paley(29))
