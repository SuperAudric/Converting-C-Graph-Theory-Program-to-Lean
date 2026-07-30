#!/usr/bin/env python3
"""DOES THE CAO-PROPAGATION FAILURE SURVIVE A k-WL CLOSURE?  (k = 2, the user's ask)

Methodology, per graph (identical to the 1-WL probe, only the closure changes):
   start   = the EXACT Aut(adj)-orbit partition   (=> CellsAreOrbits holds by construction)
   step    = individualize one vertex (one rep per root orbit suffices: reps in the same
             root orbit give conjugate colourings)
   closure = 1-WL   vs   2-WL (oblivious 2-dim WL, vertex partition = diagonal colours)
   verdict = is some closure cell NOT a single Aut(adj, col)-orbit?

Orbits come from complete refinement-guided pair search (probe_cao_vtcover.iso_exists),
never from a canon-with-pruning oracle.

Two habitats swept:
  (I)  CFI-twisted over bases of growing treewidth  (K4, prism, K3,3, Q3, cubic8, K5,
       Petersen, K6) -- the "gauge parity" story
  (II) highly regular objects (nets, SRGs, DRGs, VT/Cayley graphs, T(8)) -- regularity is
       what actually blinds WL, so this is where a 2-WL failure would live
"""
import sys
from collections import defaultdict
from itertools import combinations
sys.path.insert(0, "/workspace/scratchpad")
from probe_cao_cleanroom import wl, individualize, cells, cfi
from probe_cao_vtcover import iso_exists, cell_orbit_reps
from probe_cao_net import net

sys.setrecursionlimit(100000)


# ---------------------------------------------------------------- fast oblivious 2-WL
def twowl_fast(n, adj, vcol):
    """Oblivious 2-dim WL on ordered pairs.  Returns the diagonal (vertex) partition."""
    col = [0] * (n * n)
    init = {}
    for u in range(n):
        for v in range(n):
            k = (0 if u == v else 1, adj[u][v], vcol[u], vcol[v])
            col[u * n + v] = init.setdefault(k, len(init))
    while True:
        sig = {}
        new = [0] * (n * n)
        rank = {}
        for u in range(n):
            un = u * n
            for v in range(n):
                s = [0] * n
                for w in range(n):
                    s[w] = (col[un + w], col[w * n + v])
                s.sort()
                key = (col[un + v], tuple(s))
                r = rank.get(key)
                if r is None:
                    r = rank[key] = len(rank)
                new[un + v] = r
        if len(rank) == len(set(col)):
            return [col[u * n + u] for u in range(n)]
        col = new


def partition_of(lab):
    d = defaultdict(list)
    for v, c in enumerate(lab):
        d[c].append(v)
    return list(d.values())


def exact_orbit_start(n, adj):
    """The exact Aut(adj)-orbit partition, from the 1-WL root, by pairwise iso search."""
    root = wl(n, adj, [0] * n)
    out = [None] * n
    k = 0
    for cell in cells(root).values():
        reps = cell_orbit_reps(n, adj, root, cell)
        if reps is None:
            return None, None
        for v in cell:
            for r in reps:
                if iso_exists(n, adj, individualize(n, root, v), individualize(n, root, r)):
                    out[v] = (root[v], reps.index(r))
                    break
        k += len(reps)
    rank = {s: i for i, s in enumerate(sorted(set(out)))}
    return [rank[s] for s in out], k


def mixed_cells(n, adj, col, part):
    bad = []
    for cell in part:
        if len(cell) == 1:
            continue
        reps = cell_orbit_reps(n, adj, col, cell)
        if reps is None:
            bad.append(('?', len(cell)))
        elif len(reps) > 1:
            bad.append((len(reps), len(cell)))
    return bad


def run(label, n, adj, do2wl=True):
    oc, k = exact_orbit_start(n, adj)
    if oc is None:
        print(f"  {label:30s} n={n:4d}  orbit start INCONCLUSIVE")
        return
    reps = [c[0] for c in cells(oc).values()]
    for v0 in reps:
        c1 = wl(n, adj, individualize(n, oc, v0))
        m1 = mixed_cells(n, adj, c1, partition_of(c1))
        line = (f"  {label:30s} n={n:4d} rootorbits={k} v0={v0:3d}  "
                f"1WL cells={len(set(c1))} mixed={len(m1)}")
        if do2wl:
            d2 = twowl_fast(n, adj, individualize(n, oc, v0))
            # the vertex partition 2-WL induces (always refines the 1-WL one)
            m2 = mixed_cells(n, adj, c1, partition_of(d2))
            line += f" | 2WL cells={len(set(d2))} mixed={len(m2)}"
            if m2:
                line += f"  <<<< 2-WL COUNTEREXAMPLE {m2}"
            elif m1:
                line += "   (1-WL failure REPAIRED by 2-WL)"
        print(line)


def from_edges(nv, es):
    adj = [[0] * nv for _ in range(nv)]
    for a, b in es:
        adj[a][b] = adj[b][a] = 1
    return nv, adj


def K(m):
    return [(i, j) for i in range(m) for j in range(i + 1, m)]


def circ(m, offs):
    es = set()
    for i in range(m):
        for o in offs:
            a, b = i, (i + o) % m
            if a != b:
                es.add((min(a, b), max(a, b)))
    return from_edges(m, sorted(es))


def cayley(mods, S):
    els = list(__import__('itertools').product(*[range(m) for m in mods]))
    ix = {e: i for i, e in enumerate(els)}
    es = set()
    for e in els:
        for s in S:
            f = tuple((a + b) % m for a, b, m in zip(e, s, mods))
            if f != e:
                es.add((min(ix[e], ix[f]), max(ix[e], ix[f])))
    return from_edges(len(els), sorted(es))


def johnson(m, k):
    S = list(combinations(range(m), k))
    es = [(i, j) for i in range(len(S)) for j in range(i + 1, len(S))
          if len(set(S[i]) & set(S[j])) == k - 1]
    return from_edges(len(S), es)


def kneser(m, k):
    S = list(combinations(range(m), k))
    es = [(i, j) for i in range(len(S)) for j in range(i + 1, len(S))
          if not set(S[i]) & set(S[j])]
    return from_edges(len(S), es)


def paley(q):
    sq = {(i * i) % q for i in range(1, q)}
    return from_edges(q, [(i, j) for i in range(q) for j in range(i + 1, q)
                          if (j - i) % q in sq])


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


def clebsch():
    V = list(range(16))
    S = {1, 2, 4, 8, 15}
    return from_edges(16, [(a, b) for a in range(16) for b in range(a + 1, 16) if a ^ b in S])


PRISM = [(0,1),(1,2),(2,0),(3,4),(4,5),(5,3),(0,3),(1,4),(2,5)]
K33 = [(i, 3 + j) for i in range(3) for j in range(3)]
Q3 = [(0,1),(1,2),(2,3),(3,0),(4,5),(5,6),(6,7),(7,4),(0,4),(1,5),(2,6),(3,7)]
CUBIC8 = [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,0),(0,4),(1,5),(2,6),(3,7)]
PETB = [(0,1),(1,2),(2,3),(3,4),(4,0),(5,7),(7,9),(9,6),(6,8),(8,5),
        (0,5),(1,6),(2,7),(3,8),(4,9)]

print("=== (I) CFI-twisted over bases of growing treewidth ===")
for lab, base, m in [("CFI[K4]-tw (=net Z4)", K(4), 4), ("CFI[prism]-tw", PRISM, 6),
                     ("CFI[K3,3]-tw", K33, 6), ("CFI[Q3]-tw", Q3, 8),
                     ("CFI[cubic8]-tw", CUBIC8, 8), ("CFI[K5]-tw", K(5), 5),
                     ("CFI[Petersen]-tw", PETB, 10)]:
    n, adj, names, idx = cfi(base, m, (0,))
    if n > 80:
        print(f"  {lab:30s} n={n:4d}  SKIPPED (aut search too slow)")
        continue
    run(lab, n, adj)

print("\n=== (II) highly regular objects (where WL-blindness actually lives) ===")
CASES = [("net(Z4)", *net((4,))[:2]), ("net(Z2xZ2)", *net((2, 2))[:2]),
         ("net(Z6)", *net((6,))[:2]), ("net(Z8)", *net((8,))[:2]),
         ("net(Z9)", *net((9,))[:2]),
         ("Petersen", *from_edges(10, PETB)), ("rook4x4", *rook(4)),
         ("Shrikhande", *shrikhande()), ("Clebsch", *clebsch()),
         ("Paley(13)", *paley(13)), ("Paley(17)", *paley(17)),
         ("J(5,2)=T(5)", *johnson(5, 2)), ("J(6,2)=T(6)", *johnson(6, 2)),
         ("J(8,2)=T(8)", *johnson(8, 2)), ("Kneser(7,2)", *kneser(7, 2)),
         ("Q3 cube", *from_edges(8, Q3)), ("rook3x3=Ham(2,3)", *rook(3)),
         ("Cay(Z2^4,wt1+all1)", *cayley((2,2,2,2), [(1,0,0,0),(0,1,0,0),(0,0,1,0),
                                                    (0,0,0,1),(1,1,1,1)])),
         ("Cay(Z4xZ4,{+-e})", *cayley((4,4), [(1,0),(3,0),(0,1),(0,3)])),
         ("Cay(Z4xZ2^2,...)", *cayley((4,2,2), [(1,0,0),(3,0,0),(0,1,0),(0,0,1)])),
         ("circ(13,{1,3,9})", *circ(13, (1, 3, 9))),
         ("circ(16,{1,2,7})", *circ(16, (1, 2, 7))),
         ("circ(20,{1,4,5})", *circ(20, (1, 4, 5)))]
for lab, n, adj in CASES:
    run(lab, n, adj)
