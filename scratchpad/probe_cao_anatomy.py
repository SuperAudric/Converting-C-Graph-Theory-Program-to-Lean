"""§14 — the ANATOMY of a CAO failure, and the ARITY LADDER above it.

Four measurements, all on the clean-room machinery of §8.1 (never the broken orbit oracle):

  A  the local shape v exposes, and the far cell's split as a PULLBACK of that shape's
     PAIR-orbits.  Shrikhande vs rook 4x4 -- the two SRG(16,6,2,2) graphs, identical to
     1-WL in every parameter, one of which splits and one of which does not.
  B  the support structure of mixed cells (depth <= 2, every recorded deficient root):
     is the "mixed touches mixed" chain WELL-FOUNDED?
  C  the concrete distinguisher in Shrikhande, and that it traces back to v.
  D  the level-up analogue: a group transitive on PAIRS but not on TRIPLES (A5 on 6
     points), and the 2-closure obstruction to ever exposing one with binary structure.

Usage:  python3 probe_cao_anatomy.py [--closure]
        --closure adds the brute force over all 32768 graphs on 6 vertices (~minutes).
"""
import sys
from collections import defaultdict
from itertools import combinations, permutations

from probe_cao_cleanroom import (wl, individualize, cells, all_isos, orbits,
                                 orbit_colouring)
from probe_cao_induction import shrikhande, chang, rook, T8
from probe_cao_net import net


# --------------------------------------------------------------------------- A
def anatomy(label, n, adj, v=0):
    """The exposed local shape, its Aut_v-orbits on PAIRS, and the attachment map."""
    print(f"\n--- {label} ---")
    auts = all_isos(n, adj, [0] * n, [0] * n)
    autv = [g for g in auts if g[v] == v]
    orbv = orbit_colouring(n, orbits(n, autv))
    col = wl(n, adj, individualize(n, [0] * n, v))
    N = [u for u in range(n) if adj[v][u]]
    F = [u for u in range(n) if u != v and not adj[v][u]]
    print(f"|Aut| = {len(auts)}   |Aut_v| = {len(autv)}")

    par = {x: x for x in N}

    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for x, y in combinations(N, 2):
        if adj[x][y]:
            par[f(x)] = f(y)
    comp = defaultdict(set)
    for x in N:
        comp[f(x)].add(x)
    deg = sorted(sum(adj[x][y] for y in N) for x in N)
    print(f"shape induced on N(v): {len(N)} vertices, degrees {deg}, "
          f"{len(comp)} component(s) sizes {sorted(len(c) for c in comp.values())}")

    pairs = list(combinations(sorted(N), 2))
    pid = {p: i for i, p in enumerate(pairs)}
    par2 = list(range(len(pairs)))

    def f2(x):
        while par2[x] != x:
            par2[x] = par2[par2[x]]
            x = par2[x]
        return x
    for g in autv:
        for (a, b) in pairs:
            q = (min(g[a], g[b]), max(g[a], g[b]))
            i, j = f2(pid[(a, b)]), f2(pid[q])
            if i != j:
                par2[i] = j
    porb = defaultdict(list)
    for p in pairs:
        porb[f2(pid[p])].append(p)
    print(f"Aut_v transitive on N(v): {len({orbv[x] for x in N}) == 1}   "
          f"orbits on PAIRS inside N(v): "
          f"{[('edge' if adj[g[0][0]][g[0][1]] else 'non-edge', len(g)) for g in porb.values()]}")
    print(f"far cell: {len(F)} vertices, 1-WL cells "
          f"{sorted(len(c) for c in cells([col[u] for u in F]).values())}, "
          f"Aut_v orbits {sorted(len(c) for c in cells([orbv[u] for u in F]).values())}")

    tally = defaultdict(lambda: defaultdict(int))
    for u in F:
        common = tuple(sorted(x for x in N if adj[x][u]))
        assert len(common) == 2, f"attachment is not by pairs: {common}"
        tally[f2(pid[common])][orbv[u]] += 1
    for k, g in porb.items():
        rep = g[0]
        kind = 'ADJACENT' if adj[rep[0]][rep[1]] else 'non-adjacent'
        car = dict(tally[k]) if k in tally else "NO far vertex"
        print(f"   pair-orbit (size {len(g)}, {kind}) carries: {car}")


# --------------------------------------------------------------------------- B
def support(label, n, adj, depth=2):
    """Every mixed cell at depth <= `depth`: what mixed cells support it?"""
    try:
        auts = all_isos(n, adj, [0] * n, [0] * n, limit=4 * 10 ** 6)
    except RuntimeError:
        print(f"  {label}: budget exhausted, SKIPPED")
        return []
    seen = []

    def rec(col, gens, pinned, d):
        cs = cells(col)
        orb = orbit_colouring(n, orbits(n, gens))
        for c, vs in cs.items():
            pieces = {orb[u] for u in vs}
            if len(pieces) < 2:
                continue
            nbr = {col[w] for u in vs for w in range(n) if adj[u][w]}
            mixed_nbr = [k for k in nbr if len({orb[u] for u in cs[k]}) > 1 and k != c]
            seen.append((label, list(pinned), len(vs),
                         sorted(sum(1 for u in vs if orb[u] == p) for p in pieces),
                         c in nbr, mixed_nbr))
        if d == 0:
            return
        for c, vs in sorted(cs.items()):
            if len(vs) > 1:                      # CAO: one representative per cell
                u = vs[0]
                rec(wl(n, adj, individualize(n, col, u)),
                    [g for g in gens if g[u] == u], pinned + [u], d - 1)

    rec(list(orbit_colouring(n, orbits(n, auts))), auts, [], depth)
    for lab, pin, sz, pieces, selfadj, others in seen:
        print(f"  {lab} pinned={pin}: mixed cell {sz} -> pieces {pieces} | "
              f"self-adjacent={selfadj} | other mixed cells touching={others}")
    if not seen:
        print(f"  {label}: no mixed cell at depth <= {depth}")
    return seen


# --------------------------------------------------------------------------- C
def distinguisher(n, adj, v=0):
    """In Shrikhande: are v's two common neighbours with u adjacent to each other?"""
    auts = all_isos(n, adj, [0] * n, [0] * n)
    autv = [g for g in auts if g[v] == v]
    orbv = orbit_colouring(n, orbits(n, autv))
    col = wl(n, adj, individualize(n, [0] * n, v))
    F = [u for u in range(n) if u != v and not adj[v][u]]
    assert len({col[u] for u in F}) == 1, "far cell is not one 1-WL cell"
    tally = defaultdict(set)
    for u in F:
        common = [x for x in range(n) if adj[v][x] and adj[x][u]]
        e = sum(1 for a, b in combinations(common, 2) if adj[a][b])
        tally[orbv[u]].add(e)
    for o, es in tally.items():
        print(f"  Aut_v-orbit {o} (size {sum(1 for u in F if orbv[u]==o)}): "
              f"edges among v's common nbrs with u = {sorted(es)}")
    print(f"  separates the orbits: {len(tally) == sum(len(e) for e in tally.values())}"
          f" and no value is shared: {len(set().union(*tally.values())) == len(tally)}")


# --------------------------------------------------------------------------- D
def psl25():
    """A5 = PSL(2,5) on the 6 points of PG(1,5): x -> x+1 and x -> -1/x."""
    INF = 5

    def mk(f):
        return tuple(f(x) for x in range(6))
    g1 = mk(lambda x: INF if x == INF else (x + 1) % 5)
    g2 = mk(lambda x: 0 if x == INF else (INF if x == 0 else (-pow(x, 3, 5)) % 5))
    grp, front = {tuple(range(6))}, [tuple(range(6))]
    while front:
        g = front.pop()
        for h in (g1, g2):
            k = tuple(h[g[i]] for i in range(6))
            if k not in grp:
                grp.add(k)
                front.append(k)
    return sorted(grp)


def arity_lift(do_closure=False):
    G = psl25()
    print(f"|G| = {len(G)}  (PSL(2,5) = A5 on 6 points)")

    def orbs(objs):
        seen, out = set(), []
        for o in objs:
            if o in seen:
                continue
            orb = {tuple(sorted(g[x] for x in o)) for g in G}
            seen |= orb
            out.append(sorted(orb))
        return out
    po = orbs(list(combinations(range(6), 2)))
    to = orbs(list(combinations(range(6), 3)))
    print(f"  orbits on PAIRS   : {[len(o) for o in po]}   transitive: {len(po) == 1}")
    print(f"  orbits on TRIPLES : {[len(o) for o in to]}   transitive: {len(to) == 1}")

    if len(to) == 2:
        A, B = to

        def stats(X, Y):
            d = defaultdict(int)
            for a in X:
                for b in Y:
                    if a != b:
                        d[len(set(a) & set(b))] += 1
            return dict(sorted(d.items()))
        print(f"  |T n T'| within A : {stats(A, A)}")
        print(f"  |T n T'| within B : {stats(B, B)}")
        print(f"  |T n T'| A x B    : {stats(A, B)}")
        print("  => already separated by the crudest pair invariant a coherent closure has")

    print("\n  2-closure obstruction: a 2-transitive group has only the two orbitals")
    print("  {diagonal, rest}, so its 2-closure is the FULL symmetric group.  Hence no")
    print("  edge-coloured graph on the cell can have such a group as its automorphisms.")
    if do_closure:
        V, P = list(range(6)), list(combinations(range(6), 2))
        ALL = list(permutations(V))
        hits = 0
        for mask in range(1 << len(P)):
            col = {frozenset(p): (mask >> i) & 1 for i, p in enumerate(P)}
            A = [g for g in ALL
                 if all(col[frozenset(p)] == col[frozenset((g[p[0]], g[p[1]]))] for p in P)]
            if len({(g[0], g[1]) for g in A}) == 30 and len(A) != 720:
                hits += 1
        print(f"  brute force over all {1 << len(P)} graphs on 6 vertices: "
              f"2-transitive-but-not-S6 automorphism groups found = {hits}")


if __name__ == "__main__":
    print("=== A. the exposed local shape, and the split as a pullback of its pair-orbits ===")
    anatomy("Shrikhande  (CAO FAILS at 1-WL)", *shrikhande())
    anatomy("rook 4x4    (CAO propagates)", *rook(4))

    print("\n=== B. is the 'mixed touches mixed' chain well-founded? ===")
    seen = []
    for lab, g in [("Shrikhande", shrikhande()),
                   ("Chang-2", chang([(0, 1), (1, 2), (2, 3), (3, 4),
                                      (4, 5), (5, 6), (6, 7), (7, 0)])),
                   ("rook4x4", rook(4)),
                   ("T8", T8())]:
        seen += support(lab, *g)
    nn, na, _, _ = net([4])
    seen += support("net(Z4)", nn, na, depth=1)
    iso = [s for s in seen if not s[4] and not s[5]]
    print(f"\n  mixed cells found: {len(seen)};  with NO mixed support: {len(iso)} {iso}")

    print("\n=== C. what actually distinguishes the two orbits (Shrikhande) ===")
    distinguisher(*shrikhande())

    print("\n=== D. the arity ladder: transitive on pairs, not on triples ===")
    arity_lift(do_closure="--closure" in sys.argv)
