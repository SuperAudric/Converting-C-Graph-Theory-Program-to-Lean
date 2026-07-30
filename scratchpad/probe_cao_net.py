#!/usr/bin/env python3
"""IDENTIFICATION + GENERALISATION of the CFI[K4]-tw counterexample.

Hypothesis (from |Aut| 576 vs 192 and the meet-0 "parallel class" structure):

  CFI[K4] untwisted  ==  incidence graph of the 3-net (Latin square) of Z2 x Z2
  CFI[K4] twisted    ==  incidence graph of the 3-net (Latin square) of Z4

3-net of an abelian group G (|G| = q): points = G x G  (q^2), lines = the 3q sets
  {x = a}, {y = b}, {x + y = c}.   Point on line iff the equation holds.
Totally symmetric (x + y + z = 0) => Aut acts transitively on all 3q lines.

If the identification holds, the counterexample is NOT about F2 parity at all: it is
  "individualize one line L; 1-WL sees {L}, {q-1 parallel}, {2q crossing};
   but the stabiliser splits the q-1 parallel lines into the Aut(G)-orbits of G \\ {0}"
=> a counterexample for EVERY abelian G that is not elementary abelian, with the gap
   growing (Z_{2^k}: one cell of 2^k - 1 splitting into k orbits by element ORDER).
"""
import sys
from collections import defaultdict, Counter
from itertools import product
sys.path.insert(0, "/workspace/scratchpad")
from probe_cao_cleanroom import cfi, wl, individualize, cells, all_isos, orbits, orbit_colouring
from probe_cao_vtcover import iso_exists, cell_orbit_reps

K4 = [(i, j) for i in range(4) for j in range(i + 1, 4)]


def net(mods):
    """3-net incidence graph of G = prod Z_mods.  Returns n, adj, names."""
    els = list(product(*[range(m) for m in mods]))
    q = len(els)
    add = lambda a, b: tuple((x + y) % m for x, y, m in zip(a, b, mods))
    pts = [('P', a, b) for a in els for b in els]
    lns = [('L', d, c) for d in range(3) for c in els]
    names = pts + lns
    idx = {nm: i for i, nm in enumerate(names)}
    n = len(names)
    adj = [[0] * n for _ in range(n)]
    for (_, a, b) in pts:
        for (d, c) in ((0, a), (1, b), (2, add(a, b))):
            p, l = idx[('P', a, b)], idx[('L', d, c)]
            adj[p][l] = adj[l][p] = 1
    return n, adj, names, q


def iso_graphs(nA, aA, nB, aB):
    """Isomorphic?  Encode as one graph pair via colour-preserving iso search."""
    if nA != nB:
        return False
    n = nA
    # search for iso between two DIFFERENT graphs: brute via disjoint union trick is
    # awkward; instead compare canonical forms by exhaustive I-R canonisation.
    def canon(n, adj):
        best = [None]

        def rec(col):
            col = wl(n, adj, col)
            d = cells(col)
            big = [c for c in sorted(d) if len(d[c]) > 1]
            if not big:
                pos = {col[v]: v for v in range(n)}
                perm = [pos[c] for c in sorted(pos)]          # perm[i] = vertex ranked i
                key = tuple(adj[perm[i]][perm[j]] for i in range(n) for j in range(i + 1, n))
                if best[0] is None or key < best[0]:
                    best[0] = key
                return
            c0 = big[0]
            for x in d[c0]:
                rec(individualize(n, col, x))
        rec([0] * n)
        return best[0]
    return canon(nA, aA) == canon(nB, aB)


if __name__ == "__main__":
    print("=== A. identification ===")
    for lab, tw, mods in [("CFI[K4] untwisted", (), (2, 2)), ("CFI[K4] twisted", (0,), (4,))]:
        nC, aC, nmC, _ = cfi(K4, 4, tw)
        nN, aN, nmN, q = net(mods)
        print(f"  {lab}: n={nC} vs net(Z{mods})={nN} ... isomorphic: "
              f"{iso_graphs(nC, aC, nN, aN)}")

    print("\n=== B. the net family: does CAO propagate? ===")
    for mods in [(2, 2), (4,), (5,), (6,), (3, 3), (2, 4), (8,), (9,), (7,)]:
        n, adj, names, q = net(mods)
        root = wl(n, adj, [0] * n)
        csz = sorted(len(v) for v in cells(root).values())
        # root CAO: need Aut-orbits = cells.  Aut is transitive on points and on lines for a
        # totally symmetric net; verify by pairwise orbit test inside each cell.
        reps = {}
        okroot = True
        for c, cell in cells(root).items():
            r = cell_orbit_reps(n, adj, root, cell)
            reps[c] = r
            if r is None or len(r) > 1:
                okroot = False
        # individualize a line of class 0
        L = names.index(('L', 0, tuple(0 for _ in mods)))
        c1 = wl(n, adj, individualize(n, root, L))
        mixed = []
        for cell in cells(c1).values():
            if len(cell) == 1:
                continue
            r = cell_orbit_reps(n, adj, c1, cell)
            if r is None:
                mixed.append(('?', len(cell)))
            elif len(r) > 1:
                sub = Counter()
                for v in cell:
                    for k, rr in enumerate(r):
                        if iso_exists(n, adj, individualize(n, c1, v), individualize(n, c1, rr)):
                            sub[k] += 1
                            break
                mixed.append((sorted(sub.values()), [names[x] for x in r]))
        G = "Z" + "xZ".join(str(m) for m in mods)
        print(f"  net({G:8s}) n={n:4d} q={q:2d} root cells={csz} rootCAO={okroot} "
              f"cells-after={sorted(len(v) for v in cells(c1).values())}")
        print(f"      MIXED after individualizing one line: "
              f"{[m[0] for m in mixed] if mixed else 'none'}")
        for m in mixed:
            print(f"        orbit reps {m[1]}")
