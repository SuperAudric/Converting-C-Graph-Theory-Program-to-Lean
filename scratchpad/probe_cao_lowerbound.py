"""probe_cao_lowerbound.py -- the ONE load-bearing structural claim, measured.

Everything in the section 6e.4d argument rests on a single LOWER bound:

    (LB)  the ensemble's colouring, restricted to one copy, is at least as fine as
          that copy's own bare colour refinement.

That is what makes a rigid copy identifiable *inside the ensemble* without assuming anything about
the copies the conclusion is about.  It was argued, not measured.  This measures it.

The argument was: payload vertices of the same copy are adjacent (the payload is a clique) and of
different copies are not, so "same copy" is visible in a pair colour; hence the ensemble's stability
restricts to within-copy stability, and by section 6b the within-copy pair colours already see the
encoded adjacency.

Checked here on the real ensemble (L=4, N=332, m(0) individualized):
  A. within a copy, does the ensemble's payload colouring refine that copy's bare 1-WL colouring?
  B. ... and its bare 2-WL colouring (diagonal)?
  C. does the ensemble's within-copy PAIR colouring refine the copy's bare 2-WL pair colouring?
  D. sanity: does it also refine the copy's Aut-orbit partition (it must, being WL on a graph whose
     automorphisms include S_L, but a failure here would mean the model is wrong).
"""

import sys
import time
from itertools import combinations, permutations

import numpy as np

import probe_cao_ensemble_frame as base


def bare_wl1(L, adj):
    col = [0] * L
    for _ in range(L + 1):
        key = [(col[v], tuple(sorted(col[u] for u in range(L) if adj[v][u]))) for v in range(L)]
        tab = {k: n for n, k in enumerate(sorted(set(key)))}
        col = [tab[k] for k in key]
    return col


def bare_wl2(L, adj):
    col = [[(1 if u == v else 0, adj[u][v]) for v in range(L)] for u in range(L)]
    for _ in range(L + 1):
        new = [[(col[u][v], tuple(sorted((col[u][z], col[z][v]) for z in range(L))))
                for v in range(L)] for u in range(L)]
        tab = {k: n for n, k in enumerate(sorted({new[u][v] for u in range(L) for v in range(L)},
                                                key=repr))}
        col = [[tab[new[u][v]] for v in range(L)] for u in range(L)]
    return col


def orbits_of(L, edges_mask, PAIRS, SLOT):
    """Aut(G)-orbits on vertices, by brute force."""
    orb = list(range(L))

    def find(x):
        while orb[x] != x:
            x = orb[x]
        return x

    for p in permutations(range(L)):
        ok = True
        for k, (i, j) in enumerate(PAIRS):
            if ((edges_mask >> k) & 1) != ((edges_mask >> SLOT[(p[i], p[j])]) & 1):
                ok = False
                break
        if ok:
            for v in range(L):
                a, b = find(v), find(p[v])
                if a != b:
                    orb[a] = b
    return [find(v) for v in range(L)]


def refines(fine, coarse):
    """does `fine` refine `coarse`?  (equal fine colours => equal coarse colours)"""
    seen = {}
    for f, c in zip(fine, coarse):
        if f in seen and seen[f] != c:
            return False
        seen[f] = c
    return True


def main():
    t0 = time.time()
    L, NC, NS, PAIRS, SLOT = base.L, base.NC, base.NS, base.PAIRS, base.SLOT
    print(f'L={L}: ensemble N={base.N}, {NC} copies, m(0) individualized', flush=True)
    col = base.wl2(base.build_adj())
    print(f'  2-WL done in {time.time() - t0:.1f}s\n', flush=True)
    diag = col[np.arange(base.N), np.arange(base.N)]

    badA = badB = badC = badD = 0
    for c in range(NC):
        b = c * L
        adj = [[1 if (u != v and (c >> SLOT[(u, v)]) & 1) else 0 for v in range(L)] for u in range(L)]
        e_diag = [int(diag[b + u]) for u in range(L)]
        e_pair = [[int(col[b + u, b + v]) for v in range(L)] for u in range(L)]

        w1 = bare_wl1(L, adj)
        w2 = bare_wl2(L, adj)
        orb = orbits_of(L, c, PAIRS, SLOT)

        if not refines(e_diag, w1):
            badA += 1
        if not refines(e_diag, [w2[u][u] for u in range(L)]):
            badB += 1
        flat_e = [e_pair[u][v] for u in range(L) for v in range(L)]
        flat_w = [w2[u][v] for u in range(L) for v in range(L)]
        if not refines(flat_e, flat_w):
            badC += 1
        if not refines(e_diag, orb):
            badD += 1

    print(f'  A. ensemble within-copy vertex colouring refines the copy\'s bare 1-WL : '
          f'{NC - badA}/{NC} copies   {"OK" if not badA else "<-- FAILS"}')
    print(f'  B. ... refines the copy\'s bare 2-WL diagonal                          : '
          f'{NC - badB}/{NC} copies   {"OK" if not badB else "<-- FAILS"}')
    print(f'  C. ensemble within-copy PAIR colouring refines the copy\'s bare 2-WL   : '
          f'{NC - badC}/{NC} copies   {"OK" if not badC else "<-- FAILS"}')
    print(f'  D. (sanity) within-copy colouring refines the copy\'s Aut-orbits       : '
          f'{NC - badD}/{NC} copies   {"OK" if not badD else "<-- FAILS"}')
    print(f'\n==> (LB) HOLDS on every copy: {badA == badB == badC == 0}   ({time.time() - t0:.1f}s)')
    print('    (LB) is the only thing (P1) and (P2) need; it is a LOWER bound, so it cannot be')
    print('    weakened by the ensemble being large, symmetric, or coarser elsewhere.')


if __name__ == '__main__':
    main()
