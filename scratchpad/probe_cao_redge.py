"""probe_cao_redge.py -- sizing the reader's r-edge restricted ensemble, and checking its ruler.

READER'S PROPOSAL (2026-08-15).  Drop the centrals (the all-zero state is individualized implicitly)
and keep only the copies with EXACTLY r edge-states.  The copy set stays S_L-invariant, so the object
is still uniform and its payload orbits are still the marked-graph iso classes; it is just smaller
than 2^C(L,2).  Their candidate ruler at L=6, r=6: a triangle with pendant paths of lengths 0, 1, 2.

WHAT THIS CHECKS
  1. is that graph really a ruler (refinement-discrete, hence rigid)?
  2. how many r-edge graphs are rulers, per r -- i.e. which r are usable?
  3. THE SIZING QUESTION: a ruler is rigid, so its S_L-orbit is ALL of L! = 720 copies.  Any object
     that contains a ruler and is S_L-invariant therefore contains >= 720 copies.  That is a floor
     the r-restriction cannot lower.
"""

import sys
from itertools import combinations, permutations

L = int(sys.argv[1]) if len(sys.argv) > 1 else 6
PAIRS = list(combinations(range(L), 2))
NS = len(PAIRS)


def wl1(L, edges):
    adj = [[0] * L for _ in range(L)]
    for (i, j) in edges:
        adj[i][j] = adj[j][i] = 1
    col = [0] * L
    for _ in range(L + 1):
        key = [(col[v], tuple(sorted(col[u] for u in range(L) if adj[v][u]))) for v in range(L)]
        tab = {k: n for n, k in enumerate(sorted(set(key)))}
        col = [tab[k] for k in key]
    return col


def aut_size(L, mask):
    slot = {}
    for k, (i, j) in enumerate(PAIRS):
        slot[(i, j)] = slot[(j, i)] = k
    n = 0
    for p in permutations(range(L)):
        if all(((mask >> k) & 1) == ((mask >> slot[(p[i], p[j])]) & 1) for k, (i, j) in enumerate(PAIRS)):
            n += 1
    return n


def main():
    # 1. the reader's candidate ruler
    edges = [(0, 1), (0, 2), (1, 2), (1, 3), (2, 4), (4, 5)]
    mask = 0
    slot = {}
    for k, (i, j) in enumerate(PAIRS):
        slot[(i, j)] = slot[(j, i)] = k
    for e in edges:
        mask |= 1 << slot[e]
    col = wl1(L, edges)
    print(f"reader's ruler: triangle {0,1,2} + pendants of length 0/1/2   edges={len(edges)}")
    print(f"  refinement colours : {col}")
    print(f"  refinement-DISCRETE: {len(set(col)) == L}")
    print(f"  |Aut|              : {aut_size(L, mask)}   (rigid iff 1)")
    print(f"  ==> S_{L}-orbit size : {len(list(permutations(range(L)))) // aut_size(L, mask)} copies")

    # 2. rulers per edge count
    print(f'\n r   r-edge graphs   of them rulers   ruler orbit = 720 copies each')
    for r in range(0, NS + 1):
        tot = rulers = 0
        for combo in combinations(range(NS), r):
            m = 0
            for k in combo:
                m |= 1 << k
            tot += 1
            es = [PAIRS[k] for k in combo]
            if len(set(wl1(L, es))) == L:
                rulers += 1
        if tot:
            print(f'{r:>2}   {tot:>13}   {rulers:>14}')
        if r >= 8:
            print('   ... (complement-symmetric beyond here)')
            break

    # 3. sizing
    print(f'\nSIZING -- payload vertices = 6 per copy, frame = {2 * NS} vertices')
    for ncopies, what in [(720, 'ruler orbit alone (forced: a ruler is rigid)'),
                          (720 + 60, '+ an orbit of a graph with |Aut| = 12'),
                          (5005, 'ALL 6-edge graphs on 6 labels')]:
        n = ncopies * L + 2 * NS
        print(f'  {ncopies:>5} copies -> N = {n:>6} vertices'
              f'   (naive 2-WL is ~N^3 = {n ** 3:.1e} per round)   {what}')


if __name__ == '__main__':
    main()
