"""probe_cao_ensemble.py — IS THE ENSEMBLE PASSIVE?  Construction C at rung 1, full symmetry.

The open question from `docs/chain-descent-cao-carrier-falsifiers.md` §6.  The two-copy model does
NOT separate C6 from 2C3 under the triangle frame (measured, §5).  Here every copy is present, so
WL also gets the whole Hamming structure on colouring space as a reference frame.  If that extra
structure separates them, the ensemble is doing work no bounded-level argument covers.

OBJECT (6 labels, 15 slots, gauge Z_2 per slot, nothing restricted):
  frame    f(k,t)   k a slot, t a type; f(k,0) ~ f(k,1)          (the two corner-pairs of one cube)
  payload  p(c,i)   one copy per colouring c in {0,1}^15; the copy's 6 vertices form a K6, and
                    p(c,i) ~ f({i,j}, c({i,j})) for every j != i
  central  m(g)     one per gauge g in {0,1}^15;  m(g) ~ f(k, g(k)) for every slot k

  |V| = 6*2^15 + 30 + 2^15 = 229406,  |E| ~ 1.97M.

WHY THE TWO GROUP FACTS BELOW ARE PROVED, NOT ASSUMED (both needed for the verdict to mean anything):

  * CAO start = exactly THREE cells.  Aut contains the gauge (Z_2)^15 (sigma_h: f(k,t) -> f(k,t^h),
    p(c,i) -> p(c^h,i), m(g) -> m(g^h)) and the label group S_6.  Together they are transitive on
    payload, on frame and on centrals separately; the three kinds cannot merge (degrees 10, ~49k, 15).
    A single orbit per kind cannot be coarsened, so this IS the true orbit partition.

  * Aut_{m(0)} = S_6 EXACTLY (order 720).  Any alpha fixing m(0) preserves its neighbourhood
    {f(k,0)}, hence types; "two slots share a label" is recoverable (disjoint slots have no common
    payload neighbour), so alpha induces an automorphism of the triangular graph T(6), whose
    automorphism group is S_6; and the slot permutation then determines the action on every copy.
    So comparing against S_6-orbits is comparing against the true stabilizer, not a subgroup.
"""

import sys
from array import array
from itertools import combinations

L = 6
PAIRS = list(combinations(range(L), 2))
NS = len(PAIRS)                                   # 15 slots
SLOT = {}
for k, (i, j) in enumerate(PAIRS):
    SLOT[(i, j)] = SLOT[(j, i)] = k
NC = 1 << NS                                      # 32768 colourings / gauges

P0 = 0                                            # payload  p(c,i) = c*6 + i
F0 = L * NC                                       # frame    f(k,t) = F0 + 2k + t
M0 = F0 + 2 * NS                                  # central  m(g)   = M0 + g
N = M0 + NC

KIND_P, KIND_F, KIND_M = 0, 1, 2


def kind(v):
    return KIND_P if v < F0 else (KIND_F if v < M0 else KIND_M)


def build():
    deg = array('i', [0]) * 0
    deg = [0] * N
    edges = []
    ap = edges.append
    for c in range(NC):
        base = c * L
        for a in range(L):
            for b in range(a + 1, L):
                ap((base + a, base + b))                       # K6 inside the copy
        for a in range(L):
            for b in range(L):
                if a == b:
                    continue
                k = SLOT[(a, b)]
                ap((base + a, F0 + 2 * k + ((c >> k) & 1)))    # payload -> frame
    for k in range(NS):
        ap((F0 + 2 * k, F0 + 2 * k + 1))                       # the cube link
    for g in range(NC):
        for k in range(NS):
            ap((M0 + g, F0 + 2 * k + ((g >> k) & 1)))          # central -> frame
    for (u, w) in edges:
        deg[u] += 1
        deg[w] += 1
    indptr = array('i', [0]) * 0
    indptr = array('l', [0] * (N + 1))
    for v in range(N):
        indptr[v + 1] = indptr[v] + deg[v]
    fill = list(indptr[:N])
    indices = array('i', [0]) * (2 * len(edges))
    for (u, w) in edges:
        indices[fill[u]] = w
        fill[u] += 1
        indices[fill[w]] = u
        fill[w] += 1
    return indptr, indices


def wl1(indptr, indices, col):
    """colour refinement; signature = (own colour, sorted (colour,count) pairs) so the ~49k-degree
    frame vertices cost a count, not a 49k-tuple."""
    col = list(col)
    ncol = len(set(col))
    rounds = 0
    while True:
        rounds += 1
        table, new = {}, [0] * N
        for v in range(N):
            cnt = {}
            for z in indices[indptr[v]:indptr[v + 1]]:
                cz = col[z]
                cnt[cz] = cnt.get(cz, 0) + 1
            key = (col[v], tuple(sorted(cnt.items())))
            t = table.get(key)
            if t is None:
                t = table[key] = len(table)
            new[v] = t
        if len(table) == ncol:
            return col, rounds
        col, ncol = new, len(table)


def s6_orbits():
    """union-find on payload vertices under S_6: pi maps p(c,i) -> p(c^pi, pi(i)),
    c^pi(k) = c(pi^-1 k).  Two generators suffice."""
    gens = [[1, 0, 2, 3, 4, 5], [1, 2, 3, 4, 5, 0]]
    par = list(range(L * NC))

    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x

    for pi in gens:
        smap = [SLOT[(pi[i], pi[j])] for (i, j) in PAIRS]      # k -> image slot
        for c in range(NC):
            cc = 0
            for k in range(NS):
                if (c >> k) & 1:
                    cc |= 1 << smap[k]
            for i in range(L):
                a, b = find(c * L + i), find(cc * L + pi[i])
                if a != b:
                    par[a] = b
    return [find(x) for x in range(L * NC)]


def col_of(edges):
    c = 0
    for e in edges:
        c |= 1 << SLOT[e]
    return c


if __name__ == '__main__':
    print(f'building: {N} vertices ({L*NC} payload, {2*NS} frame, {NC} central)', flush=True)
    indptr, indices = build()
    print(f'  {len(indices)//2} edges', flush=True)

    start = [kind(v) for v in range(N)]                        # the true CAO start (3 cells)
    start[M0 + 0] = 3                                          # individualize m(all-zero gauge)
    print('CAO start cells:', sorted({k: start.count(k) for k in set(start)}.items()), flush=True)

    col, rounds = wl1(indptr, indices, start)
    pay = col[:L * NC]
    print(f'1-WL stabilized in {rounds} rounds, {len(set(col))} cells total, '
          f'{len(set(pay))} on the payload', flush=True)

    orb = s6_orbits()
    print(f'Aut_v = S_6 orbits on the payload: {len(set(orb))}', flush=True)

    cell_orbs = {}
    for v in range(L * NC):
        cell_orbs.setdefault(pay[v], set()).add(orb[v])
    mixed = {c: len(o) for c, o in cell_orbs.items() if len(o) > 1}
    print(f'MIXED CELLS (1-WL cell strictly coarser than the Aut_v-orbits): {len(mixed)}', flush=True)
    if mixed:
        top = sorted(mixed.values(), reverse=True)[:10]
        print(f'  orbits fused per mixed cell (top 10): {top}', flush=True)

    c6 = col_of([(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (0, 5)])
    c33 = col_of([(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5)])
    same_cell = {pay[c6 * L + i] for i in range(L)} & {pay[c33 * L + i] for i in range(L)}
    same_orb = {orb[c6 * L + i] for i in range(L)} & {orb[c33 * L + i] for i in range(L)}
    print(f'C6 copy cells   {sorted({pay[c6*L+i] for i in range(L)})}')
    print(f'2C3 copy cells  {sorted({pay[c33*L+i] for i in range(L)})}')
    print(f'C6 / 2C3 share a 1-WL cell: {bool(same_cell)}  | share an Aut_v-orbit: {bool(same_orb)}')
