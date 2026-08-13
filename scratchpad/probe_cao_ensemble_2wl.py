"""probe_cao_ensemble_2wl.py — 2-WL on the REAL ensemble (shared frame, every copy), never measured.

Section 6 ran the rung-1 ensemble at 1-WL only, and every 2-WL verdict in the doc comes from the
TWO-COPY model with a PRIVATE frame per copy.  That model has now been measured to over-separate
relative to the real object at 1-WL (probe_cao_ensemble_audit.py: 538 cells / 6 mixed vs the
ensemble's 292 / 100), so the 2-WL kills inherit a faithfulness question the doc never closes.

At L = 4 labels the real object is small enough to settle directly:
    payload  p(c,i)   c in {0,1}^6, i in 0..3     4*64 = 256
    frame    f(k,t)   k a slot, t a type          2*6  =  12     SHARED by all 64 copies
    central  m(g)     g in {0,1}^6                        64
    |V| = 332.

THE CLAIM UNDER TEST (an argument, so this is a check of a proof, not a fishing trip).  The frame is
shared and S_L is transitive on slots, so a frame VERTEX can never hold more than |types| colours --
which is why 1-WL on the ensemble collapses to the degree sequence.  But 2-WL colours PAIRS, and
    p(c,i) and p(c,j) have the frame vertex f({i,j}, c_{ij}) as a COMMON NEIGHBOUR,
and after m(0) is individualized that vertex's type is absolute.  An edge encoded as a typed common
neighbour is exactly what 2-WL counts, so 2-WL should recover the adjacency of EVERY copy at round 1,
however symmetric the frame is.  If so, the frame cannot hide a payload from 2-WL in principle, and
the admission test's necessary direction is a theorem rather than a model artefact.

Reports: whether payload pair colours separate edge from non-edge within every copy, and the mixed
cell count against the true Aut_{m(0)} = S_L orbits.
"""

import sys
from itertools import combinations

L = int(sys.argv[1]) if len(sys.argv) > 1 else 4
PAIRS = list(combinations(range(L), 2))
NS = len(PAIRS)
NC = 1 << NS
SLOT = {}
for k, (i, j) in enumerate(PAIRS):
    SLOT[(i, j)] = SLOT[(j, i)] = k

P0 = 0
F0 = L * NC
M0 = F0 + 2 * NS
N = M0 + NC


def build():
    adj = [set() for _ in range(N)]

    def add(u, w):
        adj[u].add(w)
        adj[w].add(u)

    for c in range(NC):
        b = c * L
        for a in range(L):
            for d in range(a + 1, L):
                add(b + a, b + d)                                  # clique payload
        for a in range(L):
            for d in range(L):
                if a != d:
                    k = SLOT[(a, d)]
                    add(b + a, F0 + 2 * k + ((c >> k) & 1))
    for k in range(NS):
        add(F0 + 2 * k, F0 + 2 * k + 1)
    for g in range(NC):
        for k in range(NS):
            add(M0 + g, F0 + 2 * k + ((g >> k) & 1))
    return adj


def kind(v):
    return 0 if v < F0 else (1 if v < M0 else 2)


def wl2(adj, vcol):
    n = N
    inadj = [[0] * n for _ in range(n)]
    for u in range(n):
        for w in adj[u]:
            inadj[u][w] = 1
    col = [0] * (n * n)
    atoms = {}
    for a in range(n):
        for b in range(n):
            k = (a == b, inadj[a][b], vcol[a], vcol[b])
            col[a * n + b] = atoms.setdefault(k, len(atoms))
    ncol = len(set(col))
    rnd = 0
    while True:
        rnd += 1
        C = ncol
        colT = [0] * (n * n)
        for a in range(n):
            for b in range(n):
                colT[b * n + a] = col[a * n + b]
        table, new = {}, [0] * (n * n)
        rng = range(n)
        for a in rng:
            ra = col[a * n:(a + 1) * n]
            for b in rng:
                rb = colT[b * n:(b + 1) * n]
                cnt = {}
                for z in rng:
                    key = ra[z] * C + rb[z]
                    cnt[key] = cnt.get(key, 0) + 1
                sig = (col[a * n + b], tuple(sorted(cnt.items())))
                t = table.get(sig)
                if t is None:
                    t = table[sig] = len(table)
                new[a * n + b] = t
        print(f'  round {rnd}: {ncol} -> {len(table)}', flush=True)
        if len(table) == ncol:
            return col
        col, ncol = new, len(table)


def s_orbits():
    def perms(k):
        if k == 1:
            yield (0,)
            return
        for p in perms(k - 1):
            for t in range(k):
                yield p[:t] + (k - 1,) + p[t:]
    par = list(range(L * NC))

    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for pi in perms(L):
        smap = [SLOT[(pi[i], pi[j])] for (i, j) in PAIRS]
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


if __name__ == '__main__':
    print(f'L={L}: {N} vertices ({L*NC} payload, {2*NS} frame, {NC} central)', flush=True)
    adj = build()
    vcol = [kind(v) for v in range(N)]
    vcol[M0] = 3                                                   # individualize m(0)
    col = wl2(adj, vcol)

    # (1) does 2-WL recover each copy's adjacency?
    bad = 0
    edgecols, noncols = set(), set()
    for c in range(NC):
        for (i, j) in PAIRS:
            pc = col[(c * L + i) * N + (c * L + j)]
            if (c >> SLOT[(i, j)]) & 1:
                edgecols.add(pc)
            else:
                noncols.add(pc)
    overlap = edgecols & noncols
    print(f'payload-pair colours on type-1 slots: {len(edgecols)}, on type-0 slots: {len(noncols)}, '
          f'overlap {len(overlap)}')
    print(f'==> 2-WL RECOVERS every copy\'s adjacency: {not overlap}')

    # (2) mixed cells against the true stabilizer orbits
    diag = [col[v * N + v] for v in range(L * NC)]
    orb = s_orbits()
    cell_orbs = {}
    for v in range(L * NC):
        cell_orbs.setdefault(diag[v], set()).add(orb[v])
    mixed = [c for c, o in cell_orbs.items() if len(o) > 1]
    print(f'payload vertex cells {len(set(diag))} | true Aut_m = S_{L} orbits {len(set(orb))} '
          f'| MIXED CELLS {len(mixed)}')
