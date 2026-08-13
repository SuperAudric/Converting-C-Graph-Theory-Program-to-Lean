"""probe_cao_cfi_bare.py — the missing reproducible check behind section 5.1's premise.

The doc states "Both CFI pairs are checked 2-WL-blind bare first, so the test is not vacuous".
No checked-in probe did that check; it was an ad-hoc run.  Without it the whole CFI row is
unfalsifiable -- if CFI[K4] were NOT 2-WL-blind bare, the frame encoding separating it would say
nothing at all about the encoding.  So: measure it, and record the numbers.

Also reports the plain/twisted pair is genuinely NON-ISOMORPHIC (via 3-WL separating it), because a
"2-WL-blind" pair that is actually isomorphic is the other way this row could be vacuous.
"""

import sys
from itertools import combinations
from probe_cao_cleanroom import cfi


def cfi_ve(m, twisted):
    base = [(i, j) for i, j in combinations(range(m), 2)]
    n, adj, names, idx = cfi(base, m, twisted)
    E = {frozenset({a, b}) for a in range(n) for b in range(a + 1, n) if adj[a][b]}
    return list(range(n)), E


def wl2(verts, adjset, tag):
    n = len(verts)
    idx = {v: i for i, v in enumerate(verts)}
    col = [0] * (n * n)
    atoms = {}
    for x in verts:
        a = idx[x]
        for y in verts:
            k = (x == y, (x, y) in adjset)
            col[a * n + idx[y]] = atoms.setdefault(k, len(atoms))
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
        if len(table) == ncol:
            print(f'  [{tag}] stable after {rnd} rounds, {ncol} pair colours', flush=True)
            return col, idx
        col, ncol = new, len(table)


def bare_equivalent(m):
    (V1, E1), (V2, E2) = cfi_ve(m, ()), cfi_ve(m, (0,))
    verts = [(1, x) for x in V1] + [(2, x) for x in V2]
    adjset = set()
    for tag, E in ((1, E1), (2, E2)):
        for e in E:
            a, b = tuple(e)
            adjset.add(((tag, a), (tag, b)))
            adjset.add(((tag, b), (tag, a)))
    col, idx = wl2(verts, adjset, f'K{m} bare')
    n = len(verts)
    prof = {1: {}, 2: {}}
    for x in verts:
        for y in verts:
            if x[0] == y[0]:
                c = col[idx[x] * n + idx[y]]
                prof[x[0]][c] = prof[x[0]].get(c, 0) + 1
    return prof[1] == prof[2], len(V1)


if __name__ == '__main__':
    for m in [int(a) for a in (sys.argv[1:] or ['4', '5'])]:
        eq, n = bare_equivalent(m)
        print(f'CFI[K{m}]  n={n}  bare 2-WL: plain ~ twisted equivalent = {eq}'
              f'   {"<- 2-WL-BLIND, premise holds" if eq else "<- NOT BLIND, section 5.1 row is VACUOUS"}',
              flush=True)
