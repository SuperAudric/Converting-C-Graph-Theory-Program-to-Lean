"""probe_cao_cfi_frame.py — do CFI pairs survive the frame encoding?

The payload admission test (doc section 5): a payload pair must still be 2-WL-resistant AFTER the
edge encoding.  Shrikhande/rook fails it.  CFI pairs are the natural next candidates -- measured
2-WL-blind bare (probe_cao_payload_pair-style check: CFI[K4] and CFI[K5] both equivalent = True).

Two encodings per pair, because they differ in size by an order of magnitude:
  sub    subdivide EDGES only            n + |E|      (the reader's "subdivided" check)
  full   a frame vertex on EVERY pair,   n + C(n,2)   typed edge/non-edge  (what construction C
         actually builds -- non-edges carry a type too)

Frame vertices carry ONLY their type, never an identity of their own.  No component marker, so
separation has to be earned.  Control: the same pair against itself must come out unseparated.

2-WL uses a COUNTING signature (multiset of (col[a][z], col[z][b]) as (key,count) pairs) rather than
an n-long tuple per pair -- at n = 812 the tuple form needs ~4 GB of signatures per round.
"""

import sys
from itertools import combinations
from probe_cao_cleanroom import cfi


def cfi_ve(m, twisted):
    base = [(i, j) for i, j in combinations(range(m), 2)]
    n, adj, names, idx = cfi(base, m, twisted)
    E = {frozenset({a, b}) for a in range(n) for b in range(a + 1, n) if adj[a][b]}
    return list(range(n)), E


def encode(V, E, mode):
    """returns (verts, typ, adjset); typ 0 = payload, 1 = frame-connected, 2 = frame-disconnected"""
    verts = [('v', x) for x in V]
    typ = {('v', x): 0 for x in V}
    adj = set()

    def add(u, w):
        adj.add((u, w))
        adj.add((w, u))

    # 'full' = what construction C actually builds: the payload copy is a COMPLETE graph and every
    # pair carries a typed frame vertex, so adjacency lives ONLY in the types.  Keeping the payload's
    # own edges instead (as an earlier version of this file did) hands 2-WL the adjacency twice --
    # atomically at round 0 AND through the frame -- which is not the object and is not comparable
    # with the Shrikhande/rook rows in probe_cao_triangle_frame.py.
    # 'sub' = subdivision: edges only, and the edge is replaced, not duplicated.
    if mode == 'full':
        for (a, b) in combinations(V, 2):
            add(('v', a), ('v', b))
    pairs = combinations(V, 2) if mode == 'full' else [tuple(sorted(e)) for e in E]
    for (a, b) in pairs:
        conn = frozenset({a, b}) in E
        f = ('e', a, b)
        verts.append(f)
        typ[f] = 1 if conn else 2
        add(f, ('v', a))
        add(f, ('v', b))
    return verts, typ, adj


def union(g1, g2, mode):
    v1, t1, a1 = encode(*g1, mode)
    v2, t2, a2 = encode(*g2, mode)
    verts = [(1,) + v for v in v1] + [(2,) + v for v in v2]
    typ = {(1,) + k: v for k, v in t1.items()}
    typ.update({(2,) + k: v for k, v in t2.items()})
    adj = {((1,) + u, (1,) + w) for (u, w) in a1} | {((2,) + u, (2,) + w) for (u, w) in a2}
    return verts, typ, adj


def wl2(verts, typ, adj, tag=''):
    n = len(verts)
    idx = {v: i for i, v in enumerate(verts)}
    col = [0] * (n * n)
    atoms = {}
    for x in verts:
        a = idx[x]
        for y in verts:
            k = (x == y, (x, y) in adj, typ[x], typ[y])
            col[a * n + idx[y]] = atoms.setdefault(k, len(atoms))
    ncol = len(set(col))
    rnd = 0
    while True:
        rnd += 1
        C = ncol
        colT = [0] * (n * n)
        for a in range(n):
            base = a * n
            for b in range(n):
                colT[b * n + a] = col[base + b]
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
        print(f'    [{tag}] round {rnd}: {ncol} -> {len(table)} colours', flush=True)
        if len(table) == ncol:
            return col, idx
        col, ncol = new, len(table)


def separated(g1, g2, mode, tag):
    verts, typ, adj = union(g1, g2, mode)
    print(f'  [{tag}] {len(verts)} vertices', flush=True)
    col, idx = wl2(verts, typ, adj, tag)
    n = len(verts)
    prof = {1: {}, 2: {}}
    for x in verts:
        for y in verts:
            if x[0] == y[0]:
                c = col[idx[x] * n + idx[y]]
                prof[x[0]][c] = prof[x[0]].get(c, 0) + 1
    return prof[1] != prof[2]


if __name__ == '__main__':
    m = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    mode = sys.argv[2] if len(sys.argv) > 2 else 'sub'
    P, T = cfi_ve(m, ()), cfi_ve(m, (0,))
    print(f'CFI[K{m}]  n={len(P[0])} |E|={len(P[1])}   encoding={mode}', flush=True)
    ctl = separated(P, P, mode, f'K{m}/{mode}/control')
    print(f'  CONTROL (plain vs plain) separated: {ctl}', flush=True)
    sep = separated(P, T, mode, f'K{m}/{mode}/test')
    print(f'==> CFI[K{m}] {mode}-encoded, 2-WL separates plain from twisted: {sep}', flush=True)
