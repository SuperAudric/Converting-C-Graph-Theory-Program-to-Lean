"""probe_cao_multipede2.py -- search for a multipede that is RIGID and 2-WL-NON-DISCRETE.

That combination is the cheap mixed-cell carrier the reader is after:
  Aut = 1  ==>  every non-singleton 2-WL cell is MIXED,
  Aut = 1  ==>  individualization is free, so the cells can be shrunk to a single size-2 cell
                and the ruler test then costs prod |cell|! = 2.
"""

import itertools
import math
import random
import sys

import networkx as nx
import numpy as np


def wl2_diag(n, adj, rounds=40):
    eye = np.eye(n, dtype=bool)
    col = (eye.astype(np.int64) * 2 + adj.astype(np.int64))
    _, col = np.unique(col, return_inverse=True)
    col = col.reshape(n, n).astype(np.int64)
    prev = len(np.unique(col))
    rng = np.random.default_rng(7)
    for _ in range(rounds):
        C = int(col.max()) + 1
        A = rng.integers(1, 2 ** 62, size=C, dtype=np.uint64)
        B = rng.integers(1, 2 ** 62, size=C, dtype=np.uint64)
        acc = np.zeros((n, n), dtype=np.uint64)
        step = max(1, 8_000_000 // (n * n) or 1)
        for lo in range(0, n, step):
            hi = min(lo + step, n)
            acc[lo:hi] = (A[col[lo:hi, :, None]] * B[col[None, :, :]]).sum(axis=1)
        key = np.stack([col.astype(np.uint64), acc], axis=-1).reshape(n * n, 2)
        _, inv = np.unique(key, axis=0, return_inverse=True)
        col = inv.reshape(n, n).astype(np.int64)
        m = len(np.unique(col))
        if m == prev:
            break
        prev = m
    return np.diag(col)


def gf2_rank(rows, m):
    rows = list(rows); r = 0
    for c in range(m):
        p = next((i for i in range(r, len(rows)) if (rows[i] >> c) & 1), None)
        if p is None:
            continue
        rows[r], rows[p] = rows[p], rows[r]
        for i in range(len(rows)):
            if i != r and ((rows[i] >> c) & 1):
                rows[i] ^= rows[r]
        r += 1
    return r


def multipede_adj(m, cons):
    verts = 2 * m
    gad = []
    for N in cons:
        for bits in itertools.product([0, 1], repeat=len(N)):
            if sum(bits) % 2 == 0:
                gad.append((N, bits))
    n = verts + len(gad)
    A = np.zeros((n, n), dtype=bool)
    for g, (N, bits) in enumerate(gad):
        u = verts + g
        for v, b in zip(N, bits):
            A[u, 2 * v + b] = A[2 * v + b, u] = True
    return n, A


def naut(n, A, cap=3):
    G = nx.from_numpy_array(A.astype(int))
    gm = nx.algorithms.isomorphism.GraphMatcher(G, G)
    c = 0
    for _ in gm.isomorphisms_iter():
        c += 1
        if c > cap:
            break
    return c


def sizes_of(diag):
    d = {}
    for v, c in enumerate(diag):
        d[c] = d.get(c, 0) + 1
    return sorted(d.values(), reverse=True)


if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 99)
    print('=== searching for RIGID + 2-WL-NON-DISCRETE multipedes ===', flush=True)
    hits = []
    for deg in (3, 4):
        for m in (8, 10, 12, 14, 16, 18, 20):
            for c in (m, m + 1, m + 2, int(1.5 * m), 2 * m):
                found = 0
                for _ in range(60):
                    cons = set()
                    while len(cons) < c:
                        cons.add(tuple(sorted(rng.sample(range(m), deg))))
                    cons = sorted(cons)
                    rows = [sum(1 << v for v in N) for N in cons]
                    if gf2_rank(rows, m) != m:
                        continue
                    n, A = multipede_adj(m, cons)
                    if n > 400:
                        continue
                    diag = wl2_diag(n, A)
                    sz = sizes_of(diag)
                    if sz[0] == 1:
                        continue                      # 2-WL discretised it
                    a = naut(n, A)
                    cost = 1
                    for s in sz:
                        cost *= math.factorial(s)
                    print(f'  deg={deg} m={m:2d} c={c:2d} n={n:3d} |Aut|'
                          f'{">3" if a > 3 else f"={a}"} cells={sz[:10]} cost={cost}', flush=True)
                    if a == 1:
                        hits.append((cost, deg, m, c, n, sz, cons))
                    found += 1
                    if found >= 2:
                        break
    print(f'\nRIGID + non-discrete found: {len(hits)}')
    for h in sorted(hits)[:5]:
        print('  cost=%d deg=%d m=%d c=%d n=%d cells=%s' % h[:6])
