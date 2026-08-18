"""probe_cao_multipede_small.py -- is m=12 really the smallest RIGID + 2-WL-non-discrete multipede?

THE GAP THIS CLOSES.  probe_cao_multipede3.py is the only earlier probe that enforces the
partial-Steiner condition, and its grid is m in {12,16,20,...}: it never tried m < 12.  The other two
sampled triples at RANDOM, which for c >= m on few points is almost never partial-Steiner.  So
"smallest is m=12" was an artefact of where the grid started.

The counting bound says smaller is possible.  For 3-uniform partial-Steiner systems on m points every
point lies in at most floor((m-1)/2) blocks, so

    c_max = floor( m * floor((m-1)/2) / 3 ),

and full GF(2) column rank (= rigidity) needs c >= m:

    m = 7  -> c_max = 7   (only the Fano plane; GF(2) rank 4, so NOT rigid)
    m = 8  -> c_max = 8   -> c = 8 forced
    m = 9  -> c_max = 12
    m =10  -> c_max = 13
    m =11  -> c_max = 18

Why it matters: the reader's prod|cell|! ruler test attaches to the FEET only (foot cells are
WL-computable), so it costs 2^m copies of a 2m-vertex ruler, i.e. about 2m * 2^m vertices.

    m = 8  ->    4,096 ruler vertices   (2-WL is comfortable)
    m = 9  ->    9,216
    m =10  ->   20,480
    m =12  ->   98,304                  (the 77 GB wall already recorded)

So one or two legs fewer is the difference between an experiment and a wall.

This probe enumerates partial-Steiner triple systems SYSTEMATICALLY (DFS in lex order, not random),
filters by GF(2) rank, builds the multipede, and reports 2-WL cells + |Aut|.
"""

import itertools
import math
import sys

import networkx as nx
import numpy as np


# ---------------------------------------------------------------- GF(2) rank

def gf2_rank(rows, m):
    rows = list(rows)
    r = 0
    for c in range(m):
        p = None
        for i in range(r, len(rows)):
            if (rows[i] >> c) & 1:
                p = i
                break
        if p is None:
            continue
        rows[r], rows[p] = rows[p], rows[r]
        for i in range(len(rows)):
            if i != r and ((rows[i] >> c) & 1):
                rows[i] ^= rows[r]
        r += 1
    return r


# ------------------------------------------------- partial-Steiner enumeration

def enumerate_ps(m, c, deg=3, cap=200000):
    """All partial-Steiner `deg`-uniform systems with exactly `c` blocks, blocks in lex order."""
    blocks = list(itertools.combinations(range(m), deg))
    pairmask = [0] * len(blocks)
    for i, N in enumerate(blocks):
        msk = 0
        for a, b in itertools.combinations(N, 2):
            msk |= 1 << (a * m + b)
        pairmask[i] = msk
    out = []
    seen = [0]

    def rec(start, chosen, used):
        if seen[0] > cap:
            return
        if len(chosen) == c:
            seen[0] += 1
            out.append([blocks[i] for i in chosen])
            return
        # prune: not enough blocks left
        if len(blocks) - start < c - len(chosen):
            return
        for i in range(start, len(blocks)):
            if pairmask[i] & used:
                continue
            chosen.append(i)
            rec(i + 1, chosen, used | pairmask[i])
            chosen.pop()
            if seen[0] > cap:
                return

    rec(0, [], 0)
    return out


# ------------------------------------------------------------- the multipede

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


def wl2_diag(n, adj, rounds=40, seed=7):
    """2-WL to stability; returns the diagonal colouring.  O(n^2) memory, hashed rounds."""
    eye = np.eye(n, dtype=bool)
    col = (eye.astype(np.int64) * 2 + adj.astype(np.int64))
    _, col = np.unique(col, return_inverse=True)
    col = col.reshape(n, n).astype(np.int64)
    prev = len(np.unique(col))
    rng = np.random.default_rng(seed)
    for _ in range(rounds):
        C = int(col.max()) + 1
        A1 = rng.integers(1, 2 ** 62, size=C, dtype=np.uint64)
        B1 = rng.integers(1, 2 ** 62, size=C, dtype=np.uint64)
        acc = np.zeros((n, n), dtype=np.uint64)
        step = max(1, 8_000_000 // (n * n) or 1)
        for lo in range(0, n, step):
            hi = min(lo + step, n)
            acc[lo:hi] = (A1[col[lo:hi, :, None]] * B1[col.T[None, :, :]]).sum(axis=1)
        key = np.stack([col.astype(np.uint64), acc], axis=-1).reshape(n * n, 2)
        _, inv = np.unique(key, axis=0, return_inverse=True)
        col = inv.reshape(n, n).astype(np.int64)
        cur = len(np.unique(col))
        if cur == prev:
            break
        prev = cur
    return [int(col[v, v]) for v in range(n)]


def cell_sizes(diag):
    d = {}
    for c in diag:
        d[c] = d.get(c, 0) + 1
    return sorted(d.values(), reverse=True)


def naut(n, A, cap=3):
    G = nx.from_numpy_array(A.astype(int))
    gm = nx.algorithms.isomorphism.GraphMatcher(G, G)
    k = 0
    for _ in gm.isomorphisms_iter():
        k += 1
        if k > cap:
            break
    return k


# ------------------------------------------------------------------- the run

if __name__ == '__main__':
    ms = [int(x) for x in sys.argv[1:]] or [7, 8, 9, 10]
    print('=== systematic search: RIGID + 2-WL-non-discrete partial-Steiner multipedes ===',
          flush=True)
    best = None
    for m in ms:
        cmax = (m * ((m - 1) // 2)) // 3
        print(f'\n-- m={m}  (partial-Steiner c_max={cmax}, need c>={m})', flush=True)
        if cmax < m:
            print('   IMPOSSIBLE: c_max < m, so no full-rank system exists', flush=True)
            continue
        for c in range(m, min(cmax, m + 3) + 1):
            systems = enumerate_ps(m, c, 3, cap=60000)
            fullrank = []
            for cons in systems:
                rows = [sum(1 << v for v in N) for N in cons]
                if gf2_rank(rows, m) == m:
                    fullrank.append(cons)
            print(f'   c={c}: {len(systems)} partial-Steiner systems, '
                  f'{len(fullrank)} of full GF(2) rank', flush=True)
            shown = 0
            for cons in fullrank:
                n, A = multipede_adj(m, cons)
                if not nx.is_connected(nx.from_numpy_array(A.astype(int))):
                    continue
                diag = wl2_diag(n, A)
                sz = cell_sizes(diag)
                if sz[0] == 1:
                    continue                                  # 2-WL discretised it
                a = naut(n, A)
                feet = diag[:2 * m]
                fd = {}
                for v, cc in enumerate(feet):
                    fd.setdefault(cc, []).append(v)
                foot_sizes = sorted((len(g) for g in fd.values()), reverse=True)
                cost = 1
                for s in foot_sizes:
                    cost *= math.factorial(s)
                print(f'      n={n:3d} |Aut|{">3" if a > 3 else f"={a}"} cells={sz[:10]}'
                      f'  FOOT cells={foot_sizes}  ruler copies={cost}'
                      f'  ruler verts={cost * 2 * m}', flush=True)
                if a == 1 and (best is None or cost * 2 * m < best[0]):
                    best = (cost * 2 * m, m, c, n, foot_sizes, cons)
                shown += 1
                if shown >= 3:
                    break
    print('\n=== cheapest RIGID + non-discrete carrier for the ruler test ===')
    if best is None:
        print('  none found')
    else:
        print(f'  ruler verts={best[0]}  m={best[1]} c={best[2]} n={best[3]} '
              f'foot cells={best[4]}\n  constraints={best[5]}')
