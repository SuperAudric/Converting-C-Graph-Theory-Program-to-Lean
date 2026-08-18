"""probe_cao_ruler_closure.py -- the two-closure comparison, isolated from the mixed cell.

The reader's test attaches a rigid ruler BIJECTIVELY to a base graph G and closes the family under a
group Gamma with Aut(G) <= Gamma.  Two choices:

  * Gamma = prod Sym(cell)   -- WL-computable, so the test is not circular.  |Gamma| = prod |cell|!
  * Gamma = Aut(G)           -- tainted as an algorithm, fine as a mechanism probe.

RulerLemma's hypothesis (i) is "the tag class equals the ORBIT".  Copies pi and pi' are in the same
Aut(G)-orbit iff pi' pi^-1 in Aut(G).  Under over-closure (|Gamma| > |Aut|) there are
|Gamma|/|Aut(G)| orbits of copies, so (i) holds iff 2-WL separates the copies into exactly those.

I predicted it would NOT (over-closure collapsing the tag).  This measures it.  The mixed cell is not
needed for this question, so it runs on tiny bases.
"""

import itertools
import math
import sys

import numpy as np


def wl2(n, adj, rounds=40):
    """exact for small n; hashed multiset round for large n (collisions can only MERGE classes,
    so a reported 'HOLDS' -- classes == orbits -- stays sound; only a spurious FAIL is possible)."""
    eye = np.eye(n, dtype=bool)
    col = (eye.astype(np.int64) * 2 + adj.astype(np.int64))
    _, col = np.unique(col, return_inverse=True)
    col = col.reshape(n, n).astype(np.int64)
    prev = len(np.unique(col))
    exact = (n <= 200)
    rng = np.random.default_rng(12345)
    for _ in range(rounds):
        C = int(col.max()) + 1
        if exact:
            rows = []
            step = max(1, 4_000_000 // (n * n) or 1)
            for lo in range(0, n, step):
                hi = min(lo + step, n)
                k = np.sort(col[lo:hi, None, :] * C + col.T[None, :, :], axis=2)
                own = col[lo:hi][:, :, None]
                rows.append(np.concatenate([own, k], axis=2).reshape(-1, n + 1))
            R = np.ascontiguousarray(np.concatenate(rows))
            v = R.view([('', np.int64)] * (n + 1)).ravel()
            tab = np.unique(v)
            col = np.searchsorted(tab, v).reshape(n, n)
            m = len(tab)
        else:
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
    return col


def aut_perms(n, adj):
    out = []
    for p in itertools.permutations(range(n)):
        q = np.array(p)
        if np.array_equal(adj[np.ix_(q, q)], adj):
            out.append(p)
    return out


def orbits_from(n, perms):
    par = list(range(n))

    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for p in perms:
        for a in range(n):
            ra, rb = find(a), find(p[a])
            if ra != rb:
                par[ra] = rb
    d = {}
    for v in range(n):
        d.setdefault(find(v), []).append(v)
    return sorted(tuple(g) for g in d.values())


# the smallest rigid graph: triangle with pendant paths of length 0, 1, 2
RUL_N = 6
RUL_E = [(0, 1), (1, 2), (0, 2), (1, 3), (2, 4), (4, 5)]


def build(n, base_edges, perms):
    """base on [0,n) + one ruler copy per perm; ruler slot i joins base vertex perm[i]."""
    m = len(perms)
    N = n + m * RUL_N
    A = np.zeros((N, N), dtype=bool)
    for u, v in base_edges:
        A[u, v] = A[v, u] = True
    for c, p in enumerate(perms):
        off = n + c * RUL_N
        for u, v in RUL_E:
            A[off + u, off + v] = A[off + v, off + u] = True
        for i in range(n):
            A[off + i, p[i]] = A[p[i], off + i] = True
    return N, A


def cells_of(labels):
    d = {}
    for v, c in enumerate(labels):
        d.setdefault(c, []).append(v)
    return sorted(tuple(g) for g in d.values())


def run(name, n, base_edges):
    adj = np.zeros((n, n), dtype=bool)
    for u, v in base_edges:
        adj[u, v] = adj[v, u] = True
    aut = aut_perms(n, adj)
    base_orbs = orbits_from(n, aut)
    bcol = wl2(n, adj)
    base_cells = cells_of([bcol[v][v] for v in range(n)])
    print(f'\n### {name}: n={n}  |Aut|={len(aut)}  bare cells={[len(c) for c in base_cells]}'
          f'  orbits={[len(o) for o in base_orbs]}')

    cellgrp = [list(itertools.permutations(c)) for c in base_cells]
    total = math.prod(len(g) for g in cellgrp)
    print(f'    prod |cell|! = {total}   over-closure factor = {total / len(aut):g}')

    for tag, perms in (('Aut-closure ', aut), ('cell-closure', None)):
        if perms is None:
            perms = []
            for combo in itertools.product(*cellgrp):
                p = [0] * n
                for cell, img in zip(base_cells, combo):
                    for a, b in zip(cell, img):
                        p[a] = b
                perms.append(tuple(p))
        m = len(perms)
        N, A = build(n, base_edges, perms)
        if N > 1200:
            print(f'    {tag}: {m} copies, N={N} -- skipped (too big)')
            continue
        col = wl2(N, A)
        diag = [col[v][v] for v in range(N)]
        # base cells in the combined object
        bc = cells_of(diag[:n])
        # copy classes: a copy's colour = the multiset of its ruler vertices' colours
        sig = {}
        for c in range(m):
            off = n + c * RUL_N
            sig.setdefault(tuple(sorted(diag[off:off + RUL_N])), []).append(c)
        # Aut-orbits on copies: pi ~ pi' iff pi' o pi^-1 in Aut
        autset = set(aut)
        par = list(range(m))

        def find(x):
            while par[x] != x:
                par[x] = par[par[x]]
                x = par[x]
            return x
        for a in range(m):
            for b in range(a + 1, m):
                pa, pb = perms[a], perms[b]
                inv = [0] * n
                for i, x in enumerate(pa):
                    inv[x] = i
                if tuple(pb[inv[x]] for x in range(n)) in autset:
                    ra, rb = find(a), find(b)
                    if ra != rb:
                        par[ra] = rb
        norb = len({find(x) for x in range(m)})
        ok = (len(sig) == norb)
        # hypothesis (ii)/(R): does SOME ruler vertex's reading of the ruler set refine every
        # base vertex's reading of it?  b_u(r) = col[u][r] for r a ruler vertex.
        X = list(range(n, N))
        best = None
        for w0 in X:
            fib = {}
            for r in X:
                fib.setdefault(col[w0][r], []).append(r)
            bad = 0
            for x in range(n):
                for grp in fib.values():
                    if len({col[x][r] for r in grp}) > 1:
                        bad += 1
                        break
            if best is None or bad < best[0]:
                best = (bad, w0, len(fib))
            if bad == 0:
                break
        ii = 'HOLDS' if best[0] == 0 else f'FAILS ({best[0]}/{n} readings not refined)'
        print(f'    {tag}: {m} copies, N={N} | base cells in object={[len(c) for c in bc]}'
              f' (orbits={[len(o) for o in base_orbs]})'
              f' | copy colour classes={len(sig)} vs copy Aut-orbits={norb}'
              f'  -> (i) {"HOLDS" if ok else "FAILS"}; (ii) {ii}'
              f' [best ruler has {best[2]} fibres on {len(X)} slots]')


if __name__ == '__main__':
    run('P4  (path)', 4, [(0, 1), (1, 2), (2, 3)])
    run('C4  (cycle)', 4, [(0, 1), (1, 2), (2, 3), (3, 0)])
    run('K4', 4, [(a, b) for a in range(4) for b in range(a + 1, 4)])
    run('paw (triangle+pendant)', 4, [(0, 1), (1, 2), (0, 2), (2, 3)])
    run('C5', 5, [(i, (i + 1) % 5) for i in range(5)])
    run('bull', 5, [(0, 1), (1, 2), (0, 2), (1, 3), (2, 4)])
