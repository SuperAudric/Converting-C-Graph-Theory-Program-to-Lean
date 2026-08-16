"""probe_cao_ruler_bolt_on.py -- the reader's test: is a ruler a bolt-on device?

THE READER'S QUESTION (2026-08-16): "Does the specific definition of a ruler apply to non-ensemble
graphs?  If so can you take a 2-WL blind graph with mixed cells, attach a ruler to every vertex, and
watch as it either resolves the graph or doesn't?  Or does it require that you first compute the
orbits in order to choose how to attach the ruler."

THE BLIND OBJECT.  X = rook(4,4) DISJOINT-UNION Shrikhande.  Both are SRG(16,6,2,2), both
vertex-transitive, non-isomorphic, and 2-WL-equivalent.  So X has 32 vertices, TWO Aut-orbits (one
per component -- no automorphism crosses between non-isomorphic components) and 2-WL puts them in
ONE cell.  A genuine 2-WL mixed cell, 32 vertices, no CFI needed.

THE TEST.  Attach a ruler (the smallest asymmetric graph, or a bigger rigid one) and see whether the
mixed cell resolves:
  (a) nothing attached                       -- the control
  (b) a private ruler copy on every vertex   -- "attach a ruler to every vertex"
  (c) one shared ruler joined to every vertex
  (d) a private ruler per vertex, all rulers also joined to each other through a shared hub
  (e) CONTROL THAT MUST WORK: attach the ruler to ONE vertex only.  This uses orbit knowledge (it
      individualizes), so if even this fails the object is stranger than advertised.

PREDICTION FROM THE ARGUMENT.  (a)-(d) do NOT resolve.  The ruler in the section 6e.4d sense is not a
gadget you bolt on: it is a member of a family that SHARES A FRAME with the others, and its power is
that cross-member pair colours record the ALIGNMENT of two members' readings of that frame.  A
bolted-on gadget gives the blind graph's vertices no reading of anything, so conditions (i) and (ii)
are not merely false -- (ii) is not even well-defined.  If (a)-(d) resolved, the argument would be a
general-purpose orbit oracle and would prove far too much.
"""

import time
from itertools import combinations

import numpy as np


def rook44():
    V = [(i, j) for i in range(4) for j in range(4)]
    idx = {v: n for n, v in enumerate(V)}
    E = []
    for a in V:
        for b in V:
            if a < b and (a[0] == b[0] or a[1] == b[1]):
                E.append((idx[a], idx[b]))
    return 16, E


def shrikhande():
    V = [(i, j) for i in range(4) for j in range(4)]
    idx = {v: n for n, v in enumerate(V)}
    S = {(1, 0), (3, 0), (0, 1), (0, 3), (1, 1), (3, 3)}
    E = []
    for a in V:
        for b in V:
            if a < b and ((b[0] - a[0]) % 4, (b[1] - a[1]) % 4) in S:
                E.append((idx[a], idx[b]))
    return 16, E


RULER6 = (6, [(0, 1), (1, 2), (0, 2), (1, 3), (2, 4), (4, 5)])       # smallest asymmetric graph


def wl2_cells(n, adj, kind, rounds=64, seed=5):
    rng = np.random.default_rng(seed)
    eye = np.eye(n, dtype=bool)
    k = np.asarray(kind, dtype=np.int64)
    col = (((k[:, None] * (k.max() + 1) + k[None, :]) * 2 + eye) * 2 + adj).astype(np.int64)
    _, col = np.unique(col, return_inverse=True)
    col = col.reshape(n, n).astype(np.int64)
    prev = -1
    for _ in range(rounds):
        C = int(col.max()) + 1
        A = rng.integers(1, 2 ** 63, size=C, dtype=np.uint64)
        B = rng.integers(1, 2 ** 63, size=C, dtype=np.uint64)
        acc = np.zeros((n, n), dtype=np.uint64)
        b = max(1, 4_000_000 // (n * n) or 1)
        for lo in range(0, n, b):
            hi = min(lo + b, n)
            acc[lo:hi] = (A[col[lo:hi, :, None]] * B[col[None, :, :]]).sum(axis=1)
        keyed = np.stack([col.astype(np.uint64).ravel(), acc.ravel()], axis=1)
        v = np.ascontiguousarray(keyed).view([('', np.uint64)] * 2).ravel()
        tab = np.unique(v)
        col = np.searchsorted(tab, v).reshape(n, n).astype(np.int64)
        if len(tab) == prev:
            break
        prev = len(tab)
    return col[np.arange(n), np.arange(n)]


def build(mode):
    """X = rook u Shrikhande (32 vertices, orbits {rook}, {Shrikhande}), plus ruler attachments."""
    nr, Er = rook44()
    ns, Es = shrikhande()
    edges = list(Er) + [(a + nr, b + nr) for (a, b) in Es]
    n = nr + ns
    orb = [0] * nr + [1] * ns
    extra = []

    rn, re = RULER6
    if mode == 'none':
        pass
    elif mode == 'per-vertex':
        for v in range(n):
            off = n + len(extra) * 0
            base = n + v * rn
            for (a, b) in re:
                edges.append((base + a, base + b))
            edges.append((v, base + 0))                     # attach at ruler vertex 0
        n += 32 * rn
    elif mode == 'shared':
        base = n
        for (a, b) in re:
            edges.append((base + a, base + b))
        for v in range(32):
            edges.append((v, base + 0))
        n += rn
    elif mode == 'per-vertex+hub':
        hub = n
        n += 1
        for v in range(32):
            base = n + v * rn
            for (a, b) in re:
                edges.append((base + a, base + b))
            edges.append((v, base + 0))
            edges.append((hub, base + 1))
        n += 32 * rn
    elif mode == 'one-vertex-only':                          # uses orbit knowledge -- must work
        base = n
        for (a, b) in re:
            edges.append((base + a, base + b))
        edges.append((0, base + 0))
        n += rn
    else:
        raise ValueError(mode)

    adj = np.zeros((n, n), dtype=bool)
    for a, b in edges:
        adj[a, b] = adj[b, a] = True
    kind = np.zeros(n, dtype=np.int64)
    kind[32:] = 1                                            # X-vertices vs attached machinery
    return n, adj, kind, orb


def main():
    print('X = rook(4,4)  u  Shrikhande   -- 32 vertices, 2 Aut-orbits, 2-WL-equivalent\n')
    print(f'  {"attachment":<22} {"|V|":>5} {"cells on X":>11} {"orbits":>7}  verdict')
    for mode in ('none', 'per-vertex', 'shared', 'per-vertex+hub', 'one-vertex-only'):
        t0 = time.time()
        n, adj, kind, orb = build(mode)
        cells = wl2_cells(n, adj, kind)
        xc = [int(cells[i]) for i in range(32)]
        by = {}
        for c, o in zip(xc, orb):
            by.setdefault(c, set()).add(o)
        ncell = len(set(xc))
        mixed = sum(1 for s in by.values() if len(s) > 1)
        verdict = ('MIXED CELL SURVIVES -- not resolved' if mixed
                   else 'resolved (rook separated from Shrikhande)')
        print(f'  {mode:<22} {n:>5} {ncell:>11} {2:>7}  {verdict}   ({time.time()-t0:.0f}s)')

    print('\n  "one-vertex-only" is the control that uses orbit knowledge: it individualizes, which')
    print('  is why it can work.  The others attach the ruler uniformly, i.e. WITHOUT knowing the')
    print('  orbits, and that is the case the reader asked about.')


if __name__ == '__main__':
    main()
