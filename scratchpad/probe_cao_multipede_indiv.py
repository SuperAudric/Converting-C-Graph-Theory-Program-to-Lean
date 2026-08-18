"""probe_cao_multipede_indiv.py -- how cheap does the reader's test get on a multipede?

A rigid multipede has Aut = 1, so EVERY non-singleton 2-WL cell is mixed AND individualization
breaks no symmetry whatever -- it is free and non-circular.  So we may individualize until the cell
structure is as small as possible while still carrying a mixed cell, and the reader's construction
then costs prod |cell|! on the RESIDUAL cells.

This measures that collapse curve: individualize one vertex at a time (always from the largest
non-singleton cell), refine with 2-WL, and record prod |cell|! at each step.
"""

import itertools
import math
import random

import numpy as np

from probe_cao_multipede2 import gf2_rank, multipede_adj
from probe_cao_multipede3 import partial_steiner


def wl2_diag_col(n, A, init, rounds=40):
    """2-WL with an initial VERTEX colouring `init` (individualization)."""
    base = (np.eye(n, dtype=np.int64) * 2 + A.astype(np.int64))
    col = base * (2 * n * n) + init[:, None] * (2 * n) + init[None, :]
    _, col = np.unique(col, return_inverse=True)
    col = col.reshape(n, n).astype(np.int64)
    prev = len(np.unique(col))
    rng = np.random.default_rng(11)
    for _ in range(rounds):
        C = int(col.max()) + 1
        Aa = rng.integers(1, 2 ** 62, size=C, dtype=np.uint64)
        Bb = rng.integers(1, 2 ** 62, size=C, dtype=np.uint64)
        acc = np.zeros((n, n), dtype=np.uint64)
        step = max(1, 8_000_000 // (n * n) or 1)
        for lo in range(0, n, step):
            hi = min(lo + step, n)
            acc[lo:hi] = (Aa[col[lo:hi, :, None]] * Bb[col[None, :, :]]).sum(axis=1)
        key = np.stack([col.astype(np.uint64), acc], axis=-1).reshape(n * n, 2)
        _, inv = np.unique(key, axis=0, return_inverse=True)
        col = inv.reshape(n, n).astype(np.int64)
        m = len(np.unique(col))
        if m == prev:
            break
        prev = m
    return np.diag(col)


def profile(diag):
    d = {}
    for v, c in enumerate(diag):
        d.setdefault(c, []).append(v)
    return sorted(d.values(), key=lambda g: (-len(g), g[0]))


if __name__ == '__main__':
    rng = random.Random(20260818)
    # rebuild the cheapest carrier found: deg=3, m=12, c=12
    inst = None
    for _ in range(4000):
        cons = partial_steiner(12, 12, 3, rng)
        if cons is None:
            continue
        rows = [sum(1 << v for v in N) for N in cons]
        if gf2_rank(rows, 12) != 12:
            continue
        n, A = multipede_adj(12, cons)
        diag = wl2_diag_col(n, A, np.zeros(n, dtype=np.int64))
        cells = profile(diag)
        if len(cells[0]) > 1:
            inst = (n, A, cons)
            break
    n, A, cons = inst
    print(f'multipede m=12 c=12: n={n}')
    init = np.zeros(n, dtype=np.int64)
    step = 0
    while True:
        diag = wl2_diag_col(n, A, init)
        cells = profile(diag)
        ns = [c for c in cells if len(c) > 1]
        cost = 1
        for c in cells:
            cost *= math.factorial(len(c))
        print(f'  individualized {step:3d}: non-singleton cells={[len(c) for c in ns]}'
              f'  prod|cell|! = {cost}', flush=True)
        if not ns:
            print('  -> discrete; the previous line is the cheapest test still carrying a mixed cell')
            break
        init = init.copy()
        init[ns[0][0]] = step + 1          # individualize one vertex of the largest mixed cell
        step += 1
