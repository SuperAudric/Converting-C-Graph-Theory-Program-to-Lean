"""probe_cao_lemma_check_np.py — numpy port of probe_cao_lemma_check.py, so that L=6 is reachable.

Same statement, same falsification form (see probe_cao_lemma_check.py's docstring for the lemma).
This file exists only because the pure-Python version is hours at L=6 and a previous background
attempt was killed unfinished (doc outstanding item A.2).

WHY L=6 MATTERS MORE NOW.  The doc says a failure here "would make R3 mandatory".  R3 is dead
(2026-08-14, doc section 6f.5a(beta)): adjoining Phi re-opens (ii) at a price that looks unpayable.
So a failure at L=6 kills R1 AND its fallback, i.e. the whole collapse route -- it is decisive, not
merely informative.

FIDELITY.  Colours are interned GLOBALLY across copies (they are compared across copies, so a
per-copy naming would be meaningless).  Frame-frame pairs are FROZEN, as in the original and as
section 6d.5 requires for level-uniformity.  Phi multisets are compared exactly: rows are lexsorted
and hashed with sha256, so a hash collision -- the only way a violation could be missed -- is not a
practical concern.

Validate before trusting: L=4 must give 20 mu-classes / 0 violations, L=5 must give 90 / 0.
"""

import hashlib
import sys
import time
from itertools import combinations

import numpy as np

L = int(sys.argv[1]) if len(sys.argv) > 1 else 4
REPS = int(sys.argv[2]) if len(sys.argv) > 2 else 3
CHUNK = int(sys.argv[3]) if len(sys.argv) > 3 else 128

PAIRS = list(combinations(range(L), 2))
NS = len(PAIRS)
NC = 1 << NS
NV = L + 2 * NS
ROUNDS = 10
T0 = time.time()


def void_view(a):
    """View a 2-D int64 array as 1-D structured rows, so np.unique/searchsorted work on rows."""
    a = np.ascontiguousarray(a, dtype=np.int64)
    return a.view([('', np.int64)] * a.shape[1]).ravel()


def intern_rows(chunks_fn, nchunk, ncol):
    """Two passes over the chunks: collect the global row table, then map rows to ids.

    Kept two-pass on purpose -- one pass would need every chunk's rows resident at once, which is
    what blew up the pure-Python attempt."""
    parts = []
    for ci in range(nchunk):
        rows = chunks_fn(ci)
        parts.append(np.unique(void_view(rows)))
    table = np.unique(np.concatenate(parts))
    out = []
    for ci in range(nchunk):
        rows = chunks_fn(ci)
        out.append(np.searchsorted(table, void_view(rows)))
    return out, len(table)


def build():
    """2-WL (frozen frame) on M(c) for every copy at once.  Returns (diag, prof)."""
    bits = ((np.arange(NC, dtype=np.int64)[:, None] >> np.arange(NS, dtype=np.int64)[None, :]) & 1)

    # ---- adjacency, per copy -------------------------------------------------
    adj = np.zeros((NC, NV, NV), dtype=bool)
    for a in range(L):
        for b in range(L):
            if a != b:
                adj[:, a, b] = True
    for k in range(NS):
        adj[:, L + 2 * k, L + 2 * k + 1] = True
        adj[:, L + 2 * k + 1, L + 2 * k] = True
    for k, (i, j) in enumerate(PAIRS):
        for t in (0, 1):
            f = L + 2 * k + t
            hit = bits[:, k] == t
            for x in (i, j):
                adj[hit, x, f] = True
                adj[hit, f, x] = True

    # ---- frozen mask and the initial colouring -------------------------------
    isf = np.zeros(NV, dtype=bool)
    isf[L:] = True
    frozen = isf[:, None] & isf[None, :]

    typ = np.full(NV, -1, dtype=np.int64)
    slotof = np.full(NV, -1, dtype=np.int64)
    for k in range(NS):
        for t in (0, 1):
            typ[L + 2 * k + t] = t
            slotof[L + 2 * k + t] = k
    inter = np.zeros((NV, NV), dtype=np.int64)
    for x in range(L, NV):
        for y in range(L, NV):
            inter[x, y] = len(set(PAIRS[slotof[x]]) & set(PAIRS[slotof[y]]))

    eye = np.eye(NV, dtype=bool)
    # frozen key: (t, tt, |k n kk|, x==y);  free key: (x==y, adj, sorts, types)
    fkey = (((typ[:, None] + 1) * 3 + (typ[None, :] + 1)) * 4 + inter) * 2 + eye
    base = (((isf[:, None].astype(np.int64) * 2 + isf[None, :]) * 3
             + (typ[:, None] + 1)) * 3 + (typ[None, :] + 1)) * 2 + eye
    col = np.where(frozen[None, :, :],
                   (1 + fkey)[None, :, :] * 4,
                   (1 + base)[None, :, :] * 4 + 2 + adj.astype(np.int64))
    # renumber the start colouring globally
    vals, col = np.unique(col, return_inverse=True)
    col = col.reshape(NC, NV, NV).astype(np.int64)

    nchunk = (NC + CHUNK - 1) // CHUNK
    prev_ncol = -1
    for rnd in range(ROUNDS):
        C = int(col.max()) + 1
        free_idx = np.argwhere(~frozen)          # pairs that actually update

        def rows_for(ci):
            lo, hi = ci * CHUNK, min((ci + 1) * CHUNK, NC)
            sub = col[lo:hi]                                   # (B, NV, NV)
            xs, ys = free_idx[:, 0], free_idx[:, 1]
            left = sub[:, xs, :]                               # (B, P, NV) = col[x, z]
            right = sub[:, :, ys].transpose(0, 2, 1)           # (B, P, NV) = col[z, y]
            k = np.sort(left * C + right, axis=2)
            own = sub[:, xs, ys][:, :, None]
            return np.concatenate([own, k], axis=2).reshape(-1, NV + 1)

        ids, ncol_new = intern_rows(rows_for, nchunk, NV + 1)
        off = int(col.max()) + 1
        xs, ys = free_idx[:, 0], free_idx[:, 1]
        # write in place -- a full `col.copy()` is 340MB at L=6 and the old values are already
        # consumed by `intern_rows`
        for ci in range(nchunk):
            lo, hi = ci * CHUNK, min((ci + 1) * CHUNK, NC)
            col[lo:hi, xs, ys] = ids[ci].reshape(hi - lo, len(xs)) + off
        del ids
        print(f'  round {rnd + 1}: {ncol_new} free-pair classes ({time.time() - T0:.0f}s)',
              flush=True)
        if ncol_new == prev_ncol:
            print(f'  stable at round {rnd + 1}', flush=True)
            break
        prev_ncol = ncol_new

    diag = col[:, np.arange(L), np.arange(L)]                  # (NC, L)
    prof = col[:, :L, L:]                                      # (NC, L, 2*NS)
    return diag, prof


def main():
    t0 = time.time()
    print(f'L={L}: {NC} copies, M(c) = {NV} vertices, {REPS} reps/class, chunk {CHUNK}', flush=True)
    diag, prof = build()
    print(f'  M built in {time.time() - t0:.1f}s', flush=True)

    dflat = diag.reshape(-1)                                   # index (c*L + i)
    pflat = prof.reshape(-1, 2 * NS)
    classes = {}
    for idx, v in enumerate(dflat.tolist()):
        classes.setdefault(v, []).append(idx)
    print(f'M-diagonal classes: {len(classes)}   (payload vertices: {len(dflat)})', flush=True)

    C = int(pflat.max()) + 1
    bad = checked = 0
    for v, members in sorted(classes.items()):
        reps = members[:REPS]
        if len(reps) < 2:
            continue
        digests = set()
        for idx in reps:
            a = pflat[idx]                                     # (2*NS,)
            key = np.sort(a[None, :] * C + pflat, axis=1)      # (NC*L, 2*NS)
            rows = np.concatenate([dflat[:, None], key], axis=1)
            order = np.lexsort(rows.T[::-1])
            digests.add(hashlib.sha256(rows[order].tobytes()).hexdigest())
        checked += 1
        if len(digests) > 1:
            bad += 1
            if bad <= 3:
                print(f'  VIOLATION: mu-class {v} (size {len(members)}): Phi differs', flush=True)
        if checked % 25 == 0:
            print(f'  ...{checked} classes checked, {bad} violations '
                  f'({time.time() - t0:.0f}s)', flush=True)

    print(f'\nmu-classes with >=2 members checked: {checked}')
    print(f'==> LEMMA HOLDS at L={L} (on the checked representatives): {bad == 0}'
          f'   [{bad} violations]   {time.time() - t0:.1f}s')


if __name__ == '__main__':
    main()
