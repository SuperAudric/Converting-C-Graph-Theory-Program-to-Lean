"""probe_cao_ensemble_frame.py — is the ENSEMBLE's frame channel coarser than M's?

Both the "guess from the ensemble's own frame channel" idea (2026-08-14) and the reader's
"gauge transparency" idea (2026-08-15) rest on the same hope: that in the ensemble, where the frame
is SHARED by every copy and highly symmetric, the pair colour col_E(p(c,i), f(k,t)) is much coarser
than M(c)'s a(c,i)_(k,t) -- coarse enough that the cross-copy Align channel cannot read the whole
slot-profile vector off (which is what refuted the lemma, doc section 6e.4a).

THE WORRY THIS TESTS.  The mechanism that made a(c,i) complete in M(c) is:  the payload of a copy is
a CLIQUE, so (p(i), f(k,t)) has common payload neighbours {j in k} exactly when c_k = t.  That
argument uses only vertices INSIDE one copy -- so it appears to work verbatim in the ensemble.  If it
does, the ensemble's frame channel is NOT coarser, and both ideas fail at the same point.

Measured at L=4 (N = 332, the object section 6b used).  Questions:
  Q1  does the ensemble profile aE(c,i) determine the copy c?
  Q2  how many aE(c,i) are injective on typed slots?  (that is what lets Align read the vector off)
  Q3  S_L-orbits of aE  vs  ensemble payload cells  vs  M's a-orbits.
"""

import sys
import time
from itertools import combinations, permutations

import numpy as np

L = int(sys.argv[1]) if len(sys.argv) > 1 else 4
PAIRS = list(combinations(range(L), 2))
NS = len(PAIRS)
NC = 1 << NS
SLOT = {}
for k, (i, j) in enumerate(PAIRS):
    SLOT[(i, j)] = SLOT[(j, i)] = k

P0, F0 = 0, L * NC
M0 = F0 + 2 * NS
N = M0 + NC
ROUNDS = 12
CH = 32


def build_adj():
    adj = np.zeros((N, N), dtype=bool)

    def add(u, w):
        adj[u, w] = adj[w, u] = True

    for c in range(NC):
        b = c * L
        for a in range(L):
            for d in range(a + 1, L):
                add(b + a, b + d)
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


def wl2(adj):
    """2-WL on the ensemble with m(base) individualized."""
    vkind = np.zeros(N, dtype=np.int64)
    vkind[F0:M0] = 1 + (np.arange(F0, M0) - F0) % 2      # frame, by type
    vkind[M0:] = 3
    vkind[M0] = 4                                        # <-- m(base) individualized
    eye = np.eye(N, dtype=bool)
    col = ((vkind[:, None] * 5 + vkind[None, :]) * 2 + eye) * 2 + adj
    _, col = np.unique(col, return_inverse=True)
    col = col.reshape(N, N).astype(np.int64)

    for rnd in range(ROUNDS):
        C = int(col.max()) + 1
        parts = []
        for lo in range(0, N, CH):
            hi = min(lo + CH, N)
            k = np.sort(col[lo:hi, None, :] * C + col.T[None, :, :], axis=2)
            own = col[lo:hi][:, :, None]
            parts.append(np.concatenate([own, k], axis=2).reshape(-1, N + 1))
        rows = np.concatenate(parts)
        v = np.ascontiguousarray(rows).view([('', np.int64)] * (N + 1)).ravel()
        tab = np.unique(v)
        new = np.searchsorted(tab, v).reshape(N, N)
        if len(tab) == len(np.unique(col)):
            print(f'  stable after {rnd} rounds, {len(tab)} pair classes', flush=True)
            col = new
            break
        col = new
        print(f'  round {rnd + 1}: {len(tab)} pair classes', flush=True)
    return col


def main():
    t0 = time.time()
    print(f'L={L}: ensemble N={N} ({NC} copies, {2 * NS} frame, {NC} centrals)', flush=True)
    col = wl2(build_adj())
    print(f'  2-WL done in {time.time() - t0:.1f}s', flush=True)

    pay = np.arange(L * NC)
    frame = np.arange(F0, M0)
    aE = col[np.ix_(pay, frame)]                      # (L*NC, 2*NS)  ensemble slot profiles
    cells = col[pay, pay]
    print(f'  ensemble payload cells: {len(set(cells.tolist()))}', flush=True)

    # Q1 -- does aE(c,i) determine the copy?
    seen, clash = {}, 0
    for v in range(L * NC):
        c, i = divmod(v, L)
        key = (i, tuple(aE[v].tolist()))
        if key in seen and seen[key] != c:
            clash += 1
        seen[key] = c
    print(f'\nQ1  aE(c,i) determines c: {clash == 0}   [{clash} collisions]')

    # Q2 -- injectivity on typed slots
    srt = np.sort(aE, axis=1)
    inj = int((srt[:, 1:] != srt[:, :-1]).all(axis=1).sum())
    print(f'Q2  aE injective on all {2 * NS} typed slots: {inj} / {len(aE)}')

    # Q3 -- S_L-orbits of the ensemble profiles
    idx = {}
    for k, (i, j) in enumerate(PAIRS):
        idx[(i, j)] = idx[(j, i)] = k
    perms = []
    for p in permutations(range(L)):
        m = np.empty(2 * NS, dtype=np.int64)
        for k, (a, b) in enumerate(PAIRS):
            kk = idx[(p[a], p[b])]
            for t in (0, 1):
                m[2 * k + t] = 2 * kk + t
        perms.append(m)
    perms = np.stack(perms)
    orbs = {min(tuple(w) for w in aE[r][perms].tolist()) for r in range(len(aE))}
    print(f'Q3  S_L-orbits of aE: {len(orbs)}      ensemble payload cells: '
          f'{len(set(cells.tolist()))}')
    print(f'\n  ==> the ensemble frame channel is '
          f'{"NOT coarser -- both ideas fail here" if clash == 0 and inj else "COARSER -- worth pursuing"}'
          f'   ({time.time() - t0:.1f}s)')


if __name__ == '__main__':
    main()
