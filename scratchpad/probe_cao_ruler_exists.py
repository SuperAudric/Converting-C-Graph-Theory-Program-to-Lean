"""probe_cao_ruler_exists.py -- do RULERS exist at L past the ensemble's reach?

The probe-isolation theorem (probe_cao_ruler.py) needs one omega0 = (H,j) with
  (i)  its tag isolates its orbit   -- provable: if M(H)'s stable colouring is DISCRETE then
       col(p(j)) determines the whole within-copy pair-colour matrix in its own labelling, hence
       (H,j) up to isomorphism, so no non-isomorphic marked copy can share the tag;
  (ii) a(H,j) injective on the 2*C(L,2) typed slots.
Both follow from "the stable colouring of M(H) is discrete", and that is a SINGLE-COPY property:
it needs no ensemble, no 2^C(L,2) copies, and no global interning.  So it is checkable at L far
beyond anything the collapse question can be tested at -- which is the point, since the whole
difficulty (doc section 6e.4c) is that the real question is not testable by climbing L.

⚠ DO NOT use the L=4/5 finding "profile injective <==> Aut(G_c)_i = 1" as the criterion.  The <==
direction of that is "individualization + refinement always discretizes", which is FALSE at large L
(that is what CFI graphs are).  Discreteness of the copy's own colouring is the honest hypothesis,
and 1-WL-discrete graphs supply it -- almost all graphs are 1-WL-discrete (Babai-Erdos-Selkow).

Usage: python3 probe_cao_ruler_exists.py [Lmax] [samples]
"""

import random
import sys
import time
from itertools import combinations

import numpy as np

LMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 9
SAMP = int(sys.argv[2]) if len(sys.argv) > 2 else 200


def wl1_discrete_one(L, edges):
    """bare 1-WL on the payload graph G alone."""
    adj = [[0] * L for _ in range(L)]
    for (i, j) in edges:
        adj[i][j] = adj[j][i] = 1
    col = [0] * L
    for _ in range(L + 1):
        key = [(col[v], tuple(sorted(col[u] for u in range(L) if adj[v][u]))) for v in range(L)]
        tab = {k: n for n, k in enumerate(sorted(set(key)))}
        col = [tab[k] for k in key]
    return len(set(col)) == L


def wl2_M(L, edges):
    """2-WL with a frozen frame on the single-copy encoding M(G).  Returns the stable colouring."""
    PAIRS = list(combinations(range(L), 2))
    NS = len(PAIRS)
    NV = L + 2 * NS
    ein = set(map(tuple, (tuple(sorted(e)) for e in edges)))
    bit = [1 if p in ein else 0 for p in PAIRS]

    adj = np.zeros((NV, NV), dtype=bool)
    for a in range(L):
        for b in range(L):
            if a != b:
                adj[a, b] = True                      # payload clique
    for k in range(NS):
        adj[L + 2 * k, L + 2 * k + 1] = adj[L + 2 * k + 1, L + 2 * k] = True
    for k, (i, j) in enumerate(PAIRS):
        f = L + 2 * k + bit[k]
        for x in (i, j):
            adj[x, f] = adj[f, x] = True

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
    fkey = (((typ[:, None] + 1) * 3 + (typ[None, :] + 1)) * 4 + inter) * 2 + eye
    base = (((isf[:, None].astype(np.int64) * 2 + isf[None, :]) * 3
             + (typ[:, None] + 1)) * 3 + (typ[None, :] + 1)) * 2 + eye
    col = np.where(frozen, (1 + fkey) * 4, (1 + base) * 4 + 2 + adj.astype(np.int64))
    _, col = np.unique(col, return_inverse=True)
    col = col.reshape(NV, NV).astype(np.int64)

    prev = -1
    for _ in range(NV):
        C = int(col.max()) + 1
        k = np.sort(col[:, None, :] * C + col.T[None, :, :], axis=2)
        rows = np.concatenate([col[:, :, None], k], axis=2).reshape(NV * NV, NV + 1)
        v = np.ascontiguousarray(rows).view([('', np.int64)] * (NV + 1)).ravel()
        tab = np.unique(v)
        new = np.searchsorted(tab, v).reshape(NV, NV)
        new = np.where(frozen, col, new + int(col.max()) + 1)      # frame-frame stays frozen
        _, new = np.unique(new, return_inverse=True)
        new = new.reshape(NV, NV)
        if len(tab) == prev:
            break
        prev = len(tab)
        col = new
    return col, L, NS


def check(L, edges):
    """The two hypotheses, measured where they actually live.

    ⚠ NOT "the M(H) colouring is discrete": frame-frame pairs are FROZEN by design (section 6d.5),
    so the frame diagonal carries 2 colours for ever and global discreteness is unreachable by
    construction.  What the argument uses is only within-PAYLOAD discreteness.
      (a) payload diagonal discrete            -- L distinct colours col(p(u),p(u))
      (b) payload rows discrete                -- for each j, col(p(j),p(u)) distinct over u
                                                  (this is the alpha-labelling (P1) runs in)
      (c) profile injective                    -- (P2)
    """
    col, L, NS = wl2_M(L, edges)
    diag = np.diag(col)[:L]
    pay_diag = len(set(diag.tolist())) == L
    pp = col[:L, :L]
    rows_disc = all(len(set(pp[j].tolist())) == L for j in range(L))
    prof = col[:L, L:]
    srt = np.sort(prof, axis=1)
    inj = (srt[:, 1:] != srt[:, :-1]).all(axis=1)
    return (pay_diag and rows_disc), int(inj.sum()), L


def rand_graph(L, rng):
    return [e for e in combinations(range(L), 2) if rng.random() < 0.5]


def main():
    t0 = time.time()
    print('L   1-WL-discrete graphs found     payload-discrete (P1)   marked profiles injective')
    print('-' * 92)
    rng = random.Random(20260815)
    for L in range(4, LMAX + 1):
        found = disc_ok = inj_ok = tried = 0
        alldisc = True
        allinj = True
        if L <= 6:                                     # exhaustive
            PAIRS = list(combinations(range(L), 2))
            for mask in range(1 << len(PAIRS)):
                edges = [p for k, p in enumerate(PAIRS) if (mask >> k) & 1]
                tried += 1
                if not wl1_discrete_one(L, edges):
                    continue
                found += 1
                if found > 40:
                    continue
                d, ninj, _ = check(L, edges)
                disc_ok += d
                inj_ok += (ninj == L)
                alldisc &= d
                allinj &= (ninj == L)
            scope = f'{found} of all {tried}'
        else:                                          # random sample
            for _ in range(SAMP):
                edges = rand_graph(L, rng)
                tried += 1
                if not wl1_discrete_one(L, edges):
                    continue
                found += 1
                if found > 20:
                    continue
                d, ninj, _ = check(L, edges)
                disc_ok += d
                inj_ok += (ninj == L)
                alldisc &= d
                allinj &= (ninj == L)
            scope = f'{found} of {tried} random'
        tested = min(found, 40 if L <= 6 else 20)
        print(f'{L}   {scope:<28} {disc_ok}/{tested} payload-discrete{"":<12} '
              f'{inj_ok}/{tested} all-marked-injective'
              f'{"" if (alldisc and allinj) or found == 0 else "   <-- FAILURE"}')
    print(f'\n({time.time() - t0:.1f}s)   a RULER exists at L as soon as one 1-WL-discrete graph does')


if __name__ == '__main__':
    main()
