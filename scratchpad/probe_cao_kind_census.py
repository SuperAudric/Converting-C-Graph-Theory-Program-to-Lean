"""probe_cao_kind_census.py -- cells vs orbits for EVERY vertex kind of the real ensemble.

WHY.  Every ensemble measurement on record counts PAYLOAD cells only (section 6 at 1-WL: 292 vs 544;
section 6b at 2-WL: "20 cells = 20 orbits, 0 mixed").  But a CAO counterexample only needs ONE mixed
cell ANYWHERE, and the ensemble has three other kinds:

  * frame  f(k,t)   -- Aut_{m(0)} = S_L is transitive on slots, so 2 orbits (one per type).
  * central m(g)    -- orbit = the ISO CLASS of the graph g.  11 classes at L=4, 156 at L=6.
  * (payload p(c,i) -- orbit = iso class of the marked graph (G_c, i).  20 at L=4, 544 at L=6.)

The central channel looks much weaker than the payload one: m(g) touches only the frame, there is no
clique, so the section 6e.4a common-neighbour mechanism does not run inside a "copy" -- and
central-central pairs see only #{k : g_k = h_k}, a Hamming-scheme quantity whose distribution over
all h is the SAME for every g.  If the centrals' cells are coarser than their orbits, Construction C
has a mixed cell after all, in a layer nobody has counted.  This is the project's standing
"root-only is not a pass" steer, applied to kinds instead of nodes.

Builds the same object as probe_cao_ensemble_frame.py (L=4, N=332, m(0) individualized).
"""

import sys
import time
from itertools import combinations, permutations

import numpy as np

import probe_cao_ensemble_frame as base


def graph_iso_classes(L, NC, PAIRS):
    """Canonical id of the GRAPH g (unmarked), for every g in {0,1}^S -- the central orbits."""
    slot_of = {}
    for k, (i, j) in enumerate(PAIRS):
        slot_of[(i, j)] = slot_of[(j, i)] = k
    NSl = len(PAIRS)
    bits = ((np.arange(NC, dtype=np.int64)[:, None] >> np.arange(NSl, dtype=np.int64)[None, :]) & 1)
    pw = (1 << np.arange(NSl, dtype=np.int64))
    best = None
    for p in permutations(range(L)):
        perm = np.array([slot_of[(p[i], p[j])] for (i, j) in PAIRS], dtype=np.int64)
        nb = np.empty_like(bits)
        nb[:, perm] = bits
        code = nb @ pw
        best = code if best is None else np.minimum(best, code)
    _, ids = np.unique(best, return_inverse=True)
    return ids


def marked_iso_classes(L, NC, PAIRS):
    slot_of = {}
    for k, (i, j) in enumerate(PAIRS):
        slot_of[(i, j)] = slot_of[(j, i)] = k
    NSl = len(PAIRS)
    bits = ((np.arange(NC, dtype=np.int64)[:, None] >> np.arange(NSl, dtype=np.int64)[None, :]) & 1)
    pw = (1 << np.arange(NSl, dtype=np.int64))
    best = None
    for p in permutations(range(L)):
        perm = np.array([slot_of[(p[i], p[j])] for (i, j) in PAIRS], dtype=np.int64)
        nb = np.empty_like(bits)
        nb[:, perm] = bits
        code = nb @ pw
        cand = code[:, None] * L + np.array(p, dtype=np.int64)[None, :]
        best = cand if best is None else np.minimum(best, cand)
    _, ids = np.unique(best.reshape(-1), return_inverse=True)
    return ids                                    # index (c*L + i)


def report(name, cells, orbits):
    nc = len(set(cells.tolist()))
    no = len(set(orbits.tolist()))
    mixed = 0
    by = {}
    for cell, orb in zip(cells.tolist(), orbits.tolist()):
        by.setdefault(cell, set()).add(orb)
    mixed = sum(1 for v in by.values() if len(v) > 1)
    verdict = 'MIXED CELLS' if mixed else 'cells = orbits'
    print(f'  {name:<10} cells {nc:>6}   orbits {no:>6}   mixed cells {mixed:>5}   <== {verdict}')
    return mixed


def main():
    t0 = time.time()
    L, NC, NS, PAIRS = base.L, base.NC, base.NS, base.PAIRS
    print(f'L={L}: ensemble N={base.N} ({NC} copies, {2 * NS} frame, {NC} centrals), '
          f'm(0) individualized', flush=True)
    col = base.wl2(base.build_adj())
    print(f'  2-WL done in {time.time() - t0:.1f}s\n', flush=True)

    diag = col[np.arange(base.N), np.arange(base.N)]

    pay = np.arange(L * NC)
    frame = np.arange(base.F0, base.M0)
    cent = np.arange(base.M0, base.N)

    # --- orbits under Aut_{m(0)} = S_L ---------------------------------------
    orb_pay = marked_iso_classes(L, NC, PAIRS)
    orb_cent = graph_iso_classes(L, NC, PAIRS)
    orb_frame = np.array([(f - base.F0) % 2 for f in frame])       # slot-transitive => type only

    bad = 0
    bad += report('payload', diag[pay], orb_pay)
    bad += report('frame', diag[frame], orb_frame)
    bad += report('central', diag[cent], orb_cent)

    print(f'\n==> ANY mixed cell in the ensemble at 2-WL: {bad > 0}')
    if not bad:
        print('    (a CAO counterexample needs one; every kind is exactly the orbit partition)')

    # ---------------------------------------------------------------- the RULER, in the REAL object
    # section 6e.4d's (P1)/(P2) and the decode, measured on the ensemble itself rather than on the
    # single-copy M(H).  This is what the doc otherwise only argues for the ensemble.
    aE = col[np.ix_(pay, frame)]                       # ensemble slot profiles
    srt = np.sort(aE, axis=1)
    inj = (srt[:, 1:] != srt[:, :-1]).all(axis=1)
    ycls = {}
    for v, t in enumerate(diag[pay].tolist()):
        ycls.setdefault(t, []).append(v)
    isolated = np.zeros(len(pay), dtype=bool)
    for t, mem in ycls.items():
        if len({orb_pay[m] for m in mem}) == 1:
            isolated[mem] = True
    rulers = np.flatnonzero(isolated & inj)
    print(f'\n  ENSEMBLE-side (P1) tag isolates : {int(isolated.sum())} / {len(pay)}')
    print(f'  ENSEMBLE-side (P2) inj profile  : {int(inj.sum())} / {len(pay)}')
    print(f'  ==> rulers in the real ensemble : {len(rulers)} / {len(pay)}')
    if len(rulers) == 0:
        return

    # S_L action on typed slots, to state the target orbit
    perms = []
    for p in permutations(range(L)):
        m = np.empty(2 * NS, dtype=np.int64)
        for k, (a, b) in enumerate(PAIRS):
            kk = (lambda x, y: [n for n, q in enumerate(PAIRS) if q == tuple(sorted((x, y)))][0])(p[a], p[b])
            for t in (0, 1):
                m[2 * k + t] = 2 * kk + t
        perms.append(m)
    perms = np.stack(perms)

    w0 = int(rulers[0])
    b0 = aE[w0]
    block = [v for v in range(len(pay)) if diag[pay][v] == diag[pay][w0]]
    reps, seen = [], set()
    for v, o in enumerate(orb_pay.tolist()):
        if o not in seen:
            seen.add(o)
            reps.append(v)
    inv0 = {int(val): x for x, val in enumerate(b0.tolist())}
    bad2 = 0
    for v in reps:
        a = aE[v]
        rec = set()
        for w in block:
            pos = {int(val): x for x, val in enumerate(aE[w].tolist())}
            if len(pos) != 2 * NS:
                bad2 += 1
                break
            dec = [0] * (2 * NS)
            for m in b0.tolist():
                dec[inv0[int(m)]] = int(a[pos[int(m)]])
            rec.add(tuple(dec))
        if rec != {tuple(r) for r in aE[v][perms].tolist()}:
            bad2 += 1
    print(f'  DECODE in the real ensemble, ruler {divmod(w0, L)}, block {len(block)}: '
          f'{len(reps) - bad2}/{len(reps)} orbit reps recovered exactly'
          f'   ==> RULER LEMMA VERIFIED ON THE ENSEMBLE: {bad2 == 0}   ({time.time() - t0:.1f}s)')


if __name__ == '__main__':
    main()
