"""probe_cao_ruler.py -- CONSTRUCTIVE check of the probe-isolation ("rigid ruler") theorem.

THE THEOREM that repairs section 6e.4c's broken isolation step.  Gamma acts on X; Omega is a
Gamma-set with EQUIVARIANT profiles b: Omega -> C^X (b_{g.w} = b_w o g^-1) and an INVARIANT tag
y: Omega -> Y.  Put Phi(w) = {{ (y(w'), Align(b_w, b_w')) : w' in Omega }}.  If there exists w0 with

    (i)  y^-1(y(w0)) = Gamma.w0          [the tag ISOLATES w0's orbit -- w0 is a RULER]
    (ii) b_{w0} injective on X           [the ruler has DISTINCT MARKS]

then Phi(w) determines {{ b_w o g : g in Gamma }}, hence the Gamma-orbit of b_w.

PROOF (this probe executes it, it does not merely check the conclusion).  Take the sub-multiset of
Phi(w) at tag y(w0): it is over w' in Gamma.w0 only, by (i).  With w' = g.w0,
Align(b_w, b_{w0} o g^-1) = Align(b_w o g, b_{w0}), and by (ii) each such contingency table is the
GRAPH of the function b_w o g read off in b_{w0}'s labelling.  So the block decodes to
{{ b_w o g : g }}. QED

WHY THIS MATTERS.  Section 6e.4c retracted "Phi determines the orbit" because isolating a probe
"presupposes the colouring already separates those copies".  It does not: the probe is CHOSEN, and
an invariant fails to be complete only on SPECIAL inputs -- a rigid, refinement-discrete copy is
always identified by its own colour.  The ensemble must contain every copy c in {0,1}^S (the gauge
acts transitively on copies, section 6c.1), so for L >= 6 it necessarily contains rigid ones.

WHAT IS CHECKED HERE, at the M fixpoint, L = 4, 5, 6:
  1. rulers exist:      how many omega0 satisfy (i) and (ii);
  2. the DECODE RUNS:   for each orbit rep, decode the y(w0)-block of Phi and check the recovered
                        multiset of profiles is exactly the S_L-orbit of a(c,i);
  3. the hypothesis is supplied by RIGIDITY, not by small L: cross-tabulate (ii) against
     "G_c is 1-WL-discrete" and against "Aut(G_c)_i = 1".
"""

import math
import sys
import time
from itertools import combinations, permutations

import numpy as np

import probe_cao_lemma_check_np as base


def wl1_discrete(L, NC, PAIRS):
    """Is the BARE 1-WL colouring of G_c discrete?  (=> the copy is a ruler candidate.)"""
    bits = ((np.arange(NC, dtype=np.int64)[:, None] >> np.arange(len(PAIRS), dtype=np.int64)[None, :]) & 1)
    adj = np.zeros((NC, L, L), dtype=np.int64)
    for k, (i, j) in enumerate(PAIRS):
        adj[:, i, j] = bits[:, k]
        adj[:, j, i] = bits[:, k]
    col = np.zeros((NC, L), dtype=np.int64)
    for _ in range(L + 1):
        C = int(col.max()) + 1
        nb = np.sort(np.where(adj.astype(bool), col[:, None, :] + 1, 0), axis=2)   # neighbour colours
        rows = np.concatenate([col[:, :, None], nb], axis=2).reshape(NC * L, L + 1)
        v = np.ascontiguousarray(rows).view([('', np.int64)] * (L + 1)).ravel()
        tab = np.unique(v)
        col = np.searchsorted(tab, v).reshape(NC, L)
    srt = np.sort(col, axis=1)
    return (srt[:, 1:] != srt[:, :-1]).all(axis=1)          # (NC,) discrete?


def stab_trivial(L, NC, PAIRS):
    """Is Aut(G_c)_i trivial?  (the obvious necessary condition for an injective profile)"""
    slot_of = {}
    for k, (i, j) in enumerate(PAIRS):
        slot_of[(i, j)] = slot_of[(j, i)] = k
    NSl = len(PAIRS)
    bits = ((np.arange(NC, dtype=np.int64)[:, None] >> np.arange(NSl, dtype=np.int64)[None, :]) & 1)
    pw = (1 << np.arange(NSl, dtype=np.int64))
    code = bits @ pw
    triv = np.ones((NC, L), dtype=bool)
    for p in permutations(range(L)):
        if all(p[i] == i for i in range(L)):
            continue
        perm = np.array([slot_of[(p[i], p[j])] for (i, j) in PAIRS], dtype=np.int64)
        nb = np.empty_like(bits)
        nb[:, perm] = bits
        same = (nb @ pw) == code                             # p is an automorphism of G_c
        for i in range(L):
            if p[i] == i:
                triv[same, i] = False                        # ... fixing i
    return triv.reshape(-1)


def main():
    L, NS, NC = base.L, base.NS, base.NC
    t0 = time.time()
    print(f'L={L}: {NC} copies, M(c) = {base.NV} vertices', flush=True)
    diag, prof = base.build()
    y = diag.reshape(-1)
    pf = prof.reshape(-1, 2 * NS)
    print(f'  M built in {time.time() - t0:.1f}s', flush=True)

    # S_L action on typed slots
    idx = {}
    for k, (i, j) in enumerate(base.PAIRS):
        idx[(i, j)] = idx[(j, i)] = k
    perms = []
    for p in permutations(range(L)):
        m = np.empty(2 * NS, dtype=np.int64)
        for k, (i, j) in enumerate(base.PAIRS):
            kk = idx[(p[i], p[j])]
            for t in (0, 1):
                m[2 * k + t] = 2 * kk + t
        perms.append(m)
    perms = np.stack(perms)

    # orbit of each marked vertex, via the profile (a determines c and i)
    canon = [min(map(tuple, pf[v][perms].tolist())) for v in range(len(pf))]
    ids = {}
    orb = np.array([ids.setdefault(k, len(ids)) for k in canon], dtype=np.int64)
    norb = len(ids)
    print(f'  S_L-orbits of profiles: {norb}', flush=True)

    # --- (i) isolated tags, (ii) injective profiles ---------------------------
    srt = np.sort(pf, axis=1)
    inj = (srt[:, 1:] != srt[:, :-1]).all(axis=1)
    ycls = {}
    for v, t in enumerate(y.tolist()):
        ycls.setdefault(t, []).append(v)
    isolated = np.zeros(len(y), dtype=bool)
    for t, mem in ycls.items():
        if len({orb[m] for m in mem}) == 1:
            isolated[mem] = True
    rulers = np.flatnonzero(isolated & inj)
    print(f'\n(i)  tag isolates the orbit : {int(isolated.sum())} / {len(y)}')
    print(f'(ii) profile injective      : {int(inj.sum())} / {len(y)}')
    print(f'==>  RULERS (i and ii)      : {len(rulers)} / {len(y)}')

    disc = wl1_discrete(L, NC, base.PAIRS)
    discv = np.repeat(disc, L)
    triv = stab_trivial(L, NC, base.PAIRS)
    print(f'\n  copies with G_c 1-WL-discrete            : {int(disc.sum())} / {NC}')
    print(f'  marked vertices with Aut(G_c)_i = 1      : {int(triv.sum())} / {len(y)}')
    print(f'  1-WL-discrete  ==> profile injective     : {bool(np.all(inj[discv]))}'
          f'   [{int((discv & ~inj).sum())} counterexamples]')
    print(f'  1-WL-discrete  ==> tag isolates          : {bool(np.all(isolated[discv]))}')
    print(f'  profile injective <==> Aut(G_c)_i = 1    : {bool(np.array_equal(inj, triv))}')

    if len(rulers) == 0:
        print('\n  no ruler at this L -- decode not attempted')
        return

    # --- 2. run the DECODE with one ruler -------------------------------------
    w0 = int(rulers[0])
    b0 = pf[w0]
    block = np.flatnonzero(y == y[w0])                 # the tag block: = Gamma.w0 by (i)
    label = {int(v): x for x, v in enumerate(b0.tolist())}     # b0 injective => a labelling of X
    order = np.array([label[int(v)] for v in b0.tolist()])     # unused, kept for clarity

    reps, seen = [], set()
    for v, o in enumerate(orb.tolist()):
        if o not in seen:
            seen.add(o)
            reps.append(v)

    bad = 0
    C = int(pf.max()) + 1
    for v in reps:
        a = pf[v]
        # decode every entry of the block: Align(a, b0 o g^-1) with b0 injective reads off a o g
        rec = set()
        for w in block.tolist():
            bw = pf[w]
            # the contingency table is the graph of  x |-> a(x)  in bw's labelling; invert bw
            pos = {int(val): x for x, val in enumerate(bw.tolist())}
            if len(pos) != 2 * NS:
                bad += 1                                    # block member not injective
                break
            dec = tuple(int(a[pos[int(m)]]) for m in b0.tolist())   # a o g, in b0's frame
            rec.add(dec)
        true_orbit = {tuple(r) for r in pf[v][perms].tolist()}
        # rec is expressed in b0's labelling of X; re-express by mapping b0's labels back to slots
        inv0 = {int(val): x for x, val in enumerate(b0.tolist())}
        rec_slots = set()
        for dec in rec:
            arr = [0] * (2 * NS)
            for pos_in_b0, m in enumerate(b0.tolist()):
                arr[inv0[int(m)]] = dec[pos_in_b0]
            rec_slots.add(tuple(arr))
        if rec_slots != true_orbit:
            bad += 1
            if bad <= 3:
                print(f'  DECODE MISMATCH at rep {divmod(v, L)}: '
                      f'recovered {len(rec_slots)} vs orbit {len(true_orbit)}')

    print(f'\n  DECODE with ruler {divmod(w0, L)} (block size {len(block)} = |S_L| {math.factorial(L)}):')
    print(f'  orbit reps decoded exactly: {len(reps) - bad} / {len(reps)}   '
          f'==> THEOREM VERIFIED: {bad == 0}   ({time.time() - t0:.1f}s)')


if __name__ == '__main__':
    main()
