"""probe_cao_orb.py — is section 6e.4's gap really just ORB?

THE REDUCTION.  Section 6e.1: Phi(c,i) is the pushforward of a fixed distribution D under
(y,b) |-> (y, Align(a(c,i), b)), so it depends on (c,i) only through a(c,i).  Section 6e.2: it depends
only on the S_L-ORBIT of a(c,i).  Hence

    ORB:  mu_c(i,i) determines the S_L-orbit of a(c,i)        ==>  section 6d.8's LEMMA.

and conversely, if some b(c',l) is INJECTIVE on typed slots then Align(a, b(c',l)) reads a off in
b's labelling, so LEMMA ==> ORB.  So ORB is (given injectivity) EQUIVALENT to the open lemma, and it
mentions no sum over copies at all -- which is where section 6e.4's whole difficulty lived.

WHAT THIS PROBE DOES.
  (A) ORB: group payload vertices by mu, brute-force S_L to test whether every member of a class has
      an S_L-equivalent slot profile.  A single failure REFUTES the lemma outright (given (B)).
  (B) injectivity: does any b(c',l) separate all 2*C(L,2) typed slots?  This is what makes the
      converse live.  If NO b is injective the ORB->LEMMA direction still stands, but a failure of
      ORB would no longer refute.

section 6e.2's trap box asserts ORB "is exactly `M` is a complete isomorphism invariant, which must
not be true".  That is a CITED pin, not a proved one, and the standing steer is to prove the pin.
This probe checks it.
"""

import sys
import time
from itertools import combinations, permutations

import numpy as np

import probe_cao_lemma_check_np as base


def main():
    L = base.L
    NS = base.NS
    t0 = time.time()
    print(f'L={L}: {base.NC} copies, M(c) = {base.NV} vertices', flush=True)
    diag, prof = base.build()
    dflat = diag.reshape(-1)
    pflat = prof.reshape(-1, 2 * NS)
    print(f'  M built in {time.time() - t0:.1f}s', flush=True)

    # slot index for an unordered pair, and the induced action of S_L on typed slots
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
    perms = np.stack(perms)                       # (L!, 2*NS)
    print(f'  {len(perms)} permutations of typed slots', flush=True)

    # ---- (B) is any b(c',l) injective on typed slots? ------------------------
    srt = np.sort(pflat, axis=1)
    distinct = (srt[:, 1:] != srt[:, :-1]).all(axis=1)
    ninj = int(distinct.sum())
    print(f'\n(B) profiles injective on all {2 * NS} typed slots: {ninj} / {len(pflat)}'
          f'   ==> LEMMA=>ORB is {"LIVE" if ninj else "NOT available"}', flush=True)

    # ---- (A) ORB -------------------------------------------------------------
    classes = {}
    for i, v in enumerate(dflat.tolist()):
        classes.setdefault(v, []).append(i)
    print(f'\n(A) mu-classes: {len(classes)}', flush=True)

    bad = checked = 0
    worst = None
    for v, members in sorted(classes.items()):
        if len(members) < 2:
            continue
        checked += 1
        ref = pflat[members[0]]
        orbit = np.unique(ref[perms], axis=0)      # every relabelling of the reference profile
        for m in members[1:]:
            row = pflat[m]
            hit = (orbit == row[None, :]).all(axis=1).any()
            if not hit:
                bad += 1
                if worst is None:
                    worst = (v, members[0], m)
                break
    print(f'  classes with >=2 members checked: {checked}')
    if worst is not None:
        v, x, y = worst
        print(f'  first violation: mu-class {v}, members {divmod(x, L)} vs {divmod(y, L)}'
              f'   (as (copy, vertex))')
    print(f'\n==> ORB HOLDS at L={L}: {bad == 0}   [{bad} classes violate]'
          f'   {time.time() - t0:.1f}s')
    if bad and ninj:
        print('==> therefore section 6d.8\'s LEMMA IS FALSE at this L (converse via injectivity).')


if __name__ == '__main__':
    main()
