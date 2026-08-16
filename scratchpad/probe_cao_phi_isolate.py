"""probe_cao_phi_isolate.py -- THE SHARP QUESTION, tested where it is NOT vacuous.

THE QUESTION (doc section 6e.4c):  does  Phi(c,i)  determine the S_L-orbit of  a(c,i)?

    Phi(c,i) = {{ (y(c',l), Align(a(c,i), b(c',l))) : (c',l) }},   y = the diagonal colour,
    a(c,i)   = ((k,t) |-> col(p(i), f(k,t))) = the typed-slot profile.

WHY IT CANNOT BE TESTED DIRECTLY.  At every reachable L the fixpoint colouring mu is a COMPLETE
invariant of the marked graph (20=20, 90=90, 544=544).  So every y-class is a single S_L-orbit, the
isolation problem that the whole question is about is VACUOUS, and "Phi determines the orbit" comes
out TRUE for a reason that has nothing to do with large L.  That is exactly the small-graph artefact
the project steer warns about (cells-are-orbits).

THE FIX -- MAKE THE TAG INCOMPLETE ON PURPOSE.  The question is an abstract one about an equivariant
profile family (b_omega) with an invariant tag y; nothing in it needs y to be a fixpoint.  Running
M(c)'s 2-WL for exactly r rounds (lockstep across ALL copies, globally interned) gives, for small r,
a tag y^(r) that is genuinely INCOMPLETE at L = 5, 6 -- several non-isomorphic marked graphs per
class -- while keeping every structural feature of the real setting: equivariance, "all copies
present", the same X = typed slots, the same Align channel.  So the isolation problem is LIVE, and
the two positions on record make OPPOSITE predictions:

  * reader (washout):  the uniform distribution over all copies washes the alignment out
                       ==>  Phi should stay ~ as coarse as y at every r.
  * probe-isolation:   Phi determines the orbit as soon as SOME omega0 has
                       (i) y-class(omega0) = its own S_L-orbit   [an isolated probe]  and
                       (ii) b(omega0) injective on the 2*C(L,2) typed slots,
                       because then that y-block of Phi is exactly {{Align(a o pi, b0) : pi}},
                       which reads a o pi off in b0's labelling for every pi.

CALIBRATION POINT (a PROVED one, doc section 6e.3): at r = 1 the profile is
b(c,l)_(k,t) = ([l in k], [c_k = t]), which takes 4 values, so NO probe is injective and Phi is
provably determined by y.  Any correct account must reproduce washout at r = 1.  If Phi's
completeness switches on exactly when the first isolated injective probe appears, the criterion is
confirmed and the reader's washout is refuted as a general phenomenon.

OUTPUT, per r:  #orbits (ground truth) >= #Phi-classes,  #y-classes,  #(y,Phi)-classes (washout iff
= #y-classes), and the probe census.

Usage:  python3 probe_cao_phi_isolate.py L [rmax] [chunk]
"""

import hashlib
import sys
import time
from itertools import combinations, permutations

import numpy as np

L = int(sys.argv[1]) if len(sys.argv) > 1 else 5
RMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 6
CHUNK = int(sys.argv[3]) if len(sys.argv) > 3 else 128

PAIRS = list(combinations(range(L), 2))
NS = len(PAIRS)
NC = 1 << NS
NV = L + 2 * NS
T0 = time.time()


def log(msg):
    print(f'[{time.time() - T0:7.1f}s] {msg}', flush=True)


# --------------------------------------------------------------------------- M(c), r rounds
def void_view(a):
    a = np.ascontiguousarray(a, dtype=np.int64)
    return a.view([('', np.int64)] * a.shape[1]).ravel()


def intern_rows(chunks_fn, nchunk):
    parts = []
    for ci in range(nchunk):
        parts.append(np.unique(void_view(chunks_fn(ci))))
    table = np.unique(np.concatenate(parts))
    return [np.searchsorted(table, void_view(chunks_fn(ci))) for ci in range(nchunk)], len(table)


def build_all(rmax):
    """2-WL on M(c) with a FROZEN frame, for every copy at once, yielding (r, diag, prof) for
    r = 0 .. rmax.  Colours are interned globally per round, so they are comparable across copies
    (project trap: per-copy naming / different round counts are not comparable)."""
    bits = ((np.arange(NC, dtype=np.int64)[:, None] >> np.arange(NS, dtype=np.int64)[None, :]) & 1)

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
    col = np.where(frozen[None, :, :],
                   (1 + fkey)[None, :, :] * 4,
                   (1 + base)[None, :, :] * 4 + 2 + adj.astype(np.int64))
    _, col = np.unique(col, return_inverse=True)
    col = col.reshape(NC, NV, NV).astype(np.int64)
    del adj

    yield 0, col[:, np.arange(L), np.arange(L)].copy(), col[:, :L, L:].copy()

    nchunk = (NC + CHUNK - 1) // CHUNK
    free_idx = np.argwhere(~frozen)
    xs, ys = free_idx[:, 0], free_idx[:, 1]
    prev = -1
    for rnd in range(1, rmax + 1):
        C = int(col.max()) + 1

        def rows_for(ci):
            lo, hi = ci * CHUNK, min((ci + 1) * CHUNK, NC)
            sub = col[lo:hi]
            left = sub[:, xs, :]
            right = sub[:, :, ys].transpose(0, 2, 1)
            k = np.sort(left * C + right, axis=2)
            own = sub[:, xs, ys][:, :, None]
            return np.concatenate([own, k], axis=2).reshape(-1, NV + 1)

        ids, ncol_new = intern_rows(rows_for, nchunk)
        off = int(col.max()) + 1
        for ci in range(nchunk):
            lo, hi = ci * CHUNK, min((ci + 1) * CHUNK, NC)
            col[lo:hi, xs, ys] = ids[ci].reshape(hi - lo, len(xs)) + off
        del ids
        log(f'  round {rnd}: {ncol_new} free-pair classes')
        yield rnd, col[:, np.arange(L), np.arange(L)].copy(), col[:, :L, L:].copy()
        if ncol_new == prev:
            log(f'  stable at round {rnd}')
            return
        prev = ncol_new


# --------------------------------------------------------------------------- marked-graph orbits
def orbit_ids():
    """Canonical id of the marked graph (G_c, i), for every (c, i).  Ground truth for 'orbit'."""
    slot_of = {}
    for k, (i, j) in enumerate(PAIRS):
        slot_of[(i, j)] = slot_of[(j, i)] = k
    bits = ((np.arange(NC, dtype=np.int64)[:, None] >> np.arange(NS, dtype=np.int64)[None, :]) & 1)
    pw = (1 << np.arange(NS, dtype=np.int64))
    best = None
    for p in permutations(range(L)):
        perm = np.array([slot_of[(p[i], p[j])] for (i, j) in PAIRS], dtype=np.int64)
        newbits = np.empty_like(bits)
        newbits[:, perm] = bits                      # slot k of c goes to slot perm[k]
        code = newbits @ pw                          # (NC,)
        cand = code[:, None] * L + np.array(p, dtype=np.int64)[None, :]   # (NC, L): vertex i -> p[i]
        best = cand if best is None else np.minimum(best, cand)
    _, ids = np.unique(best.reshape(-1), return_inverse=True)
    return ids                                       # index (c*L + i)


# --------------------------------------------------------------------------- Phi
def phi_digests(y, prof, reps, seed=20260815):
    """Phi(omega) for each omega in reps, as a sha256 over the sorted multiset of (y, Align) rows.

    Each row is folded to a uint64 by a random linear hash before sorting -- sorting a structured
    (lexicographic) array is ~50x slower and L=6 needs 550 of these.  A hash collision can only
    MERGE two distinct Phi values, i.e. it can only UNDERSTATE the Phi-class count; the hypothesis
    under test predicts the maximum (= #orbits), so collisions push against it, never for it.
    Two independent seeds agreeing is the check."""
    C = np.uint64(int(prof.max()) + 1)
    rng = np.random.default_rng(seed)
    W = rng.integers(1, 2 ** 63, size=prof.shape[1] + 1, dtype=np.uint64) * np.uint64(2) + np.uint64(1)
    yu = y.astype(np.uint64)
    pu = prof.astype(np.uint64)
    out = []
    for idx in reps:
        a = pu[idx]
        key = np.sort(a[None, :] * C + pu, axis=1)
        h = yu * W[0] + (key * W[None, 1:]).sum(axis=1)
        h.sort()
        out.append(hashlib.sha256(h.tobytes()).hexdigest())
    return out


def nclasses(labels):
    return len(set(labels))


def main():
    log(f'L={L}: {NC} copies, M(c) = {NV} vertices, {NC * L} marked payload vertices')
    orb = orbit_ids()
    norb = nclasses(orb.tolist())
    log(f'marked-graph iso classes (ground truth orbits): {norb}')

    # one representative per orbit -- Phi is orbit-invariant, so this loses nothing.  Two reps for
    # a sample of orbits, as a self-check that Phi really is orbit-invariant (pipeline validation).
    first = {}
    second = {}
    for idx, o in enumerate(orb.tolist()):
        if o not in first:
            first[o] = idx
        elif o not in second:
            second[o] = idx
    reps = [first[o] for o in sorted(first)]
    check = [o for o in sorted(second)][:8]

    print()
    print(f'{"r":>2} {"y-cls":>7} {"Phi-cls":>8} {"(y,Phi)":>8} {"washout":>8} '
          f'{"Phi=orb":>8} {"inj":>9} {"isolated":>9} {"iso+inj":>8}')
    print('-' * 82)

    for r, diag, prof in build_all(RMAX):
        y = diag.reshape(-1)
        pf = prof.reshape(-1, 2 * NS)

        # --- probe census ---------------------------------------------------
        srt = np.sort(pf, axis=1)
        inj = (srt[:, 1:] != srt[:, :-1]).all(axis=1)          # b injective on typed slots
        ycls = {}
        for idx, v in enumerate(y.tolist()):
            ycls.setdefault(v, []).append(idx)
        isolated = np.zeros(len(y), dtype=bool)
        for v, mem in ycls.items():
            if len(set(orb[m] for m in mem)) == 1:             # y-class = a single orbit
                isolated[mem] = True
        both = int((isolated & inj).sum())

        # --- Phi -------------------------------------------------------------
        dig = phi_digests(y, pf, reps)
        dmap = dict(zip(sorted(first), dig))
        # self-check: Phi must be constant on orbits
        dig2 = phi_digests(y, pf, [second[o] for o in check])
        ok = all(dmap[o] == d for o, d in zip(check, dig2))

        phi_of = [dmap[o] for o in orb.tolist()]
        nphi = nclasses(dig)
        ny = len(ycls)
        nyphi = nclasses(list(zip(y.tolist(), phi_of)))
        washout = (nyphi == ny)                                # y determines Phi  (= the LEMMA)
        complete = (nphi == norb)                              # Phi determines the orbit

        print(f'{r:>2} {ny:>7} {nphi:>8} {nyphi:>8} {str(washout):>8} '
              f'{str(complete):>8} {int(inj.sum()):>9} {int(isolated.sum()):>9} {both:>8}'
              + ('' if ok else '   <-- ORBIT-INVARIANCE SELF-CHECK FAILED'))

    print()
    print(f'orbits (ground truth) = {norb}')
    print('columns:  y-cls = #tag classes | Phi-cls = #Phi values (<= orbits, Phi is orbit-invariant)')
    print('          washout = y determines Phi (section 6d.8 LEMMA) | Phi=orb = Phi determines the orbit')
    print('          inj = profiles injective on typed slots | isolated = y-class is a single orbit')
    print('          iso+inj = ISOLATED INJECTIVE PROBES -- the predicted switch for Phi=orb')


if __name__ == '__main__':
    main()
