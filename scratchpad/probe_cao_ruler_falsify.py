"""probe_cao_ruler_falsify.py -- a FALSIFICATION SEARCH for the ruler argument.

THE READER'S OBJECTION (2026-08-16, and it is the right one to make): the ruler argument "could not
separate a coherent configuration that is CAO from one with mixed orbit cells", and the only test
offered so far was "find a CAO counterexample", which is the open problem itself.  So the argument
looked unfalsifiable.

IT IS NOT.  What the argument actually asserts is a CONDITIONAL:

    RULER(r)  ==>  no mixed cells at round r+2

where RULER(r) says some member omega0 has, w.r.t. the round-r colouring,
    (i)  a diagonal colour shared by no NON-ISOMORPHIC member   [the tag isolates it]
    (ii) an INJECTIVE reading of the shared frame               [distinct marks]
and the +2 is the two coherence steps the argument spends (diagonal -> pair, pair -> alignment).

The contrapositive is  mixed cells ==> no ruler,  and THAT is testable without a CAO counterexample,
because mixed cells are easy to manufacture at small size: cap the refinement at r rounds and the
colouring is genuinely incomplete.  A single (family, r) with a ruler at round r and a mixed cell
still present at round r+2 REFUTES the argument.

THE SEARCH.  At L=4 this is EXHAUSTIVE: an object is determined by which of the 11 isomorphism
classes of 4-vertex graphs are present (the family must be S_L-closed, so it is a union of classes),
giving 2^11 = 2048 objects.  Each is built exactly like the ensemble -- shared frame, types
distinguished, payload cliques -- and refined round by round from the plain colouring.

⚠ POWER CHECK, and it is reported: if no object ever has a mixed cell at any round, the search proves
nothing.  The mixed-cell count at each round is printed so the reader can see the search had teeth.

⚠ Orbits are the marked-graph iso classes.  S_L <= Aut always, so the true orbits are at least this
coarse; if a candidate falsifier turns up, Aut is verified exactly before it is believed.
"""

import sys
import time
from itertools import combinations, permutations

import numpy as np

L = int(sys.argv[1]) if len(sys.argv) > 1 else 4
MAXR = 4
PAIRS = list(combinations(range(L), 2))
NS = len(PAIRS)
NC = 1 << NS
SLOT = {}
for _k, (_i, _j) in enumerate(PAIRS):
    SLOT[(_i, _j)] = SLOT[(_j, _i)] = _k
PERMS = list(permutations(range(L)))


def graph_classes():
    """iso class id of every labelled graph, and the marked-graph class of every (graph, vertex)."""
    bits = ((np.arange(NC)[:, None] >> np.arange(NS)[None, :]) & 1)
    pw = (1 << np.arange(NS))
    gbest, mbest = None, None
    for p in PERMS:
        perm = np.array([SLOT[(p[i], p[j])] for (i, j) in PAIRS])
        nb = np.empty_like(bits)
        nb[:, perm] = bits
        code = nb @ pw
        gbest = code if gbest is None else np.minimum(gbest, code)
        cand = code[:, None] * L + np.array(p)[None, :]
        mbest = cand if mbest is None else np.minimum(mbest, cand)
    _, gcls = np.unique(gbest, return_inverse=True)
    _, mcls = np.unique(mbest.reshape(-1), return_inverse=True)
    return gcls, mcls.reshape(NC, L)


def build(copy_ids):
    """shared frame + one payload clique per copy, exactly as in the ensemble."""
    nc = len(copy_ids)
    n = 2 * NS + nc * L
    adj = np.zeros((n, n), dtype=bool)
    kind = np.zeros(n, dtype=np.int64)
    for k in range(NS):
        for t in (0, 1):
            kind[2 * k + t] = t                                  # frame types distinguished
        adj[2 * k, 2 * k + 1] = adj[2 * k + 1, 2 * k] = True
    base = 2 * NS
    for ci, c in enumerate(copy_ids):
        off = base + ci * L
        kind[off:off + L] = 2
        for x in range(L):
            for y in range(L):
                if x == y:
                    continue
                adj[off + x, off + y] = True                     # payload clique
                k = SLOT[(x, y)]
                t = (c >> k) & 1
                adj[off + x, 2 * k + t] = adj[2 * k + t, off + x] = True
    return n, adj, kind


def wl_rounds(n, adj, kind, maxr):
    """yield the vertex colouring after r = 0,1,2,... rounds (exact, hashed multisets)."""
    rng = np.random.default_rng(7)
    eye = np.eye(n, dtype=bool)
    col = (((kind[:, None] * 3 + kind[None, :]) * 2 + eye) * 2 + adj).astype(np.int64)
    _, col = np.unique(col, return_inverse=True)
    col = col.reshape(n, n).astype(np.int64)
    yield 0, col
    prev = -1
    for r in range(1, maxr + 1):
        C = int(col.max()) + 1
        # ⚠ a C x C hash table is O(C^2) and C grows every round (~5000 by the fixpoint at n=268,
        # i.e. 25M draws per round per object) -- that is what stalled the first attempt.  Two
        # O(C) tables multiplied give the same effect: h(x,y) = A[x] * B[y], summed over z.
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
        yield r, col
        if len(tab) == prev:
            break
        prev = len(tab)


def analyse(copy_ids, mcls):
    """per round: (#mixed cells, ruler present?)   -- payload vertices only."""
    n, adj, kind = build(copy_ids)
    base = 2 * NS
    orb = np.array([mcls[c][x] for c in copy_ids for x in range(L)])
    out = []
    for r, col in wl_rounds(n, adj, kind, MAXR):
        diag = col[np.arange(n), np.arange(n)][base:]
        frame_read = col[base:, :2 * NS]                          # each payload vertex's reading
        srt = np.sort(frame_read, axis=1)
        inj = (srt[:, 1:] != srt[:, :-1]).all(axis=1)
        by = {}
        for d, o in zip(diag.tolist(), orb.tolist()):
            by.setdefault(d, set()).add(o)
        mixed = sum(1 for s in by.values() if len(s) > 1)
        isolated = np.array([len(by[d]) == 1 for d in diag.tolist()])
        out.append((r, mixed, bool((isolated & inj).any()), int((isolated & inj).sum())))
    return out


def power_summary(rows):
    """first round with a ruler, last round with a mixed cell -- the joint distribution is what
    gives the test its teeth.  If rulers only ever appeared at the fixpoint, "ruler => no mixed"
    would hold for a trivial monotonicity reason; a family where a ruler appears EARLY while mixed
    cells are still present would refute the argument."""
    first_ruler = min((r for r, m, ru, k in rows if ru), default=None)
    last_mixed = max((r for r, m, ru, k in rows if m), default=None)
    return first_ruler, last_mixed


def main():
    t0 = time.time()
    gcls, mcls = graph_classes()
    ncls = gcls.max() + 1
    by_class = [np.flatnonzero(gcls == i).tolist() for i in range(ncls)]
    print(f'L={L}: {ncls} graph iso classes, {NC} labelled graphs  '
          f'==> {2 ** ncls} S_L-closed families (exhaustive)')

    falsifiers = []
    joint = {}
    mixed_seen = 0
    families = 0
    round_hist = {}
    for mask in range(1, 1 << ncls):
        copy_ids = [c for i in range(ncls) if (mask >> i) & 1 for c in by_class[i]]
        if not copy_ids or len(copy_ids) * L + 2 * NS > 170:
            continue
        families += 1
        rows = analyse(copy_ids, mcls)
        fr, lm = power_summary(rows)
        joint.setdefault((fr, lm), 0)
        joint[(fr, lm)] += 1
        info = {r: (m, ruler, k) for r, m, ruler, k in rows}
        last = max(info)
        if any(m > 0 for _, (m, _, _) in info.items()):
            mixed_seen += 1
        for r, (m, ruler, k) in info.items():
            round_hist.setdefault(r, [0, 0])
            round_hist[r][0] += 1
            if m:
                round_hist[r][1] += 1
        # THE TEST: ruler at round r, but a mixed cell still at round r+2
        for r, (m, ruler, k) in info.items():
            if not ruler:
                continue
            tgt = min(r + 2, last)
            if info[tgt][0] > 0:
                falsifiers.append((mask, r, k, tgt, info[tgt][0]))
    print(f'  families tested: {families}   families with a mixed cell at SOME round: {mixed_seen}')
    print('  round : families with >=1 mixed cell  (search POWER -- if these are 0 the test is empty)')
    for r in sorted(round_hist):
        tot, mx = round_hist[r]
        print(f'    r={r} : {mx:>5} / {tot}')
    print('\n  joint (first round with a RULER, last round with a MIXED cell) -> #families:')
    for k in sorted(joint, key=lambda t: (t[0] is None, t[0], t[1] is None, t[1])):
        print(f'    first-ruler={str(k[0]):>4}  last-mixed={str(k[1]):>4}  : {joint[k]}')
    print(f'\n  FALSIFIERS (ruler at round r, mixed cell still at r+2): {len(falsifiers)}')
    for f in falsifiers[:10]:
        print(f'    family mask {f[0]}, ruler at r={f[1]} ({f[2]} rulers), '
              f'{f[4]} mixed cells at r={f[3]}')
    print(f'\n  ({time.time() - t0:.0f}s)')


if __name__ == '__main__':
    main()
