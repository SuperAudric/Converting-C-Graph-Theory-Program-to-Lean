"""probe_cao_ruler_test.py -- THE DECISIVE TEST the reader's r-edge construction unlocks.

THE DISAGREEMENT.  Does the CROSS-COPY channel (payload pairs in different copies, mediated by the
shared frame) separate things the WITHIN-COPY channel cannot?  My section 6e.4d argument says yes,
via a "ruler": a refinement-discrete copy whose reading of the frame is injective.  The reader says
no -- the information is coherent-configuration-level and washes out.

WHY IT COULD NOT BE TESTED BEFORE.  The full ensemble is 2^15 copies (196638 vertices at L=6), and at
every reachable L the within-copy channel is ALREADY a complete invariant, so there is nothing left
for the cross-copy channel to add and any comparison comes out "equal" for free.

THE READER'S UNLOCK (2026-08-15).  Drop the centrals (frame types individualized directly) and keep
an S_L-invariant set of copies.  Their ruler: at L=6, r=6 edges, a triangle with pendant paths of
lengths 0,1,2 -- verified refinement-discrete and rigid, and the ONLY ruler iso class at r=6.
A ruler is rigid so its orbit is all 720 relabellings: minimum fair object = 720*6+30 = 4350
vertices.  Naive 2-WL is hopeless there; exact-integer BLAS hashing does a round in seconds.

MY FAIRNESS CORRECTION TO THE PROPOSED EXPERIMENT.  "Wipe the target clique and see if the outside
can rebuild it" tests something STRONGER than my claim -- my argument BUILDS the reading out of the
within-copy channel, so wiping it removes one of my own premises and a null result would not refute
me.  It is also not the shape of the real failure: at large L the within-copy channel is not absent,
it PLATEAUS at an invariant that is complete for generic graphs and blind on a designed pair.

So the handicap applied here models that instead: **freeze the within-copy payload pair colours at
their bare 1-WL value.**  Then
  * the within-copy channel is genuinely blind on a designed pair -- C6 vs 2C3, both 2-regular, both
    6 edges, so identical under 1-WL;  <-- this is the plateau, and it is what makes the test live
  * the reading is NOT crippled: (p(c,u), f(k,t)) still counts common payload neighbours {w in k},
    which runs off ADJACENCY, not off pair colours, so the reading still determines the copy;
  * the RULER still works, because it is refinement-DISCRETE: its within-copy labels stay distinct
    even frozen at 1-WL.  That is exactly why the reader's choice of a refinement-discrete ruler is
    the right one.
⟹ the test isolates precisely the disputed step, and it can come out either way.

CONFIGURATIONS
  A  copies = orbit(C6) + orbit(2C3), handicap ON    -- no ruler.  Control.
  B  copies = A + orbit(ruler),       handicap ON    -- the test.
  A0/B0  the same with the handicap OFF              -- calibration; both should separate fully.
VERDICT: if C6-dots and 2C3-dots share a cell in A but not in B, the cross-copy ruler channel
demonstrably separates what the within-copy channel cannot.  If they are merged in B too, my
mechanism fails under the plateau and section 6e.4d's argument is in serious trouble.

Usage: python3 probe_cao_ruler_test.py [A|B|A0|B0|all] [hashes]
"""

import sys
import time
from itertools import combinations, permutations

import numpy as np

L = 6
PAIRS = list(combinations(range(L), 2))
NS = len(PAIRS)
SLOT = {}
for _k, (_i, _j) in enumerate(PAIRS):
    SLOT[(_i, _j)] = SLOT[(_j, _i)] = _k
PERMS = list(permutations(range(L)))
T0 = time.time()


def log(m):
    print(f'[{time.time() - T0:7.1f}s] {m}', flush=True)


def mask_of(edges):
    m = 0
    for e in edges:
        m |= 1 << SLOT[tuple(e)]
    return m


def relabel(mask, p):
    out = 0
    for k, (i, j) in enumerate(PAIRS):
        if (mask >> k) & 1:
            out |= 1 << SLOT[(p[i], p[j])]
    return out


def orbit(mask):
    return sorted({relabel(mask, p) for p in PERMS})


def wl1_colours(mask):
    adj = [[1 if (u != v and (mask >> SLOT[(u, v)]) & 1) else 0 for v in range(L)] for u in range(L)]
    col = [0] * L
    for _ in range(L + 1):
        key = [(col[v], tuple(sorted(col[u] for u in range(L) if adj[v][u]))) for v in range(L)]
        tab = {k: n for n, k in enumerate(sorted(set(key)))}
        col = [tab[k] for k in key]
    return col


def marked_iso(mask, v):
    """canonical id of the marked graph (G_mask, v)"""
    return min((relabel(mask, p), p[v]) for p in PERMS)


# --------------------------------------------------------------------------- the object
RULER = mask_of([(0, 1), (0, 2), (1, 2), (1, 3), (2, 4), (4, 5)])
C6 = mask_of([(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0)])
C33 = mask_of([(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3)])


def build(copies, handicap):
    """Returns adj (bool), start colour matrix, frozen mask, and bookkeeping."""
    nc = len(copies)
    NP = nc * L
    N = NP + 2 * NS
    F0 = NP
    adj = np.zeros((N, N), dtype=bool)
    for ci, c in enumerate(copies):
        b = ci * L
        for u in range(L):
            for v in range(u + 1, L):
                adj[b + u, b + v] = adj[b + v, b + u] = True          # payload clique
            for v in range(L):
                if u != v:
                    k = SLOT[(u, v)]
                    f = F0 + 2 * k + ((c >> k) & 1)
                    adj[b + u, f] = adj[f, b + u] = True
    for k in range(NS):
        adj[F0 + 2 * k, F0 + 2 * k + 1] = adj[F0 + 2 * k + 1, F0 + 2 * k] = True

    kind = np.zeros(N, dtype=np.int64)
    for k in range(NS):
        for t in (0, 1):
            kind[F0 + 2 * k + t] = 1 + t                               # frame types individualized
    eye = np.eye(N, dtype=bool)
    col = ((kind[:, None] * 3 + kind[None, :]) * 2 + eye) * 2 + adj
    col = col.astype(np.int64)

    frozen = np.zeros((N, N), dtype=bool)
    # frame-frame pairs frozen at (t, t', |k n k'|)   -- section 6d.5's rule
    slotof = np.full(N, -1, dtype=np.int64)
    for k in range(NS):
        for t in (0, 1):
            slotof[F0 + 2 * k + t] = k
    big = int(col.max()) + 1
    for x in range(F0, N):
        for y in range(F0, N):
            inter = len(set(PAIRS[slotof[x]]) & set(PAIRS[slotof[y]]))
            col[x, y] = big + ((kind[x] * 3 + kind[y]) * 4 + inter) * 2 + (x == y)
            frozen[x, y] = True

    if handicap >= 1:
        # within-copy payload OFF-DIAGONAL pairs frozen at their bare 1-WL value.
        # the diagonal stays FREE: that is where the answer has to appear.
        big = int(col.max()) + 1
        for ci, c in enumerate(copies):
            b = ci * L
            w = wl1_colours(c)
            nw = max(w) + 1
            for u in range(L):
                for v in range(L):
                    if u == v:
                        continue
                    a = 1 if (c >> SLOT[(u, v)]) & 1 else 0
                    col[b + u, b + v] = big + (w[u] * nw + w[v]) * 2 + a
                    frozen[b + u, b + v] = True

    if handicap >= 2:
        # ★ THE FAITHFUL PLATEAU.  Freeze the READING itself -- every (payload, frame) pair -- at
        # 1-WL strength: (is u an endpoint of k, the type t, does c decide k as t, u's 1-WL colour,
        # the 1-WL colours of k's two endpoints).  Equivariant, and:
        #   * as a MULTISET over typed slots it carries only (deg u, |E|) -- so C6 and 2C3 are
        #     INDISTINGUISHABLE by anything inside a copy.  That is the plateau.
        #   * as a FUNCTION on typed slots it still spells out the whole graph.
        #   * for a refinement-DISCRETE copy the endpoints' 1-WL colours NAME the slot, so the
        #     ruler's reading stays INJECTIVE -- which is the whole point of choosing that ruler.
        # ⟹ converting multiset -> function is exactly and only what a ruler can do.
        big = int(col.max()) + 1
        for ci, c in enumerate(copies):
            b = ci * L
            w = wl1_colours(c)
            nw = max(w) + 1
            for u in range(L):
                for k, (a, bb) in enumerate(PAIRS):
                    ends = tuple(sorted((w[a], w[bb])))
                    for t in (0, 1):
                        f = F0 + 2 * k + t
                        key = ((((1 if u in (a, bb) else 0) * 2 + t) * 2
                                + (1 if ((c >> k) & 1) == t else 0)) * nw + w[u]) * nw * nw \
                            + ends[0] * nw + ends[1]
                        col[b + u, f] = col[f, b + u] = big + key
                        frozen[b + u, f] = frozen[f, b + u] = True

    if handicap >= 3:
        # ABLATION: freeze the CROSS-COPY payload pairs too, at their start value.  Now nothing is
        # free except the payload diagonal, and every channel that could carry a comparison between
        # two copies is shut.  If C6 and 2C3 still separate here, the separation seen at handicap 2
        # did NOT come from the cross-copy channel and my reading of that result is wrong.
        for ci in range(nc):
            for cj in range(nc):
                if ci == cj:
                    continue
                frozen[ci * L:(ci + 1) * L, cj * L:(cj + 1) * L] = True

    _, col = np.unique(col, return_inverse=True)
    return adj, col.reshape(N, N).astype(np.int64), frozen, N, F0, nc


# --------------------------------------------------------------------------- hashed exact 2-WL
def wl2(col, frozen, nhash, rounds=12, seed=7):
    """2-WL.  The multiset {(col[u,z], col[z,v]) : z} is fingerprinted by sum_z f[a]*g[b] with
    f,g random integers < 2^19, so every product < 2^38 and every sum < N*2^38 < 2^53 -- the dgemm
    is therefore EXACT in float64 and cannot manufacture a spurious separation (which is the
    dangerous direction here).  Independent draws make a spurious MERGE negligible."""
    N = col.shape[0]
    rng = np.random.default_rng(seed)
    prev = -1
    for rnd in range(rounds):
        C = int(col.max()) + 1
        # progressive interning: never hold more than two N^2 columns at once (N=4770 is 182 MB each)
        acc = col.reshape(-1)
        for _ in range(nhash):
            f = rng.integers(0, 1 << 19, size=C).astype(np.float64)
            g = rng.integers(0, 1 << 19, size=C).astype(np.float64)
            M = f[col] @ g[col]
            assert np.all(np.abs(M) < 2.0 ** 53), 'exactness budget blown'
            rows = np.stack([acc, M.reshape(-1).astype(np.int64)], axis=1)
            del M
            v = np.ascontiguousarray(rows).view([('', np.int64)] * 2).ravel()
            del rows
            tab = np.unique(v)
            acc = np.searchsorted(tab, v)
            del v
        new = acc.reshape(N, N)
        new = np.where(frozen, col, new + int(col.max()) + 1)
        _, new = np.unique(new, return_inverse=True)
        new = new.reshape(N, N)
        n = len(np.unique(new))
        col = new
        if n == prev:
            log(f'    stable after {rnd + 1} rounds, {n} pair classes')
            break
        prev = n
        log(f'    round {rnd + 1}: {n} pair classes')
    return col


# --------------------------------------------------------------------------- run
def run(name, seeds, handicap, nhash):
    copies = sorted({m for s in seeds for m in orbit(s)})
    log(f'{name}: {len(copies)} copies, handicap={handicap}')
    adj, col, frozen, N, F0, nc = build(copies, handicap)
    log(f'  N = {N} vertices')
    col = wl2(col, frozen, nhash)

    diag = col[np.arange(N), np.arange(N)]
    ids, cells, orbs = {}, {}, {}
    for ci, c in enumerate(copies):
        for u in range(L):
            v = ci * L + u
            o = ids.setdefault(marked_iso(c, u), len(ids))
            cells.setdefault(int(diag[v]), set()).add(o)
            orbs.setdefault(o, set()).add(int(diag[v]))
    mixed = {k: s for k, s in cells.items() if len(s) > 1}
    log(f'  payload cells {len(cells)}   S_6-orbits {len(ids)}   MIXED CELLS {len(mixed)}')

    # the specific question: are C6-dots and 2C3-dots in the same cell?
    def cell_of(mask):
        ci = copies.index(mask)
        return {int(diag[ci * L + u]) for u in range(L)}

    out = {}
    for nm, m in (('C6', C6), ('2C3', C33), ('ruler', RULER)):
        if m in copies:
            out[nm] = cell_of(m)
    if 'C6' in out and '2C3' in out:
        shared = out['C6'] & out['2C3']
        log(f'  C6 cells {sorted(out["C6"])}   2C3 cells {sorted(out["2C3"])}')
        log(f'  ==> C6 and 2C3 SEPARATED: {not shared}'
            f'{"" if not shared else f"   (share cells {sorted(shared)})"}')
    if 'ruler' in out:
        log(f'  ruler dots occupy {len(out["ruler"])} cells (6 = fully split)')
    return len(mixed)


def main():
    which = sys.argv[1] if len(sys.argv) > 1 else 'all'
    nhash = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    cfg = {
        'A': ('A  control, no ruler, handicap 1', [C6, C33], 1),
        'B': ('B  with ruler orbit, handicap 1', [C6, C33, RULER], 1),
        'A0': ('A0 calibration, no ruler, no handicap', [C6, C33], 0),
        'B0': ('B0 calibration, with ruler, no handicap', [C6, C33, RULER], 0),
        'A2': ('A2 CONTROL, no ruler, FAITHFUL PLATEAU', [C6, C33], 2),
        'A3': ('A3 ABLATION, plateau + cross-copy channel SHUT', [C6, C33], 3),
        'B2': ('B2 THE TEST, with ruler orbit, FAITHFUL PLATEAU', [C6, C33, RULER], 2),
    }
    order = ['A0', 'A', 'A2', 'B2'] if which == 'all' else [which]
    for key in order:
        nm, seeds, hc = cfg[key]
        run(nm, seeds, hc, nhash)
        print()


if __name__ == '__main__':
    main()
