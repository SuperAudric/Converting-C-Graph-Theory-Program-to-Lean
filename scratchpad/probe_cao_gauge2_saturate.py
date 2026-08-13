"""probe_cao_gauge2_saturate.py — HOW MANY COPIES does the sharing effect need?

probe_cao_gauge2_ablate.py established two things at L = 4:
  * the 2^d CENTRALS contribute nothing to the payload-pair partition beyond making the frame types
    absolute -- so a faithful test object does not need them;
  * SHARING is the whole difference, and the two-copy model is strictly finer than the full ensemble
    on 1936 / 2016 copy pairs.

Those two together say the faithful object is "k copies + one shared frame + absolute types".  The
binding cost of Construction C has always been the 2^d copies -- but nothing says 2^d is REQUIRED for
the sharing effect to saturate.  If the payload-pair partition on a fixed pair of copies stops moving
once k reaches some modest number, then the faithful re-test of Shrikhande/rook (L=16, d=120: frame
240 vertices, 16 per copy, so 16k + 240) becomes directly runnable -- k = 16 would be 496 vertices.

Method: fix a copy pair (c, c') on which the two-copy model is strictly finer than FULL.  Grow the
copy set from {c, c'} upward with random additions, and compare the induced partition on (c, c')'s
payload pairs against the FULL-ensemble answer at each k.  Report the k at which it first matches and
then stays matched.

⚠ A caveat that must travel with any use of this: a RANDOM subset of copies is itself a modelling
choice.  In the real object the copy set is all 2^d and is gauge-closed; a sample is neither.  What
this probe can establish is a NECESSARY size (below the saturation point no sample can be faithful);
it cannot by itself certify that a sample at or above it IS faithful.
"""

import sys
from itertools import combinations
import random

L = 4
PAIRS = list(combinations(range(L), 2))
NS = len(PAIRS)
NC = 1 << NS
SLOT = {}
for k, (i, j) in enumerate(PAIRS):
    SLOT[(i, j)] = SLOT[(j, i)] = k


def build(copies):
    verts = [('p', c, i) for c in copies for i in range(L)]
    verts += [('f', k, t) for k in range(NS) for t in (0, 1)]
    adj = set()

    def add(u, w):
        adj.add((u, w))
        adj.add((w, u))

    for c in copies:
        for a in range(L):
            for b in range(a + 1, L):
                add(('p', c, a), ('p', c, b))
        for a in range(L):
            for b in range(L):
                if a != b:
                    add(('p', c, a), ('f', SLOT[(a, b)], (c >> SLOT[(a, b)]) & 1))
    for k in range(NS):
        add(('f', k, 0), ('f', k, 1))
    vcol = {v: (0 if v[0] == 'p' else 1 + v[2]) for v in verts}
    return verts, adj, vcol


def wl2(verts, adj, vcol):
    n = len(verts)
    idx = {v: i for i, v in enumerate(verts)}
    col = [0] * (n * n)
    atoms = {}
    for x in verts:
        a = idx[x]
        for y in verts:
            k = (x == y, (x, y) in adj, vcol[x], vcol[y])
            col[a * n + idx[y]] = atoms.setdefault(k, len(atoms))
    ncol = len(set(col))
    while True:
        C = ncol
        colT = [0] * (n * n)
        for a in range(n):
            for b in range(n):
                colT[b * n + a] = col[a * n + b]
        table, new = {}, [0] * (n * n)
        rng = range(n)
        for a in rng:
            ra = col[a * n:(a + 1) * n]
            for b in rng:
                rb = colT[b * n:(b + 1) * n]
                cnt = {}
                for z in rng:
                    key = ra[z] * C + rb[z]
                    cnt[key] = cnt.get(key, 0) + 1
                sig = (col[a * n + b], tuple(sorted(cnt.items())))
                t = table.get(sig)
                if t is None:
                    t = table[sig] = len(table)
                new[a * n + b] = t
        if len(table) == ncol:
            return {(x, y): col[idx[x] * n + idx[y]] for x in verts for y in verts
                    if x[0] == 'p' and y[0] == 'p'}
        col, ncol = new, len(table)


def part_on(pc, copies):
    keys = [('p', c, i) for c in copies for i in range(L)]
    lab, out = {}, {}
    for x in keys:
        for y in keys:
            v = pc[(x, y)]
            out[(x, y)] = lab.setdefault(v, len(lab))
    return out


def same(a, b):
    m1, m2 = {}, {}
    for k in a:
        if m1.setdefault(a[k], b[k]) != b[k] or m2.setdefault(b[k], a[k]) != a[k]:
            return False
    return True


def coset(c, cp, rank, rng):
    """section 3.4's own proposal: a GAUGE-CLOSED copy set.  H = <c^c'> extended to the given RANK by
    slot generators, copies = c ^ H, size exactly 2^rank.  ⚠ generators must be checked for GF(2)
    independence -- c^c' can lie in the span of the slot indicators picked after it, and an unchecked
    version silently produced sets of size 16 labelled "2^5".  Returns None if the rank is
    unreachable.  Note H = <c^c'> alone (rank 1) is already gauge-closed and is exactly the two-copy
    model, so gauge-closure by itself is NOT the faithfulness criterion."""
    basis = []

    def reduce_(x):
        for b in basis:
            x = min(x, x ^ b)
        return x

    def add_(x):
        x = reduce_(x)
        if x == 0:
            return False
        basis.append(x)
        basis.sort(reverse=True)
        return True

    if not add_(c ^ cp):
        return None
    pool = [1 << k for k in range(NS)]
    rng.shuffle(pool)
    for g in pool:
        if len(basis) >= rank:
            break
        add_(g)
    if len(basis) != rank:
        return None
    H = {0}
    for g in basis:
        H |= {h ^ g for h in H}
    assert len(H) == 1 << rank
    return sorted({c ^ h for h in H})


if __name__ == '__main__':
    rng = random.Random(20260813)
    full = wl2(*build(list(range(NC))))
    KS = [2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64]
    trials = [(c, cp) for (c, cp) in combinations(range(NC), 2)]
    rng.shuffle(trials)
    picks = trials[:4]
    print(f'L={L}, {NC} copies total.  frame {2*NS} vertices, {L} payload per copy.', flush=True)
    print('✓ = partition on the pair matches the FULL ensemble\n')
    print('A. RANDOM subsets, k copies (the pair + random others)')
    for (c, cp) in picks:
        ref = part_on(full, [c, cp])
        others = [x for x in range(NC) if x not in (c, cp)]
        rng.shuffle(others)
        row = []
        for k in KS:
            p = part_on(wl2(*build([c, cp] + others[:k - 2])), [c, cp])
            row.append(f'{k}:{"✓" if same(p, ref) else "·"}')
        print(f'  copies {c:2d},{cp:2d}  ' + '  '.join(row), flush=True)

    print('\nB. GAUGE-CLOSED subsets (section 3.4\'s proposal), 2^j copies')
    for (c, cp) in picks:
        ref = part_on(full, [c, cp])
        row = []
        for j in range(1, NS + 1):
            cs = coset(c, cp, j, rng)
            if cs is None:
                row.append(f'2^{j}:n/a')
                continue
            p = part_on(wl2(*build(cs)), [c, cp])
            row.append(f'{len(cs):2d}:{"✓" if same(p, ref) else "·"}')
        print(f'  copies {c:2d},{cp:2d}  ' + '  '.join(row), flush=True)
