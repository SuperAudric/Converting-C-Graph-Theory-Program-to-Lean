"""probe_cao_gauge2_ablate.py — with a Z_2 gauge, ABLATE the two channels that separate the real
ensemble from the admission-test model, and measure what each is worth at 2-WL.

The reader's simplification (2026-08-13) replaces the Q_4 cube by a connected PAIR per slot.  That is
already what rung 1 builds, and it matters because it collapses the gap between the real object and
probe_cao_triangle_frame.py's model to exactly two differences:

    (i)  SHARING   -- one frame carries every copy, instead of a private frame per copy
    (ii) CENTRALS  -- the 2^d gauge vertices m(g), which no two-copy model has at all

section 6a.1 listed (ii) as a channel the ensemble has and the model lacks, and left it unmeasured.
With a 2-element gauge it becomes a one-line ablation, because the ONLY thing the centrals do for the
rest of the graph is make the frame types absolute (m(0) is individualized, and m(g) touches
f(k, g_k)).  So:

    FULL      all 2^d copies + all 2^d centrals, m(0) individualized
    ABLATED   all 2^d copies, NO centrals, frame vertices coloured by type outright
    TWOCOPY   two copies only, shared frame, frame coloured by type outright

If FULL and ABLATED induce the same partition on payload pairs, channel (ii) is EMPTY and the
centrals are analytically removable -- which would repair the model in the direction of section 4 and
section 5.1's kills.  If TWOCOPY (restricted to its two copies) is strictly finer than FULL, channel
(i) over-separates at 2-WL, which is the 1-WL finding of section 6a repeated one level up.

Everything is compared as a PARTITION of payload x payload pairs, never as a single verdict -- at
L = 4 every pair of non-isomorphic copies separates under all three models, so a separation verdict
cannot discriminate and the fine structure is the only signal.  (section 7 filter 7.)
"""

import sys
from itertools import combinations

L = int(sys.argv[1]) if len(sys.argv) > 1 else 4
PAIRS = list(combinations(range(L), 2))
NS = len(PAIRS)
NC = 1 << NS
SLOT = {}
for k, (i, j) in enumerate(PAIRS):
    SLOT[(i, j)] = SLOT[(j, i)] = k


def build(copies, centrals):
    """vertices: ('p', c, i) | ('f', k, t) | ('m', g).  Returns verts, adjset, vcol."""
    verts = [('p', c, i) for c in copies for i in range(L)]
    verts += [('f', k, t) for k in range(NS) for t in (0, 1)]
    if centrals:
        verts += [('m', g) for g in range(NC)]
    adj = set()

    def add(u, w):
        adj.add((u, w))
        adj.add((w, u))

    for c in copies:
        for a in range(L):
            for b in range(a + 1, L):
                add(('p', c, a), ('p', c, b))                    # clique payload
        for a in range(L):
            for b in range(L):
                if a != b:
                    k = SLOT[(a, b)]
                    add(('p', c, a), ('f', k, (c >> k) & 1))
    for k in range(NS):
        add(('f', k, 0), ('f', k, 1))
    if centrals:
        for g in range(NC):
            for k in range(NS):
                add(('m', g), ('f', k, (g >> k) & 1))

    vcol = {}
    for v in verts:
        if v[0] == 'p':
            vcol[v] = 0
        elif v[0] == 'f':
            # with centrals, the type is EARNED from the individualized m(0); without them it is
            # handed over, which is precisely the thing being ablated.
            vcol[v] = 1 if centrals else (1 + v[2])
        else:
            vcol[v] = 3
    if centrals:
        vcol[('m', 0)] = 4                                       # individualize m(0)
    return verts, adj, vcol


def wl2(verts, adj, vcol, tag):
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
    rnd = 0
    while True:
        rnd += 1
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
            print(f'  [{tag}] {n} vertices, stable after {rnd} rounds, {ncol} pair colours',
                  flush=True)
            return {(x, y): col[idx[x] * n + idx[y]] for x in verts for y in verts
                    if x[0] == 'p' and y[0] == 'p'}
        col, ncol = new, len(table)


def compare(name_a, pa, name_b, pb, keys):
    """refinement relation between two partitions of the same key set"""
    a2b, b2a = {}, {}
    a_ref_b = b_ref_a = True
    for k in keys:
        x, y = pa[k], pb[k]
        if a2b.setdefault(x, y) != y:
            a_ref_b = False
        if b2a.setdefault(y, x) != x:
            b_ref_a = False
    na = len({pa[k] for k in keys})
    nb = len({pb[k] for k in keys})
    if a_ref_b and b_ref_a:
        rel = 'IDENTICAL'
    elif a_ref_b:
        rel = f'{name_a} strictly FINER'
    elif b_ref_a:
        rel = f'{name_b} strictly FINER'
    else:
        rel = 'INCOMPARABLE'
    print(f'  {name_a} ({na} colours) vs {name_b} ({nb} colours): {rel}')
    return rel


if __name__ == '__main__':
    allc = list(range(NC))
    print(f'L={L}, {NS} slots, {NC} copies', flush=True)

    print('FULL (all copies + all centrals, m(0) individualized):', flush=True)
    full = wl2(*build(allc, True), 'full')
    print('ABLATED (all copies, no centrals, frame types given):', flush=True)
    abl = wl2(*build(allc, False), 'ablated')

    keys = [(x, y) for x in [('p', c, i) for c in allc for i in range(L)]
            for y in [('p', c, i) for c in allc for i in range(L)]]
    print('\n--- channel (ii): are the CENTRALS worth anything at 2-WL? ---')
    compare('FULL', full, 'ABLATED', abl, keys)

    print('\n--- channel (i): does the TWO-COPY model over-separate at 2-WL? ---')
    verdicts = {}
    import io
    import contextlib
    for (c, cp) in combinations(allc, 2):
        with contextlib.redirect_stdout(io.StringIO()):
            two = wl2(*build([c, cp], False), '')
        sub = [(x, y) for x in [('p', d, i) for d in (c, cp) for i in range(L)]
               for y in [('p', d, i) for d in (c, cp) for i in range(L)]]
        with contextlib.redirect_stdout(io.StringIO()):
            rel = compare('TWOCOPY', two, 'FULL', full, sub)
        verdicts[rel] = verdicts.get(rel, 0) + 1
    for r, n in sorted(verdicts.items(), key=lambda t: -t[1]):
        print(f'  {n:5d} / {NC*(NC-1)//2} copy pairs: {r}')
