"""probe_cao_mfrozen.py — THE FAITHFUL TEST, poly-size.  M_frozen(G) for any payload graph G.

What sections 6d + the freeze result establish (L=4 at 2-WL on every channel; L=6 at 1-WL
elementwise): the ensemble's k-WL colouring of a copy equals the k-WL colouring of

    M_frozen(G)  =  K_L payload  +  2d frame vertices,  d = C(L,2)
                    f(k,0) ~ f(k,1),   p(i) ~ f(k, G_k)  for every slot k containing i
                    frame VERTEX colours frozen at t
                    frame-frame PAIR colours frozen at (t, t', |k ∩ k'|)   [2-WL only]

|M| = L + 2d = L^2.   Shrikhande/rook L=16 -> 256.   CFI[K4] L=28 -> 784.   CFI[K5] L=60 -> 3540.

⚠ THE GAP THIS FIXES.  probe_cao_triangle_frame.py put BOTH payloads in one object.  The ensemble's
job is to make cross-payload information uniform -- every other graph is present, so stepping off a
payload onto the frame reaches every alternative and carries nothing back.  A two-copy object gives
WL ONE specific other graph instead of every one, so exactly the channel that is supposed to be
uniform is not.  The fix is ONE copy per object; two objects are compared as a disjoint union.

⚠ Comparison uses a SHARED intern table with LOCKSTEP rounds rather than an explicit disjoint union.
That is equivalent (components are independent) and it keeps n at |M| instead of 2|M|, which is an
8x saving in the n^3 inner loop.  Colours from different round counts are NOT comparable (8(e)).
"""

import sys
from itertools import combinations

ROUNDS = 8


def build_m(L, edges):
    """edges: a set of frozenset({i,j}).  Returns (verts, adjset, vcol, frame_class)."""
    pairs = list(combinations(range(L), 2))
    verts = [('p', i) for i in range(L)] + [('f', k, t) for k in range(len(pairs)) for t in (0, 1)]
    adj = set()

    def add(u, w):
        adj.add((u, w))
        adj.add((w, u))

    for a in range(L):
        for b in range(a + 1, L):
            add(('p', a), ('p', b))                       # clique payload: adjacency is NOT here
    for k, (i, j) in enumerate(pairs):
        t = 1 if frozenset({i, j}) in edges else 0
        add(('p', i), ('f', k, t))
        add(('p', j), ('f', k, t))
        add(('f', k, 0), ('f', k, 1))
    vcol = {v: (0 if v[0] == 'p' else 1 + v[2]) for v in verts}   # frame vertices frozen at t
    return verts, adj, vcol, pairs


def wl2_frozen(L, edges, intern, tag):
    verts, adj, vcol, pairs = build_m(L, edges)
    n = len(verts)
    idx = {v: i for i, v in enumerate(verts)}
    col = [0] * (n * n)
    frozen = [False] * (n * n)
    for x in verts:
        a = idx[x]
        for y in verts:
            p = a * n + idx[y]
            if x[0] == 'f' and y[0] == 'f':
                ov = len(set(pairs[x[1]]) & set(pairs[y[1]]))
                key = ('F', x[2], y[2], ov)               # the 12 orbit classes, frozen
                frozen[p] = True
            else:
                key = (x == y, (x, y) in adj, vcol[x], vcol[y])
            col[p] = intern.setdefault(key, len(intern))
    rng = range(n)
    for r in range(ROUNDS):
        C = max(col) + 1
        colT = [0] * (n * n)
        for a in rng:
            base = a * n
            for b in rng:
                colT[b * n + a] = col[base + b]
        new = [0] * (n * n)
        for a in rng:
            ra = col[a * n:(a + 1) * n]
            for b in rng:
                p = a * n + b
                if frozen[p]:
                    new[p] = col[p]
                    continue
                rb = colT[b * n:(b + 1) * n]
                cnt = {}
                for z in rng:
                    k = ra[z] * C + rb[z]
                    cnt[k] = cnt.get(k, 0) + 1
                new[p] = intern.setdefault((col[p], tuple(sorted(cnt.items()))), len(intern))
        col = new
        print(f'    [{tag}] round {r+1}: {len(set(col))} pair colours', flush=True)
    prof = {}
    for x in verts:
        if x[0] != 'p':
            continue
        for y in verts:
            if y[0] == 'p':
                c = col[idx[x] * n + idx[y]]
                prof[c] = prof.get(c, 0) + 1
    return prof


def shrikhande_rook():
    V = [(i, j) for i in range(4) for j in range(4)]
    ix = {v: k for k, v in enumerate(V)}
    S = set()
    for (i, j) in V:
        for (a, b) in [(1, 0), (3, 0), (0, 1), (0, 3), (1, 1), (3, 3)]:
            S.add(frozenset({ix[(i, j)], ix[((i + a) % 4, (j + b) % 4)]}))
    R = set()
    for u in V:
        for w in V:
            if u != w and (u[0] == w[0] or u[1] == w[1]):
                R.add(frozenset({ix[u], ix[w]}))
    return 16, S, R


if __name__ == '__main__':
    which = sys.argv[1] if len(sys.argv) > 1 else 'sr'
    if which == 'sr':
        L, A, B = shrikhande_rook()
        na, nb = 'Shrikhande', 'rook4x4'
    else:
        from probe_cao_cfi_bare import cfi_ve
        m = int(which)
        (V1, E1), (V2, E2) = cfi_ve(m, ()), cfi_ve(m, (0,))
        L, A, B = len(V1), E1, E2
        na, nb = f'CFI[K{m}] plain', f'CFI[K{m}] twisted'
    print(f'M_frozen: L={L}, |M| = {L + L*(L-1)} vertices each', flush=True)
    intern = {}
    print(f'  {na}:', flush=True)
    pa = wl2_frozen(L, A, intern, na)
    print(f'  {nb}:', flush=True)
    pb = wl2_frozen(L, B, intern, nb)
    print(f'  control ({na} again):', flush=True)
    pc = wl2_frozen(L, A, intern, 'control')
    print(f'\n  CONTROL separated (must be False): {pa != pc}')
    print(f'  ==> M_frozen 2-WL separates {na} from {nb}: {pa != pb}')
