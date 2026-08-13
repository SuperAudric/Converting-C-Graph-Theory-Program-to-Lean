"""probe_cao_triangle_frame.py — the reader's triangle-frame test, both readings.

Model.  K16 with every edge {i,j} carrying a TRIANGLE vertex e_ij adjacent to i and j.
e_ij is coloured by the EDGE TYPE only -- "connected" or "disconnected" -- never given an
identity of its own.  That two-colour palette is the faithful abstraction of the full
construction's frame: after the central vertex is individualized the cube corners sit in
shared position-cells, and because the ensemble contains every colouring, nothing
copy-specific can accumulate on them.

  DISJOINT (the reader's spec): each copy carries its own 120 triangle vertices.
      16 + 120 = 136 per copy, 272 in the union.
  SHARED  : both copies hang off ONE frame -- slot {i,j} owns both corner-pairs
      (conn and disc, linked as one cube), and each copy attaches to the one matching
      its own edge set.  32 payload + 240 frame = 272.  This is the variant that can
      leak, because a cross-copy pair of payload vertices meets at a shared slot.

Neither model marks which component a vertex belongs to; separation must be earned.
"""

import sys
from probe_cao_payload_pair import shrikhande, rook

CONN, DISC = 1, 2


def edgeset(g):
    return {frozenset(e) for e in g[1]}


def build(mode):
    S, R = shrikhande(), rook()
    ES, ER = edgeset(S), edgeset(R)
    V = S[0]                                    # the 16 labels, shared indexing
    pairs = [(V[a], V[b]) for a in range(16) for b in range(a + 1, 16)]

    verts, typ, adj = [], {}, set()

    def add(u, w):
        adj.add((u, w))
        adj.add((w, u))

    for c in ('S', 'R'):
        for x in V:
            verts.append((c, x))
            typ[(c, x)] = 0
        for a in range(16):
            for b in range(a + 1, 16):
                add((c, V[a]), (c, V[b]))       # K16 inside each copy

    if mode == 'disjoint':
        for c, E in (('S', ES), ('R', ER)):
            for (i, j) in pairs:
                e = (c, 'e', i, j)
                verts.append(e)
                typ[e] = CONN if frozenset({i, j}) in E else DISC
                add(e, (c, i))
                add(e, (c, j))
    else:
        for (i, j) in pairs:
            f = {}
            for t in (CONN, DISC):
                e = ('e', i, j, t)
                verts.append(e)
                typ[e] = t
                f[t] = e
            add(f[CONN], f[DISC])               # the two corner-pairs of one cube
            for c, E in (('S', ES), ('R', ER)):
                t = CONN if frozenset({i, j}) in E else DISC
                add(f[t], (c, i))
                add(f[t], (c, j))
    return verts, typ, adj


def wl2(verts, typ, adj, freeze=False):
    """freeze=True pins every FRAME-FRAME pair colour at its orbit-level atom and never
    refines it.  Justification: WL cells are always unions of Aut-orbits, and in the full
    construction Aut_m contains the label symmetries, so a pair (corner in cube k, corner
    in cube k') can only ever be classified by (types, same cube?, share a label?).
    Letting those pairs refine by payload data -- which the small model otherwise does --
    hands 2-WL power the real object forbids.  Payload-frame and payload-payload pairs
    stay free; monotone, since frozen pairs are constant from round 0."""
    n = len(verts)
    idx = {v: i for i, v in enumerate(verts)}
    isframe = [v[0] == 'e' or (len(v) == 4 and v[1] == 'e') for v in verts]
    nbr = {v: {w for (u, w) in adj if u == v} for v in verts}
    col = [0] * (n * n)
    atoms, frozen = {}, [False] * (n * n)
    for x in verts:
        a = idx[x]
        for y in verts:
            b = idx[y]
            if freeze and isframe[a] and isframe[b]:
                if freeze == 'minimal':
                    # strictly COARSER than the Aut_m-orbit partition of frame pairs:
                    # types only, no same-cube and no share-a-label.  Gives 2-WL less
                    # than the real object, so a separation here is unambiguous.
                    k = ('F', x == y, typ[x], typ[y])
                else:
                    k = ('F', x == y, typ[x], typ[y],
                         x[:-1] == y[:-1] if len(x) == 4 and len(y) == 4 else False,
                         bool(nbr[x] & nbr[y]))
                frozen[a * n + b] = True
            else:
                k = (x == y, (x, y) in adj, typ[x], typ[y])
            col[a * n + b] = atoms.setdefault(k, len(atoms))
    rounds = 0
    while True:
        rounds += 1
        C = max(col) + 1
        colT = [0] * (n * n)
        for a in range(n):
            base = a * n
            for b in range(n):
                colT[b * n + a] = col[base + b]
        table, new = {}, [0] * (n * n)
        rng = range(n)
        for a in rng:
            ra = col[a * n:(a + 1) * n]
            for b in rng:
                rb = colT[b * n:(b + 1) * n]
                p = a * n + b
                if frozen[p]:
                    k = ('frozen', col[p])
                else:
                    k = (col[p], tuple(sorted(ra[z] * C + rb[z] for z in rng)))
                v = table.get(k)
                if v is None:
                    v = table[k] = len(table)
                new[p] = v
        if len(table) == len(set(col)):
            return col, idx, rounds
        col = new


def profile(col, idx, verts, tag):
    """multiset of pair colours over the payload vertices of one copy"""
    P = [v for v in verts if v[0] == tag and len(v) == 2]
    n = int(len(col) ** 0.5)
    out = {}
    for x in P:
        for y in P:
            c = col[idx[x] * n + idx[y]]
            out[c] = out.get(c, 0) + 1
    return out


if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'disjoint'
    # ⚠ freeze was previously not wired to argv, so only the two freeze=False rows of the doc's
    # section 4.2 table were reproducible from the committed file.  argv[2] in {none,orbit,minimal}.
    fz = {'none': False, 'orbit': True, 'minimal': 'minimal'}[sys.argv[2] if len(sys.argv) > 2
                                                              else 'none']
    verts, typ, adj = build(mode)
    print(f'[{mode}/freeze={fz}] {len(verts)} vertices', flush=True)
    col, idx, rounds = wl2(verts, typ, adj, fz)
    pS, pR = profile(col, idx, verts, 'S'), profile(col, idx, verts, 'R')
    n = len(verts)
    diagS = sorted(sum(1 for v in verts if v[0] == 'S' and len(v) == 2
                       and col[idx[v] * n + idx[v]] == c)
                   for c in {col[idx[v] * n + idx[v]] for v in verts
                             if v[0] == 'S' and len(v) == 2})
    diagR = sorted(sum(1 for v in verts if v[0] == 'R' and len(v) == 2
                       and col[idx[v] * n + idx[v]] == c)
                   for c in {col[idx[v] * n + idx[v]] for v in verts
                             if v[0] == 'R' and len(v) == 2})
    print(f'  stabilized in {rounds} rounds, {len(set(col))} pair colours')
    print(f'  Shrikhande copy: vertex cells {diagS}')
    print(f'  rook copy      : vertex cells {diagR}')
    print(f'  SEPARATED: {pS != pR}')
