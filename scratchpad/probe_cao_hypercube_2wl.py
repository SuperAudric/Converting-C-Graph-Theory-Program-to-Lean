"""probe_cao_hypercube_2wl.py — does the Q4 carrier construction survive 2-WL?

Reduced model of probe_cao_hypercube.py: the direction-i edge gadget (a K_{i+1} joined to
both endpoints) is replaced by an EDGE COLOUR i.  112 vertices instead of 352.
CALIBRATION: 1-WL on the reduced model must reproduce the full graph's verdict
(16 corner cells of 3, four carrier cells of 12, each splitting 6+6 under Aut_v).

Then 2-WL (pair colouring, m_0 individualized) on the same object.
"""

from probe_cao_hypercube import cosets, patterns, key, COPIES

ALL = 15
EC_CUBE = {i: i + 1 for i in range(4)}   # direction i -> edge colour
EC_CENTRE = 5
EC_CARR = 6
BITS = [1, 2, 4, 8]


def build_reduced():
    ecol, verts = {}, []
    for p in range(16):
        verts.append(('centre', p))
        for c in COPIES:
            verts.append(('corner', p, c))
    for R in cosets():
        for phi in patterns(R):
            verts.append(key(phi))

    def put(u, w, c):
        ecol[(u, w)] = c
        ecol[(w, u)] = c

    for p in range(16):
        for c in COPIES:
            put(('centre', p), ('corner', p, c), EC_CENTRE)
        for i, b in enumerate(BITS):
            q = p ^ b
            if p < q:
                for c in COPIES:
                    put(('corner', p, c), ('corner', q, c), EC_CUBE[i])
    for R in cosets():
        for phi in patterns(R):
            for pos, c in phi.items():
                put(key(phi), ('corner', pos, c), EC_CARR)
    return verts, ecol


def wl1(verts, ecol, indiv):
    col = {v: (v == indiv,) for v in verts}
    nbr = {v: [] for v in verts}
    for (u, w), c in ecol.items():
        nbr[u].append((w, c))
    while True:
        sig = {v: (col[v], tuple(sorted((c, col[w]) for w, c in nbr[v]))) for v in verts}
        rk = {s: i for i, s in enumerate(sorted(set(sig.values()), key=repr))}
        new = {v: (rk[sig[v]],) for v in verts}
        if len(set(new.values())) == len(set(col.values())):
            return col
        col = new


def wl2(verts, ecol, indiv):
    n = len(verts)
    idx = {v: i for i, v in enumerate(verts)}
    col = {}
    for x in verts:
        for y in verts:
            col[(idx[x], idx[y])] = (x == y, ecol.get((x, y), 0), x == indiv, y == indiv)
    rng = range(n)
    rounds = 0
    while True:
        rounds += 1
        sig = {}
        for a in rng:
            for b in rng:
                sig[(a, b)] = (col[(a, b)],
                               tuple(sorted((col[(a, z)], col[(z, b)]) for z in rng)))
        rk = {s: i for i, s in enumerate(sorted(set(sig.values()), key=repr))}
        new = {p: (rk[sig[p]],) for p in sig}
        if len(set(new.values())) == len(set(col.values())):
            return col, idx, rounds
        col = new


def cells(col, verts, keep):
    out = {}
    for v in verts:
        if keep(v):
            out.setdefault(col[v], []).append(v)
    return out


if __name__ == '__main__':
    verts, ecol = build_reduced()
    m0 = ('centre', 0)
    g1 = key({3: 0, 12: 0, 5: 1, 10: 2})
    g2 = key({3: 1, 12: 2, 5: 0, 10: 0})
    print('reduced model:', len(verts), 'vertices')

    c1 = wl1(verts, ecol, m0)
    print('CALIBRATION 1-WL  corner cells',
          sorted(len(x) for x in cells(c1, verts, lambda v: v[0] == 'corner').values()),
          '| carrier cells',
          sorted(len(x) for x in cells(c1, verts, lambda v: v[0] == 'carr').values()),
          '| g1,g2 same cell:', c1[g1] == c1[g2])

    col2, idx, rounds = wl2(verts, ecol, m0)
    diag = {v: col2[(idx[v], idx[v])] for v in verts}
    print(f'2-WL stabilized in {rounds} rounds')
    print('2-WL  corner cells',
          sorted(len(x) for x in cells(diag, verts, lambda v: v[0] == 'corner').values()),
          '| carrier cells',
          sorted(len(x) for x in cells(diag, verts, lambda v: v[0] == 'carr').values()))
    print('2-WL separates g1 from g2:', diag[g1] != diag[g2])
