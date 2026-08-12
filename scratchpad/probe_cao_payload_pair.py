"""probe_cao_payload_pair.py — is {Shrikhande, rook 4x4} a usable 2-WL-blind PAYLOAD?

The proposed lift wants a pair of structures 2-WL cannot separate, selected by a carrier,
so that the carrier's branch stays fused.  But the CAO test INDIVIDUALIZES a vertex before
refining.  So the property the payload needs is not "2-WL cannot distinguish G from H"
but "2-WL cannot distinguish the ONE-POINT EXTENSIONS of G and H".

Measured here, by 2-WL on the disjoint union (the standard equivalence test):
  A. G vs H, plain
  B. G vs H, one vertex individualized in each        <- the property the test actually needs
  C. subdivisions of G vs H, plain                    <- the reader's own "intermediate vertices" worry
  D. subdivisions, one original vertex individualized in each
"""


def shrikhande():
    V = [(i, j) for i in range(4) for j in range(4)]
    S = [(1, 0), (3, 0), (0, 1), (0, 3), (1, 1), (3, 3)]
    E = set()
    for (i, j) in V:
        for (a, b) in S:
            w = ((i + a) % 4, (j + b) % 4)
            E.add(frozenset({(i, j), w}))
    return V, E


def rook():
    V = [(i, j) for i in range(4) for j in range(4)]
    E = set()
    for u in V:
        for w in V:
            if u != w and (u[0] == w[0] or u[1] == w[1]):
                E.add(frozenset({u, w}))
    return V, E


def subdivide(V, E):
    V2 = [('v', x) for x in V]
    E2 = set()
    for e in E:
        a, b = sorted(e)
        m = ('e', a, b)
        V2.append(m)
        E2.add(frozenset({('v', a), m}))
        E2.add(frozenset({('v', b), m}))
    return V2, E2


def union(g1, g2, mark1=None, mark2=None):
    (V1, E1), (V2, E2) = g1, g2
    verts = [(1, x) for x in V1] + [(2, x) for x in V2]
    ecol = {}
    for tag, E in ((1, E1), (2, E2)):
        for e in E:
            a, b = tuple(e)
            ecol[((tag, a), (tag, b))] = 1
            ecol[((tag, b), (tag, a))] = 1
    marks = set()
    if mark1 is not None:
        marks.add((1, mark1))
    if mark2 is not None:
        marks.add((2, mark2))
    return verts, ecol, marks


def wl2(verts, ecol, marks):
    n = len(verts)
    idx = {v: i for i, v in enumerate(verts)}
    col = {}
    for x in verts:
        for y in verts:
            col[(idx[x], idx[y])] = (x == y, ecol.get((x, y), 0),
                                     x in marks, y in marks)
    rng = range(n)
    while True:
        sig = {}
        for a in rng:
            for b in rng:
                sig[(a, b)] = (col[(a, b)],
                               tuple(sorted((col[(a, z)], col[(z, b)]) for z in rng)))
        rk = {s: i for i, s in enumerate(sorted(set(sig.values()), key=repr))}
        new = {p: (rk[sig[p]],) for p in sig}
        if len(set(new.values())) == len(set(col.values())):
            return col, idx
        col = new


def equivalent(g1, g2, m1=None, m2=None):
    """True iff 2-WL gives the two components identical pair-colour multisets."""
    verts, ecol, marks = union(g1, g2, m1, m2)
    col, idx = wl2(verts, ecol, marks)
    prof = {1: {}, 2: {}}
    for x in verts:
        for y in verts:
            if x[0] == y[0]:
                d = prof[x[0]]
                c = col[(idx[x], idx[y])]
                d[c] = d.get(c, 0) + 1
    return prof[1] == prof[2], prof


def diag_cells(g, m=None):
    """2-WL diagonal cell sizes of a single graph, optionally with m individualized."""
    V, E = g
    ecol = {}
    for e in E:
        a, b = tuple(e)
        ecol[(a, b)] = ecol[(b, a)] = 1
    col, idx = wl2(V, ecol, {m} if m is not None else set())
    cells = {}
    for v in V:
        c = col[(idx[v], idx[v])]
        cells[c] = cells.get(c, 0) + 1
    return sorted(cells.values())


if __name__ == '__main__':
    S, R = shrikhande(), rook()
    print('Shrikhande |V|,|E| =', len(S[0]), len(S[1]), ' rook |V|,|E| =', len(R[0]), len(R[1]))

    eq, _ = equivalent(S, R)
    print('A. 2-WL, plain                     : equivalent =', eq)

    eq, _ = equivalent(S, R, m1=(0, 0), m2=(0, 0))
    print('B. 2-WL, one vertex individualized : equivalent =', eq)
    print('     Shrikhande extension cells', diag_cells(S, (0, 0)),
          '| rook extension cells', diag_cells(R, (0, 0)))

    Ss, Rs = subdivide(*S), subdivide(*R)
    eq, _ = equivalent(Ss, Rs)
    print('C. 2-WL, subdivided, plain         : equivalent =', eq)

    eq, _ = equivalent(Ss, Rs, m1=('v', (0, 0)), m2=('v', (0, 0)))
    print('D. 2-WL, subdivided + individualized: equivalent =', eq)
