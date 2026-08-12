"""probe_cao_gauge_decode.py — what can WL DECODE from a base-point-selected gauge?

Minimal faithful model of the reader's encoding, stripped to the mechanism:
  * payload  p0..p3, carrying NO intrinsic edges;
  * for each pair {i,j} a two-channel gadget ch(i,j,0), ch(i,j,1), both joined to p_i, p_j.
    The channels carry a TYPE label (channel 1 gets a pendant) -- without one, "the decoded
    graph" is not a defined object;
  * one central vertex m_g for EVERY gauge g in {0,1}^6, joined to ch(i,j,g_ij) for each pair.
    This is the reader's "add a central vertex for every flip" repair, in miniature.

Decoded graph at m_g := the graph on the payload whose edges are the pairs where m_g selects
the type-1 channel.  Individualize one central vertex and ask what the refinement recovers:

    1-WL : does it recover the decoded DEGREES?
    2-WL : does it recover the decoded ADJACENCY?

That fixes which rung of the ladder a payload pair has to be blind at, and hence whether a
small rung-1 experiment says anything about rung 2.
"""

from itertools import product

NP = 4
PAIRS = [(i, j) for i in range(NP) for j in range(i + 1, NP)]
# gauge making the decoded graph the path p0-p1-p2-p3
G0 = tuple(1 if e in [(0, 1), (1, 2), (2, 3)] else 0 for e in PAIRS)


def build():
    adj = {}

    def add(u, w):
        adj.setdefault(u, set()).add(w)
        adj.setdefault(w, set()).add(u)

    for i in range(NP):
        adj.setdefault(('p', i), set())
    for (i, j) in PAIRS:
        for t in (0, 1):
            add(('ch', i, j, t), ('p', i))
            add(('ch', i, j, t), ('p', j))
        add(('tag', i, j), ('ch', i, j, 1))          # the type label
    for g in product((0, 1), repeat=len(PAIRS)):
        m = ('m', g)
        adj.setdefault(m, set())
        for k, (i, j) in enumerate(PAIRS):
            add(m, ('ch', i, j, g[k]))
    return adj


def wl1(adj, indiv):
    col = {v: (v == indiv,) for v in adj}
    while True:
        sig = {v: (col[v], tuple(sorted(col[w] for w in adj[v]))) for v in adj}
        rk = {s: i for i, s in enumerate(sorted(set(sig.values()), key=repr))}
        new = {v: (rk[sig[v]],) for v in adj}
        if len(set(new.values())) == len(set(col.values())):
            return col
        col = new


def wl2(adj, indiv):
    verts = sorted(adj, key=repr)
    n = len(verts)
    idx = {v: i for i, v in enumerate(verts)}
    col = {}
    for x in verts:
        for y in verts:
            col[(idx[x], idx[y])] = (x == y, y in adj[x], x == indiv, y == indiv)
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


if __name__ == '__main__':
    adj = build()
    m0 = ('m', G0)
    decoded = {e for k, e in enumerate(PAIRS) if G0[k] == 1}
    deg = {i: sum(1 for (a, b) in decoded if i in (a, b)) for i in range(NP)}
    print('vertices', len(adj), '| decoded graph =', sorted(decoded), '| degrees', deg)

    c1 = wl1(adj, m0)
    groups = {}
    for i in range(NP):
        groups.setdefault(c1[('p', i)], []).append(i)
    print('1-WL payload classes        :', sorted(sorted(v) for v in groups.values()))
    print('   matches decoded degrees? :',
          sorted(sorted(v) for v in groups.values()) ==
          sorted(sorted(v for v in range(NP) if deg[v] == d)
                 for d in sorted(set(deg.values()))))

    col2, idx = wl2(adj, m0)
    edge_cols = {col2[(idx[('p', i)], idx[('p', j)])] for (i, j) in PAIRS if (i, j) in decoded}
    non_cols = {col2[(idx[('p', i)], idx[('p', j)])] for (i, j) in PAIRS if (i, j) not in decoded}
    print('2-WL payload pair colours   : decoded-edge', len(edge_cols),
          'classes, decoded-non-edge', len(non_cols), 'classes')
    print('   separates adjacency?     :', edge_cols.isdisjoint(non_cols))
