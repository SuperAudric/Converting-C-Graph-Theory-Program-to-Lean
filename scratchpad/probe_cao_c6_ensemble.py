"""probe_cao_c6_ensemble.py -- the READER'S C6 CONSTRUCTION, built and measured exactly.

THE PROPOSAL (reader, 2026-08-16).  An ensemble around a symmetry group other than S_L:

  * 15 gauges (= the 15 slots of a 6-label set), two frame vertices each, types distinguished
    ("the ground state is individualized by default"), no central vertices;
  * a RULER: the smallest asymmetric 6-vertex graph = a triangle with pendant paths of lengths
    0, 1, 2 -- encoded through the frame in the usual way;
  * the symmetry preserved is the 6 ROTATIONS of C6, not all of S_6: add one encoded copy of the
    ruler per rotation;
  * likewise one encoded copy per rotation of a second, payload graph.

THE READER'S ARGUMENT, which this tests.  "Every vertex has a ruler that calls it vertex 1, another
that calls it vertex 2, and so on.  The payload can't draw from it which vertex is which -- you can
work out which one is +k in the cycle, but that is meta-graph structure you already knew from the
rulers.  There should be literally no useful cross-clique information provided by the ruler."

WHY THE OBJECT IS DECISIVE.  The rotations act SIMPLY TRANSITIVELY on the copies, so individualizing
any payload vertex kills the whole group: Aut_v is trivial and CAO then demands that the 2-WL closure
DISCRETIZE the entire graph.  That is a far harsher demand than in the full ensemble (where Aut_v is
still S_L).  So this construction is a strictly harder test of the ruler mechanism than the object it
was designed to criticize -- if the mechanism is vacuous, this graph will not discretize.

⚠ Start colouring = the exact Aut-ORBIT partition, per the CAO hypothesis (doc section 0), not the
plain WL colouring.  Automorphisms are computed exactly (VF2), not assumed to be the rotations.
"""

import sys
import time
from itertools import combinations

import networkx as nx

ROT = 6
LAB = list(range(6))
PAIRS = list(combinations(LAB, 2))
SLOT = {}
for _k, (_i, _j) in enumerate(PAIRS):
    SLOT[(_i, _j)] = SLOT[(_j, _i)] = _k

# the smallest asymmetric graph: triangle 0-1-2, pendant 3 on 1, path 2-4-5
RULER = [(0, 1), (1, 2), (0, 2), (1, 3), (2, 4), (4, 5)]

PAYLOADS = {
    'C6':     [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0)],
    '2C3':    [(0, 2), (2, 4), (4, 0), (1, 3), (3, 5), (5, 1)],
    'K33':    [(0, 1), (0, 3), (0, 5), (2, 1), (2, 3), (2, 5), (4, 1), (4, 3), (4, 5)],
    'prism':  [(0, 2), (2, 4), (4, 0), (1, 3), (3, 5), (5, 1), (0, 1), (2, 3), (4, 5)],
    'P6':     [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)],
    'ruler2': [(0, 1), (1, 2), (0, 2), (1, 3), (2, 4), (4, 5)],
}


def rotate(edges, h):
    return frozenset(frozenset(((x + h) % 6, (y + h) % 6)) for (x, y) in edges)


def build(payload_name, clique=True, tags=('R', 'P')):
    """The object.  Vertices: ('f', slot, type) | ('p', tag, h, label).

    `tags` is the ABLATION handle: ('R','P') = the reader's object, ('P',) = the same object with the
    ruler copies deleted.  If the ruler contributes "literally no useful cross-clique information",
    deleting it must not change what the closure can separate."""
    G = nx.Graph()
    for k in range(len(PAIRS)):
        for t in (0, 1):
            G.add_node(('f', k, t), kind=f'f{t}')          # types distinguished = ground state indiv.
        G.add_edge(('f', k, 0), ('f', k, 1))

    copies = {}
    for tag, base in (('R', RULER), ('P', PAYLOADS[payload_name])):
        if tag not in tags:
            continue
        for h in range(ROT):
            copies[(tag, h)] = rotate(base, h)

    for (tag, h), eset in copies.items():
        for x in LAB:
            G.add_node(('p', tag, h, x), kind=f'p{tag}')
        if clique:
            for x, y in combinations(LAB, 2):
                G.add_edge(('p', tag, h, x), ('p', tag, h, y))
        for x in LAB:
            for y in LAB:
                if x == y:
                    continue
                k = SLOT[(x, y)]
                t = 1 if frozenset((x, y)) in eset else 0
                G.add_edge(('p', tag, h, x), ('f', k, t))
    return G, copies


def automorphisms(G):
    gm = nx.algorithms.isomorphism.GraphMatcher(
        G, G, node_match=lambda a, b: a['kind'] == b['kind'])
    return list(gm.isomorphisms_iter())


def orbits_from(auts, nodes):
    idx = {v: i for i, v in enumerate(nodes)}
    par = list(range(len(nodes)))

    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x

    for a in auts:
        for v, w in a.items():
            rv, rw = find(idx[v]), find(idx[w])
            if rv != rw:
                par[rv] = rw
    return [find(idx[v]) for v in nodes]


def wl2(nodes, adj, start, individualize=None):
    """2-WL from a given vertex start colouring (the CAO start = the orbit partition)."""
    n = len(nodes)
    s = list(start)
    if individualize is not None:
        s = [c * 2 + (1 if i == individualize else 0) for i, c in enumerate(s)]
    col = [[0] * n for _ in range(n)]
    for u in range(n):
        for v in range(n):
            col[u][v] = (s[u], s[v], 1 if u == v else 0, 1 if adj[u][v] else 0)
    tab = {k: i for i, k in enumerate(sorted({col[u][v] for u in range(n) for v in range(n)},
                                             key=repr))}
    col = [[tab[col[u][v]] for v in range(n)] for u in range(n)]

    prev = -1
    for _ in range(4 * n):
        new = [[None] * n for _ in range(n)]
        for u in range(n):
            cu = col[u]
            for v in range(n):
                new[u][v] = (col[u][v], tuple(sorted((cu[z], col[z][v]) for z in range(n))))
        keys = sorted({new[u][v] for u in range(n) for v in range(n)}, key=repr)
        tab = {k: i for i, k in enumerate(keys)}
        col = [[tab[new[u][v]] for v in range(n)] for u in range(n)]
        if len(keys) == prev:
            break
        prev = len(keys)
    return [col[u][u] for u in range(n)], col


def report(payload_name, tags=('R', 'P')):
    t0 = time.time()
    G, copies = build(payload_name, tags=tags)
    nodes = sorted(G.nodes(), key=repr)
    n = len(nodes)
    idx = {v: i for i, v in enumerate(nodes)}
    adj = [[False] * n for _ in range(n)]
    for u, v in G.edges():
        adj[idx[u]][idx[v]] = adj[idx[v]][idx[u]] = True

    distinct = len(set(copies.values()))
    auts = automorphisms(G)
    orb = orbits_from(auts, nodes)
    norb = len(set(orb))

    print(f'\n=== payload = {payload_name} ===')
    print(f'  vertices {n}  (30 frame + 36 ruler + 36 payload)   distinct copies {distinct}/12')
    print(f'  |Aut| = {len(auts)}   orbits = {norb}')
    pay_idx = [i for i, v in enumerate(nodes) if v[0] == 'p']
    print(f'  payload-vertex orbits = {len({orb[i] for i in pay_idx})}  (72 payload vertices)')

    # CAO: start from the orbit partition, individualize one vertex, close under 2-WL
    reps = {}
    for i in pay_idx:
        reps.setdefault(orb[i], i)
    worst = None
    for o, i in sorted(reps.items()):
        cells, _ = wl2(nodes, adj, orb, individualize=i)
        stab = [a for a in auts if a[nodes[i]] == nodes[i]]
        sorb = orbits_from(stab, nodes)
        mixed = {}
        for c, s in zip(cells, sorb):
            mixed.setdefault(c, set()).add(s)
        nmix = sum(1 for v in mixed.values() if len(v) > 1)
        tag = nodes[i]
        line = (f'    individualize {str(tag):<22} |Aut_v|={len(stab):>3}  '
                f'cells {len(set(cells)):>3}  Aut_v-orbits {len(set(sorb)):>3}  '
                f'MIXED {nmix}')
        print(line + ('   <<< CAO FAILS' if nmix else ''))
        if nmix and worst is None:
            worst = (tag, nmix)
    print(f'  ({time.time() - t0:.1f}s)')
    return worst


if __name__ == '__main__':
    which = sys.argv[1:] or ['C6', '2C3', 'K33', 'prism', 'P6', 'ruler2']
    bad = []
    for name in which:
        w = report(name)
        if w:
            bad.append((name, w))
    print('\n' + '=' * 70)
    print('CAO FAILURES:', bad if bad else 'none')
