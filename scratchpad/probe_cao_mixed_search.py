"""probe_cao_mixed_search.py -- find the CHEAPEST graph carrying a 2-WL mixed cell.

The reader's proposed test (2026-08-16) attaches a rigid ruler bijectively to a graph X that has a
2-WL mixed cell, and closes the ruler family under the cell-preserving group so that the family is
built from WL-computable data only (no Aut knowledge -> not circular).  Its cost is

    |X| * (1 + prod_over_cells |cell|!)

so the test is affordable only if every cell is SMALL.  A mixed cell needs two vertices that 2-WL
cannot separate but Aut does not identify, so the cheapest possible shape is a graph that is RIGID
(or nearly so) with a 2-WL cell of size 2: then prod |cell|! = 2 and the whole object is tiny.

This searches for that.  Reported per graph: the 2-WL cell partition, the Aut-orbit partition, which
cells are mixed, and the cost prod |cell|!.
"""

import sys
from itertools import combinations

import networkx as nx


def wl2_cells(n, adj):
    """2-WL (coherent closure) pair colouring; returns the diagonal cell partition as a tuple."""
    col = [[0 if u == v else (1 if adj[u][v] else 2) for v in range(n)] for u in range(n)]
    ncls = len({col[u][v] for u in range(n) for v in range(n)})
    for _ in range(n * n + 2):
        cand = [[(col[u][v], tuple(sorted((col[u][z], col[z][v]) for z in range(n))))
                 for v in range(n)] for u in range(n)]
        keys = sorted({cand[u][v] for u in range(n) for v in range(n)}, key=repr)
        tab = {k: i for i, k in enumerate(keys)}
        col = [[tab[cand[u][v]] for v in range(n)] for u in range(n)]
        m = len(keys)
        if m == ncls:
            break
        ncls = m
    return col


def part_of(labels):
    d = {}
    for v, c in enumerate(labels):
        d.setdefault(c, []).append(v)
    return sorted(tuple(g) for g in d.values())


def orbits(G):
    n = G.number_of_nodes()
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    gm = nx.algorithms.isomorphism.GraphMatcher(G, G)
    cnt = 0
    for m in gm.isomorphisms_iter():
        cnt += 1
        for a, b in m.items():
            ra, rb = find(a), find(b)
            if ra != rb:
                parent[ra] = rb
        if cnt > 200000:
            break
    return part_of([find(v) for v in range(n)]), cnt


def cost(cells):
    import math
    p = 1
    for c in cells:
        p *= math.factorial(len(c))
    return p


def analyse(G, name):
    n = G.number_of_nodes()
    adj = [[G.has_edge(u, v) for v in range(n)] for u in range(n)]
    col = wl2_cells(n, adj)
    cells = part_of([col[v][v] for v in range(n)])
    orbs, naut = orbits(G)
    omap = {}
    for i, o in enumerate(orbs):
        for v in o:
            omap[v] = i
    mixed = [c for c in cells if len({omap[v] for v in c}) > 1]
    return dict(name=name, n=n, cells=cells, orbits=orbs, mixed=mixed,
                cost=cost(cells), naut=naut)


if __name__ == '__main__':
    from networkx.generators.atlas import graph_atlas_g
    best = None
    hits = 0
    for i, G in enumerate(graph_atlas_g()):
        n = G.number_of_nodes()
        if n < 3 or not nx.is_connected(G):
            continue
        G = nx.convert_node_labels_to_integers(G)
        r = analyse(G, f'atlas#{i}')
        if r['mixed']:
            hits += 1
            print('MIXED', r['name'], 'n=', r['n'], 'cost=', r['cost'],
                  'mixed=', r['mixed'], flush=True)
            if best is None or r['cost'] < best['cost']:
                best = r
    print(f'\natlas (all connected graphs on <= 7 vertices): {hits} with a 2-WL mixed cell')
    if best:
        print('cheapest:', best)
