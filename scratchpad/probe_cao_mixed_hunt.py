"""probe_cao_mixed_hunt.py -- hunt for a CHEAP 2-WL mixed cell (see probe_cao_mixed_search.py).

Cost of the reader's construction is prod over cells of |cell|!, so we want a mixed cell in a graph
whose cells are all SMALL -- i.e. a nearly-rigid graph that 2-WL still cannot resolve.

Orbits are computed by individualization + isomorphism test (n^2 cheap tests) rather than by
enumerating Aut, which blows up on the symmetric graphs that carry mixed cells.
"""

import math
import random
import sys
from itertools import combinations

import networkx as nx


def wl2_cells(n, adj):
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
    return [col[v][v] for v in range(n)]


def part_of(labels):
    d = {}
    for v, c in enumerate(labels):
        d.setdefault(c, []).append(v)
    return sorted(tuple(sorted(g)) for g in d.values())


def same_orbit(G, v, w):
    if v == w:
        return True
    A = G.copy(); B = G.copy()
    nx.set_node_attributes(A, {u: (1 if u == v else 0) for u in A}, 'c')
    nx.set_node_attributes(B, {u: (1 if u == w else 0) for u in B}, 'c')
    return nx.is_isomorphic(A, B, node_match=lambda a, b: a['c'] == b['c'])


def analyse(G):
    n = G.number_of_nodes()
    adj = [[G.has_edge(u, v) for v in range(n)] for u in range(n)]
    cells = part_of(wl2_cells(n, adj))
    cost = 1
    for c in cells:
        cost *= math.factorial(len(c))
    mixed = []
    for c in cells:
        if len(c) == 1:
            continue
        rep = c[0]
        for other in c[1:]:
            if not same_orbit(G, rep, other):
                mixed.append(c)
                break
    return cells, mixed, cost


def report(G, name):
    cells, mixed, cost = analyse(G)
    tag = 'MIXED' if mixed else '  ok '
    print(f'{tag} {name:34s} n={G.number_of_nodes():3d} cells={[len(c) for c in cells]}'
          f' cost={cost} mixed={[len(c) for c in mixed]}', flush=True)
    return mixed, cost


def rook44():
    G = nx.Graph()
    for i in range(4):
        for j in range(4):
            G.add_node(4 * i + j)
    for a in range(16):
        for b in range(a + 1, 16):
            if (a // 4 == b // 4) or (a % 4 == b % 4):
                G.add_edge(a, b)
    return G


def shrikhande():
    G = nx.Graph()
    S = {(1, 0), (3, 0), (0, 1), (0, 3), (1, 1), (3, 3)}
    for a in range(16):
        G.add_node(a)
    for a in range(16):
        for b in range(16):
            d = ((a // 4 - b // 4) % 4, (a % 4 - b % 4) % 4)
            if d in S:
                G.add_edge(a, b)
    return G


if __name__ == '__main__':
    print('=== known 2-WL-hard objects ===')
    R, S = rook44(), shrikhande()
    report(R, 'rook(4,4)')
    report(S, 'Shrikhande')
    report(nx.disjoint_union(R, S), 'rook(4,4) + Shrikhande')

    print('\n=== random search: rigid-ish graphs 2-WL cannot resolve ===')
    rng = random.Random(20260816)
    found = []
    trials = 0
    for n in range(8, 15):
        for _ in range(4000):
            trials += 1
            p = rng.choice([0.2, 0.3, 0.4, 0.5, 0.6])
            G = nx.gnp_random_graph(n, p, seed=rng.randint(0, 10 ** 9))
            if not nx.is_connected(G):
                continue
            adj = [[G.has_edge(u, v) for v in range(n)] for u in range(n)]
            cells = part_of(wl2_cells(n, adj))
            if all(len(c) == 1 for c in cells):
                continue
            _, mixed, cost = analyse(G)
            if mixed:
                found.append((cost, n, sorted(G.edges())))
                print(f'  MIXED n={n} cost={cost} cells={[len(c) for c in cells]}', flush=True)
    print(f'\nrandom: {trials} graphs sampled, {len(found)} with a mixed cell')

    print('\n=== random REGULAR graphs (where 2-WL actually struggles) ===')
    for n, d in [(8, 3), (10, 3), (10, 4), (12, 3), (12, 4), (12, 5), (14, 3), (14, 4),
                 (16, 3), (16, 5), (16, 6)]:
        best = None
        for _ in range(300):
            try:
                G = nx.random_regular_graph(d, n, seed=rng.randint(0, 10 ** 9))
            except Exception:
                break
            if not nx.is_connected(G):
                continue
            adj = [[G.has_edge(u, v) for v in range(n)] for u in range(n)]
            cells = part_of(wl2_cells(n, adj))
            if all(len(c) == 1 for c in cells):
                continue
            _, mixed, cost = analyse(G)
            if mixed and (best is None or cost < best[0]):
                best = (cost, [len(c) for c in cells])
        print(f'  n={n} d={d}: ' + (f'cheapest mixed cost={best[0]} cells={best[1]}'
                                    if best else 'none'), flush=True)
