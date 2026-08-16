"""probe_cao_c6_ablate.py -- does the ruler contribute cross-clique information?  Reader's object.

The reader's claim (2026-08-16): "There should be literally no useful cross clique information
provided by the ruler", and "cross copy information is implicitly weaker than within copy as you have
to spend one pairing to traverse the ensemble frame."

That is a DIFFERENCE claim, so it is testable by ablation, and it does not need the orbit partition
(starting from the orbit partition would hand the answer over -- root cells are orbits by fiat).
Start from the PLAIN colouring (frame type 0 / frame type 1 / payload) and ask what 2-WL can
DISCOVER on its own, in three objects that differ only in what is present:

  (i)   shared frame + the 6 rotated payload copies + the 6 rotated ruler copies   [reader's object]
  (ii)  shared frame + the 6 rotated payload copies                                [ruler deleted]
  (iii) each copy with its OWN private frame, disjoint union                       [triangle frame]

(iii) is the "the triangle frame is applicable to the ensemble" model: no cross-copy channel exists
there at all, since different components share no vertices.

Reported: the number of cells 2-WL puts the 36 payload-copy vertices into, in each object, plus the
true Aut-orbit count for each object.  If (i) > (ii) = (iii), the ruler supplies separating power
across cliques that the disjoint model cannot see, measured in the reader's own construction.
"""

import sys
import time
from itertools import combinations

import networkx as nx
import numpy as np

import probe_cao_c6_ensemble as base

ROT, LAB, PAIRS, SLOT = base.ROT, base.LAB, base.PAIRS, base.SLOT


def build(payload_name, tags=('R', 'P'), shared=True):
    G = nx.Graph()
    copies = {}
    for tag, edges in (('R', base.RULER), ('P', base.PAYLOADS[payload_name])):
        if tag not in tags:
            continue
        for h in range(ROT):
            copies[(tag, h)] = base.rotate(edges, h)

    def frame(k, t, tag, h):
        return ('f', k, t) if shared else ('f', k, t, tag, h)

    for (tag, h), eset in copies.items():
        for k in range(len(PAIRS)):
            for t in (0, 1):
                G.add_node(frame(k, t, tag, h), kind=f'f{t}')
            G.add_edge(frame(k, 0, tag, h), frame(k, 1, tag, h))
        for x in LAB:
            G.add_node(('p', tag, h, x), kind='payload')          # tags NOT pre-separated
        for x, y in combinations(LAB, 2):
            G.add_edge(('p', tag, h, x), ('p', tag, h, y))
        for x in LAB:
            for y in LAB:
                if x == y:
                    continue
                k = SLOT[(x, y)]
                t = 1 if frozenset((x, y)) in eset else 0
                G.add_edge(('p', tag, h, x), frame(k, t, tag, h))
    return G


def wl2_np(n, adj, start):
    """exact 2-WL, numpy (the pure-Python one is O(n^3) per round in the interpreter and the
    disjoint objects reach n = 432)."""
    eye = np.eye(n, dtype=bool)
    s = np.asarray(start, dtype=np.int64)
    col = (((s[:, None] * (s.max() + 1) + s[None, :]) * 2 + eye) * 2 + adj).astype(np.int64)
    _, col = np.unique(col, return_inverse=True)
    col = col.reshape(n, n).astype(np.int64)
    prev = -1
    for _ in range(n):
        C = int(col.max()) + 1
        parts = []
        step = max(1, 4_000_000 // (n * n) or 1)
        for lo in range(0, n, step):
            hi = min(lo + step, n)
            k = np.sort(col[lo:hi, None, :] * C + col.T[None, :, :], axis=2)
            parts.append(np.concatenate([col[lo:hi][:, :, None], k], axis=2).reshape(-1, n + 1))
        rows = np.ascontiguousarray(np.concatenate(parts))
        v = rows.view([('', np.int64)] * (n + 1)).ravel()
        tab = np.unique(v)
        col = np.searchsorted(tab, v).reshape(n, n)
        if len(tab) == prev:
            break
        prev = len(tab)
    return col[np.arange(n), np.arange(n)]


def payload_cells(G, tag_wanted):
    nodes = sorted(G.nodes(), key=repr)
    n = len(nodes)
    idx = {v: i for i, v in enumerate(nodes)}
    adj = np.zeros((n, n), dtype=bool)
    for u, v in G.edges():
        adj[idx[u], idx[v]] = adj[idx[v], idx[u]] = True
    kinds = {}
    start = [kinds.setdefault(G.nodes[v]['kind'], len(kinds)) for v in nodes]
    cells = wl2_np(n, adj, start)
    sel = [i for i, v in enumerate(nodes) if v[0] == 'p' and v[1] == tag_wanted]
    return len({int(cells[i]) for i in sel}), len(sel), nodes, cells


def aut_orbit_count(G, tag_wanted, cap=200000):
    """⚠ Only usable on the SHARED objects.  A disjoint object with 6 (or 12) isomorphic components
    has |Aut| = (component group)^k * k!, which is billions -- VF2 enumerates for ever.  Returns
    (None, None) rather than hanging; the cell counts are what the ablation actually compares."""
    gm = nx.algorithms.isomorphism.GraphMatcher(
        G, G, node_match=lambda a, b: a['kind'] == b['kind'])
    auts = []
    for a in gm.isomorphisms_iter():
        auts.append(a)
        if len(auts) > cap:
            return None, None
    nodes = sorted(G.nodes(), key=repr)
    orb = base.orbits_from(auts, nodes)
    sel = [i for i, v in enumerate(nodes) if v[0] == 'p' and v[1] == tag_wanted]
    return len({orb[i] for i in sel}), len(auts)


def main():
    names = sys.argv[1:] or ['P6', 'prism', 'C6']
    for name in names:
        print(f'\n=== payload = {name} ===   (36 payload-copy vertices in every row)')
        print(f'  {"object":<44} {"|V|":>5} {"2-WL cells":>11} {"Aut-orbits":>11} {"|Aut|":>8}')
        rows = [
            ('(i)   shared frame, ruler PRESENT', ('R', 'P'), True),
            ('(ii)  shared frame, ruler DELETED', ('P',), True),
            ('(iii) private frames (triangle frame, disjoint)', ('P',), False),
            ('(iv)  private frames + ruler (control)', ('R', 'P'), False),
        ]
        for label, tags, shared in rows:
            t0 = time.time()
            G = build(name, tags=tags, shared=shared)
            cells, ncount, _, _ = payload_cells(G, 'P')
            orbs, naut = (aut_orbit_count(G, 'P') if shared else (None, None))
            flag = '' if (orbs is None or cells == orbs) else '   <-- MIXED CELLS'
            print(f'  {label:<44} {G.number_of_nodes():>5} {cells:>11} '
                  f'{"-" if orbs is None else orbs:>11} {"huge" if naut is None else naut:>8}'
                  f'{flag}   ({time.time() - t0:.0f}s)', flush=True)


if __name__ == '__main__':
    main()
