"""probe_cao_ir_vs_wl.py -- is 2-WL the same thing as "pin a vertex, pin a second, refine"?

IR_k = individualize k vertices, run 1-WL (colour refinement), aggregate over all k-tuples.
Part 1 places IR_1 and IR_2 against 1-WL and 2-WL on the canonical 2-WL blind spot
(Shrikhande vs rook 4x4, both SRG(16,6,2,2)).
Part 2 asks what IR_2 does to the Q4 carrier construction: after pinning m_0, is there a
SECOND vertex whose individualization splits g1 from g2 under plain 1-WL?

Cross-graph colour names are made comparable by a shared signature table plus a fixed
round count; Part 2 compares within one graph, where naming is automatic.
"""

from probe_cao_hypercube_2wl import build_reduced
from probe_cao_wl_ladder import distinguishes, srg16
from probe_cao_hypercube import key

TBL = {}


def nbrs(n, ecol):
    nb = [[] for _ in range(n)]
    for (a, b), c in ecol.items():
        nb[a].append((b, c))
    return nb


def refine(n, nb, init, rounds):
    col = list(init)
    for _ in range(rounds):
        sig = [(col[v], tuple(sorted((c, col[w]) for w, c in nb[v]))) for v in range(n)]
        col = [TBL.setdefault(s, len(TBL)) for s in sig]
    return col


def ir_invariant(n, ecol, k, rounds):
    nb = nbrs(n, ecol)
    out = []
    if k == 0:
        return [tuple(sorted(refine(n, nb, [0] * n, rounds)))]
    if k == 1:
        for v in range(n):
            init = [0] * n
            init[v] = 1
            out.append(tuple(sorted(refine(n, nb, init, rounds))))
    else:
        for v in range(n):
            for u in range(n):
                if u == v:
                    continue
                init = [0] * n
                init[v], init[u] = 1, 2
                out.append(tuple(sorted(refine(n, nb, init, rounds))))
    return sorted(out)


if __name__ == '__main__':
    print('== PART 1: Shrikhande vs rook 4x4 (both SRG(16,6,2,2)) ==')
    (n1, e1), (n2, e2) = srg16('shrikhande'), srg16('rook')
    for k in (0, 1, 2):
        a, b = ir_invariant(n1, e1, k, 16), ir_invariant(n2, e2, k, 16)
        lab = {0: '1-WL          ', 1: 'IR_1 (pin 1)  ', 2: 'IR_2 (pin 2)  '}[k]
        print(f'  {lab}: {"DISTINGUISHED" if a != b else "blind"}')
    print(f'  2-WL          : '
          f'{"DISTINGUISHED" if distinguishes(2, n1, e1, n2, e2) else "blind"}')

    print()
    print('== PART 2: the Q4 carrier construction under a SECOND individualization ==')
    verts, ecol = build_reduced()
    idx = {v: i for i, v in enumerate(verts)}
    n = len(verts)
    e = {(idx[a], idx[b]): c for (a, b), c in ecol.items()}
    nb = nbrs(n, e)
    m0 = idx[('centre', 0)]
    g1 = idx[key({3: 0, 12: 0, 5: 1, 10: 2})]
    g2 = idx[key({3: 1, 12: 2, 5: 0, 10: 0})]

    init = [0] * n
    init[m0] = 1
    col = refine(n, nb, init, 40)
    print(f'  pin m_0 only            : g1,g2 separated = {col[g1] != col[g2]}')

    hits, kinds = 0, {}
    for u in range(n):
        if u == m0:
            continue
        init = [0] * n
        init[m0], init[u] = 1, 2
        c = refine(n, nb, init, 40)
        if c[g1] != c[g2]:
            hits += 1
            kinds[verts[u][0]] = kinds.get(verts[u][0], 0) + 1
    print(f'  pin m_0 + one other     : separated for {hits} of {n - 1} choices, by kind {kinds}')

    for probe in [('corner', 3, 0), ('corner', 3, 1), ('centre', 6), ('corner', 0, 0)]:
        u = idx[probe]
        init = [0] * n
        init[m0], init[u] = 1, 2
        c = refine(n, nb, init, 40)
        print(f'    pin m_0 + {str(probe):20s}: separated = {c[g1] != c[g2]}')
