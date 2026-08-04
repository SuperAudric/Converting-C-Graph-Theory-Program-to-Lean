#!/usr/bin/env python3
"""probe_w1_cellshape.py — W1 step 0b: pin the CELL-SHAPE lemma the Lean proof will need.

probe_w1_multipartite.py answers "is every cell an orbit?" (yes, measured).  That is the
TARGET.  This one measures the intended PROOF: the claim that every cell has one of exactly
two shapes, which is what splits the Lean argument into its two constructions.

    CLAIM S.  At every reached node of a complete multipartite graph, every 1-WL cell is
              either  (i)  contained in a single part          -> Equiv.swap of two twins, or
                      (ii) a disjoint union of >= 2 COMPLETE parts, all of the same size
                                                                -> an explicit part-swap perm.

Case (i) is the twin transposition (cheap in Lean: `Consume.IsColAut` is two conjuncts).
Case (ii) is the only real construction — and the claim that the parts are COMPLETE (not
partially individualized) and EQUAL-SIZED is exactly what makes that permutation exist.

⛔ If claim S fails anywhere, the two-case Lean proof is wrong even though the target may still
hold — the failing node would need a third construction.  That is why this is measured
separately from the target rather than assumed alongside it.

Convention-immune for the same reason as probe_w1_multipartite (nothing reads a colour-id
order); reuses that module's certified walk so the orbit reduction licence is identical.

    cd /workspace/scratchpad && python3 -u probe_w1_cellshape.py > probe_w1_cellshape.out 2>&1
"""

import os
from collections import Counter

import probe_w1_multipartite as P
from probe_cao_cleanroom import wl, individualize, cells


def classify_cell(vs, part_of, part_size):
    """Return 'in-part', 'union-of-parts', or a violation string."""
    met = {part_of[v] for v in vs}
    if len(met) == 1:
        return 'in-part'
    counts = Counter(part_of[v] for v in vs)
    incomplete = [p for p in met if counts[p] != part_size[p]]
    if incomplete:
        return f'VIOLATION: spans {len(met)} parts but parts {incomplete} are INCOMPLETE'
    sizes = {part_size[p] for p in met}
    if len(sizes) != 1:
        return f'VIOLATION: spans parts of DIFFERENT sizes {sorted(sizes)}'
    return 'union-of-parts'


def walk_shapes(n, adj, part_of, cap=P.NODE_CAP):
    part_size = Counter(part_of)
    root = P.root_colouring(n, adj)
    seen = {tuple(root): 0}
    frontier = [root]
    tally = Counter()
    violations = []
    truncated = False
    while frontier and not truncated:
        nxt = []
        for col in frontier:
            if P.is_discrete(col):
                continue
            verdict, _, _ = P.cells_all_orbits(n, adj, col, part_of)
            for c, vs in cells(col).items():
                if len(vs) < 2:
                    continue
                k = classify_cell(vs, part_of, part_size)
                tally[k if not k.startswith('VIOLATION') else 'VIOLATION'] += 1
                if k.startswith('VIOLATION'):
                    violations.append((tuple(col), tuple(vs), k))
            for v in P.expansion_vertices(col, verdict is True):
                child = wl(n, adj, individualize(n, col, v))
                key = tuple(child)
                if key in seen:
                    continue
                if len(seen) >= cap:
                    truncated = True
                    break
                seen[key] = seen[tuple(col)] + 1
                nxt.append(child)
            if truncated:
                break
        frontier = nxt
    return tally, violations, truncated


def main():
    nmax = int(os.environ.get('W1_NMAX', '14'))
    print('=' * 96)
    print(f'W1 step 0b — CLAIM S (cell shape) on complete multipartite graphs, n <= {nmax}')
    print('=' * 96)
    total = Counter()
    all_viol = []
    graphs = 0
    for p in P.profiles(nmax):
        n, adj, part_of = P.complete_multipartite(list(p))
        tally, viol, trunc = walk_shapes(n, adj, part_of)
        graphs += 1
        total.update(tally)
        all_viol += [(p,) + v for v in viol]
        if viol:
            print(f'  ⛔ {p}  n={n}  {len(viol)} violations, first: {viol[0][2]}')
            print(f'       colouring={viol[0][0]}  cell={viol[0][1]}')
    print()
    print(f'graphs                 : {graphs}')
    print(f'cells inside one part  : {total["in-part"]}      -> Equiv.swap of twins')
    print(f'cells = union of parts : {total["union-of-parts"]}      -> explicit part-swap perm')
    print(f'VIOLATIONS             : {total["VIOLATION"]}')
    print()
    print('CLAIM S: ' + ('HOLDS — the two-case Lean proof is the right decomposition'
                         if not all_viol else 'REFUTED — a third case exists, see above'))


if __name__ == '__main__':
    main()
