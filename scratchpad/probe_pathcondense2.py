"""Follow-ups to probe_pathcondense.py.

(1) Is net(Z4)'s condensation failure substantive, or a transpose artifact?
    Walk counts (A^k)_ab are symmetric; [cell,adj,cell] is ordered. Re-test against the
    SYMMETRIZED cell object so the comparison is like-for-like, and print a witness.
(2) The other half of the user's argument: individualize v at the CAO residue and ask
    whether the 2-WL extension's FIBRE partition equals the Aut_v-orbits, and at which
    round v's row first separates.  (Round count = doc 12.3 "term 2".)
"""
import sys
from probe_pathcondense import (shrikhande, rook44, net_z4, rank_partition, npairclasses,
                                finer_or_equal, same, orbital_partition, wl2_pair_closure,
                                walk_partition, cell_partition, v4_pair_partition)
from probe_cao_cleanroom import all_isos, orbits, wl, individualize, cells


def sym(P):
    """Symmetrize a pair partition: class of (a,b) becomes {class(a,b), class(b,a)}."""
    return rank_partition({(a, b): tuple(sorted((P[(a, b)], P[(b, a)])))
                           for (a, b) in P})


def condensation_witness(n, P_cell, P_walk):
    """A pair-of-pairs in one [cell,adj,cell] class whose walk vectors differ."""
    byc = {}
    for k in P_cell:
        byc.setdefault(P_cell[k], []).append(k)
    for c, ks in byc.items():
        vals = {}
        for k in ks:
            vals.setdefault(P_walk[k], []).append(k)
        if len(vals) > 1:
            groups = list(vals.values())
            return groups[0][0], groups[1][0], len(vals)
    return None


def part1(label, build):
    n, adj = build()
    auts = all_isos(n, adj, [0] * n, [0] * n)
    orb = orbits(n, auts)
    vc = rank_partition({(v, v): orb[v] for v in range(n)})
    vcol = [vc[(v, v)] for v in range(n)]
    P_orb = orbital_partition(n, auts)
    P_walk = walk_partition(n, adj)
    P_cell = cell_partition(n, adj, vcol)
    _, P_v4 = v4_pair_partition(n, adj, vcol)
    P_2wl = wl2_pair_closure(n, adj)

    print(f'--- {label}  n={n} |Aut|={len(auts)}')
    print(f'    ordered  : cell={npairclasses(P_cell)} walk={npairclasses(P_walk)} '
          f'v4={npairclasses(P_v4)} 2wl={npairclasses(P_2wl)} orb={npairclasses(P_orb)}')
    sc, sw, sv, so = sym(P_cell), sym(P_walk), sym(P_v4), sym(P_orb)
    print(f'    symmetric: cell={npairclasses(sc)} walk={npairclasses(sw)} '
          f'v4={npairclasses(sv)} orb={npairclasses(so)}')
    print(f'    CONDENSATION ordered   (cell refines walk)? {finer_or_equal(P_cell, P_walk)}')
    print(f'    CONDENSATION symmetric (cell refines walk)? {finer_or_equal(sc, sw)}')
    print(f'    CONDENSATION symmetric (cell refines V4)?   {finer_or_equal(sc, sv)}')
    w = condensation_witness(n, sc, sw)
    if w:
        (a, b), (c, d), k = w
        print(f'    witness: ({a},{b}) and ({c},{d}) share [cell,adj,cell] but differ in walks '
              f'({k} distinct walk-vectors in that class)')
    print(f'    root schurian (2-WL = orbitals)? {same(P_2wl, P_orb)}   '
          f'orbitals finer than walk? {finer_or_equal(P_orb, P_walk)}')
    return n, adj, auts, orb, vcol


def part2(label, n, adj, auts, orb, vcol):
    """Individualize one rep per orbit-cell; compare 2-WL extension fibres to Aut_v-orbits."""
    reps = sorted({orb[v]: v for v in range(n)}.values())
    for v in reps:
        stab = [g for g in auts if g[v] == v]
        korb = orbits(n, stab)
        target = rank_partition({(x, x): korb[x] for x in range(n)})
        target = [target[(x, x)] for x in range(n)]

        # 2-WL closure of the CAO colouring with v individualized, tracked per round.
        c = {(a, b): (vcol[a], vcol[b], adj[a][b], a == b, a == v, b == v)
             for a in range(n) for b in range(n)}
        c = rank_partition(c)
        sep_round = None
        for r in range(1, 40):
            nxt = rank_partition({(a, b): (c[(a, b)],
                                           tuple(sorted((c[(a, x)], c[(x, b)]) for x in range(n))))
                                  for a in range(n) for b in range(n)})
            row = rank_partition({(v, u): nxt[(v, u)] for u in range(n)})
            rowpart = [row[(v, u)] for u in range(n)]
            if sep_round is None and len(set(rowpart)) > len(set(
                    [rank_partition({(v, u): c[(v, u)] for u in range(n)})[(v, u)]
                     for u in range(n)])):
                sep_round = r
            if same(nxt, c):
                break
            c = nxt
        fib = [c[(u, u)] for u in range(n)]
        nf, nt = len(set(fib)), len(set(target))
        ok = all((fib[x] == fib[y]) == (target[x] == target[y])
                 for x in range(n) for y in range(n))
        print(f'    v={v:3d} |Aut_v|={len(stab):5d}  2-WL fibres={nf:3d}  Aut_v-orbits={nt:3d}'
              f'  CAO PRESERVED={ok}   v-row first splits at round {sep_round}')


if __name__ == '__main__':
    for label, build in [('Shrikhande', shrikhande), ('rook 4x4', rook44), ('net(Z4)', net_z4)]:
        n, adj, auts, orb, vcol = part1(label, build)
        part2(label, n, adj, auts, orb, vcol)
        print()
        sys.stdout.flush()
