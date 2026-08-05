"""Is V4's path-multiset recursion the SAME partition as the 2-WL pair closure?

probe_pathcondense.py showed matching class COUNTS on 3 objects. Counts are not
partitions. This checks equality of the partitions, and adds CFI (where 2-WL is known
to fail) to see whether V4 fails in exactly the same place.

V4's recursion (Archive/V4/CanonGraphOrdererV4.cs:70-75, 294-301):
    P_d(a,b) = {{ ( rank P_{d-1}(a,mid), adj(mid,b) ) : mid }},  keyed also by vcol[b]
2-WL:
    c'(a,b) = ( c(a,b), {{ ( c(a,x), c(x,b) ) : x }} )
Difference: V4 uses the RAW adj(mid,b) on the right hop, 2-WL the refined c(mid,b).
"""
import sys
from probe_pathcondense import (shrikhande, rook44, net_z4, rank_partition, npairclasses,
                                same, finer_or_equal, wl2_pair_closure, v4_pair_partition,
                                walk_partition, orbital_partition)
from probe_cao_cleanroom import cfi, all_isos, orbits


def check(label, n, adj, vcol=None, do_aut=True):
    vcol = vcol or [0] * n
    _, P_v4 = v4_pair_partition(n, adj, vcol)
    P_2wl = wl2_pair_closure(n, adj)
    P_walk = walk_partition(n, adj)
    print(f'--- {label}  n={n}')
    print(f'    V4={npairclasses(P_v4)}  2-WL={npairclasses(P_2wl)}  walk={npairclasses(P_walk)}')
    print(f'    V4 == 2-WL (as partitions)?   {same(P_v4, P_2wl)}')
    print(f'    V4 refines 2-WL?              {finer_or_equal(P_v4, P_2wl)}')
    print(f'    2-WL refines V4?              {finer_or_equal(P_2wl, P_v4)}')
    print(f'    walk refines V4?              {finer_or_equal(P_walk, P_v4)}')
    if do_aut:
        auts = all_isos(n, adj, [0] * n, [0] * n)
        P_orb = orbital_partition(n, auts)
        print(f'    |Aut|={len(auts)}  orbitals={npairclasses(P_orb)}  '
              f'V4=orbitals? {same(P_v4, P_orb)}  2-WL=orbitals? {same(P_2wl, P_orb)}')
    sys.stdout.flush()


if __name__ == '__main__':
    for label, build in [('Shrikhande', shrikhande), ('rook 4x4', rook44), ('net(Z4)', net_z4)]:
        n, adj = build()
        check(label, n, adj)

    # CFI over K4, twisted and plain: the family the user says the CONDENSED V4 fell to.
    K4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    for tw, name in [((), 'CFI[K4] plain'), ((0,), 'CFI[K4] twisted')]:
        n, adj, names, idx = cfi(K4, 4, tw)
        check(name, n, adj)

    # A bigger CFI where 2-WL provably fails to distinguish the pair.
    K33 = [(0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5)]
    for tw, name in [((), 'CFI[K3,3] plain'), ((0,), 'CFI[K3,3] twisted')]:
        n, adj, names, idx = cfi(K33, 6, tw)
        check(name, n, adj, do_aut=False)
