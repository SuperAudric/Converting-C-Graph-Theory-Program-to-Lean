"""Is V4's path-multiset recursion the SAME partition as the 2-WL pair closure?

probe_pathcondense.py showed matching class COUNTS on 3 objects. Counts are not
partitions. This checks equality of the partitions, and adds CFI (where 2-WL is known
to fail) to see whether V4 fails in exactly the same place.

V4's recursion (Archive/V4/CanonGraphOrdererV4.cs:70-75, 294-301):
    P_d(a,b) = {{ ( rank P_{d-1}(a,mid), adj(mid,b) ) : mid }},  keyed also by vcol[b]
2-WL:
    c'(a,b) = ( c(a,b), {{ ( c(a,x), c(x,b) ) : x }} )
Difference: V4 uses the RAW adj(mid,b) on the right hop, 2-WL the refined c(mid,b).

⛔⛔ CORRECTED 2026-08-10 — THE 7/7 BELOW IS A POPULATION ARTIFACT.
The 7 objects all tie, and they still do (this file reproduces). But `V4 == 2-WL` is FALSE in
general; only `V4 <= 2-WL` is a theorem (doc §14.5g's all-splits closure). The 8th object added
below, the truncated tetrahedron, separates them: V4 6 = walk 6, 2-WL 7, with 2-WL refining V4
and the single merge being a class TOGETHER WITH ITS TRANSPOSE.

*** THE DEFICIT IS THE ONE TOKEN NAMED FOUR LINES UP. ***
Substituting the refined c(mid,b) for the raw adj(mid,b) on the right hop makes the recursion
2-WL EXACTLY. Nothing else about V4 is implicated: not the order-insensitive list comparison
(a cost choice, moves no partition), not the join across depths, not the vcol feedback -- which
is provably inert here, the witness being vertex-transitive.

REJECTED MECHANISM, do not re-derive: "V4 cannot represent an asymmetric relation" is FALSE.
net(Z4) and all four CFI objects have ASYMMETRIC stable 2-WL colourings and V4 matches them
exactly. V4 represents asymmetry fine; on the truncated tetrahedron it just lacks the power to
reach it, and the deficit happens to surface as a transpose pair.

POPULATION STEER: all 7 banked objects are SRG / CFI / vertex-transitive -- an |Aut|-rich set
where these objects tie by default. Before reading any k/k as an equivalence, test something
with a NON-COMMUTATIVE coherent closure; a Cayley graph of a nonabelian group is the cheapest
source (this witness came from sweeping S3, D4, Q8, A4, D6 and their inverse-closed conn. sets).
"""
import sys
from probe_pathcondense import (shrikhande, rook44, net_z4, rank_partition, npairclasses,
                                same, finer_or_equal, wl2_pair_closure, v4_pair_partition,
                                walk_partition, orbital_partition, cayley)
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


def truncated_tetrahedron():
    """Cay(A4, {(123),(132),(12)(34)}) -- n=12, cubic, vertex-transitive.

    THE FALSIFIER of `V4 == 2-WL` (see the 2026-08-10 block in the module docstring).
    Vertex-transitive, so any sound vcol is constant and the vcol feedback cannot rescue V4.
    """
    from itertools import permutations
    els = [p for p in permutations(range(4))
           if sum(1 for i in range(4) for j in range(i + 1, 4) if p[i] > p[j]) % 2 == 0]
    mul = lambda a, b: tuple(a[b[i]] for i in range(len(b)))
    e = tuple(range(4))
    c = next(g for g in els if len({g[i] for i in range(4) if g[i] != i}) == 3)
    cinv = next(g for g in els if mul(g, c) == e)
    t = next(g for g in els if g != e and mul(g, g) == e)
    return cayley(els, mul, [c, cinv, t])


if __name__ == '__main__':
    for label, build in [('Shrikhande', shrikhande), ('rook 4x4', rook44), ('net(Z4)', net_z4)]:
        n, adj = build()
        check(label, n, adj)

    # ⛔ The 8th object: V4 < 2-WL strictly. Everything above ties; this does not.
    n, adj = truncated_tetrahedron()
    check('trunc.tetrahedron', n, adj)

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
