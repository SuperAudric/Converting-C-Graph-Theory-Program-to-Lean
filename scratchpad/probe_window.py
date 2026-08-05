"""How much repeat-tracking is actually NEEDED to reach the orbitals?

Ladder of r-avoiding walks: x_i != x_j whenever 0 < j-i <= r.
  r=1  plain walks           (= coherent-algebra entries; never beats 2-WL)
  r=2  non-backtracking      (Hashimoto/Ihara; a pair-indexed object)
  r=3,4,...                  needs an (r)-vertex window of state
  r=L  full simple paths     (the exponential object)

Reported per r: the induced pair partition vs the true orbitals, and vs 2-WL.
The r at which the orbitals are reached is the amount of repeat-tracking the route
must buy; probe_loopdetect.py says how much the condensation can actually afford.
"""
import sys
from probe_pathcondense import (shrikhande, rook44, net_z4, rank_partition,
                                orbital_partition, wl2_pair_closure, npairclasses,
                                finer_or_equal)
from probe_cao_cleanroom import cfi, all_isos


def ravoid_profile(n, adj, r, maxlen):
    """counts[a][b][L] = # walks a->b of length L with no repeat within separation r."""
    cnt = {(a, b): [0] * (maxlen + 1) for a in range(n) for b in range(n)}

    def dfs(a, w):
        L = len(w) - 1
        if L:
            cnt[(a, w[-1])][L] += 1
        if L == maxlen:
            return
        x = w[-1]
        tail = w[-r:] if r > 0 else ()
        for y in range(n):
            if adj[x][y] and y not in tail:
                dfs(a, w + (y,))

    for a in range(n):
        dfs(a, (a,))
    return rank_partition({k: tuple(v) for k, v in cnt.items()})


def run(label, n, adj, maxlen, rs=(1, 2, 3, 4, 5, 6, 7)):
    auts = all_isos(n, adj, [0] * n, [0] * n)
    P_orb = orbital_partition(n, auts)
    P_2wl = wl2_pair_closure(n, adj)
    print(f'=== {label}  n={n} |Aut|={len(auts)}  orbitals={npairclasses(P_orb)}  '
          f'2-WL={npairclasses(P_2wl)}  maxlen={maxlen}')
    for r in rs:
        if r > maxlen:
            break
        P = ravoid_profile(n, adj, min(r, maxlen), maxlen)
        k = npairclasses(P)
        name = 'walks' if r <= 1 else 'non-backtracking' if r == 2 else f'window {r}'
        eq_orb = finer_or_equal(P, P_orb) and finer_or_equal(P_orb, P)
        eq_wl = finer_or_equal(P, P_2wl) and finer_or_equal(P_2wl, P)
        print(f'    r={r} ({name:16s}): {k:3d} classes   '
              f'== orbitals? {str(eq_orb):5s}   == 2-WL? {str(eq_wl):5s}   '
              f'2-WL refines it? {finer_or_equal(P_2wl, P)}')
        sys.stdout.flush()
    print()


if __name__ == '__main__':
    n, adj = shrikhande(); run('Shrikhande (orbitals 4, 2-WL 3)', n, adj, 7)
    n, adj = rook44();     run('rook 4x4', n, adj, 7)
    K4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    n, adj, _, _ = cfi(K4, 4)
    run('CFI[K4] plain', n, adj, 8)
    n, adj = net_z4();     run('net(Z4) = CFI[K4]-twisted', n, adj, 8)
