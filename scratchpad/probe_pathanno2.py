"""Fair-truncation rerun of probe_pathanno.py for the n=28 objects.

In the first run A0 used walks up to length n while A1/A2 used simple paths up to
maxlen=6, so 'A1 refines A0' came back False as a TRUNCATION artifact, not a finding.
Here all three profiles are truncated to the SAME maxlen, and maxlen is pushed up.
"""
import sys, time
from probe_pathcondense import (shrikhande, net_z4, rank_partition, npairclasses,
                                same, finer_or_equal, orbital_partition, wl2_pair_closure)
from probe_pathanno import simple_paths_profiles
from probe_cao_cleanroom import cfi, all_isos


def walk_partition_trunc(n, adj, maxlen):
    P = [[1 if a == b else 0 for b in range(n)] for a in range(n)]
    lay = [[[P[a][b]] for b in range(n)] for a in range(n)]
    for _ in range(maxlen):
        Q = [[sum(P[a][x] * adj[x][b] for x in range(n)) for b in range(n)] for a in range(n)]
        for a in range(n):
            for b in range(n):
                lay[a][b].append(Q[a][b])
        P = Q
    return rank_partition({(a, b): tuple(lay[a][b]) for a in range(n) for b in range(n)})


def run(label, n, adj, maxlens):
    auts = all_isos(n, adj, [0] * n, [0] * n)
    Porb = orbital_partition(n, auts)
    P2wl = wl2_pair_closure(n, adj)
    print(f'=== {label}  n={n}  |Aut|={len(auts)}  orbitals={npairclasses(Porb)}  '
          f'2-WL={npairclasses(P2wl)}  (2-WL==orb? {same(P2wl, Porb)})')
    for L in maxlens:
        t0 = time.time()
        A0 = walk_partition_trunc(n, adj, L)
        try:
            A1, A2 = simple_paths_profiles(n, adj, L, deadline=t0 + 900)
        except (TimeoutError, RecursionError) as e:
            print(f'    maxlen={L:2d}  SKIPPED ({type(e).__name__})')
            continue
        print(f'    maxlen={L:2d}  A0={npairclasses(A0):3d}  A1={npairclasses(A1):3d}  '
              f'A2={npairclasses(A2):3d}   A1>=A0? {finer_or_equal(A1, A0)}  '
              f'A2>=A1? {finer_or_equal(A2, A1)}   '
              f'A1==orb? {str(same(A1, Porb)):5s} A2==orb? {str(same(A2, Porb)):5s}  '
              f'A2 refines orb? {finer_or_equal(A2, Porb)}   [{time.time()-t0:.1f}s]')
        sys.stdout.flush()


if __name__ == '__main__':
    n, adj = shrikhande()
    run('Shrikhande', n, adj, [3, 4, 5, 6, 7])
    n, adj = net_z4()
    run('net(Z4) = CFI[K4]-tw', n, adj, [6, 8, 10, 12])
    K4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    n, adj, _, _ = cfi(K4, 4, ())
    run('CFI[K4] plain', n, adj, [6, 8, 10, 12])
