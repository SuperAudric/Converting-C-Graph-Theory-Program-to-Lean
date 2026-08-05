"""Which part of the 'uncondensed' path object closes the Shrikhande gap?

probe_pathcondense.py measured, at Shrikhande's CAO root:
    walk counts = V4 = 2-WL = 3 pair classes,  orbitals = 4.

Two competing diagnoses of the missing class:
  (U) user, 2026-08-05: the loss is REPEATED VERTICES -- a walk that returns to an
      already-visited vertex conflated with one reaching a different same-orbit vertex
      (the CFI cycle-parity mechanism).  Prediction: SIMPLE-path counts recover it.
  (A) arity: the loss is relations between NON-CONSECUTIVE positions of the path
      (Shrikhande's distinguisher is 'are v's two common nbrs with u adjacent' -- a
      relation between the interiors of two DIFFERENT length-2 paths).
      Prediction: simple-path counts do NOT recover it; full induced annotation does.

Three nested objects, each a partition of V x V:
  A0  walk counts            (A^k)_ab                      -- consecutive only, repeats allowed
  A1  simple-path counts     #{simple paths a->b of len k}  -- adds ONLY the all-distinct condition
  A2  annotated simple paths multiset over paths of the FULL induced ordered adjacency
                             (adj(v_i,v_j))_{i<j}          -- all pairwise relations
A0 <= A1 <= A2 by construction.  The question is where the 4th class appears.
"""
import sys, time
from probe_pathcondense import (shrikhande, rook44, net_z4, rank_partition, npairclasses,
                                same, finer_or_equal, orbital_partition, wl2_pair_closure,
                                walk_partition)
from probe_cao_cleanroom import cfi, all_isos


def simple_paths_profiles(n, adj, maxlen, deadline=None):
    """For every ordered pair, two profiles over path length:
         count[k]  = number of simple paths a->b with k edges
         anno[k]   = multiset of induced ordered adjacency patterns of those paths
    Returns (count_profile, anno_profile) as dicts (a,b) -> hashable."""
    nbr = [[b for b in range(n) if adj[a][b]] for a in range(n)]
    cnt = {(a, b): [0] * (maxlen + 1) for a in range(n) for b in range(n)}
    ann = {(a, b): [dict() for _ in range(maxlen + 1)] for a in range(n) for b in range(n)}
    for a in range(n):
        if deadline and time.time() > deadline:
            raise TimeoutError('path enumeration deadline')
        path = [a]
        seen = 1 << a

        def rec(cur, depth):
            b = cur
            k = depth
            cnt[(a, b)][k] += 1
            pat = tuple(adj[path[i]][path[j]]
                        for i in range(len(path)) for j in range(i + 1, len(path)))
            d = ann[(a, b)][k]
            d[pat] = d.get(pat, 0) + 1
            if depth == maxlen:
                return
            for x in nbr[cur]:
                if seen_get(x):
                    continue
                mark(x)
                path.append(x)
                rec(x, depth + 1)
                path.pop()
                unmark(x)

        def seen_get(x):
            return (seen >> x) & 1

        def mark(x):
            nonlocal seen
            seen |= 1 << x

        def unmark(x):
            nonlocal seen
            seen &= ~(1 << x)

        rec(a, 0)
    cprof = {k: tuple(v) for k, v in cnt.items()}
    aprof = {k: tuple(tuple(sorted(d.items())) for d in v) for k, v in ann.items()}
    return rank_partition(cprof), rank_partition(aprof)


def run(label, n, adj, maxlen, do_aut=True):
    print(f'--- {label}  n={n}  maxlen={maxlen}')
    t0 = time.time()
    A0 = walk_partition(n, adj)
    try:
        A1, A2 = simple_paths_profiles(n, adj, maxlen, deadline=t0 + 600)
    except TimeoutError as e:
        print(f'    SKIPPED: {e}')
        return
    P2wl = wl2_pair_closure(n, adj)
    print(f'    A0 walk counts          : {npairclasses(A0):3d} classes')
    print(f'    A1 simple-path counts   : {npairclasses(A1):3d} classes   '
          f'(refines A0? {finer_or_equal(A1, A0)})')
    print(f'    A2 annotated simple pth : {npairclasses(A2):3d} classes   '
          f'(refines A1? {finer_or_equal(A2, A1)})')
    print(f'    2-WL pair closure       : {npairclasses(P2wl):3d} classes')
    if do_aut:
        auts = all_isos(n, adj, [0] * n, [0] * n)
        Porb = orbital_partition(n, auts)
        print(f'    ORBITALS (truth)        : {npairclasses(Porb):3d} classes   |Aut|={len(auts)}')
        for nm, P in [('A0', A0), ('A1', A1), ('A2', A2), ('2-WL', P2wl)]:
            print(f'      {nm:5s} == orbitals? {str(same(P, Porb)):5s}   '
                  f'refines orbitals? {finer_or_equal(P, Porb)}')
    print(f'    [{time.time()-t0:.1f}s]')
    sys.stdout.flush()


if __name__ == '__main__':
    n, adj = shrikhande();  run('Shrikhande', n, adj, 6)
    n, adj = rook44();      run('rook 4x4', n, adj, 6)
    n, adj = net_z4();      run('net(Z4) = CFI[K4]-tw', n, adj, 6)
    K4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    n, adj, _, _ = cfi(K4, 4, ());  run('CFI[K4] plain', n, adj, 6)
