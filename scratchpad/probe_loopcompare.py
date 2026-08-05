"""Does 'CAO makes the loop-comparison unnecessary' hold at the COUNT level?

User's argument: an interior repeat decomposes as prefix + closed walk at loopStart + suffix.
The closed walk IS detected (it is an endpoint repeat, and the loop profile of loopStart is
stored in the path type).  Only WHICH vertex loopStart is gets forgotten by the condense step.
Under CAO all cell members carry the same loop, so the comparison should not be needed and the
next layer object should still be constructible.

Purity (probe_loopdetect) is only SUFFICIENT, not necessary -- counts could still come out right
by cancellation.  So test the counts directly, at a CAO root:

  P1  is the loop profile really orbit-uniform?          (the argument's PREMISE)
  P2  are the loop-aware counts determined by 2-WL?      (the argument's CONCLUSION)

If P1 holds and P2 fails, the premise is true and the conclusion is false: orbit-uniformity of
loop-CARRYING is not the quantity the recursion needs -- it needs the COINCIDENCE pattern.
"""
import sys
from probe_pathcondense import (shrikhande, rank_partition, orbital_partition,
                                wl2_pair_closure, npairclasses)
from probe_window import ravoid_profile
from probe_cao_cleanroom import all_isos, orbits


def closed_walk_profile(n, adj, v, maxlen=8):
    """(A^k)_{vv} for k<=maxlen -- the vertex's loop profile, a coherent-algebra diagonal."""
    row = [[1 if i == j else 0 for j in range(n)] for i in range(n)]
    prof = []
    cur = [1 if i == v else 0 for i in range(n)]
    for _ in range(maxlen):
        cur = [sum(cur[x] for x in range(n) if adj[x][y]) for y in range(n)]
        prof.append(cur[v])
    return tuple(prof)


def ravoid_counts(n, adj, a, b, r, maxlen):
    """Per-length counts of r-avoiding walks a->b."""
    out = [0] * (maxlen + 1)

    def dfs(w):
        L = len(w) - 1
        if L and w[-1] == b:
            out[L] += 1
        if L == maxlen:
            return
        tail = w[-r:]
        for y in range(n):
            if adj[w[-1]][y] and y not in tail:
                dfs(w + (y,))
    dfs((a,))
    return tuple(out)


def main():
    n, adj = shrikhande()
    auts = all_isos(n, adj, [0] * n, [0] * n)
    orb = orbits(n, auts)
    P_orb = orbital_partition(n, auts)
    P_2wl = wl2_pair_closure(n, adj)
    print(f'Shrikhande  n={n} |Aut|={len(auts)}  cells={len(set(orb))}  '
          f'orbitals={npairclasses(P_orb)}  2-WL pair classes={npairclasses(P_2wl)}')
    print(f'  CAO AT THE ROOT: {len(set(orb))} cell(s) = {len(set(orb))} orbit(s) -> HOLDS '
          f'(vertex-transitive)\n')

    # ---- P1: is the loop profile orbit-uniform? (the argument's premise) ----
    profs = {x: closed_walk_profile(n, adj, x) for x in range(n)}
    percell = {}
    for x in range(n):
        percell.setdefault(orb[x], set()).add(profs[x])
    print('P1  PREMISE -- loop profile constant on each cell?  '
          f'{all(len(s) == 1 for s in percell.values())}')
    print(f'    every vertex has closed-walk profile {profs[0]}')
    print('    ==> orbit-uniformity of loop-CARRYING is TRUE, and maximally so.\n')

    # ---- P2: are the loop-aware counts determined by 2-WL? (the conclusion) ----
    fused = {}
    for (a, b), k in P_2wl.items():
        if a != b:
            fused.setdefault(k, set()).add(P_orb[(a, b)])
    bad = [k for k, v in fused.items() if len(v) > 1]
    print(f'P2  CONCLUSION -- 2-WL classes that merge distinct orbitals: {len(bad)}')
    pick = None
    for (a, b), k in P_2wl.items():
        if k in bad and a != b:
            for (a2, b2), k2 in P_2wl.items():
                if k2 == k and P_orb[(a2, b2)] != P_orb[(a, b)]:
                    pick = ((a, b), (a2, b2))
                    break
        if pick:
            break
    (a, b), (a2, b2) = pick
    print(f'    representatives: ({a},{b}) and ({a2},{b2})   same 2-WL class? '
          f'{P_2wl[(a,b)] == P_2wl[(a2,b2)]}   same orbital? {P_orb[(a,b)] == P_orb[(a2,b2)]}')
    print(f'    adj({a},{b})={adj[a][b]}  adj({a2},{b2})={adj[a2][b2]}   '
          f'same cell for all four endpoints? {len({orb[a],orb[b],orb[a2],orb[b2]})==1}')
    ML = 9
    for r in (1, 2, 3, 4, 5, 9):
        c1 = ravoid_counts(n, adj, a, b, r, ML)
        c2 = ravoid_counts(n, adj, a2, b2, r, ML)
        name = 'plain walks' if r == 1 else 'non-backtracking' if r == 2 else f'window {r}'
        print(f'    r={r} ({name:16s}) counts by length: {list(c1[1:])}  vs  {list(c2[1:])}   '
              f'{"IDENTICAL" if c1 == c2 else "DIFFER <-- loop-aware count separates them"}')
        sys.stdout.flush()

    # ---- the mechanism: same cell, different coincidence ----
    print('\n  MECHANISM (why the premise does not deliver the conclusion):')
    print('    Shrikhande residue witness, v=0:  simple (0,1,2,3,4,9)  vs  looped (0,1,2,1,5,9)')
    print(f'    position 3 is vertex 3 in the first, vertex 1 in the second;  '
          f'same cell? {orb[1] == orb[3]}')
    print('    CAO says vertices 1 and 3 carry identical loops -- TRUE, and it does not help:')
    print('    what the recursion needs is whether position 3 IS position 1, not whether its')
    print('    cell can carry a loop.  Cell-level support does not fix vertex-level identity.')
    sys.stdout.flush()


if __name__ == '__main__':
    main()
