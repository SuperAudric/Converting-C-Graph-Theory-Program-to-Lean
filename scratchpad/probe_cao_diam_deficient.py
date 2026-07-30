#!/usr/bin/env python3
"""Close the strict gap in the diameter refutation of M2.

Johnson is SCHURIAN, so it bounds the *recovery* round count, not the *fused-orbital separation*
count that M2 actually asks about.  Need: a DEFICIENT root (fused orbitals) at GROWING diameter.

Construction: Shrikhande [] C_m (Cartesian product).  Shrikhande is the recorded deficient root
(its 9 non-neighbours split [3,6] under Aut_v while the SRG closure keeps them one class).
C_m is VT of diameter floor(m/2), so the product is VT of diameter 2 + floor(m/2) -- unbounded.
Aut(G [] H) = Aut(G) x Aut(H) for non-isomorphic connected factors (Sabidussi-Vizing), so the
group is built PROGRAMMATICALLY -- no search at n = 80.
"""
import sys
from collections import defaultdict
sys.path.insert(0, "/workspace/scratchpad")
from probe_cao_cleanroom import wl, all_isos, orbits
from probe_cao_induction import shrikhande, orbital_partition
from probe_cao_diameter import prounds, init_pairs, bfs_ecc

def cart(n1, a1, n2, a2):
    N = n1*n2
    A = [[0]*N for _ in range(N)]
    for i in range(n1):
        for j in range(n2):
            for i2 in range(n1):
                for j2 in range(n2):
                    if (i == i2 and a2[j][j2]) or (j == j2 and a1[i][i2]):
                        A[i*n2+j][i2*n2+j2] = 1
    return N, A

def cyc(m):
    a = [[0]*m for _ in range(m)]
    for i in range(m):
        a[i][(i+1) % m] = a[(i+1) % m][i] = 1
    return m, a

def run(m):
    n1, a1 = shrikhande()
    n2, a2 = cyc(m)
    N, A = cart(n1, a1, n2, a2)
    S = all_isos(n1, a1, wl(n1, a1, [0]*n1), wl(n1, a1, [0]*n1), limit=3_000_000)
    # Aut(C_m) = dihedral: rotation + reflection
    D = [tuple((j+1) % m for j in range(m)), tuple((-j) % m for j in range(m))]
    gens = []
    for s in S:
        gens.append(tuple(s[i]*n2 + j for i in range(n1) for j in range(n2)))
    for t in D:
        gens.append(tuple(i*n2 + t[j] for i in range(n1) for j in range(n2)))
    orb = orbits(N, gens)
    vt = len(set(orb)) == 1
    diam = bfs_ecc(N, A, 0)
    # root closure X vs the orbitals
    X = None
    for r, c in prounds(N, init_pairs(N, A, [0]*N)):
        X = c
    orbl = orbital_partition(N, gens)
    byc = defaultdict(set)
    for i in range(N*N):
        byc[X[i]].add(orbl[i])
    fused = {c: o for c, o in byc.items() if len(o) > 1}
    print(f"  Shrikhande [] C_{m}: n={N:4d} diameter={diam}  VT={vt}  "
          f"X-classes={len(set(X))} orbitals={len(set(orbl))}  FUSED classes={len(fused)}")
    if not fused:
        print("     (schurian root -- no fused orbitals to separate)")
        return
    # individualize v=0; time the separation of the fused orbitals meeting v's row
    v = 0
    vcol = [1 if i == v else 0 for i in range(N)]
    Av = [g for g in gens if g[v] == v]
    # need the full stabilizer orbit closure, not just generators fixing v: use orbital fibres
    tgt = []
    for c, os_ in fused.items():
        fib = defaultdict(list)
        for u in range(N):
            if X[v*N+u] == c:
                fib[orbl[v*N+u]].append(u)
        if len(fib) > 1:
            tgt.append((c, [x[0] for x in fib.values()], sorted(len(x) for x in fib.values())))
    if not tgt:
        print("     fused classes do not meet v's row in >1 orbital")
        return
    init_v = {}
    col0 = [0]*(N*N)
    for a in range(N):
        for b in range(N):
            k = (X[a*N+b], a == v, b == v)
            col0[a*N+b] = init_v.setdefault(k, len(init_v))
    hit = {}
    for r, col in prounds(N, col0):
        for c, reps, sizes in tgt:
            if c in hit: continue
            if len({col[v*N+u] for u in reps}) == len(reps):
                hit[c] = r
        if len(hit) == len(tgt): break
    for c, reps, sizes in tgt:
        print(f"     fused class {c}: orbital fibres over v sizes {sizes} -> "
              f"SEPARATED at round {hit.get(c, 'NEVER(cap)')}  [counted from coherent X]")

if __name__ == "__main__":
    print("Deficient root at growing diameter (Shrikhande is the [3,6] deficient root):")
    for m in (3, 5, 7):
        run(m)
