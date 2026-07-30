#!/usr/bin/env python3
"""THE DISJOINT-UNION CRITIQUE (user, 2026-07-30).  Two claims of mine to test:

  C1  "bounded shattering depth" as a route -- disjoint union keeps VT/CAO but each extra
      copy costs another block of individualizations, so the depth bound is NOT closed under
      union while the TARGET property is.  => the route proves something strictly stronger
      than needed, and that stronger thing is fragile.

  C2  "non-schurity disappears after the first individualization" -- in G (+) G, one
      individualization lands in ONE copy; the other copy still carries the whole deficient
      scheme.  => full schurity should FAIL at depth 1, refuting the law I recorded.

Aut(G (+) G) = Aut(G) wr S2, so the group is built PROGRAMMATICALLY from Aut(G) -- no
enumeration at n = 32 -- and orbits/orbitals come from generators by union-find (exact).
Aut_v for v in copy A is Aut(G)_v x Aut(G) (the swap cannot fix v).
"""
import sys, time
from collections import defaultdict
sys.path.insert(0, "/workspace/scratchpad")
from probe_cao_cleanroom import wl, individualize, cells, all_isos, orbits, is_perm_aut
from probe_cao_induction import (twowl_pairs, orbital_partition, same_partition,
                                 shrikhande, rook, from_edges, T8, chang)

sys.setrecursionlimit(100000)


def disjoint(n, adj, k=2):
    N = n * k
    out = [[0] * N for _ in range(N)]
    for c in range(k):
        off = c * n
        for a in range(n):
            for b in range(n):
                out[off + a][off + b] = adj[a][b]
    return N, out


def lift(perms_A, perms_B, n, swap=False):
    """Permutations of the 2n-point union: copy A by sigma, copy B by tau (then swap)."""
    out = []
    for s in perms_A:
        for t in perms_B:
            p = [0] * (2 * n)
            for v in range(n):
                if swap:
                    p[v] = n + s[v]
                    p[n + v] = t[v]
                else:
                    p[v] = s[v]
                    p[n + v] = n + t[v]
            out.append(tuple(p))
    return out


def analyse(lab, n, adj):
    A = all_isos(n, adj, wl(n, adj, [0] * n), wl(n, adj, [0] * n), limit=3_000_000)
    ident = tuple(range(n))
    N, U = disjoint(n, adj)
    # generators of Aut(G (+) G): A on copy 1, A on copy 2, and the swap
    gens = (lift(A, [ident], n) + lift([ident], A, n) + lift([ident], [ident], n, swap=True))
    print(f"\n=== {lab} (+) {lab} ===  n={N}  |Aut(G)|={len(A)}  "
          f"|Aut(G(+)G)| = 2*{len(A)}^2 = {2*len(A)**2}  (generators used: {len(gens)})")
    root = wl(N, U, [0] * N)
    orb = orbits(N, gens)
    print(f"  1-WL root cells {sorted(len(c) for c in cells(root).values())}  "
          f"Aut-orbit sizes {sorted(len({o for o in orb}) and [sum(1 for x in orb if x == o) for o in set(orb)])}")
    m = {}
    oc = [m.setdefault(orb[v], len(m)) for v in range(N)]
    p2 = twowl_pairs(N, U, oc)
    diag = [p2[v * N + v] for v in range(N)]
    print(f"  ROOT : CAO(fibres=orbits) = {same_partition(diag, orb)} | "
          f"full-schurian = {same_partition(p2, orbital_partition(N, gens))}")

    # individualize v = 0 (copy A).  Aut_v = Aut(G)_v x Aut(G), no swap.
    Av = [g for g in A if g[0] == 0]
    gens_v = lift(Av, [ident], n) + lift([ident], A, n)
    col1 = individualize(N, oc, 0)
    p2v = twowl_pairs(N, U, col1)
    diagv = [p2v[v * N + v] for v in range(N)]
    orbv = orbits(N, gens_v)
    fib = same_partition(diagv, orbv)
    full = same_partition(p2v, orbital_partition(N, gens_v))
    print(f"  DEPTH 1 (individualize v=0 in copy A): |Aut_v| = {len(Av)}*{len(A)} = "
          f"{len(Av)*len(A)}")
    print(f"         2-WL cells {sorted(len(c) for c in cells(diagv).values())}")
    print(f"         Aut_v-orbit sizes {sorted(sum(1 for x in orbv if x == o) for o in set(orbv))}")
    print(f"         CAO(fibres=orbits) = {fib}    full-schurian = {full}"
          + ("   <<<< NON-SCHURITY SURVIVED THE INDIVIDUALIZATION" if not full else ""))
    return fib, full


def depth_to_discrete(n, adj, k):
    """Greedy lowest-id descent from the orbit partition: how many individualizations?"""
    A = all_isos(n, adj, wl(n, adj, [0] * n), wl(n, adj, [0] * n), limit=3_000_000)
    ident = tuple(range(n))
    N = n * k
    _, U = disjoint(n, adj, k)
    gens = []
    for c in range(k):
        for s in A:
            p = list(range(N))
            for v in range(n):
                p[c * n + v] = c * n + s[v]
            gens.append(tuple(p))
    # component swaps (adjacent transpositions) generate the S_k part
    for c in range(k - 1):
        p = list(range(N))
        for v in range(n):
            p[c * n + v] = (c + 1) * n + v
            p[(c + 1) * n + v] = c * n + v
        gens.append(tuple(p))
    orb = orbits(N, gens)
    m = {}
    col = [m.setdefault(orb[v], len(m)) for v in range(N)]
    steps = 0
    while True:
        p2 = twowl_pairs(N, U, col)
        col = [p2[v * N + v] for v in range(N)]
        d = cells(col)
        big = [c for c in sorted(d) if len(d[c]) > 1]
        if not big:
            return steps
        col = individualize(N, col, d[big[0]][0])
        steps += 1
        if steps > 40:
            return None


print("=== C2: does non-schurity survive one individualization under disjoint union? ===")
for lab, (n, adj) in [("Shrikhande", shrikhande()), ("rook4x4", rook(4))]:
    analyse(lab, n, adj)

print("\n=== C1: shattering depth under k disjoint copies (2-WL descent to discreteness) ===")
for lab, (n, adj) in [("Shrikhande", shrikhande())]:
    for k in (1, 2, 3):
        t0 = time.time()
        d = depth_to_discrete(n, adj, k)
        print(f"  {lab} x{k}: n={n*k:3d}  individualizations to discreteness = {d}"
              f"   ({time.time()-t0:.0f}s)")
