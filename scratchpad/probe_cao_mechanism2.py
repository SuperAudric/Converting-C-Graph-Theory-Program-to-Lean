#!/usr/bin/env python3
"""WHERE DOES THE BLIND SPOT ACTUALLY SIT?  (2026-07-30, after the G(+)G critique)

Exact mechanism: individualizing v (in cell D) changes cell C's orbits ONLY by fibring C
over the Aut-orbitals inside D x C -- orbital O contributes {u in C : (v,u) in O}, of size
|O|/|D|.  2-WL detects the change iff its closure SEPARATES those orbitals.

So a CAO failure needs two things AT THE SAME PLACE:
   (group side)  Aut_v must act on C with >= 2 orbits      -- "the individualization reaches C"
   (combi side)  the closure must FUSE those orbitals      -- "the deficiency lives at C"

G (+) G shows these can be pulled APART: the deficiency survives in the untouched copy, but
the group is untouched there too, so the fibres are still orbits and CAO holds.  Measure that
directly: at depth 1 of Shrikhande (+) Shrikhande, WHICH pairs sit in a fused class?
"""
import sys
from collections import defaultdict
sys.path.insert(0, "/workspace/scratchpad")
from probe_cao_cleanroom import wl, individualize, cells, all_isos, orbits
from probe_cao_induction import (twowl_pairs, orbital_partition, same_partition,
                                 shrikhande, T8, chang)
from probe_cao_union import disjoint, lift
from probe_cao_net import net

sys.setrecursionlimit(100000)


def fused_pairs(N, U, col, gens):
    """Pairs whose 2-WL class strictly contains >1 orbital: (class -> #orbitals)."""
    p2 = twowl_pairs(N, U, col)
    orbl = orbital_partition(N, gens)
    byclass = defaultdict(set)
    for i in range(N * N):
        byclass[p2[i]].add(orbl[i])
    fused = {c: len(o) for c, o in byclass.items() if len(o) > 1}
    members = defaultdict(list)
    for i in range(N * N):
        if p2[i] in fused:
            members[p2[i]].append((i // N, i % N))
    return fused, members, p2, orbl


def report_union(lab, n, adj):
    A = all_isos(n, adj, wl(n, adj, [0] * n), wl(n, adj, [0] * n), limit=3_000_000)
    ident = tuple(range(n))
    N, U = disjoint(n, adj)
    gens_root = (lift(A, [ident], n) + lift([ident], A, n)
                 + lift([ident], [ident], n, swap=True))
    orb = orbits(N, gens_root)
    m = {}
    oc = [m.setdefault(orb[v], len(m)) for v in range(N)]
    Av = [g for g in A if g[0] == 0]
    gens_v = lift(Av, [ident], n) + lift([ident], A, n)
    col1 = individualize(N, oc, 0)
    fused, members, p2, orbl = fused_pairs(N, U, col1, gens_v)
    print(f"\n=== {lab} (+) {lab}, depth 1 (v=0 in copy A), n={N} ===")
    print(f"  fused 2-WL classes: {len(fused)}  (class -> #orbitals merged: "
          f"{sorted(fused.values())})")
    loc = defaultdict(int)
    for c in fused:
        for (a, b) in members[c]:
            ca = 'A' if a < n else 'B'
            cb = 'A' if b < n else 'B'
            loc[ca + cb] += 1
    print(f"  WHERE the fused pairs live: {dict(sorted(loc.items()))}")
    print("  (AA = both endpoints in the individualized copy, BB = both in the untouched copy)")
    # does the group actually change on each copy?
    orbv = orbits(N, gens_v)
    sizesA = sorted({sum(1 for x in range(n) if orbv[x] == orbv[u]) for u in range(n)})
    sizesB = sorted({sum(1 for x in range(n, N) if orbv[x] == orbv[u]) for u in range(n, N)})
    print(f"  Aut_v-orbit sizes inside copy A (reached): {sizesA}")
    print(f"  Aut_v-orbit sizes inside copy B (untouched): {sizesB}"
          f"   <- one orbit => fibres trivially = orbits, CAO cannot fail there")


def report_single(lab, n, adj):
    """At the ROOT of a deficient object: which orbitals does the closure fuse?"""
    A = all_isos(n, adj, wl(n, adj, [0] * n), wl(n, adj, [0] * n), limit=3_000_000)
    orb = orbits(n, A)
    m = {}
    oc = [m.setdefault(orb[v], len(m)) for v in range(n)]
    fused, members, p2, orbl = fused_pairs(n, adj, oc, A)
    print(f"\n=== {lab}, ROOT, n={n} ===")
    print(f"  2-WL classes {len(set(p2))} vs orbitals {len(set(orbl))}; fused classes: "
          f"{len(fused)} merging {sorted(fused.values())} orbitals")
    for c in sorted(fused):
        os_ = defaultdict(int)
        for (a, b) in members[c]:
            os_[orbl[a * n + b]] += 1
        # valency of each merged orbital, from a fixed first coordinate
        v0 = members[c][0][0]
        val = defaultdict(int)
        for (a, b) in members[c]:
            if a == v0:
                val[orbl[a * n + b]] += 1
        print(f"    class {c}: orbital sizes {sorted(os_.values())}, "
              f"VALENCIES from one point {sorted(val.values())}")


for lab, (n, adj) in [("Shrikhande", shrikhande())]:
    report_single(lab, n, adj)
report_single("net(Z4)", *net((4,))[:2])
report_single("Chang-2", *chang([(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,0)]))
report_union("Shrikhande", *shrikhande())
