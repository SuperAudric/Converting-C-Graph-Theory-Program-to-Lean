#!/usr/bin/env python3
"""
probe_coset.py — WITNESS vs RELATION: why cross-cell information is non-canonical  (2026-08-07)

============================================================================================
THE CLAIM BEING TESTED (user, 2026-08-07)
============================================================================================
  > every descent contains every vertex, so either it is guaranteed to find a valid descent
  > in that other cell AND that automorphism moves within the cell, OR it will find nothing.
  > That should be canonical.

The dichotomy assumes deepen finds *the* automorphism for a pair, or none.  What it actually
finds is *an* automorphism realising the pair — one member of a coset `t · Stab(r₁)`.  Two
members of that coset agree on the branch cell (both send `r₁ ↦ rⱼ`) and can act COMPLETELY
DIFFERENTLY on another cell.  Which member you get is decided by the descent's lowest-index
tie-breaks, hence by the labelling.

So the third case the dichotomy is missing is:
    "it finds a valid automorphism for the pair, which happens to FIX the other cell,
     while an equally valid one that SWAPS it also exists."

============================================================================================
WHAT IS DEMONSTRATED
============================================================================================
At the recorded falsifier (CFI cubic m=8, depth 1, off-branch colour 13, guard OPEN on both
sides, count `(2,)` vs `(1,1)`), `deepenGens` is re-run with per-generator provenance:

    for each ordered branch-cell pair (r₁, rⱼ) that yields a verified twist `t`,
    record whether `t` moves the off-branch cell `c` at all.

Then the SAME pair is followed through a relabelling σ — pair `(σ r₁, σ rⱼ)` — and the two
witnesses are compared.  A pair where the witness moves `c` on one side and fixes it on the
other IS the coset ambiguity, exhibited.

Also reported, to separate the two levels:
  * BRANCH pair-relation identical on both sides?   (the CANONICAL object — the guard's content)
  * off-branch action identical on both sides?      (the NON-canonical object — the witness)

    cd /workspace/scratchpad && python3 -u probe_coset.py > probe_coset.out 2>&1
"""
import random
import sys
from collections import defaultdict

sys.setrecursionlimit(10000)
sys.path.insert(0, '/workspace/scratchpad')

from probe_dualdeepen import build_cfi_base, cubic
from probe_polyloop import (adjlist, refine, indiv, target_cell,
                            greedy_deepen, replay, twist)
from probe_offbranch import orbits_all, relabel


def gens_with_provenance(n, adj, adjl, chi, C):
    """`deepenGens`, but returning (r1, rj, perm) so each generator keeps its defining pair."""
    out = []
    firsts = {r: indiv(n, adjl, chi, r) for r in C}
    for r1 in sorted(C):
        leaf1, seq = greedy_deepen(n, adjl, firsts[r1])
        if leaf1 is None:
            continue
        for rj in sorted(C):
            if rj == r1:
                continue
            leafj = replay(n, adjl, firsts[rj], seq)
            if leafj is None:
                continue
            t = twist(n, adj, chi, leaf1, leafj)
            if t is not None:
                out.append((r1, rj, t))
    return out


def cells_of(n, col):
    d = defaultdict(list)
    for v in range(n):
        d[col[v]].append(v)
    return {c: m for c, m in d.items() if len(m) >= 2}


def main():
    n, adj = build_cfi_base(cubic(8, seed=8), 8, twist=False)
    adjl = adjlist(n, adj)
    col0 = refine(n, adjl, [0] * n)

    # the depth-1 node and the relabelling where probe_offbranch2/3 recorded the failure
    rng = random.Random(abs(hash("CFI cubic m=8 pl")) & 0xffff)
    sigmas = []
    for _ in range(4):
        s = list(range(n))
        rng.shuffle(s)
        sigmas.append(s)

    cid0, C0 = target_cell(n, col0)
    target = None
    for v in sorted(C0)[:3]:
        col = indiv(n, adjl, col0, v)
        cid, C = target_cell(n, col)
        if cid is None:
            continue
        gA = [g for _, _, g in gens_with_provenance(n, adj, adjl, col, C)]
        orbA = orbits_all(n, gA)
        cells = cells_of(n, col)
        for s in sigmas:
            adj2 = relabel(n, adj, s)
            adjl2 = adjlist(n, adj2)
            col2 = [0] * n
            for w in range(n):
                col2[s[w]] = col[w]
            cid2, C2 = target_cell(n, col2)
            gB = [g for _, _, g in gens_with_provenance(n, adj2, adjl2, col2, C2)]
            orbB = orbits_all(n, gB)
            for c, mem in cells.items():
                if c == cid:
                    continue
                mem2 = [s[x] for x in mem]
                a = len({orbA[x] for x in mem})
                b = len({orbB[x] for x in mem2})
                if a != b:
                    target = (v, col, cid, C, c, mem, s, adj2, adjl2, col2, cid2, C2, a, b)
                    break
            if target:
                break
        if target:
            break

    if target is None:
        print("no falsifier reproduced — nothing to demonstrate")
        return

    v, col, cid, C, c, mem, s, adj2, adjl2, col2, cid2, C2, a, b = target
    print(f"CFI cubic m=8 pl, n={n}")
    print(f"  node        : root individualized at {v}  (depth 1)")
    print(f"  branch cell : colour {cid}, size {len(C)}")
    print(f"  off-branch  : colour {c}, size {len(mem)} = {mem}")
    print(f"  harvest orbit-blocks on that cell:  side A = {a},  side B = {b}   <<< the falsifier")
    print()

    PA = gens_with_provenance(n, adj, adjl, col, C)
    PB = gens_with_provenance(n, adj2, adjl2, col2, C2)

    relA = {(r1, rj) for r1, rj, _ in PA}
    relB = {(r1, rj) for r1, rj, _ in PB}
    relB_back = {(x, y) for x, y in relB}
    relA_fwd = {(s[x], s[y]) for x, y in relA}
    print(f"  BRANCH pair-relation (the CANONICAL object the guard certifies):")
    print(f"    |pairs| A = {len(relA)},  |pairs| B = {len(relB)},  "
          f"σ(A) == B ? {'YES' if relA_fwd == relB_back else 'NO'}")

    memset = set(mem)
    memset2 = {s[x] for x in mem}
    actA = {}
    for r1, rj, t in PA:
        actA[(r1, rj)] = any(t[x] != x for x in memset)
    actB = {}
    for r1, rj, t in PB:
        actB[(r1, rj)] = any(t[x] != x for x in memset2)

    movA = sum(actA.values())
    movB = sum(actB.values())
    print(f"  WITNESS action on colour {c} (the NON-canonical object):")
    print(f"    A: {movA}/{len(actA)} witnesses move that cell")
    print(f"    B: {movB}/{len(actB)} witnesses move that cell")
    print()

    diffs = []
    for (r1, rj), m1 in actA.items():
        key = (s[r1], s[rj])
        if key in actB and actB[key] != m1:
            diffs.append((r1, rj, m1, actB[key]))
    print(f"  ★ SAME PAIR, DIFFERENT WITNESS BEHAVIOUR OFF-CELL: {len(diffs)} of {len(actA)} pairs")
    for r1, rj, m1, m2 in diffs[:6]:
        print(f"      pair ({r1:3d} -> {rj:3d})  [σ: ({s[r1]:3d} -> {s[rj]:3d})]   "
              f"moves colour {c}?   A={m1}   B={m2}")
    if not diffs:
        print("      none — the coset explanation is NOT confirmed by this instance")
    print()
    print("  Reading: the branch-cell pair relation is the same object on both sides (the guard's")
    print("  content, canonical).  The individual automorphism realising a given pair is not —")
    print("  it is one member of t·Stab(r₁), and members of that coset differ off the cell.")


if __name__ == '__main__':
    main()
