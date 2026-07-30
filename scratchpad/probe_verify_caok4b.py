#!/usr/bin/env python3
"""
VERIFY the CFI[K4]-tw counterexample, take 2 — refinement-guided pair search.

Take 1 (all_auts) capped at n=28.  This version never enumerates Aut.  It decides
"same orbit" pairwise by the standard reduction

    u ~_Aut(adj,col) w   <=>   (adj, refine(indiv(col,u)))  iso  (adj, refine(indiv(col,w)))

with the isomorphism decided by refinement-guided backtracking (nauty-style: refine, pick
the first non-singleton cell, branch only inside the corresponding target cell).  Fully
independent of probe_orbit_oracle.canon, whose reliability at n=30 is in doubt
(multipede[6x5] self-inconsistency).
"""
import sys
from collections import defaultdict

sys.path.insert(0, "/workspace/scratchpad")
from probe_dualdeepen import refine, indiv, build_cfi_base, is_aut

def cells(col):
    d = defaultdict(list)
    for v, c in enumerate(col):
        d[c].append(v)
    return d

def profile(col):
    return tuple(sorted((c, len(v)) for c, v in cells(col).items()))

def iso_exists(n, adj, cA, cB, depth=0, budget=None):
    """Is there a colour-preserving automorphism of `adj` carrying colouring cA to cB?"""
    if budget is None:
        budget = [400000]
    budget[0] -= 1
    if budget[0] <= 0:
        return None                                    # inconclusive
    cA = refine(n, adj, cA); cB = refine(n, adj, cB)
    if profile(cA) != profile(cB):
        return False
    dA = cells(cA); dB = cells(cB)
    tgt = [c for c in sorted(dA) if len(dA[c]) >= 2]
    if not tgt:
        # both discrete: the rank-matching map is forced
        ra = {cA[v]: v for v in range(n)}
        rb = {cB[v]: v for v in range(n)}
        sigma = [None] * n
        for c in ra:
            sigma[ra[c]] = rb[c]
        return is_aut(n, adj, sigma)
    c0 = tgt[0]
    x = dA[c0][0]
    unknown = False
    for y in dB[c0]:
        r = iso_exists(n, adj, indiv(n, cA, x), indiv(n, cB, y), depth + 1, budget)
        if r is True:
            return True
        if r is None:
            unknown = True
    return None if unknown else False

def orbit_blocks(n, adj, col, verts):
    """Exact orbit partition of `verts` under Aut(adj,col), pairwise. None if inconclusive."""
    reps = []
    assign = {}
    for v in verts:
        placed = False
        for r in reps:
            res = iso_exists(n, adj, refine(n, adj, indiv(n, col, v)),
                             refine(n, adj, indiv(n, col, r)))
            if res is None:
                return None
            if res:
                assign[v] = r; placed = True; break
        if not placed:
            reps.append(v); assign[v] = v
    return assign

K4 = [(i, j) for i in range(4) for j in range(i + 1, 4)]
n, adj = build_cfi_base(K4, 4, twist=True)
print(f"CFI[K4]-tw : n = {n}")
root = refine(n, adj, [0] * n)
print(f"1-WL root cells: {sorted(len(c) for c in cells(root).values())}")

# ── step 1: exact root orbits, pairwise ───────────────────────────────────────
a0 = orbit_blocks(n, adj, root, list(range(n)))
if a0 is None:
    print("root orbit computation inconclusive"); sys.exit()
b0 = defaultdict(list)
for v in range(n):
    b0[a0[v]].append(v)
print(f"root orbit sizes: {sorted(len(b) for b in b0.values())}")

bad = [c for c in cells(root).values() if len({a0[v] for v in c}) > 1]
print(f"CAO at the 1-WL root: {not bad}"
      + (f"  (mixed cells: {[len(c) for c in bad]})" if bad else ""))

# ── step 2: supply the orbit partition, confirm it is Aut-stable ──────────────
reps = sorted(b0)
rank = {r: i for i, r in enumerate(reps)}
oc = [rank[a0[v]] for v in range(n)]
a1 = orbit_blocks(n, adj, oc, list(range(n)))
if a1 is None:
    print("orbit-partition check inconclusive"); sys.exit()
bad1 = [c for c in cells(oc).values() if len({a1[v] for v in c}) > 1]
print(f"CAO at the SUPPLIED orbit partition: {not bad1}")
if bad1:
    print("  ⚠ supplied partition not Aut-stable — abort"); sys.exit()

# ── step 3: individualize each vertex; does CAO survive? ──────────────────────
print()
hit = False
for v0 in range(n):
    c1 = refine(n, adj, indiv(n, oc, v0))
    a2 = orbit_blocks(n, adj, c1, list(range(n)))
    if a2 is None:
        print(f"  v={v0}: inconclusive"); continue
    mixed = [c for c in cells(c1).values() if len({a2[x] for x in c}) > 1]
    if not mixed:
        continue
    hit = True
    print(f"★★★ v={v0}: CAO BROKEN by one individualization")
    print(f"    1-WL cells: {sorted(len(c) for c in cells(c1).values())}")
    for c in mixed:
        prof = sorted(sum(1 for x in c if a2[x] == o) for o in {a2[x] for x in c})
        print(f"    cell {sorted(c)}  ->  orbit sizes {prof}")
    # explicit witness pair, re-checked directly
    c = mixed[0]
    for i in range(len(c)):
        for j in range(i + 1, len(c)):
            u, w = c[i], c[j]
            if a2[u] != a2[w]:
                direct = iso_exists(n, adj, refine(n, adj, indiv(n, c1, u)),
                                    refine(n, adj, indiv(n, c1, w)))
                print(f"    WITNESS u={u} w={w}: same colour {c1[u]}=={c1[w]}, "
                      f"exists aut u->w = {direct}  (False confirms RigidObstructionAt)")
                sys.exit()
if not hit:
    print("no individualization broke CAO — the earlier hit was a probe artefact")
