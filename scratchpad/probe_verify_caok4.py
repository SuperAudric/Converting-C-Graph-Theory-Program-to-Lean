#!/usr/bin/env python3
"""
VERIFY the CFI[K4]-tw counterexample to "CAO propagates", WITHOUT the canon oracle.

probe_cao_propagates.py reported: starting from the exact orbit partition of CFI[K4]-tw,
individualizing vertex 0 and taking the 1-WL closure leaves cells with orbit sizes
[[1,2],[4,8]].  But the same run produced a self-inconsistent `sanity-fail` on
multipede[6x5], so the oracle is not trustworthy here.

This script re-derives everything by DIRECT automorphism enumeration (backtracking over
the colour classes), which is independent of probe_orbit_oracle.canon:

  1. enumerate Aut(adj) explicitly  -> exact root orbit partition
  2. supply it as the colouring, confirm CAO holds
  3. individualize 0, 1-WL close
  4. enumerate Aut(adj, col_1) explicitly -> exact orbits
  5. report any cell containing two vertices with NO automorphism between them,
     and print the explicit witness pair
"""
import sys
from collections import defaultdict

sys.path.insert(0, "/workspace/scratchpad")
from probe_dualdeepen import refine, indiv, build_cfi_base

def all_auts(n, adj, col, cap=4_000_000):
    """Every colour-preserving automorphism, by backtracking. Exact (or None if capped)."""
    bycol = defaultdict(list)
    for v in range(n):
        bycol[col[v]].append(v)
    order = sorted(range(n), key=lambda v: (len(bycol[col[v]]), col[v], v))
    nbr = [[u for u in range(n) if adj[v][u]] for v in range(n)]
    nbrset = [set(x) for x in nbr]
    img = [None] * n
    used = [False] * n
    out = []
    budget = [cap]

    def rec(i):
        if budget[0] <= 0:
            return False
        budget[0] -= 1
        if i == len(order):
            out.append(tuple(img))
            return True
        v = order[i]
        for w in bycol[col[v]]:
            if used[w] or len(nbr[v]) != len(nbr[w]):
                continue
            ok = True
            for u in range(n):
                iu = img[u]
                if iu is None:
                    continue
                if (u in nbrset[v]) != (iu in nbrset[w]):
                    ok = False
                    break
            if not ok:
                continue
            img[v] = w; used[w] = True
            rec(i + 1)
            img[v] = None; used[w] = False
        return True

    rec(0)
    return None if budget[0] <= 0 else out

def orbits_from_auts(n, auts):
    par = list(range(n))
    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]; x = par[x]
        return x
    for g in auts:
        for i in range(n):
            a, b = f(i), f(g[i])
            if a != b:
                par[a] = b
    return [f(i) for i in range(n)]

def cells(col):
    d = defaultdict(list)
    for v, c in enumerate(col):
        d[c].append(v)
    return list(d.values())

K4 = [(i, j) for i in range(4) for j in range(i + 1, 4)]
n, adj = build_cfi_base(K4, 4, twist=True)
print(f"CFI[K4]-tw : n = {n}")

root = refine(n, adj, [0] * n)
print(f"1-WL root cells: {sorted(len(c) for c in cells(root))}")

A0 = all_auts(n, adj, root)
if A0 is None:
    print("aut enumeration capped at the root — inconclusive"); sys.exit()
print(f"|Aut(adj, 1-WL root)| = {len(A0)}")

orb0 = orbits_from_auts(n, A0)
blocks0 = defaultdict(list)
for v in range(n):
    blocks0[orb0[v]].append(v)
print(f"root orbit sizes: {sorted(len(b) for b in blocks0.values())}")

# step 2: supply the orbit partition as the colouring
reps = sorted(blocks0)
rank = {r: i for i, r in enumerate(reps)}
oc = [rank[orb0[v]] for v in range(n)]
A1 = all_auts(n, adj, oc)
orb1 = orbits_from_auts(n, A1)
bad0 = [c for c in cells(oc) if len({orb1[v] for v in c}) > 1]
print(f"CAO at the supplied orbit partition: {not bad0}   (|Aut| = {len(A1)})")
if bad0:
    print("  ⚠ sanity failure — the supplied partition is not Aut-stable; abort")
    sys.exit()

# step 3+4: individualize 0, 1-WL close, exact orbits
print()
for v0 in range(min(n, 28)):
    c1 = refine(n, adj, indiv(n, oc, v0))
    A2 = all_auts(n, adj, c1)
    if A2 is None:
        print(f"  v={v0}: aut enumeration capped — skipped")
        continue
    orb2 = orbits_from_auts(n, A2)
    mixed = [c for c in cells(c1) if len({orb2[x] for x in c}) > 1]
    if not mixed:
        continue
    print(f"★★★ individualizing v={v0}: CAO BROKEN.  |Aut(adj,col_1)| = {len(A2)}")
    print(f"    1-WL cells: {sorted(len(c) for c in cells(c1))}")
    for c in mixed:
        prof = sorted(sum(1 for x in c if orb2[x] == o) for o in {orb2[x] for x in c})
        print(f"    cell {sorted(c)} -> orbit sizes {prof}")
        # explicit witness pair with NO automorphism between them
        for i in range(len(c)):
            for j in range(i + 1, len(c)):
                u, w = c[i], c[j]
                if orb2[u] != orb2[w]:
                    ex = any(g[u] == w for g in A2)
                    print(f"      witness: u={u}, w={w} share colour {c1[u]}, "
                          f"exists aut u->w: {ex}  (must be False)")
                    break
            else:
                continue
            break
    break
else:
    print("no individualization broke CAO (verified by direct enumeration)")
