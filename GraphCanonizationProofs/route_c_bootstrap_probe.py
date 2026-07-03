#!/usr/bin/env python3
# ROUTE C — META-POLY BOOTSTRAP PROBE (2026-07-03).
#
# The question. Route C's poly claim needs F1 to coordinatize V ~ (F_p)^d in poly time
# WITHOUT already having Aut (computing Aut is the open T0 problem Route C claims to
# sidestep). F1 as built consumes a harvested Aut (T = O_p(Aut)). Is coordinatization
# recoverable from the GRAPH ALONE, in poly time, non-circularly?
#
# The distinction that keeps Route C alive. The node-4 wall is about *bounded-round WL
# refinement* stalling. Coordinatization is a *global* computation (all n vertices, linear
# algebra / geometry), a strictly stronger model where poly is reachable even when bounded
# WL-dim is unbounded. So the concern is NOT the node-4 wall in disguise — IF a concrete
# global Aut-free procedure exists. This probe tests the enabling geometric step:
#
#   Can the isotropic-LINE geometry through a vertex o be recovered from adjacency alone?
#   (Lines -> polar-space geometry -> coordinates by Buekenhout-Shult/fund. thm of geometry,
#    which is poly + citable for rank >= 3, i.e. d >= 6; d = 4 is the special GQ case.)
#
# Concretely: for triangles (o,x,y) with x,y in N(o), does a LOCAL graph invariant separate
# "o,x,y collinear on an isotropic line" from "isotropic but non-collinear"? If yes, lines are
# poly-recoverable from the graph (no Aut), the enabling step for geometric coordinatization.

import sys
from itertools import combinations
sys.path.insert(0, '.')
from model_gap import make_Q, sub, span_of

def build(d, q, eps):
    Q = make_Q(d, q, eps)
    V = [tuple((i // q**k) % q for k in range(d)) for i in range(q**d)]
    pos = {v: i for i, v in enumerate(V)}
    n = len(V)
    # adjacency as neighbor-sets keyed by vertex index; x~y iff Q(x-y)=0, x!=y
    adj = [set() for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if Q(sub(V[i], V[j], q, d)) == 0:
                adj[i].add(j); adj[j].add(i)
    return Q, V, pos, n, adj

def dependent(x, y, q, d):
    # are x, y linearly dependent over F_q (both nonzero): y = c*x for some c
    for c in range(q):
        if all((c * x[k]) % q == y[k] for k in range(d)):
            return True
    for c in range(q):
        if all((c * y[k]) % q == x[k] for k in range(d)):
            return True
    return False

def run(d, q, eps):
    Q, V, pos, n, adj = build(d, q, eps)
    o = pos[tuple(0 for _ in range(d))]
    No = adj[o]                       # cone points (neighbors of origin)
    Noset = set(No)
    name = f"VO^{'+' if eps>0 else '-'}_{d}({q}) n={n} |N(o)|={len(No)}"

    # For each isotropic triangle (o,x,y): x,y in N(o), x~y. Compute a local invariant and
    # compare against ground-truth collinearity. Invariant = # common cone-neighbors of x,y
    # that are ALSO cone points (|N(o) ∩ N(x) ∩ N(y)|), a purely local count.
    coll_vals, noncoll_vals = [], []
    triangles = 0
    for x, y in combinations(No, 2):
        if y not in adj[x]:
            continue                  # need x~y (a triangle with o)
        triangles += 1
        inv = len(Noset & adj[x] & adj[y])
        if dependent(V[x], V[y], q, d):
            coll_vals.append(inv)
        else:
            noncoll_vals.append(inv)

    cset, ncset = set(coll_vals), set(noncoll_vals)
    separated = cset.isdisjoint(ncset)
    print(f"{name}: triangles(o,x,y)={triangles}")
    print(f"    collinear   inv-values: {sorted(cset)}  (count {len(coll_vals)})")
    print(f"    NONcollinear inv-values: {sorted(ncset)[:8]}{'...' if len(ncset)>8 else ''}  (count {len(noncoll_vals)})")
    print(f"    >>> local invariant SEPARATES collinear from non-collinear: {separated}")

    if separated:
        # Reconstruct the isotropic lines through o from the graph via the invariant, then
        # check they SPAN V (the enabling property for coordinatization). A line through o =
        # a maximal set L ⊆ N(o)∪{o} with all triangles (o,x,y), x,y∈L, collinear-per-invariant.
        thr = max(cset)               # collinear <=> inv >= thr (see values); use membership in cset
        # group cone points by the equivalence "x ~coll y" (invariant says collinear)
        parent = {v: v for v in No}
        def find(a):
            while parent[a] != a:
                parent[a] = parent[parent[a]]; a = parent[a]
            return a
        def union(a, b):
            parent[find(a)] = find(b)
        for x, y in combinations(No, 2):
            if y in adj[x] and (len(Noset & adj[x] & adj[y]) in cset) and \
               (len(Noset & adj[x] & adj[y]) not in ncset):
                union(x, y)
        lines = {}
        for v in No:
            lines.setdefault(find(v), []).append(v)
        # collect one representative direction per recovered line; check they span V
        dirs = [V[cls[0]] for cls in lines.values()]
        sp = span_of(q, [tuple(dd) for dd in dirs], d)
        print(f"    recovered lines: {len(lines)} classes; sizes {sorted(set(len(c) for c in lines.values()))}; "
              f"directions span dim {len(sp) if isinstance(sp,(list,set)) else '?'} (want {q**d})")
    print()

if __name__ == "__main__":
    for (d, q, eps) in [(4,3,+1),(4,3,-1),(4,5,+1),(4,5,-1),(6,3,+1),(6,3,-1)]:
        run(d, q, eps)
