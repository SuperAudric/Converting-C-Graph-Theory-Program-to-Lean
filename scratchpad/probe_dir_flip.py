#!/usr/bin/env python3
"""
PROBE (2026-08-02): can mixed-cell picks made BEFORE identification flip the direction
of the 1-WL comparison?  (user's sharpened question)

No reference "correct" direction is needed: if two legal choice sequences on the SAME
labelled graph emit opposite directions, the read is not a function of the isomorphism
type, full stop.  Relabelling is just one way to vary the pick sequence; here we vary it
directly, which is the targeted test.

Instances: (graph, prefix of individualizations, pair u,w in one 1-WL cell but different
Aut-orbits).  We also count how many MIXED cells were individualized before divergence.

Clean-room: own 1-WL, own exact coloured-automorphism enumeration (IR backtracking),
no orbit oracle.
"""
import random, sys, itertools
from collections import defaultdict

# ---------- 1-WL -------------------------------------------------------------
def refine(n, adj, col):
    col = list(col)
    while True:
        sig = [(col[v], tuple(sorted(col[u] for u in adj[v]))) for v in range(n)]
        order = {s: i for i, s in enumerate(sorted(set(sig)))}
        new = [order[s] for s in sig]
        if new == col:
            return col
        col = new

def indiv(n, col, v):
    return [2 * c + (1 if u == v else 0) for u, c in enumerate(col)]

def signature(col):
    d = defaultdict(int)
    for c in col:
        d[c] += 1
    return tuple(sorted(d.items()))

def cells(col):
    d = defaultdict(list)
    for v, c in enumerate(col):
        d[c].append(v)
    return d

def target(col):
    d = cells(col)
    ns = [c for c in sorted(d) if len(d[c]) > 1]
    return (ns[0], d[ns[0]]) if ns else (None, None)

# ---------- exact colour-preserving automorphisms ----------------------------
def all_auts(n, adj, col, cap=500000):
    aset = [set(a) for a in adj]
    out = []
    def rec(c):
        cid, cell = target(c)
        if cid is None:
            perm = [0]*n
            inv = {x: v for v, x in enumerate(c)}
            base = sorted(range(n), key=lambda v: c[v])
            # c is discrete: colour -> vertex, compare against the reference discrete col
            for v in range(n):
                perm[v] = inv[ref[v]]
            for v in range(n):
                if {perm[u] for u in aset[v]} != aset[perm[v]]:
                    return
            out.append(perm)
            return
        a = min(cell)
        for b in cell:
            if len(out) >= cap:
                return
            rec(refine(n, adj, indiv(n, c, b)))
    # reference discrete colouring: follow min-pick path
    ref = list(col)
    while True:
        cid, cell = target(ref)
        if cid is None: break
        ref = refine(n, adj, indiv(n, ref, min(cell)))
    rec(list(col))
    return out

def orbits_of(n, auts):
    p = list(range(n))
    def f(x):
        while p[x] != x: p[x] = p[p[x]]; x = p[x]
        return x
    for a in auts:
        for v in range(n):
            rv, rw = f(v), f(a[v])
            if rv != rw: p[rv] = rw
    return [f(v) for v in range(n)]

# ---------- the scheme, with RANDOMIZED picks --------------------------------
def scheme_rand(n, adj, col, u, w, rng, orb=None):
    """returns (verdict, nmixed) where verdict in {SYM, LT, GT} and nmixed = number of
    individualized cells that were orbit-MIXED before the verdict was reached."""
    A = refine(n, adj, indiv(n, col, u))
    B = refine(n, adj, indiv(n, col, w))
    nmixed = 0
    if signature(A) != signature(B):
        return verdict(A, B), nmixed
    while True:
        cidA, cellA = target(A)
        cidB, cellB = target(B)
        if cidA is None and cidB is None:
            inv = {c: v for v, c in enumerate(B)}
            perm = [inv[A[v]] for v in range(n)]
            aset = [set(x) for x in adj]
            ok = all({perm[y] for y in aset[v]} == aset[perm[v]] for v in range(n))
            return ('SYM' if ok else verdict(A, B)), nmixed
        if cidA != cidB:
            return verdict(A, B), nmixed
        if orb is not None and len({orb[x] for x in cellA}) > 1:
            nmixed += 1
        a = rng.choice(cellA)
        A2 = refine(n, adj, indiv(n, A, a))
        sA = signature(A2)
        cands = []
        for b in cellB:
            B2 = refine(n, adj, indiv(n, B, b))
            if signature(B2) == sA:
                cands.append(B2)
        if not cands:
            return verdict(A2, refine(n, adj, indiv(n, B, rng.choice(cellB)))), nmixed
        A, B = A2, rng.choice(cands)

def verdict(A, B):
    sA, sB = signature(A), signature(B)
    if sA == sB: return 'TIE'
    return 'LT' if sA < sB else 'GT'

# ---------- graphs -----------------------------------------------------------
def net(q, group='Z'):
    """3-net of an abelian group of order q: points GxG, lines x=a, y=b, x+y=c."""
    if group == 'Z':
        add = lambda a, b: (a + b) % q
        els = list(range(q))
    else:                                   # Z2 x Z2
        els = [(0,0),(0,1),(1,0),(1,1)]
        add = lambda a, b: ((a[0]^b[0]), (a[1]^b[1]))
    pts = [(x, y) for x in els for y in els]
    lines = [('x', a) for a in els] + [('y', b) for b in els] + [('s', c) for c in els]
    n = len(pts) + len(lines)
    idx = {p: i for i, p in enumerate(pts)}
    for j, L in enumerate(lines): idx[L] = len(pts) + j
    adj = [[] for _ in range(n)]
    def E(a, b):
        adj[a].append(b); adj[b].append(a)
    for (x, y) in pts:
        E(idx[(x,y)], idx[('x', x)])
        E(idx[(x,y)], idx[('y', y)])
        E(idx[(x,y)], idx[('s', add(x, y))])
    return n, [sorted(a) for a in adj]

def shrikhande():
    n = 16
    adj = [[] for _ in range(n)]
    S = [(1,0),(3,0),(0,1),(0,3),(1,1),(3,3)]
    def i(x, y): return 4*x + y
    for x in range(4):
        for y in range(4):
            for (dx, dy) in S:
                u, v = i(x,y), i((x+dx)%4, (y+dy)%4)
                if v not in adj[u]: adj[u].append(v)
    return n, [sorted(a) for a in adj]

def t8_chang(switch):
    """T(8) = triangular graph on 8 points; Seidel-switch w.r.t. `switch` (a set of
    2-subsets).  switch = 8-cycle edges -> Chang-2."""
    V = list(itertools.combinations(range(8), 2))
    n = len(V)
    idx = {e: i for i, e in enumerate(V)}
    A = [[0]*n for _ in range(n)]
    for i in range(n):
        for j in range(i+1, n):
            if set(V[i]) & set(V[j]):
                A[i][j] = A[j][i] = 1
    S = {idx[e] for e in switch}
    for i in range(n):
        for j in range(i+1, n):
            if (i in S) != (j in S):
                A[i][j] = A[j][i] = 1 - A[i][j]
    return n, [[j for j in range(n) if A[i][j]] for i in range(n)]

def disjoint(n1, a1, n2, a2):
    return n1+n2, [sorted(a1[v]) for v in range(n1)] + [sorted(x+n1 for x in a2[v]) for v in range(n2)]

# ---------- instance generation ----------------------------------------------
def instances(name, n, adj, max_prefix=2, max_pairs=6):
    """yield (label, colouring, u, w) with u,w same colour, different Aut-orbits."""
    root = refine(n, adj, [0]*n)
    frontier = [([], root)]
    seen = 0
    for depth in range(max_prefix + 1):
        nxt = []
        for prefix, col in frontier:
            auts = all_auts(n, adj, col)
            orb = orbits_of(n, auts)
            found = 0
            for cid, cell in sorted(cells(col).items()):
                if len(cell) < 2: continue
                byorb = defaultdict(list)
                for v in cell: byorb[orb[v]].append(v)
                if len(byorb) > 1:
                    reps = [vs[0] for vs in byorb.values()]
                    for u, w in itertools.combinations(reps, 2):
                        yield (f"{name} prefix={prefix} cell{cid}({len(cell)})"
                               f" orbs={sorted(len(v) for v in byorb.values())}",
                               col, u, w, orb, len(auts))
                        found += 1
                        if found >= max_pairs: break
                if found >= max_pairs: break
            if depth < max_prefix:
                cid, cell = target(col)
                if cid is not None:
                    for b in cell[:3]:
                        nxt.append((prefix + [b], refine(n, adj, indiv(n, col, b))))
        frontier = nxt

# ---------- run ---------------------------------------------------------------
def run(name, n, adj, trials=120, max_prefix=2):
    print(f"\n{'='*78}\n{name}  n={n}\n{'='*78}")
    any_inst = False
    flips = 0
    for label, col, u, w, orb, na in instances(name, n, adj, max_prefix=max_prefix):
        any_inst = True
        rng = random.Random(5)
        tally = defaultdict(int); mx = 0
        for _ in range(trials):
            v, nm = scheme_rand(n, adj, col, u, w, rng, orb)
            tally[v] += 1; mx = max(mx, nm)
        dirs = {k for k in tally if k in ('LT', 'GT')}
        flag = ""
        if len(dirs) > 1:
            flag = "   *** DIRECTION FLIP ***"; flips += 1
        elif 'SYM' in tally and dirs:
            flag = "   (sym/diverge split)"
        print(f"  {label}  |Aut_chi|={na}  pair=({u},{w})")
        print(f"     {dict(sorted(tally.items()))}  maxMixedPicksBefore={mx}{flag}")
    if not any_inst:
        print("  (no mixed cell found at depth <= %d)" % max_prefix)
    return flips

if __name__ == "__main__":
    tot = 0
    n, a = net(4);          tot += run("net(Z4) = CFI[K4]-tw", n, a, max_prefix=2)
    n, a = shrikhande();    tot += run("Shrikhande", n, a, max_prefix=2)
    n, a = net(6);          tot += run("net(Z6)", n, a, max_prefix=1, trials=60)
    C8 = [(i, (i+1) % 8) for i in range(8)]
    C8 = [tuple(sorted(e)) for e in C8]
    n, a = t8_chang(C8);    tot += run("Chang-2 (C8 switch of T(8))", n, a, max_prefix=1, trials=60)
    n1, a1 = shrikhande(); n2, a2 = shrikhande()
    n, a = disjoint(n1, a1, n2, a2)
    tot += run("Shrikhande + Shrikhande", n, a, max_prefix=2, trials=60)
    print(f"\n>>> TOTAL DIRECTION FLIPS: {tot}")
