#!/usr/bin/env python3
"""
PROBE (2026-08-02): the user's "lift the divergence verdict to the ROOT" design.

Scheme under test (poly, no backtracking, no stall):
  - pick u, w in one 1-WL root cell; individualize each in its own instance; 1-WL.
  - repeatedly: target cell = lowest canonical colour id that is non-singleton (same id in
    both instances while signatures agree); pick a vertex in each; individualize; 1-WL.
  - if the colour signatures ever disagree -> DIVERGENCE; 1-WL's "opinion" = which side is
    lexicographically smaller -> emit a strict order u < w (or w < u) AT THE ROOT.
  - if it runs to discrete with signatures matching -> candidate automorphism, VERIFIED.

Invariance test: the verdict is a claim about the ABSTRACT pair. Run the same abstract
(G, u, w) under many relabellings.  An iso-invariant scheme must return the same verdict
every time.  Clean-room: own 1-WL, own automorphism check, hand-known orbits, NO oracle.

Beam width W generalises the scheme: W=1 is the deterministic no-stall version; larger W
is bounded backtracking (still poly for fixed W).
"""
import random, sys
from collections import defaultdict

# ---------- 1-WL with canonical colour ids ----------------------------------
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
    """Iso-invariant fingerprint of a colouring: the multiset of colour class sizes,
    keyed by colour id (ids are canonical because refine() sorts signatures)."""
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
    """lowest canonical colour id among non-singleton cells"""
    d = cells(col)
    ns = [c for c in sorted(d) if len(d[c]) > 1]
    return (ns[0], d[ns[0]]) if ns else (None, None)

# ---------- exact automorphism check ----------------------------------------
def is_aut(n, adj, perm):
    aset = [set(adj[v]) for v in range(n)]
    for v in range(n):
        if {perm[u] for u in aset[v]} != aset[perm[v]]:
            return False
    return True

# ---------- the scheme ------------------------------------------------------
def scheme(n, adj, root, u, w, width=1):
    """returns ('SYM', perm) | ('LT', trace) meaning u<w | ('GT', trace) meaning w<u"""
    A = refine(n, adj, indiv(n, root, u))
    Bs = [(refine(n, adj, indiv(n, root, w)), {u: w})]
    if signature(A) != signature(Bs[0][0]):
        return verdict(A, Bs[0][0])
    while True:
        cidA, cellA = target(A)
        if cidA is None:                       # A is discrete
            for B, m in Bs:
                if target(B)[0] is None:
                    # read off the bijection from matching colours
                    posA = {c: v for v, c in enumerate(A)}
                    perm = [0] * n
                    for v in range(n):
                        perm[posA[A[v]]] = [x for x in range(n) if B[x] == A[v]][0]
                    perm = [None] * n
                    invB = {c: v for v, c in enumerate(B)}
                    for v in range(n):
                        perm[v] = invB[A[v]]
                    if is_aut(n, adj, perm):
                        return ('SYM', perm)
            return verdict(A, Bs[0][0])
        a = min(cellA)
        A2 = refine(n, adj, indiv(n, A, a))
        sA = signature(A2)
        nxt = []
        for B, m in Bs:
            cidB, cellB = target(B)
            if cidB != cidA:
                continue
            for b in cellB:
                B2 = refine(n, adj, indiv(n, B, b))
                if signature(B2) == sA:
                    m2 = dict(m); m2[a] = b
                    nxt.append((B2, m2))
                    if len(nxt) >= width:
                        break
            if len(nxt) >= width:
                break
        if not nxt:
            return verdict(A2, Bs[0][0])
        A, Bs = A2, nxt

def verdict(A, B):
    """1-WL's opinion: lexicographically smaller signature side comes first."""
    sA, sB = signature(A), signature(B)
    return ('LT', (sA, sB)) if sA <= sB else ('GT', (sA, sB))

# ---------- graphs ----------------------------------------------------------
def relabel(n, adj, sig):
    out = [[] for _ in range(n)]
    for v in range(n):
        for u in adj[v]:
            out[sig[v]].append(sig[u])
    return [sorted(x) for x in out]

def c3c4(copies=2, k1=3, k2=4):
    per = 1 + k1 + k2
    n = per * copies
    adj = [[] for _ in range(n)]
    def E(a, b):
        adj[a].append(b); adj[b].append(a)
    for c in range(copies):
        b = c * per
        C1 = [b + 1 + i for i in range(k1)]
        C2 = [b + 1 + k1 + i for i in range(k2)]
        for i in range(k1): E(C1[i], C1[(i + 1) % k1])
        for i in range(k2): E(C2[i], C2[(i + 1) % k2])
        for v in C1 + C2: E(b, v)
    return n, [sorted(x) for x in adj], [c * per for c in range(copies)]

def cay_z12_5_z2(S=((0,1),(1,1),(2,1),(4,1),(7,1))):
    """Cay(Z12 :_5 Z2), n=24, the VT non-Tinhofer witness. (r,s) -> 2r+s."""
    def mul(x, y):
        r1,s1 = x; r2,s2 = y
        return ((r1 + (5**s1) * r2) % 12, (s1 + s2) % 2)
    els = [(r,s) for r in range(12) for s in range(2)]
    idx = {e: 2*e[0]+e[1] for e in els}
    Sset = set()
    for g in S:
        Sset.add(g)
        # inverse
        for h in els:
            if mul(g,h) == (0,0): Sset.add(h)
    n = 24
    adj = [[] for _ in range(n)]
    for x in els:
        for g in Sset:
            y = mul(x, g)
            if idx[y] not in adj[idx[x]]:
                adj[idx[x]].append(idx[y])
    return n, [sorted(x) for x in adj]

# ---------- run -------------------------------------------------------------
def run(name, n, adj, pair, same_orbit_note, trials=400, widths=(1, 4, 32)):
    print(f"\n{'='*74}\n{name}   n={n}   pair={pair}   ({same_orbit_note})\n{'='*74}")
    root = refine(n, adj, [0]*n)
    print(f"  1-WL root cells: {sorted(len(v) for v in cells(root).values())}")
    for W in widths:
        random.seed(11)
        tally = defaultdict(int)
        for _ in range(trials):
            sig = list(range(n)); random.shuffle(sig)
            a2 = relabel(n, adj, sig)
            r2 = refine(n, a2, [0]*n)
            v, kind = scheme(n, a2, r2, sig[pair[0]], sig[pair[1]], width=W)[0], None
            tally[v] += 1
        tot = sum(tally.values())
        parts = "  ".join(f"{k}:{v}" for k, v in sorted(tally.items()))
        inv = "INVARIANT" if len(tally) == 1 else "*** NOT INVARIANT ***"
        print(f"  width {W:>3d}: {parts:<40s} {inv}")
        if 'LT' in tally or 'GT' in tally:
            bad = tally['LT'] + tally['GT']
            print(f"            -> {bad}/{tot} runs emit a strict ROOT ORDER on this pair")

if __name__ == "__main__":
    n, adj, apex = c3c4()
    run("C3/C4 double apex", n, adj, (apex[0], apex[1]),
        "apexes are ONE orbit by hand: Aut = (D3 x D4) wr S2, orbits [2,6,8]")

    # FAILURE MODE 2: u,w share a 1-WL colour but are in DIFFERENT orbits.
    # The 14-cell of C3/C4 is overmerged (C3-vertices 6 | C4-vertices 8).
    # Divergence here is LEGITIMATE; the question is whether the DIRECTION is invariant.
    run("C3/C4 mixed 14-cell: C3-vtx vs C4-vtx", n, adj, (1, 4),
        "vtx 1 in a C3, vtx 4 in a C4: same 1-WL colour, DIFFERENT orbits")
    run("C3/C4 mixed 14-cell: C3-vtx vs C3-vtx (other copy)", n, adj, (1, 9),
        "both C3 vertices: SAME orbit")

    n2, adj2 = cay_z12_5_z2()
    run("Cay(Z12:5Z2)  (VT, T2 witness)", n2, adj2, (0, 1),
        "VT by construction: every pair is one orbit", trials=200,
        widths=(1, 2, 4, 32))
