#!/usr/bin/env python3
"""
PROBE 2: hunt a VERTEX-TRANSITIVE graph that is NOT `Tinhofer`.

probe_vt_transparent.py found 0/78, but its sample was ~60 circulants (circulant GI is in
P) at n <= 20.  This one targets the families where the WL-cells-vs-orbits gap actually
lives: Cayley graphs of 2-groups (the CFI/Miyazaki habitat) and the SRG(16,6,2,2) pair.

A counterexample = VT graph + a descent-reachable node whose individualized cell carries
>= 2 orbits of the CURRENT stabiliser (= `RigidObstructionAt`, `DeepenTinhofer.lean:204`).
"""
import sys, random
from itertools import product

sys.path.insert(0, "/workspace/scratchpad")
from probe_vt_transparent import is_vt, tinhofer

# ─────────────────────────────────────────────────────────── group machinery

def elem_abelian(k):
    els = list(product(range(2), repeat=k))
    return els, (lambda a, b: tuple((x + y) % 2 for x, y in zip(a, b)))

def zn_times_zm(nn, mm):
    els = list(product(range(nn), range(mm)))
    return els, (lambda a, b: ((a[0] + b[0]) % nn, (a[1] + b[1]) % mm))

def dihedral(m):
    els = [(r, s) for s in range(2) for r in range(m)]
    def mul(a, b):
        r1, s1 = a; r2, s2 = b
        return ((r1 + r2) % m, s2) if s1 == 0 else ((r1 - r2) % m, (s1 + s2) % 2)
    return els, mul

def quaternion16():
    """Generalised quaternion Q16 = <a,b | a^8=1, b^2=a^4, b a b^-1 = a^-1>."""
    els = [(i, j) for j in range(2) for i in range(8)]
    def mul(x, y):
        i, j = x; k, l = y
        i2 = (i + k) % 8 if j == 0 else (i - k) % 8
        if j == 1 and l == 1:
            return ((i2 + 4) % 8, 0)
        return (i2, (j + l) % 2)
    return els, mul

def cayley(els, mul, S):
    idx = {e: i for i, e in enumerate(els)}
    n = len(els)
    adj = [[0] * n for _ in range(n)]
    for e in els:
        for s in S:
            f = mul(e, s)
            if f != e:
                adj[idx[e]][idx[f]] = adj[idx[f]][idx[e]] = 1
    return n, adj

def inv_closed(els, mul, S):
    ident = None
    for e in els:
        if all(mul(e, x) == x for x in els):
            ident = e
            break
    out = set(S)
    for s in S:
        for t in els:
            if mul(s, t) == ident:
                out.add(t)
    out.discard(ident)
    return sorted(out)

# ─────────────────────────────────────────────────────────── explicit SRG pair

def rook44():
    vs = list(product(range(4), repeat=2))
    n = 16
    adj = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if (vs[i][0] == vs[j][0]) != (vs[i][1] == vs[j][1]):
                adj[i][j] = adj[j][i] = 1
    return n, adj

def shrikhande():
    """Cay(Z4 x Z4, {+-(1,0), +-(0,1), +-(1,1)}) — SRG(16,6,2,2), VT, not rook's."""
    els, mul = zn_times_zm(4, 4)
    S = [(1, 0), (3, 0), (0, 1), (0, 3), (1, 1), (3, 3)]
    return cayley(els, mul, S)

# ─────────────────────────────────────────────────────────────────── run
random.seed(20260729)

CASES = [("rook 4x4", *rook44()), ("Shrikhande", *shrikhande())]

GROUPS = [("Z2^4", *elem_abelian(4)), ("Z4xZ4", *zn_times_zm(4, 4)),
          ("Z8xZ2", *zn_times_zm(8, 2)), ("D8", *dihedral(8)),
          ("Q16", *quaternion16()), ("Z2^3", *elem_abelian(3)),
          ("Z6xZ3", *zn_times_zm(6, 3)), ("D9", *dihedral(9))]

for gname, els, mul in GROUPS:
    n = len(els)
    nonid = [e for e in els if not all(mul(e, x) == x for x in els)]
    seen = set()
    for _ in range(60):
        k = random.randint(2, max(2, len(nonid) // 2))
        S = inv_closed(els, mul, random.sample(nonid, k))
        if not S:
            continue
        key = tuple(S)
        if key in seen:
            continue
        seen.add(key)
        CASES.append((f"Cay({gname},|S|={len(S)})", *cayley(els, mul, S)))

print(f"{'graph':26s} {'n':>3s}  verdict")
print("-" * 74)
tested = fails = skipped = 0
for name, n, adj in CASES:
    try:
        if not is_vt(n, adj):
            skipped += 1
            continue
    except Exception:
        skipped += 1
        continue
    tested += 1
    verdict, info = tinhofer(n, adj)
    if verdict == "FAIL":
        fails += 1
        r, bad = info
        print(f"{name:26s} {n:3d}  ★★ NOT Tinhofer: branch {r}, {bad[0]} at level {bad[1]}, "
              f"cell {bad[2]}" + (f", orbits {bad[3]}" if len(bad) > 3 else ""))
    elif fails == 0 and tested <= 6:
        print(f"{name:26s} {n:3d}  transparent")
print("-" * 74)
print(f"VT tested: {tested}   NOT Tinhofer: {fails}   (skipped non-VT/err: {skipped})")
