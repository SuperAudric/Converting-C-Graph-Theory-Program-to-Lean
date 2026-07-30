"""THE NAMED VT WITNESS: Cay(Z12 :_5 Z2), n=24 -- VT, CAO at root, and (recorded) ALL cells
mixed after one individualization.  Question: can the FORCE resolver fire there?
(probe_vt_witness.py is NOT import-safe -- module-level search -- so build inline.)"""
import sys
from collections import defaultdict
sys.path.insert(0, "/workspace/scratchpad")
from probe_cao_cleanroom import wl, individualize, cells, all_isos, orbits
from probe_cao_2wl import twowl_fast

def build(k, n_=12, m=2):
    els = [(r, s) for r in range(n_) for s in range(m)]
    mul = lambda x, y: ((x[0] + pow(k, x[1], n_) * y[0]) % n_, (x[1] + y[1]) % m)
    inv = {x: next(y for y in els if mul(x, y) == (0, 0)) for x in els}
    return els, mul, inv

def cay(els, mul, S):
    ix = {g: i for i, g in enumerate(els)}; n = len(els)
    adj = [[0]*n for _ in range(n)]
    for g in els:
        for s in S:
            a, b = ix[g], ix[mul(g, s)]
            adj[a][b] = adj[b][a] = 1
    return n, adj

def profile(n, col):
    d = defaultdict(int)
    for v in range(n): d[col[v]] += 1
    return tuple(sorted(d.values()))
def leafkey(n, adj, col):
    o = sorted(range(n), key=lambda v: col[v])
    return tuple(adj[o[i]][o[j]] for i in range(n) for j in range(n))
def key_d(n, adj, col, d):
    if len(set(col)) == n: return ("D", leafkey(n, adj, col))
    if d == 0: return ("P", profile(n, col))
    subs = []
    for cid, C in cells(col).items():
        if len(C) < 2: continue
        for u in C:
            subs.append(repr(key_d(n, adj, wl(n, adj, individualize(n, col, u)), d-1)))
    return ("P", profile(n, col), tuple(sorted(subs)))

els, mul, inv = build(5)
e = (0, 0)
cls, seen = [], set()
for x in els:
    if x == e or x in seen: continue
    c = {x, inv[x]}; seen |= c; cls.append(sorted(c))
best = None
for mask in range(1, 2**len(cls)):
    S = [g for i, c in enumerate(cls) if mask >> i & 1 for g in c]
    n, adj = cay(els, mul, S)
    if any(sum(r) == 0 for r in adj): continue
    root = wl(n, adj, [0]*n)
    if len(set(root)) != 1: continue          # 1-WL sees one cell (VT-consistent)
    try: A = all_isos(n, adj, root, root, limit=400_000)
    except RuntimeError: continue
    if len(set(orbits(n, A))) != 1: continue   # CAO at root: one orbit
    oc = [0]*n
    chi1 = wl(n, adj, individualize(n, oc, 0))
    Av = [g for g in A if g[0] == 0]
    orbv = orbits(n, Av)
    ns = [C for C in cells(chi1).values() if len(C) > 1]
    if ns and all(len({orbv[v] for v in C}) > 1 for C in ns):
        best = (S, n, adj, A, chi1, Av, orbv, ns); break

S, n, adj, A, chi1, Av, orbv, ns = best
print(f"Cay(Z12:_5 Z2)  n={n} |Aut|={len(A)} |Aut_v|={len(Av)}  S={sorted(S)}")
print(f"  root: 1-WL one cell, Aut-orbit = one orbit (CAO holds)")
print(f"  depth 1: 1-WL cells {profile(n, chi1)}; ALL {len(ns)} non-singleton cells mixed")
d2 = twowl_fast(n, adj, individualize(n, [0]*n, 0))
print(f"  depth 1: 2-WL cells {profile(n, d2)}")
for C in ns:
    bl = defaultdict(list)
    for u in C: bl[orbv[u]].append(u)
    reps = [b[0] for b in bl.values()]
    best_d = "blind(>3)"
    for d in range(1, 4):
        ks = {u: repr(key_d(n, adj, wl(n, adj, individualize(n, chi1, u)), d-1)) for u in reps}
        if len(set(ks.values())) > 1: best_d = f"depth {d}"; break
    tw = len({d2[u] for u in reps}) > 1
    print(f"   cell {sorted(C)} -> orbits {[sorted(b) for b in bl.values()]} | "
          f"1-WL force key: {best_d} | 2-WL splits: {tw}")
