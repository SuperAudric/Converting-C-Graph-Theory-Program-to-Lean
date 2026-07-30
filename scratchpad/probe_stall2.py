"""Harden the stall witness: is the 1-WL force key blind at DEPTH d, for d = 1,2,3?
key_d(u) = the sorted multiset, over all length-d individualization sequences below u,
of the resulting 1-WL cell profile (discrete leaves give their canonical leaf matrix).
This is the strongest *1-WL-derived* equivariant lookahead of bounded depth -- strictly
stronger than lookaheadKey (d=1, profile only) and than holKey's per-vertex signature."""
import sys
from collections import defaultdict
sys.path.insert(0, "/workspace/scratchpad")
from probe_cao_cleanroom import wl, individualize, cells, all_isos, orbits
from probe_cao_net import net
from probe_cao_2wl import twowl_fast

def profile(n, col):
    d = defaultdict(int)
    for v in range(n): d[col[v]] += 1
    return tuple(sorted(d.values()))

def leafkey(n, adj, col):
    o = sorted(range(n), key=lambda v: col[v])
    return tuple(adj[o[i]][o[j]] for i in range(n) for j in range(n))

def key_d(n, adj, col, d):
    if len(set(col)) == n:
        return ("D", leafkey(n, adj, col))
    if d == 0:
        return ("P", profile(n, col))
    subs = []
    for cid, C in cells(col).items():
        if len(C) < 2: continue
        for u in C:
            subs.append(key_d(n, adj, wl(n, adj, individualize(n, col, u)), d - 1))
    return ("P", profile(n, col), tuple(sorted(map(repr, subs))))

n, adj = net((4,))[:2]
A = all_isos(n, adj, wl(n, adj, [0]*n), wl(n, adj, [0]*n), limit=3_000_000)
orb0 = orbits(n, A); m = {}
oc = [m.setdefault(orb0[v], len(m)) for v in range(n)]
v0 = 16
chi1 = wl(n, adj, individualize(n, oc, v0))
Av = [g for g in A if all(oc[g[x]] == oc[x] for x in range(n)) and g[v0] == v0]
orbv = orbits(n, Av)
CELL = [17, 18, 19]
print(f"net(Z4) n={n} |Aut|={len(A)}  v0={v0}  |Aut_v|={len(Av)}")
print(f"stall cell {CELL}  Aut_v-orbits: ", end="")
bl = defaultdict(list)
for u in CELL: bl[orbv[u]].append(u)
print([sorted(b) for b in bl.values()])
for d in (1, 2, 3):
    ks = {u: key_d(n, adj, wl(n, adj, individualize(n, chi1, u)), d - 1) for u in CELL}
    reps = [b[0] for b in bl.values()]
    sep = len({repr(ks[u]) for u in reps}) > 1
    same = repr(ks[17]) == repr(ks[19])
    print(f"  depth-{d} 1-WL lookahead key: separates the two orbits? {sep}   "
          f"(and ties 17~19 correctly? {same})")
d2 = twowl_fast(n, adj, individualize(n, oc, v0))
print(f"  2-WL colours on the cell: {[(u, d2[u]) for u in CELL]}")
