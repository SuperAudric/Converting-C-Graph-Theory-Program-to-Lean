"""SWEEP: at every 1-WL MANUFACTURED mixed cell (CAO root -> individualize -> 1-WL),
what is the MINIMUM 1-WL lookahead depth at which the force key separates the true
Aut_v-orbits?  d = 0 means 1-WL already split them (no manufactured mixing).
'blind' = not separated by depth <= 3.  Also: does 2-WL separate at depth 0?"""
import sys
from collections import defaultdict
sys.path.insert(0, "/workspace/scratchpad")
from probe_cao_cleanroom import wl, individualize, cells, all_isos, orbits
from probe_cao_net import net
from probe_cao_2wl import twowl_fast
from probe_cao_induction import shrikhande, rook, T8, chang, from_edges

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
            subs.append(repr(key_d(n, adj, wl(n, adj, individualize(n, col, u)), d - 1)))
    return ("P", profile(n, col), tuple(sorted(subs)))

def run(lab, n, adj, maxd=3):
    A = all_isos(n, adj, wl(n, adj, [0]*n), wl(n, adj, [0]*n), limit=3_000_000)
    orb0 = orbits(n, A); m = {}
    oc = [m.setdefault(orb0[v], len(m)) for v in range(n)]
    print(f"\n=== {lab}  n={n} |Aut|={len(A)} root-orbits={len(set(oc))} ===")
    for v0 in sorted({oc.index(c) for c in set(oc)}):
        chi1 = wl(n, adj, individualize(n, oc, v0))
        Av = [g for g in A if all(oc[g[x]] == oc[x] for x in range(n)) and g[v0] == v0]
        orbv = orbits(n, Av)
        d2 = twowl_fast(n, adj, individualize(n, oc, v0))
        for cid, C in cells(chi1).items():
            bl = defaultdict(list)
            for u in C: bl[orbv[u]].append(u)
            if len(C) < 2 or len(bl) < 2: continue
            reps = [b[0] for b in bl.values()]
            best = "blind(>3)"
            for d in range(1, maxd + 1):
                ks = {u: repr(key_d(n, adj, wl(n, adj, individualize(n, chi1, u)), d - 1))
                      for u in reps}
                if len(set(ks.values())) > 1:
                    best = f"depth {d}"; break
            tw = len({d2[u] for u in reps}) > 1
            print(f"   v0={v0:3d} mixed cell size {len(C):3d} -> {len(bl)} orbits "
                  f"{sorted(len(b) for b in bl.values())} | 1-WL force key: {best:10s}"
                  f" | 2-WL splits at depth 0: {tw}")

if __name__ == "__main__":
    run("net(Z4)=CFI[K4]-tw", *net((4,))[:2])
    run("Shrikhande", *shrikhande())
    run("Chang-2 (C8)", *chang([(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,0)]))
