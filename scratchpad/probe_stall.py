"""THE STALL TEST.  At a 1-WL MANUFACTURED mixed cell (CAO root -> individualize -> 1-WL),
can the FORCE resolver fire?  If not, the node is a true mutual stall and the 1-WL design is
provably incomplete there; if yes, force covers what consume drops and there is no stall.

Force fires iff an EQUIVARIANT key separates the cell.  We test the built key shapes:
  K1  lookaheadKey non-discrete branch  = sorted cell-size profile of 1WL(indiv(chi,u))
  K2  strictly stronger 1-WL lookahead  = the full sorted colour-signature multiset
  K3  discreteness check                = does indiv+1WL discretize (then leafMatrix separates)
A key CAN separate only if it differs across the true Aut_v-orbits inside the cell.
"""
import sys
from collections import defaultdict
sys.path.insert(0, "/workspace/scratchpad")
from probe_cao_cleanroom import wl, individualize, cells, all_isos, orbits
from probe_cao_net import net
from probe_cao_2wl import twowl_fast

def prof(n, adj, col):
    d = defaultdict(int)
    for v in range(n):
        d[col[v]] += 1
    return tuple(sorted(d.values()))

def sig(n, adj, col):
    # full sorted colour-signature multiset: each vertex's (colour, sorted nbr-colour multiset)
    out = []
    for v in range(n):
        out.append((col[v], tuple(sorted(col[u] for u in range(n) if adj[v][u]))))
    return tuple(sorted(out))

def run(lab, n, adj):
    A = all_isos(n, adj, wl(n, adj, [0]*n), wl(n, adj, [0]*n), limit=3_000_000)
    print(f"\n=== {lab}  n={n}  |Aut|={len(A)} ===")
    orb0 = orbits(n, A); m = {}
    oc = [m.setdefault(orb0[v], len(m)) for v in range(n)]
    print(f"  root orbit partition (CAO by construction): sizes {prof(n,adj,oc)}")
    for v0 in sorted({oc.index(c) for c in set(oc)}):
        chi1 = wl(n, adj, individualize(n, oc, v0))
        Av = [g for g in A if all(oc[g[x]] == oc[x] for x in range(n)) and g[v0] == v0]
        orbv = orbits(n, Av)
        d2 = twowl_fast(n, adj, individualize(n, oc, v0))
        print(f"\n  -- individualize v0={v0}:  |Aut_v|={len(Av)}  "
              f"1WL cells={prof(n,adj,chi1)}  2WL cells={prof(n,adj,d2)}")
        for cid, C in cells(chi1).items():
            if len(C) < 2: continue
            blocks = defaultdict(list)
            for u in C: blocks[orbv[u]].append(u)
            if len(blocks) < 2:
                continue
            print(f"     MIXED 1-WL cell {sorted(C)}  ->  Aut_v-orbits {[sorted(b) for b in blocks.values()]}")
            k1, k2, disc = {}, {}, {}
            for u in C:
                c2 = wl(n, adj, individualize(n, chi1, u))
                k1[u] = prof(n, adj, c2)
                k2[u] = sig(n, adj, c2)
                disc[u] = len(set(c2)) == n
            reps = [b[0] for b in blocks.values()]
            s1 = len({k1[u] for u in reps}) > 1
            s2 = len({k2[u] for u in reps}) > 1
            print(f"       K1 lookahead cell-profile separates orbits? {s1}")
            print(f"       K2 full colour-signature  separates orbits? {s2}")
            print(f"       K3 indiv+1WL discretizes for all u in cell? {all(disc.values())}")
            # is the 2-WL cell containing these already split?
            print(f"       2-WL colours on this cell: "
                  f"{[sorted({d2[u] for u in b}) for b in blocks.values()]}")

if __name__ == "__main__":
    run("net(Z4) = CFI[K4]-tw", *net((4,))[:2])
