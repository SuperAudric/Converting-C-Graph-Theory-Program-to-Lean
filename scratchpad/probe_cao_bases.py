#!/usr/bin/env python3
"""(1) Is untwisted CFI[K4] the incidence graph of the 3-net of Z2xZ2?
   (2) Does the counterexample extend to other min-degree-3 bases (K3,3, prism)?"""
import sys
from collections import defaultdict, Counter
sys.path.insert(0, "/workspace/scratchpad")
from probe_cao_cleanroom import cfi, wl, individualize, cells, all_isos, orbits, orbit_colouring

K4 = [(i, j) for i in range(4) for j in range(i + 1, 4)]


def wire_geometry(label, twisted_nodes, base, m):
    n, adj, names, idx = cfi(base, m, twisted_nodes)
    wires = [v for v in range(n) if names[v][0] == 'E']
    meet = {}
    for a in range(len(wires)):
        for b in range(a + 1, len(wires)):
            u, w = wires[a], wires[b]
            k = sum(1 for x in range(n) if adj[u][x] and adj[w][x])
            meet[(u, w)] = k
    print(f"\n[{label}] wire-pair common-gadget counts: {Counter(meet.values())}")
    # "parallel" = meet in 0 gadgets; is parallelism an equivalence relation (= a net)?
    par = defaultdict(set)
    for (u, w), k in meet.items():
        if k == 0:
            par[u].add(w)
            par[w].add(u)
    classes = []
    seen = set()
    for u in wires:
        if u in seen:
            continue
        cl = {u} | par[u]
        ok = all(par[x] | {x} == cl for x in cl)
        classes.append((sorted(cl), ok))
        seen |= cl
    print(f"  parallelism classes (meet-0): sizes {[len(c) for c, _ in classes]}, "
          f"equivalence-relation: {all(o for _, o in classes)}")
    for cl, _ in classes[:4]:
        print(f"    class {[names[x][1] for x in cl]}")


wire_geometry("CFI[K4] UNTWISTED", (), K4, 4)
wire_geometry("CFI[K4] TWISTED", (0,), K4, 4)

# ---------------------------------------------------------------- other bases
K33 = [(i, 3 + j) for i in range(3) for j in range(3)]
PRISM = [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (0, 3), (1, 4), (2, 5)]
K4e = K4


def cao_propagates(label, base, m, twisted_nodes, vlist=None):
    n, adj, names, idx = cfi(base, m, twisted_nodes)
    root = wl(n, adj, [0] * n)
    print(f"\n=== {label} === n={n}, 1-WL root cells {sorted(len(v) for v in cells(root).values())}")
    try:
        A = all_isos(n, adj, root, root, limit=4 * 10 ** 6)
    except RuntimeError:
        print("  aut enumeration budget exhausted")
        return
    orb = orbits(n, A)
    ob = defaultdict(list)
    for v in range(n):
        ob[orb[v]].append(v)
    print(f"  |Aut| = {len(A)}, root orbit sizes {sorted(len(b) for b in ob.values())}")
    cao_root = all(len({orb[v] for v in c}) == 1 for c in cells(root).values())
    print(f"  CAO at 1-WL root: {cao_root}")
    oc = orbit_colouring(n, orb)
    for v0 in (vlist if vlist is not None else range(n)):
        c1 = wl(n, adj, individualize(n, oc, v0))
        try:
            A1 = all_isos(n, adj, c1, c1, limit=4 * 10 ** 6)
        except RuntimeError:
            print(f"  v0={v0}: budget exhausted")
            continue
        o1 = orbits(n, A1)
        mixed = [c for c in cells(c1).values() if len({o1[x] for x in c}) > 1]
        cs = sorted(len(v) for v in cells(c1).values())
        os_ = sorted(Counter(o1).values())
        print(f"  v0={v0} ({names[v0][0]}): |stab|={len(A1)} cells={cs} orbits={os_} "
              f"MIXED={len(mixed)}  {'<-- CAO BROKEN' if mixed else ''}")
        if vlist is None and mixed:
            return


cao_propagates("CFI[K3,3] untwisted", K33, 6, (), vlist=[0, 18])
cao_propagates("CFI[K3,3] twisted", K33, 6, (0,), vlist=[0, 18])
cao_propagates("CFI[prism] untwisted", PRISM, 6, (), vlist=[0, 18])
cao_propagates("CFI[prism] twisted", PRISM, 6, (0,), vlist=[0, 18])
