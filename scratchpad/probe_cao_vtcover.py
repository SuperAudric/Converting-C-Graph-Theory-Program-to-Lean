#!/usr/bin/env python3
"""THE LEAD the CFI[K4]-tw mechanism suggests:

the counterexample needs (i) a size-2 block system that (ii) 1-WL cannot see, so that
individualizing one point of a block PINS its partner non-locally.  CFI supplies both, but
pays for it with gadget/wire asymmetry (=> not vertex-transitive).

F2-VOLTAGE DOUBLE COVERS of a VT base keep transitivity while still having 2-element
fibres as blocks.  So: sweep all switching classes of Z2-covers of small VT graphs and ask

    cover is VT   AND   individualizing one vertex leaves a 1-WL cell that is NOT a single
                        Aut(cover, v)-orbit                      <-- refutes VT => Tinhofer

Also sweeps Z3 / Z4 covers (blocks of size 3 / 4).
"""
import sys
from itertools import product
from collections import defaultdict
sys.path.insert(0, "/workspace/scratchpad")
from probe_cao_cleanroom import wl, individualize, cells, is_perm_aut

sys.setrecursionlimit(100000)


def iso_exists(n, adj, cA, cB, budget=None):
    """One colour-preserving automorphism carrying cA to cB?  None = budget out."""
    if budget is None:
        budget = [200000]
    budget[0] -= 1
    if budget[0] <= 0:
        return None
    cA = wl(n, adj, cA)
    cB = wl(n, adj, cB)
    dA, dB = cells(cA), cells(cB)
    if sorted((c, len(v)) for c, v in dA.items()) != sorted((c, len(v)) for c, v in dB.items()):
        return False
    big = [c for c in sorted(dA) if len(dA[c]) > 1]
    if not big:
        posB = {cB[v]: v for v in range(n)}
        return is_perm_aut(n, adj, [posB[cA[v]] for v in range(n)])
    c0 = big[0]
    x = dA[c0][0]
    unk = False
    for y in dB[c0]:
        r = iso_exists(n, adj, individualize(n, cA, x), individualize(n, cB, y), budget)
        if r is True:
            return True
        if r is None:
            unk = True
    return None if unk else False


def same_orbit(n, adj, col, u, w):
    return iso_exists(n, adj, individualize(n, col, u), individualize(n, col, w))


def cell_orbit_reps(n, adj, col, cell):
    reps = []
    for v in cell:
        for r in reps:
            s = same_orbit(n, adj, col, v, r)
            if s is None:
                return None
            if s:
                break
        else:
            reps.append(v)
    return reps


# ---------------------------------------------------------------- voltage covers
def cover(nb, edges, volt, k):
    """Z_k voltage cover: (v,b) ~ (u, b + volt[e]) for e = (v,u) oriented v<u."""
    n = nb * k
    idx = lambda v, b: v * k + (b % k)
    adj = [[0] * n for _ in range(n)]
    for (v, u), t in zip(edges, volt):
        for b in range(k):
            a, c = idx(v, b), idx(u, b + t)
            adj[a][c] = adj[c][a] = 1
    return n, adj


def spanning_tree(nb, edges):
    par = list(range(nb))

    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    tree, cot = [], []
    for i, (v, u) in enumerate(edges):
        a, b = f(v), f(u)
        if a != b:
            par[a] = b
            tree.append(i)
        else:
            cot.append(i)
    return tree, cot


def sweep(label, nb, edges, k=2, quiet=True):
    tree, cot = spanning_tree(nb, edges)
    hits = 0
    tested = 0
    for vals in product(range(k), repeat=len(cot)):
        volt = [0] * len(edges)
        for i, t in zip(cot, vals):
            volt[i] = t
        n, adj = cover(nb, edges, volt, k)
        root = wl(n, adj, [0] * n)
        if len(set(root)) != 1:
            continue                                   # 1-WL already non-transitive
        # VT?  every vertex in one Aut-orbit
        vt = True
        for v in range(1, n):
            s = same_orbit(n, adj, root, 0, v)
            if s is not True:
                vt = False
                break
        if not vt:
            continue
        tested += 1
        c1 = wl(n, adj, individualize(n, root, 0))
        mixed = []
        for c in cells(c1).values():
            if len(c) == 1:
                continue
            reps = cell_orbit_reps(n, adj, c1, c)
            if reps is None:
                mixed.append(('?', c))
            elif len(reps) > 1:
                mixed.append((len(reps), c))
        tag = ""
        if mixed:
            hits += 1
            tag = f"  <<< MIXED {mixed}"
        if mixed or not quiet:
            print(f"  {label} Z{k} volt={vals}: n={n} VT cells-after="
                  f"{sorted(len(v) for v in cells(c1).values())}{tag}")
    print(f"[{label} Z{k}] VT covers tested: {tested}, CAO-propagation failures: {hits}")


def K(m):
    return [(i, j) for i in range(m) for j in range(i + 1, m)]


CUBE = [(0,1),(1,2),(2,3),(3,0),(4,5),(5,6),(6,7),(7,4),(0,4),(1,5),(2,6),(3,7)]
PET = [(0,1),(1,2),(2,3),(3,4),(4,0),(5,7),(7,9),(9,6),(6,8),(8,5),
       (0,5),(1,6),(2,7),(3,8),(4,9)]
K33 = [(i, 3 + j) for i in range(3) for j in range(3)]


def circ(m, offs):
    es = set()
    for i in range(m):
        for o in offs:
            a, b = i, (i + o) % m
            if a != b:
                es.add((min(a, b), max(a, b)))
    return sorted(es)


if __name__ == "__main__":
    for lab, nb, es in [("K4", 4, K(4)), ("K5", 5, K(5)), ("K33", 6, K33),
                        ("C6", 6, circ(6, (1,))), ("cube", 8, CUBE),
                        ("K6", 6, K(6)), ("circ(8,{1,4})", 8, circ(8, (1, 4))),
                        ("circ(9,{1,3})", 9, circ(9, (1, 3))),
                        ("Petersen", 10, PET)]:
        sweep(lab, nb, es, 2)
    for lab, nb, es in [("K4", 4, K(4)), ("C5", 5, circ(5, (1,))), ("K33", 6, K33)]:
        sweep(lab, nb, es, 3)
    for lab, nb, es in [("K4", 4, K(4))]:
        sweep(lab, nb, es, 4)
