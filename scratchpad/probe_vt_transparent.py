#!/usr/bin/env python3
"""
PROBE: is every VERTEX-TRANSITIVE graph ORBIT-TRANSPARENT?

The hypothesis under test (user, 2026-07-29):
    "Vertex-transitive graphs provably have no exposed rigid obstructions, let alone a
     place for force to fire.  So `consume_fail_locates` forces consume to fire on them."

`consume_fail_locates` kills the FIRST disjunct on a VT graph (the root cell is one
Aut-orbit, so no `RigidObstructionAt` there).  The SECOND disjunct is at a *deeper*
reachable node, where `IsColAut adj psi` is a POINT STABILIZER, not Aut(G).  So the
argument closes iff

    VT  ==>  Tinhofer  (every cell individualized along the descent is a single
                        orbit of the CURRENT stabiliser)

This probe searches for a counterexample: a vertex-transitive graph carrying a
`RigidObstructionAt` at some descent-reachable node.  Mirrors `DeepenTinhofer.Tinhofer` /
`CellSingleOrbit` exactly (target_cell = chooseIdK, first vertex of the cell = the Lean
`w :: _` pick).
"""
import sys
from collections import defaultdict
from itertools import combinations, product

sys.path.insert(0, "/workspace/scratchpad")
from probe_dualdeepen import refine, indiv, target_cell, build_cfi_base, cubic
from probe_orbit_oracle import orbit_partition

# ─────────────────────────────────────────────────────── CellSingleOrbit / Tinhofer

def cell_single_orbit(n, adj, col, cell):
    """`DeepenTinhofer.CellSingleOrbit` — is `cell` ONE orbit of Aut(adj, col)?"""
    part = orbit_partition(n, adj, col, cell)
    if part is None:
        return None                       # canon blew the leaf cap
    return len({part[v] for v in cell}) == 1

def tinhofer_path(n, adj, col, trace):
    """`TinhoferPath` down one greedy deepening path.  Returns the failing level or None."""
    lvl = 0
    while True:
        cid, cell = target_cell(n, col)
        if cid is None:
            return None                    # discrete: path certified vacuously
        ok = cell_single_orbit(n, adj, col, cell)
        if ok is None:
            return ("BLOWN", lvl, len(cell))
        if not ok:
            part = orbit_partition(n, adj, col, cell)
            sizes = sorted(defaultdict(int, {r: sum(1 for v in cell if part[v] == r)
                                             for r in {part[v] for v in cell}}).values())
            return ("RIGID", lvl, len(cell), tuple(sizes))
        col = refine(n, adj, indiv(n, col, cell[0]))
        lvl += 1
        if lvl > n:
            return None

def tinhofer(n, adj):
    """`Tinhofer adj chi_root` — every branch's deepening path is transparent."""
    root = refine(n, adj, [0] * n)
    cid, cell = target_cell(n, root)
    if cid is None:
        return ("DISCRETE", None)
    for r in cell:
        bad = tinhofer_path(n, adj, refine(n, adj, indiv(n, root, r)), [])
        if bad is not None:
            return ("FAIL", (r, bad))
    return ("OK", None)

def is_vt(n, adj):
    """Root cell = every vertex, and it is a single Aut-orbit."""
    root = refine(n, adj, [0] * n)
    if len(set(root)) != 1:
        return False                       # 1-WL already splits => not VT
    part = orbit_partition(n, adj, root, list(range(n)))
    return part is not None and len({part[v] for v in range(n)}) == 1

# ─────────────────────────────────────────────────────── vertex-transitive families

def cayley(elems, mul, conn):
    idx = {e: i for i, e in enumerate(elems)}
    n = len(elems)
    adj = [[0] * n for _ in range(n)]
    for e in elems:
        for s in conn:
            f = mul(e, s)
            adj[idx[e]][idx[f]] = adj[idx[f]][idx[e]] = 1
    return n, adj

def circulant(m, offs):
    adj = [[0] * m for _ in range(m)]
    for i in range(m):
        for d in offs:
            j = (i + d) % m
            adj[i][j] = adj[j][i] = 1
    return m, adj

def kneser(m, k):
    vs = list(combinations(range(m), k))
    n = len(vs)
    adj = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if not set(vs[i]) & set(vs[j]):
                adj[i][j] = adj[j][i] = 1
    return n, adj

def paley(q):
    sq = {(x * x) % q for x in range(1, q)}
    adj = [[0] * q for _ in range(q)]
    for i in range(q):
        for j in range(q):
            if i != j and (i - j) % q in sq:
                adj[i][j] = 1
    return q, adj

def lexprod(n1, a1, n2, a2):
    """G[H]: VT whenever both are."""
    n = n1 * n2
    adj = [[0] * n for _ in range(n)]
    for i in range(n1):
        for j in range(n1):
            for a in range(n2):
                for b in range(n2):
                    if i == j:
                        e = a2[a][b]
                    else:
                        e = a1[i][j]
                    adj[i * n2 + a][j * n2 + b] = e
    for v in range(n):
        adj[v][v] = 0
    return n, adj

def hamming_2_3():
    vs = list(product(range(3), repeat=2))
    n = len(vs)
    adj = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if sum(a != b for a, b in zip(vs[i], vs[j])) == 1:
                adj[i][j] = adj[j][i] = 1
    return n, adj

def zmul(m):
    return lambda a, b: (a + b) % m

CANDIDATES = []
for m in range(5, 15):
    for offs in [(1,), (1, 2), (1, 3), (1, 2, 3), (1, 4), (2, 3), (1, 2, 4), (1, 5)]:
        if max(offs) * 2 <= m:
            CANDIDATES.append((f"circ({m},{offs})", *circulant(m, offs)))
CANDIDATES += [
    ("Petersen", *kneser(5, 2)),
    ("Kneser(6,2)", *kneser(6, 2)),
    ("Paley(9)", *paley(9)),
    ("Paley(13)", *paley(13)),
    ("Hamming(2,3)", *hamming_2_3()),
]
_, c5 = circulant(5, (1,))
_, k2 = circulant(2, (1,))
_, e2 = (2, [[0, 0], [0, 0]])
_, c6 = circulant(6, (1,))
_, c4 = circulant(4, (1,))
CANDIDATES += [
    ("C5[K2]", *lexprod(5, c5, 2, k2)),
    ("C5[2K1]", *lexprod(5, c5, 2, e2)),
    ("C6[2K1]", *lexprod(6, c6, 2, e2)),
    ("C4[K2]", *lexprod(4, c4, 2, k2)),
    ("C3[C3]", *lexprod(3, circulant(3, (1,))[1], 3, circulant(3, (1,))[1])),
]
# CFI over vertex-transitive bases (the canonical non-refinable construction)
for bm, bname in [(4, "K4"), (5, "C5"), (6, "K33")]:
    if bname == "K4":
        be = [(i, j) for i in range(4) for j in range(i + 1, 4)]
    elif bname == "C5":
        be = [(i, (i + 1) % 5) for i in range(5)]
    else:
        be = [(i, 3 + j) for i in range(3) for j in range(3)]
    for tw in (False, True):
        try:
            n, adj = build_cfi_base(be, bm, twist=tw)
            CANDIDATES.append((f"CFI[{bname}]{'-tw' if tw else ''}", n, adj))
        except Exception:
            pass

# ─────────────────────────────────────────────────────────────────────── run
print(f"{'graph':22s} {'n':>3s}  {'VT':>5s}  Tinhofer / located obstruction")
print("-" * 78)
vt_total = vt_fail = 0
for name, n, adj in CANDIDATES:
    if n > 20:
        continue
    try:
        vt = is_vt(n, adj)
    except Exception as ex:
        print(f"{name:22s} {n:3d}  ERR {ex}")
        continue
    if not vt:
        continue
    vt_total += 1
    verdict, info = tinhofer(n, adj)
    if verdict == "FAIL":
        vt_fail += 1
        r, bad = info
        print(f"{name:22s} {n:3d}  {'YES':>5s}  ★ NOT Tinhofer: branch {r}, "
              f"{bad[0]} at level {bad[1]}, cell {bad[2]}"
              + (f", orbit sizes {bad[3]}" if len(bad) > 3 else ""))
    else:
        print(f"{name:22s} {n:3d}  {'YES':>5s}  transparent ({verdict})")
print("-" * 78)
print(f"vertex-transitive tested: {vt_total}   NOT orbit-transparent: {vt_fail}")
