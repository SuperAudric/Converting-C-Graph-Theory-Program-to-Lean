#!/usr/bin/env python3
"""IS THE SHRIKHANDE GRAPH `Tinhofer`?   (2026-07-30, clean-room)

`probe_cao_2wl.py` turned up a VT graph -- Shrikhande, n=16 -- whose 1-WL closure after ONE
individualization has a MIXED cell.  That is exactly `RigidObstructionAt`, so it bears on
`VT => Tinhofer` (the live open lemma).  This script emulates the Lean definitions verbatim:

  CellSingleOrbit adj chi c   = the c-cell is a single orbit of {sigma : Aut(adj), sigma preserves chi}
  chooseIdK                   = the non-singleton cell of LOWEST COLOUR ID
  step adj chi w              = warm-refine (indivOne chi w)
  TinhoferPath  fuel cur      = chooseIdK = none, or (CellSingleOrbit at cid AND
                                TinhoferPath (step cur (first member of the cid-cell)))
  Tinhofer adj chi            = for EVERY r in branches chi, TinhoferPath (step chi r)

The colour-ID convention of `Refine.warmRefineVec` need not match this file's `wl`, and
`chooseIdK` depends on it.  So the verdict is made CONVENTION-INDEPENDENT by computing both:

  EXISTS-Tinhofer : some pick-rule (any non-singleton cell per level) survives the descent
  FORALL-Tinhofer : every pick-rule survives

EXISTS = False  =>  refutation under ANY id convention.   FORALL = True => Tinhofer for all.
(The MEMBER pick inside a cell is immaterial: if the cell is a single orbit, all members give
isomorphic children, so the verdict cannot depend on which one `w :: _` names.)
"""
import sys
from collections import defaultdict
from itertools import combinations
sys.path.insert(0, "/workspace/scratchpad")
from probe_cao_cleanroom import wl, individualize, cells, all_isos, orbits, is_perm_aut
from probe_cao_vtcover import iso_exists

sys.setrecursionlimit(100000)


def single_orbit(n, adj, col, cell):
    """CellSingleOrbit: every pair in `cell` linked by an automorphism preserving `col`."""
    r = cell[0]
    for v in cell[1:]:
        if iso_exists(n, adj, individualize(n, col, r), individualize(n, col, v)) is not True:
            return False
    return True


def descend(n, adj, col, memo):
    """(exists_ok, forall_ok) for the TinhoferPath descent from state `col`."""
    key = tuple(col)
    if key in memo:
        return memo[key]
    memo[key] = (True, True)                       # cycle guard (cannot happen: depth strict)
    ns = [c for c in sorted(cells(col)) if len(cells(col)[c]) > 1]
    if not ns:
        memo[key] = (True, True)
        return memo[key]
    ex, fa = False, True
    for c in ns:
        cell = cells(col)[c]
        if not single_orbit(n, adj, col, cell):
            fa = False
            continue
        e2, f2 = descend(n, adj, wl(n, adj, individualize(n, col, cell[0])), memo)
        ex = ex or e2
        fa = fa and f2
    memo[key] = (ex, fa)
    return memo[key]


def tinhofer(n, adj):
    """(exists, forall) verdicts for `Tinhofer adj chi_root`."""
    root = wl(n, adj, [0] * n)
    ns = [c for c in sorted(cells(root)) if len(cells(root)[c]) > 1]
    if not ns:
        return True, True, "root discrete"
    memo = {}
    ex, fa = True, True
    # branches chi = the chooseIdK cell of the root; convention-independently, try each
    # candidate root cell and each of its members (members of one orbit are conjugate, but
    # the root cell need not be a single orbit, so all members are tried).
    per_cell = {}
    for c in ns:
        e, f = True, True
        for r in cells(root)[c]:
            e2, f2 = descend(n, adj, wl(n, adj, individualize(n, root, r)), memo)
            e, f = (e and e2), (f and f2)
        per_cell[c] = (e, f)
    ex = any(e for e, _ in per_cell.values())
    fa = all(f for _, f in per_cell.values())
    return ex, fa, f"root cells {[len(cells(root)[c]) for c in ns]}"


# ---------------------------------------------------------------- graph library
def from_edges(nv, es):
    adj = [[0] * nv for _ in range(nv)]
    for a, b in es:
        adj[a][b] = adj[b][a] = 1
    return nv, adj


def circ(m, offs):
    es = set()
    for i in range(m):
        for o in offs:
            a, b = i, (i + o) % m
            if a != b:
                es.add((min(a, b), max(a, b)))
    return from_edges(m, sorted(es))


def rook(m):
    V = [(i, j) for i in range(m) for j in range(m)]
    return from_edges(len(V), [(a, b) for a in range(len(V)) for b in range(a + 1, len(V))
                               if (V[a][0] == V[b][0]) != (V[a][1] == V[b][1])])


def shrikhande():
    V = [(i, j) for i in range(4) for j in range(4)]
    S = {(0,1),(0,3),(1,0),(3,0),(1,1),(3,3)}
    return from_edges(16, [(a, b) for a in range(16) for b in range(a + 1, 16)
                           if ((V[b][0]-V[a][0]) % 4, (V[b][1]-V[a][1]) % 4) in S
                           or ((V[a][0]-V[b][0]) % 4, (V[a][1]-V[b][1]) % 4) in S])


def clebsch():
    S = {1, 2, 4, 8, 15}
    return from_edges(16, [(a, b) for a in range(16) for b in range(a + 1, 16) if a ^ b in S])


def paley(q):
    sq = {(i * i) % q for i in range(1, q)}
    return from_edges(q, [(i, j) for i in range(q) for j in range(i + 1, q)
                          if (j - i) % q in sq])


def johnson(m, k):
    S = list(combinations(range(m), k))
    return from_edges(len(S), [(i, j) for i in range(len(S)) for j in range(i + 1, len(S))
                               if len(set(S[i]) & set(S[j])) == k - 1])


PET = from_edges(10, [(0,1),(1,2),(2,3),(3,4),(4,0),(5,7),(7,9),(9,6),(6,8),(8,5),
                      (0,5),(1,6),(2,7),(3,8),(4,9)])

def path_lowest_id(n, adj, col):
    """The CONVENTION-FAITHFUL TinhoferPath: always pick the lowest-colour-id cell.
    Returns (True, None) or (False, (level, cellsize))."""
    lvl = 0
    while True:
        d = cells(col)
        ns = [c for c in sorted(d) if len(d[c]) > 1]
        if not ns:
            return True, None
        cell = d[ns[0]]
        if not single_orbit(n, adj, col, cell):
            return False, (lvl, len(cell))
        col = wl(n, adj, individualize(n, col, cell[0]))
        lvl += 1


def tinhofer_faithful(n, adj):
    root = wl(n, adj, [0] * n)
    d = cells(root)
    ns = [c for c in sorted(d) if len(d[c]) > 1]
    if not ns:
        return True, "root discrete"
    for r in d[ns[0]]:                                   # branches chi = the chooseIdK cell
        ok, why = path_lowest_id(n, adj, wl(n, adj, individualize(n, root, r)))
        if not ok:
            return False, f"branch r={r} fails at level {why[0]} on a cell of {why[1]}"
    return True, "all branches clean"


print("=== the sharp case: the two SRG(16,6,2,2) ===")
for lab, (n, adj) in [("Shrikhande", shrikhande()), ("rook 4x4 = L2(4)", rook(4))]:
    A = all_isos(n, adj, wl(n, adj, [0] * n), wl(n, adj, [0] * n))
    root = wl(n, adj, [0] * n)
    vt = len(set(root)) == 1 and len({o for o in orbits(n, A)}) == 1
    ex, fa, info = tinhofer(n, adj)
    print(f"  {lab:20s} n={n} |Aut|={len(A)} |Aut_v|={len(A)//n} VT={vt}  {info}")
    ff, why = tinhofer_faithful(n, adj)
    print(f"      EXISTS-Tinhofer = {ex}   FORALL-Tinhofer = {fa}"
          + ("   <<<< NOT Tinhofer under ANY id convention" if not ex else ""))
    print(f"      lowest-id (chooseIdK-faithful) Tinhofer = {ff}   [{why}]")
    A2 = all_isos(n, adj, wl(n, adj, individualize(n, wl(n, adj, [0]*n), 0)),
                  wl(n, adj, individualize(n, wl(n, adj, [0]*n), 0)))
    o2 = orbits(n, A2)
    from collections import Counter
    print(f"      |Aut_v| enumerated = {len(A2)}, stabiliser orbit sizes "
          f"{sorted(Counter(o2).values())}")
    # the level-1 picture, with the Lagrange argument spelled out
    c1 = wl(n, adj, individualize(n, root, 0))
    print(f"      after individualizing v=0: 1-WL cells "
          f"{sorted(len(c) for c in cells(c1).values())}; "
          f"orbit sizes must divide |Aut_v| = {len(A)//n}")
    for c in sorted(cells(c1)):
        cell = cells(c1)[c]
        if len(cell) > 1:
            print(f"        cell size {len(cell)}: single orbit = "
                  f"{single_orbit(n, adj, c1, cell)}")

print("\n=== controls / other VT + regular objects ===")
CASES = [("Petersen", *PET), ("Clebsch", *clebsch()), ("Paley(13)", *paley(13)),
         ("Paley(17)", *paley(17)), ("J(6,2)=T(6)", *johnson(6, 2)),
         ("J(8,2)=T(8)", *johnson(8, 2)), ("rook 3x3", *rook(3)),
         ("circ(16,{1,2,7})", *circ(16, (1, 2, 7))),
         ("circ(13,{1,3,9})", *circ(13, (1, 3, 9))),
         ("C6", *circ(6, (1,))), ("circ(9,{1,3})", *circ(9, (1, 3)))]
for lab, n, adj in CASES:
    root = wl(n, adj, [0] * n)
    ex, fa, info = tinhofer(n, adj)
    ff, why = tinhofer_faithful(n, adj)
    print(f"  {lab:20s} n={n:3d} VTcells={len(set(root))}  EXISTS={ex} FORALL={fa} "
          f"lowest-id={ff}  {info}"
          + ("   <<<< NOT Tinhofer" if not ff else ""))
