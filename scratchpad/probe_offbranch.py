#!/usr/bin/env python3
"""
probe_offbranch.py — IS DEEPEN'S PER-CELL ORBIT COUNT RELABELLING-INVARIANT
                     **OFF THE BRANCH CELL**?                            (2026-08-07)

============================================================================================
WHY THIS QUESTION — and why it is the ONLY thing `①` reads
============================================================================================
`Publication.canonForm?` is the FUSED object (`Select.selNode`).  Tracing its `①`
(`SelectNode.nodeTransport_selNode`, the `some c` branch): once a colour is committed, both
sides are rewritten by `aggregate_cellNarrow_eq` down to an aggregate over
`keepMin key adj χ (cellList χ c)`, which **does not mention the supply at all**, and are then
matched by `keepMin_transport_perm` from `KeyEquivariant` alone.

So the supply enters `①` through exactly ONE channel — `selColour_transport`, and there only
through `cellNarrow_length_transport`:

    >>> the NUMBER of orbits meeting each cell must be relabelling-invariant, PER CELL.

That is weaker than "the emitted relation is complete".  A supply that is *invariantly wrong*
on a cell (e.g. always collapses nothing there) satisfies `①` fine — it costs coverage (`③`),
never correctness.

Every completeness fact the project has about deepen — `OrbitComplete`, `CellIsOrbit`,
`exec_recovers_refgen_at` — is indexed at `u ∈ Descend.branches χ`, the BRANCH cell.  And
every sweep on record (`probe_verdict_invariance` 17/17, `probe_union_need` 13/13,
`probe_certkey`, `probe_selfsep`) is explicitly scoped to the ROOT BRANCH CELL.

Nobody has measured the other cells.  `deepenGens`' twists are identity only off
`K = coupled χ leaf` = the union of the NON-SINGLETON χ-cells, so they demonstrably DO act on
the other cells.  Whether they act invariantly is unmeasured, and it decides whether the
per-cell-harvest plan is necessary or merely sufficient.

============================================================================================
WHAT IS MEASURED
============================================================================================
Harvest is the CURRENT design, unchanged: anchors = the branch cell only (`deepenGens`).
The generated group's orbits are then read on EVERY non-singleton cell.

Per witness, for the identity labelling and K random relabellings σ:

  * refine the root; colours are ranks of sorted signatures, hence relabelling-INVARIANT
    values, so cells are matched across labellings by colour value (checked, not assumed);
  * harvest `deepenGens` from the branch cell;
  * union-find over ALL n vertices with the emitted (IsColAut-gated) generators;
  * per non-singleton cell: the sorted multiset of orbit-block sizes inside that cell.

VERDICT per cell = do all K+1 labellings agree on that multiset?
  branch cell   — expected Y (this is what 17/17 already measured)
  OFF-BRANCH    — <<< THE QUESTION.  An N here means `①` genuinely needs the per-cell harvest.
                      All Y means the plan is aiming at a sufficient-but-unnecessary condition.

Also reported: `collapsed` = how many off-branch cells the harvest resolves to ONE block
(coverage-relevant, not `①`-relevant).

============================================================================================
SOUNDNESS
============================================================================================
* `refine`/`indiv`/`greedy_deepen`/`replay`/`twist` are `probe_polyloop`'s ports of the landed
  Lean objects; `twist` carries the `IsColAut` gate, so every generator used is verified.
* NO orbit oracle is consulted anywhere.  This probe compares a labelling against its own
  relabellings; it never needs the true Aut-orbits, so `probe_orbit_oracle` (recorded WRONG)
  cannot contaminate it.
* Cell matching across labellings is CHECKED: if the transported colour vector disagrees with
  the refined colour vector of the relabelled graph, the row is SKIPPED and counted, never
  silently reinterpreted.
* Every skip is printed.

    cd /workspace/scratchpad && python3 -u probe_offbranch.py > probe_offbranch.out 2>&1
"""
import random
import sys
from collections import defaultdict

sys.setrecursionlimit(10000)
sys.path.insert(0, '/workspace/scratchpad')

from probe_dualdeepen import (circ, FANO, MIXED, rand_incidence, build_mp,
                              build_cfi_base, cubic)
from probe_polyloop import (adjlist, refine, indiv, target_cell,
                            greedy_deepen, replay, twist)
from probe_selfsep import g8

NREL = 4          # relabellings per witness, plus the identity
SKIPS = []


# ------------------------------------------------------------------ harvest (current design)

def deepen_gens(n, adj, adjl, chi, C):
    """`Deepen.deepenGens` verbatim: ALL anchors of the BRANCH cell `C`, replay, twist,
    IsColAut-gated.  Returns the list of verified generators (full permutations of Fin n)."""
    gens = []
    firsts = {r: indiv(n, adjl, chi, r) for r in C}
    for r1 in C:
        leaf1, seq = greedy_deepen(n, adjl, firsts[r1])
        if leaf1 is None:
            continue
        for rj in C:
            if rj == r1:
                continue
            leafj = replay(n, adjl, firsts[rj], seq)
            if leafj is None:
                continue
            t = twist(n, adj, chi, leaf1, leafj)
            if t is not None:
                gens.append(t)
    return gens


def orbits_all(n, gens):
    """Union-find over the WHOLE vertex set (not just the branch cell)."""
    par = list(range(n))

    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x

    for g in gens:
        for v in range(n):
            a, b = f(v), f(g[v])
            if a != b:
                par[a] = b
    return [f(v) for v in range(n)]


def percell_profile(n, adj):
    """{colour -> sorted multiset of orbit-block sizes inside that cell} for every
    non-singleton cell, plus the branch colour.  None if the root is discrete."""
    adjl = adjlist(n, adj)
    col = refine(n, adjl, [0] * n)
    cid, C = target_cell(n, col)
    if cid is None:
        return None, None, None
    gens = deepen_gens(n, adj, adjl, col, C)
    orb = orbits_all(n, gens)

    cells = defaultdict(list)
    for v in range(n):
        cells[col[v]].append(v)

    prof = {}
    for c, mem in cells.items():
        if len(mem) < 2:
            continue
        blocks = defaultdict(int)
        for v in mem:
            blocks[orb[v]] += 1
        prof[c] = tuple(sorted(blocks.values()))
    return prof, cid, col


def relabel(n, adj, sigma):
    """sigma[v] = image of v.  adj'[sigma u][sigma v] = adj[u][v]."""
    out = [[0] * n for _ in range(n)]
    for u in range(n):
        for v in range(n):
            out[sigma[u]][sigma[v]] = adj[u][v]
    return out


def run(name, n, adj):
    base, bcid, bcol = percell_profile(n, adj)
    if base is None:
        SKIPS.append((name, 'root discrete'))
        print(f"  {name:28s} n={n:<4d} SKIPPED — root discrete")
        return

    rng = random.Random(hash(name) & 0xffff)
    agree_branch = True
    bad_cells = set()
    checked = 0

    for _ in range(NREL):
        sigma = list(range(n))
        rng.shuffle(sigma)
        adj2 = relabel(n, adj, sigma)
        prof2, cid2, col2 = percell_profile(n, adj2)
        if prof2 is None:
            SKIPS.append((name, 'relabelled copy root-discrete (IMPOSSIBLE — refiner bug)'))
            continue
        # cell matching must be EARNED: the refined colouring of the relabelled graph must be
        # the transport of the original's.  If not, colour values are not comparable.
        if any(col2[sigma[v]] != bcol[v] for v in range(n)):
            SKIPS.append((name, 'colour values not transported — cannot match cells'))
            continue
        checked += 1
        if cid2 != bcid:
            agree_branch = False
        for c in set(base) | set(prof2):
            if base.get(c) != prof2.get(c):
                if c == bcid:
                    agree_branch = False
                else:
                    bad_cells.add(c)

    ncells = len(base)
    offb = ncells - 1
    # ⚠ NON-VACUITY.  An off-branch profile that is all-singletons (the harvest does nothing
    # there) or a single block (it does everything) is invariant for FREE and evidences
    # nothing.  Only a PARTIAL collapse can discriminate.
    nontriv = sum(1 for c, p in base.items()
                  if c != bcid and len(p) > 1 and max(p) > 1)
    collapsed = sum(1 for c, p in base.items() if c != bcid and len(p) == 1)
    verdict = 'Y' if not bad_cells else 'N'
    flag = ''
    if bad_cells:
        flag = f'   <<<< OFF-BRANCH COUNT VARIES at colours {sorted(bad_cells)}'
    if not agree_branch:
        flag += '   <<<< BRANCH CELL VARIES (contradicts the 17/17 sweep)'
    if offb == 0:
        flag += '   (single-cell — VACUOUS)'
    elif nontriv == 0:
        flag += '   (no partial off-branch collapse — VACUOUS pass)'
    else:
        flag += '   <<< NON-VACUOUS ROW'
    print(f"  {name:28s} n={n:<4d} cells={ncells:<3d} off-branch={offb:<3d} "
          f"rel={checked}/{NREL}  branch-inv={'Y' if agree_branch else 'N'}  "
          f"OFF-BRANCH-INV={verdict}  collapsed={collapsed}/{offb}  "
          f"partial={nontriv}/{offb}{flag}")


# ------------------------------------------------------------------ multi-cell witnesses

def disjoint(n1, adj1, n2, adj2):
    n = n1 + n2
    adj = [[0] * n for _ in range(n)]
    for u in range(n1):
        for v in range(n1):
            adj[u][v] = adj1[u][v]
    for u in range(n2):
        for v in range(n2):
            adj[n1 + u][n1 + v] = adj2[u][v]
    return n, adj


def cycle(m):
    adj = [[0] * m for _ in range(m)]
    for i in range(m):
        adj[i][(i + 1) % m] = adj[(i + 1) % m][i] = 1
    return m, adj


def complete(m):
    adj = [[1] * m for _ in range(m)]
    for i in range(m):
        adj[i][i] = 0
    return m, adj


def subdivision(n, adj):
    """S(G): subdivide every edge.  Original vertices keep degree deg(v); the new vertices all
    have degree 2 — so on a regular G of degree ≥ 3 the two families are DIFFERENT 1-WL cells,
    and Aut(S(G)) = Aut(G) acts non-trivially on BOTH.  This is the shape that can produce a
    PARTIAL off-branch collapse, which the disjoint-union witnesses cannot."""
    edges = [(u, v) for u in range(n) for v in range(u + 1, n) if adj[u][v]]
    m = n + len(edges)
    out = [[0] * m for _ in range(m)]
    for i, (u, v) in enumerate(edges):
        w = n + i
        out[u][w] = out[w][u] = 1
        out[v][w] = out[w][v] = 1
    return m, out


def petersen():
    pts = [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]
    n = 10
    adj = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if not (set(pts[i]) & set(pts[j])):
                adj[i][j] = adj[j][i] = 1
    return n, adj


def cube():
    n = 8
    adj = [[0] * n for _ in range(n)]
    for i in range(n):
        for b in range(3):
            j = i ^ (1 << b)
            adj[i][j] = adj[j][i] = 1
    return n, adj


def kmn(a, b):
    n = a + b
    adj = [[0] * n for _ in range(n)]
    for u in range(a):
        for v in range(a, n):
            adj[u][v] = adj[v][u] = 1
    return n, adj


def main():
    print("Is deepen's PER-CELL orbit count relabelling-invariant OFF THE BRANCH CELL?")
    print("`①` at the fused object reads ONLY the per-cell orbit COUNT (cellNarrow_length_transport).")
    print("Harvest is the CURRENT branch-cell-only design; the question is its effect elsewhere.")
    print(f"{NREL} random relabellings per witness; cell matching by invariant colour value, checked.")
    print()

    print("### designed multi-cell witnesses (different degrees ⟹ 1-WL keeps the parts apart)")
    for a, b in [(5, 4), (6, 4), (7, 4), (5, 5), (8, 4), (9, 5)]:
        na, A = cycle(a)
        nb, B = complete(b)
        run(f"C{a} + K{b}", *disjoint(na, A, nb, B))
    n1, A = cycle(6)
    n2, B = cycle(8)
    run("C6 + C8 (same degree)", *disjoint(n1, A, n2, B))
    print()

    print("### ★ SUBDIVISIONS — Aut acts on BOTH cells, the shape that can collapse off-branch")
    run("S(K4)", *subdivision(*complete(4)))
    run("S(K5)", *subdivision(*complete(5)))
    run("S(K6)", *subdivision(*complete(6)))
    run("S(K3,3)", *subdivision(*kmn(3, 3)))
    run("S(cube Q3)", *subdivision(*cube()))
    run("S(Petersen)", *subdivision(*petersen()))
    run("S(C6)+K4", *disjoint(*subdivision(*cycle(6)), *complete(4)))
    print()

    print("### bipartite / two-family witnesses")
    run("K3,4", *kmn(3, 4))
    run("K4,6", *kmn(4, 6))
    print()

    print("### the recorded rich partially-firing witness")
    run("G8 cubic non-VT", *g8())
    print()

    print("### rigid multipedes")
    for V, W, seed in [(6, 5, 1), (8, 6, 2), (10, 7, 3), (12, 8, 4)]:
        run(f"rand multipede V={V} W={W}", *build_mp(rand_incidence(V, W, 3, seed)))
    print()

    print("### mixed / gauge")
    run("MIXED multipede", *build_mp(MIXED))
    run("circ(5) multipede", *build_mp(circ(5)))
    run("mp7 Fano multipede", *build_mp(FANO))
    print()

    print("### CFI over random cubic bases")
    for m in (8, 10):
        base = cubic(m, seed=m)
        for tw in (False, True):
            run(f"CFI cubic m={m} {'tw' if tw else 'pl'}", *build_cfi_base(base, m, twist=tw))
    print()

    if SKIPS:
        print(f">>> SKIPPED {len(SKIPS)}, none silently:")
        for nm, why in SKIPS:
            print(f"      {nm}: {why}")
    else:
        print(">>> no witness skipped")


if __name__ == '__main__':
    main()
