#!/usr/bin/env python3
"""
probe_offbranch4.py — DOES A **PER-CELL** GENERATOR LIST REPAIR THE FALSIFIER?   (2026-08-07)

============================================================================================
THE TWO ARCHITECTURES BEING COMPARED
============================================================================================
`SelectNode.cellNarrow key S adj χ c = cellNarrowV key (verified S adj χ) adj χ c` — the KEY
half is per-cell (`keepMin key adj χ (cellList χ c)`) but the CONSUME half is NODE-GLOBAL: one
`verified S adj χ` list, probed by every cell.  That is sound for cell-agnostic supplies
(`foldSupply`/`deckSupply`/`deck2Supply`/`kernelSupply` harvest from the whole graph), but
`deepenSupply` is CELL-ANCHORED — its generators come from deepening the BRANCH cell's anchors.

  (A) NODE-GLOBAL  — cell `c` is judged by generators anchored in the BRANCH cell.
                     ⛔ REFUTED by probe_offbranch3: CFI m=8/10, depth 1, guard OPEN on both
                     sides, off-branch count `(1,1)` vs `(2,)`.
  (B) PER-CELL     — cell `c` is judged by generators anchored in `c` ITSELF.
                     <<< THIS PROBE.  "The resolver is run on a single cell."

Harvest cost is identical: both pay `Σ_c m_c² ≤ n²` deepenings per node.  Trap #2's measured
10× was re-evaluating the WHOLE node-global supply once per probed cell; (B) evaluates only
cell `c`'s own harvest for cell `c`, so that blow-up does not apply.

============================================================================================
WHAT IS MEASURED
============================================================================================
At every reached node χ (BFS depth D) and every non-singleton cell c, under NREL relabellings,
comparing a fixed χ against its own transport (the shape `cellNarrow_length_transport` states):

  A-count(c) = #orbit-blocks of ⟨deepenGens anchored at the BRANCH cell⟩ restricted to c
  B-count(c) = #orbit-blocks of ⟨deepenGens anchored at c ITSELF⟩ restricted to c

  A-INV / B-INV : are those counts invariant under transport, at every node and cell?
  B-fires       : cells where B-count = 1 (the per-cell harvest resolves the cell) — coverage,
                  reported because an architecture that is invariant by doing NOTHING is
                  worthless (the standing vacuity trap).

⚠ A row where B-INV=Y but B-fires=0 everywhere is a VACUOUS pass and is flagged as such.

============================================================================================
SOUNDNESS
============================================================================================
* No orbit oracle: each labelling is compared against its own transport.
* `twist` carries the `IsColAut` gate, so every generator counted is verified.
* Skips printed, never silent.

    cd /workspace/scratchpad && python3 -u probe_offbranch4.py > probe_offbranch4.out 2>&1
"""
import random
import sys
from collections import defaultdict

sys.setrecursionlimit(10000)
sys.path.insert(0, '/workspace/scratchpad')

from probe_dualdeepen import circ, FANO, MIXED, rand_incidence, build_mp, build_cfi_base, cubic
from probe_polyloop import adjlist, refine, indiv, target_cell
from probe_selfsep import g8
from probe_offbranch import (deepen_gens, orbits_all, relabel, subdivision,
                             petersen, cube, kmn, cycle, complete, disjoint)

NREL = 4
DEPTH = 2
BRANCH = 3
SKIPS = []


def cells_of(n, col):
    d = defaultdict(list)
    for v in range(n):
        d[col[v]].append(v)
    return {c: m for c, m in d.items() if len(m) >= 2}


def counts(n, adj, adjl, col):
    """(A-counts, B-counts, branch colour): per non-singleton cell, the number of harvest-orbit
    blocks inside it, under the node-global (A) and per-cell (B) generator lists."""
    cid, C = target_cell(n, col)
    if cid is None:
        return None, None, None
    cs = cells_of(n, col)

    orbA = orbits_all(n, deepen_gens(n, adj, adjl, col, C))
    A = {c: len({orbA[v] for v in mem}) for c, mem in cs.items()}

    B = {}
    for c, mem in cs.items():
        orbB = orbits_all(n, deepen_gens(n, adj, adjl, col, mem))
        B[c] = len({orbB[v] for v in mem})
    return A, B, cid


def reached(n, adjl, col0):
    out, frontier, seen = [(0, col0)], [(0, col0)], {tuple(col0)}
    while frontier:
        d, col = frontier.pop(0)
        if d >= DEPTH:
            continue
        cid, C = target_cell(n, col)
        if cid is None:
            continue
        for v in sorted(C)[:BRANCH]:
            ch = indiv(n, adjl, col, v)
            k = tuple(ch)
            if k not in seen:
                seen.add(k)
                out.append((d + 1, ch))
                frontier.append((d + 1, ch))
    return out


def run(name, n, adj):
    adjl = adjlist(n, adj)
    col0 = refine(n, adjl, [0] * n)
    if target_cell(n, col0)[0] is None:
        SKIPS.append((name, 'root discrete'))
        print(f"  {name:24s} n={n:<4d} SKIPPED — root discrete")
        return

    rng = random.Random(abs(hash(name)) & 0xffff)
    rel = []
    for _ in range(NREL):
        s = list(range(n))
        rng.shuffle(s)
        a2 = relabel(n, adj, s)
        rel.append((s, a2, adjlist(n, a2)))

    aok = bok = True
    afail = bfail = None
    nodes = ncellchk = bfires = bcells = 0

    for depth, col in reached(n, adjl, col0):
        A, B, cid = counts(n, adj, adjl, col)
        if A is None:
            continue
        nodes += 1
        for c in A:
            bcells += 1
            if B[c] == 1:
                bfires += 1
        for s, adj2, adjl2 in rel:
            col2 = [0] * n
            for v in range(n):
                col2[s[v]] = col[v]
            A2, B2, cid2 = counts(n, adj2, adjl2, col2)
            if A2 is None:
                SKIPS.append((name, 'transported node lost its target cell'))
                continue
            ncellchk += 1
            for c in set(A) | set(A2):
                if A.get(c) != A2.get(c):
                    if aok:
                        afail = (depth, c, A.get(c), A2.get(c), c == cid)
                    aok = False
                if B.get(c) != B2.get(c):
                    if bok:
                        bfail = (depth, c, B.get(c), B2.get(c), c == cid)
                    bok = False

    flag = ''
    if bok and bfires == 0:
        flag = '   (B never fires — VACUOUS pass)'
    elif bok and not aok:
        flag = '   <<< PER-CELL REPAIRS IT'
    elif not bok:
        flag = '   <<<< PER-CELL ALSO VARIES'
    print(f"  {name:24s} n={n:<4d} nodes={nodes:<3d} cells={bcells:<4d} "
          f"A-INV={'Y' if aok else 'N'}  B-INV={'Y' if bok else 'N'}  "
          f"B-fires={bfires}/{bcells}{flag}")
    if afail:
        d, c, x, y, isbr = afail
        print(f"        A first fail: depth {d} colour {c} "
              f"({'branch' if isbr else 'OFF-BRANCH'})  {x} vs {y}")
    if bfail:
        d, c, x, y, isbr = bfail
        print(f"        B first fail: depth {d} colour {c} "
              f"({'branch' if isbr else 'OFF-BRANCH'})  {x} vs {y}")


def main():
    print("Does a PER-CELL generator list repair the off-branch falsifier?")
    print("A = cell judged by BRANCH-anchored generators (today).  B = cell judged by its OWN.")
    print(f"BFS depth {DEPTH}, ≤{BRANCH} members/node, {NREL} relabellings, compared by transport.")
    print()

    print("### CFI over random cubic bases — where A is refuted")
    for m in (8, 10):
        base = cubic(m, seed=m)
        for tw in (False, True):
            run(f"CFI cubic m={m} {'tw' if tw else 'pl'}", *build_cfi_base(base, m, twist=tw))
    print()

    print("### mixed / gauge / multipedes")
    run("MIXED multipede", *build_mp(MIXED))
    run("circ(5) multipede", *build_mp(circ(5)))
    run("mp7 Fano multipede", *build_mp(FANO))
    for V, W, seed in [(6, 5, 1), (8, 6, 2)]:
        run(f"rand multipede V={V} W={W}", *build_mp(rand_incidence(V, W, 3, seed)))
    print()

    print("### structured / multi-cell")
    run("G8 cubic non-VT", *g8())
    run("S(K5)", *subdivision(*complete(5)))
    run("S(Petersen)", *subdivision(*petersen()))
    run("S(cube Q3)", *subdivision(*cube()))
    run("C7 + K4", *disjoint(*cycle(7), *complete(4)))
    run("K4,6", *kmn(4, 6))
    print()

    if SKIPS:
        print(f">>> SKIPPED {len(SKIPS)}, none silently:")
        for nm, why in sorted(set(SKIPS)):
            print(f"      {nm}: {why}")
    else:
        print(">>> no witness skipped")


if __name__ == '__main__':
    main()
