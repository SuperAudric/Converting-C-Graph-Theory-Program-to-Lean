#!/usr/bin/env python3
"""
probe_offbranch2.py — PER-CELL ORBIT-COUNT INVARIANCE AT **REACHED NODES**   (2026-08-07)

============================================================================================
WHY v2 — v1 WAS UNDER-SCOPED IN EXACTLY THE RECORDED BLIND SPOT
============================================================================================
`probe_offbranch.py` measured the ROOT only and found 30/30 invariant (7 rows non-vacuous).
That is not decisive, because `ChainDescent/DeepenGuard.lean`'s header records:

  > on the CFI graph over a random cubic base with m = 8 there is **a node** whose branch cell
  > the all-anchor harvest certifies as ONE ORBIT under some labellings and splits 8 + 8 under
  > others.  The certificate is computed *by* the index-picked descent, so it inherits exactly
  > that descent's labelling dependence.

"a node" — not the root.  Every sweep on record (17/17, 13/13, and v1) is root-only, so the
one recorded falsifier of harvest invariance lives where none of them looked.

============================================================================================
WHAT IS MEASURED, AND WHY THIS SHAPE IS THE RIGHT ONE
============================================================================================
`SelectNode.cellNarrow_length_transport` is stated at a FIXED `(adj, χ, σ)`:

    (cellNarrow key S (relabelAdj σ adj) (transportColouring σ χ) c).length
      = (cellNarrow key S adj χ c).length

So the correct experiment does NOT re-derive a node in the relabelled graph.  It fixes a
reached `χ`, TRANSPORTS it by `σ`, and compares per-cell orbit counts on the two sides.  Cells
correspond under `σ` by construction, so no colour-matching heuristic is needed at all.

Per witness: reached nodes by BFS to depth D over the target cell (≤ B distinct members per
node, deduped by colour vector), each compared under NREL relabellings.

Reported per witness:
  nodes       — reached nodes tested (root included)
  nv          — nodes with a NON-VACUOUS off-branch profile (some off-branch cell partially
                collapsed: neither all-singletons nor one block).  A vacuous node evidences
                nothing, exactly as in v1.
  BRANCH-INV  — branch-cell count invariant at every node?   (the recorded falsifier's shape)
  OFFBR-INV   — off-branch counts invariant at every node?   <<< THE QUESTION
  first failure is printed with the node depth and the two differing profiles.

============================================================================================
SOUNDNESS
============================================================================================
* No orbit oracle anywhere: this compares a labelling against its own transport.
* `twist` carries the `IsColAut` gate, so every generator counted is verified.
* Harvest is the CURRENT branch-cell-only `deepenGens`.
* Every skip is printed.

    cd /workspace/scratchpad && python3 -u probe_offbranch2.py > probe_offbranch2.out 2>&1
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
from probe_offbranch import (deepen_gens, orbits_all, relabel, subdivision,
                             petersen, cube, kmn, cycle, complete, disjoint)

NREL = 4     # relabellings per node
DEPTH = 3    # BFS depth over reached nodes
BRANCH = 3   # distinct cell members individualized per node
SKIPS = []


def profile(n, adj, adjl, col):
    """{colour -> sorted multiset of harvest-orbit block sizes} over non-singleton cells,
    plus the branch colour.  Harvest = branch-cell anchors (the current `deepenGens`)."""
    cid, C = target_cell(n, col)
    if cid is None:
        return None, None
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
    return prof, cid


def reached_nodes(n, adjl, col0):
    """Colourings reachable by individualizing a member of the target cell, BFS to DEPTH,
    ≤ BRANCH members per node, deduped."""
    seen = {tuple(col0)}
    out = [(0, col0)]
    frontier = [(0, col0)]
    while frontier:
        d, col = frontier.pop(0)
        if d >= DEPTH:
            continue
        cid, C = target_cell(n, col)
        if cid is None:
            continue
        for v in sorted(C)[:BRANCH]:
            ch = indiv(n, adjl, col, v)
            key = tuple(ch)
            if key in seen:
                continue
            seen.add(key)
            out.append((d + 1, ch))
            frontier.append((d + 1, ch))
    return out


def run(name, n, adj):
    adjl = adjlist(n, adj)
    col0 = refine(n, adjl, [0] * n)
    if target_cell(n, col0)[0] is None:
        SKIPS.append((name, 'root discrete'))
        print(f"  {name:26s} n={n:<4d} SKIPPED — root discrete")
        return

    rng = random.Random(abs(hash(name)) & 0xffff)
    sigmas = []
    for _ in range(NREL):
        s = list(range(n))
        rng.shuffle(s)
        sigmas.append(s)
    relabelled = [(s, relabel(n, adj, s)) for s in sigmas]
    reladjl = [(s, a, adjlist(n, a)) for s, a in relabelled]

    nodes = reached_nodes(n, adjl, col0)
    nnodes = 0
    nv = 0
    branch_ok = True
    offbr_ok = True
    first_fail = None

    for depth, col in nodes:
        prof, cid = profile(n, adj, adjl, col)
        if prof is None:
            continue
        nnodes += 1
        if any(c != cid and len(p) > 1 and max(p) > 1 for c, p in prof.items()):
            nv += 1

        for s, adj2, adjl2 in reladjl:
            # transportColouring σ χ : (σ v) ↦ χ v
            col2 = [0] * n
            for v in range(n):
                col2[s[v]] = col[v]
            prof2, cid2 = profile(n, adj2, adjl2, col2)
            if prof2 is None:
                SKIPS.append((name, 'transported node has no target cell (refiner bug)'))
                continue
            if cid2 != cid or prof.get(cid) != prof2.get(cid):
                if branch_ok and first_fail is None:
                    first_fail = ('BRANCH', depth, prof.get(cid), prof2.get(cid))
                branch_ok = False
            for c in set(prof) | set(prof2):
                if c == cid:
                    continue
                if prof.get(c) != prof2.get(c):
                    if first_fail is None or first_fail[0] == 'BRANCH':
                        if offbr_ok:
                            first_fail = ('OFF-BRANCH', depth, prof.get(c), prof2.get(c))
                    offbr_ok = False

    flag = ''
    if not branch_ok:
        flag += '   <<<< BRANCH count varies'
    if not offbr_ok:
        flag += '   <<<< OFF-BRANCH count varies'
    if nv == 0:
        flag += '   (no non-vacuous node — VACUOUS)'
    print(f"  {name:26s} n={n:<4d} nodes={nnodes:<3d} non-vacuous={nv:<3d} "
          f"BRANCH-INV={'Y' if branch_ok else 'N'}  OFFBR-INV={'Y' if offbr_ok else 'N'}{flag}")
    if first_fail:
        kind, d, a, b = first_fail
        print(f"        first {kind} failure at depth {d}: {a}  vs  {b}")


def main():
    print("PER-CELL orbit-count invariance at REACHED NODES (v1 measured the root only).")
    print("Stated as `cellNarrow_length_transport` is: fix χ, TRANSPORT it by σ, compare counts.")
    print(f"BFS depth {DEPTH}, ≤{BRANCH} members/node, {NREL} relabellings per node.")
    print("⚠ DeepenGuard's header records a CFI m=8 falsifier AT A NODE — if this probe is")
    print("  sensitive it should reproduce it; if it does not, say so rather than claim a pass.")
    print()

    print("### CFI over random cubic bases — where the recorded falsifier lives")
    for m in (8, 10):
        base = cubic(m, seed=m)
        for tw in (False, True):
            run(f"CFI cubic m={m} {'tw' if tw else 'pl'}", *build_cfi_base(base, m, twist=tw))
    print()

    print("### mixed / gauge")
    run("MIXED multipede", *build_mp(MIXED))
    run("circ(5) multipede", *build_mp(circ(5)))
    run("mp7 Fano multipede", *build_mp(FANO))
    print()

    print("### rigid multipedes")
    for V, W, seed in [(6, 5, 1), (8, 6, 2)]:
        run(f"rand multipede V={V} W={W}", *build_mp(rand_incidence(V, W, 3, seed)))
    print()

    print("### small structured / multi-cell")
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
