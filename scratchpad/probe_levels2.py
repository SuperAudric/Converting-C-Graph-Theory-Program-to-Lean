#!/usr/bin/env python3
"""
probe_levels2.py — FULL SWEEP OF THE **LEVEL-GENERATOR** HARVEST `C`        (2026-08-07)

============================================================================================
THE CANDIDATE
============================================================================================
  A = today: node-global list, generators from deepening pairs of the BRANCH cell only.
      ⛔ REFUTED (probe_offbranch2/3): CFI m=8/10, depth 1, guard OPEN both sides, an
         off-branch cell counts (1,1) vs (2,).
  B = cell-indexed list (probe_offbranch4/5).  Works, but needs `cellNarrow`'s signature to
      change — a new `CellSupply` type threaded through selColour/selNode/selProbeCost.
  C = A ∪ { deepen's harvest at EVERY level ψ of EVERY anchor's deepening path }.
      Every such generator is verified `IsColAut adj ψ`, and ψ refines χ, so it is
      `IsColAut adj χ` — legitimate at the original node.  The guard ALREADY computes these
      (`CertPath`'s per-level `CellIsOrbit`) and discards them.

★ WHY `C` MATTERS ARCHITECTURALLY: it keeps the generator list NODE-GLOBAL.  No `CellSupply`
type, no signature change in `SelectNode`, no per-cell guard — a pure supply change, which is
what the plan claims to be and (as B) is not.

★ WHY IT SHOULD WORK (user, 2026-08-07): the harvest emits ONE witness per related pair — a
transversal of `Stab(r₁)` — and never a generator OF `Stab(r₁)`.  The stabilizer is exactly
what acts on the other cells.  A level-generator is an automorphism of a colouring that FIXES
everything individualized above it, i.e. it IS a stabilizer element.  So `C` supplies the
missing half of the generating set.

============================================================================================
MEASURED
============================================================================================
Reached nodes (BFS depth D), every non-singleton cell, NREL relabellings, comparing a fixed χ
against its own transport.  Per witness:

  A-INV   — are A's per-cell counts invariant?     (expected N on CFI)
  C-INV   — are C's per-cell counts invariant?     <<< THE QUESTION
  C-fires — cells C collapses to one block          (vacuity guard: invariant-by-doing-nothing
                                                     is worthless)
  C>A     — cells C fires that A does not           (coverage gained)

⚠ COST GATE: `C` is `≤ n` anchors × `≤ n` levels × a harvest, i.e. the guard's own (unbilled,
≈ n⁸) cost.  Nodes whose branch cell exceeds CELLCAP are SKIPPED and COUNTED, never silently
treated as passes.

    cd /workspace/scratchpad && python3 -u probe_levels2.py > probe_levels2.out 2>&1
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
                             petersen, cube, complete, cycle, disjoint, kmn)

NREL = 3
DEPTH = 2
BRANCH = 2
CELLCAP = 10       # skip a node whose branch cell exceeds this (C is guard-cost)
MAXLEVEL = 60
SKIPS = []


def cells_of(n, col):
    d = defaultdict(list)
    for v in range(n):
        d[col[v]].append(v)
    return {c: m for c, m in d.items() if len(m) >= 2}


def gens_A(n, adj, adjl, col):
    cid, C = target_cell(n, col)
    return [] if cid is None else deepen_gens(n, adj, adjl, col, C)


def gens_C(n, adj, adjl, col):
    cid, C = target_cell(n, col)
    if cid is None:
        return []
    out = list(deepen_gens(n, adj, adjl, col, C))
    for r in sorted(C):
        psi = indiv(n, adjl, col, r)
        for _ in range(MAXLEVEL):
            c2, C2 = target_cell(n, psi)
            if c2 is None:
                break
            out.extend(deepen_gens(n, adj, adjl, psi, C2))
            psi = indiv(n, adjl, psi, min(C2))
    return out


def counts(n, gens, cells):
    orb = orbits_all(n, gens)
    return {c: len({orb[v] for v in mem}) for c, mem in cells.items()}


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
        print(f"  {name:24s} SKIPPED — root discrete")
        return
    rng = random.Random(abs(hash(name)) & 0xffff)
    rel = []
    for _ in range(NREL):
        s = list(range(n))
        rng.shuffle(s)
        a2 = relabel(n, adj, s)
        rel.append((s, a2, adjlist(n, a2)))

    aok = cok = True
    cfail = None
    tested = skipped = 0
    cfires = ctot = cgtA = 0

    for depth, col in reached(n, adjl, col0):
        cid, C = target_cell(n, col)
        if cid is None:
            continue
        if len(C) > CELLCAP:
            skipped += 1
            SKIPS.append((name, f'node depth {depth}: branch cell {len(C)} > CELLCAP'))
            continue
        tested += 1
        cells = cells_of(n, col)
        A1, C1 = counts(n, gens_A(n, adj, adjl, col), cells), counts(n, gens_C(n, adj, adjl, col), cells)
        for c in cells:
            ctot += 1
            if C1[c] == 1:
                cfires += 1
                if A1[c] != 1:
                    cgtA += 1
        for s, adj2, adjl2 in rel:
            col2 = [0] * n
            for v in range(n):
                col2[s[v]] = col[v]
            cells2 = {c: [s[x] for x in mem] for c, mem in cells.items()}
            A2 = counts(n, gens_A(n, adj2, adjl2, col2), cells2)
            C2c = counts(n, gens_C(n, adj2, adjl2, col2), cells2)
            for c in cells:
                if A1[c] != A2[c]:
                    aok = False
                if C1[c] != C2c[c]:
                    if cok:
                        cfail = (depth, c, len(cells[c]), C1[c], C2c[c])
                    cok = False

    tag = ''
    if cok and cfires == 0:
        tag = '   (C never fires — VACUOUS)'
    elif cok and not aok:
        tag = '   <<< C REPAIRS IT'
    elif not cok:
        tag = '   <<<< C ALSO VARIES'
    print(f"  {name:24s} nodes={tested:<3d} skipped={skipped:<2d} cells={ctot:<4d} "
          f"A-INV={'Y' if aok else 'N'}  C-INV={'Y' if cok else 'N'}  "
          f"C-fires={cfires}/{ctot}  C>A={cgtA}{tag}")
    if cfail:
        d, c, sz, x, y = cfail
        print(f"        C first fail: depth {d} colour {c} (size {sz}): {x} vs {y}")


def main():
    print("FULL SWEEP of the LEVEL-GENERATOR harvest C (keeps the node-global list).")
    print("C = A ∪ deepen's harvest at every level of every anchor's certified path.")
    print(f"BFS depth {DEPTH}, ≤{BRANCH} members/node, {NREL} relabellings, CELLCAP={CELLCAP}.")
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
        agg = defaultdict(int)
        for nm, why in SKIPS:
            agg[(nm, why.split(':')[0])] += 1
        print(f">>> SKIPPED {len(SKIPS)} node-checks, none silently:")
        for (nm, why), k in sorted(agg.items()):
            print(f"      {nm}: {why} × {k}")
    else:
        print(">>> nothing skipped")


if __name__ == '__main__':
    main()
