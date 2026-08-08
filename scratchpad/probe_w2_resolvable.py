#!/usr/bin/env python3
"""
probe_w2_resolvable.py — W2 STEP 0 (2026-08-08)

============================================================================================
THE QUESTION
============================================================================================
`RecordDeepenCell.ResolvableCellAt adj χ` is now the single named W2 obligation:

    ∃ c ∈ nonSingletonColours χ,  GoodCell adj χ c  ∧  CellSingleOrbit adj χ c

i.e. SOME non-singleton cell is (a) good-anchored — the per-cell deepen guard opens on it — and
(b) a single Aut(adj,χ)-orbit.  `handledSC_of_resolvableCells` turns "that holds at every reached
non-discrete node" into `HandledSC` at the PUBLISHED object, hence "never flags".

Two things this probe must settle before any CFI Lean is written:

  Q1  NON-VACUITY / FEASIBILITY — does `ResolvableCellAt` actually hold at every reached node of
      the CFI / multipede witnesses?  (If not, W2 is not reachable through this socket.)

  Q2  IS THE WIDENING LOAD-BEARING — is there a node where the TARGET cell is not resolvable but
      some OTHER cell is?  If yes, the `SomeCellOrbit` socket (SelectCell §9) is necessary, not
      cosmetic; if no, the old target-cell route would have sufficed and the socket bought nothing.

============================================================================================
SOUNDNESS DISCIPLINE  (read before quoting a number)
============================================================================================
* `GoodCell` is `probe_offbranch5.guard_cell` verbatim — the per-cell CertPath walk, each level
  tested against generators anchored in that same level's cell.  `None` = budgeted out, and is
  NEVER counted as a pass.
* `CellSingleOrbit` is decided by union-find over the generators `Ctx`/`canon` discovers
  (`probe_verdict_invariance.true_partition`'s method, the sanctioned reference — ⛔ never
  `probe_orbit_oracle`, which is recorded WRONG and errs by merging).  Every such generator is an
  automorphism of `(adj, col)`, so:
      single-orbit = YES is a POSITIVE CERTIFICATE (the cell demonstrably is one orbit);
      single-orbit = NO  is only a FAILURE TO CERTIFY (the generating set may be incomplete).
  ⟹ a "resolvable at every node" verdict is sound; a "not resolvable" verdict is a lower bound and
  is reported as such.
* Reached nodes are the BFS of `Deepen.step` to `DEPTH`, ≤`BRANCH` members per node — the same
  scoping as `probe_offbranch5`.  ⚠ NOT a family-level claim: root-only sweeps are recorded VACUOUS
  and this one is depth-limited too.

    cd /workspace/scratchpad && python3 -u probe_w2_resolvable.py > probe_w2_resolvable.out 2>&1
"""
import random
import sys
from collections import defaultdict

sys.setrecursionlimit(10000)
sys.path.insert(0, '/workspace/scratchpad')

from probe_dualdeepen import (circ, FANO, MIXED, rand_incidence, build_mp,
                              build_cfi_base, cubic, Ctx, canon)
from probe_polyloop import adjlist, refine, indiv, target_cell
from probe_selfsep import g8
from probe_offbranch import subdivision, petersen, complete
from probe_offbranch5 import guard_cell, cells_of, reached

DEPTH = 1
BRANCH = 2
LEAFCAP = 200000
SKIPS = []


def aut_gens(n, adj, col):
    """Generators of Aut(adj, col) discovered by the canonical search — SOUND, not complete."""
    ctx = Ctx(n, adj, prune=True, leafcap=LEAFCAP)
    canon(ctx, list(col), [], root=True)
    return [g for (g, p) in ctx.gens]


def orbit_classes(n, gens):
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


def run(name, n, adj):
    adjl = adjlist(n, adj)
    col0 = refine(n, adjl, [0] * n)
    if target_cell(n, col0)[0] is None:
        SKIPS.append((name, 'root discrete'))
        return

    nodes = 0
    all_resolvable = True
    target_resolvable_all = True
    widening_needed = 0          # nodes where target is NOT resolvable but some other cell IS
    first_bad = None
    cells_tot = cells_good = cells_single = cells_res = 0

    for depth, col in reached(n, adjl, col0):
        tid, _T = target_cell(n, col)
        if tid is None:
            continue
        nodes += 1
        cls = orbit_classes(n, aut_gens(n, adj, col))
        res_here = []
        for c, mem in cells_of(n, col).items():
            cells_tot += 1
            g = guard_cell(n, adj, adjl, col, mem)
            single = len({cls[v] for v in mem}) == 1
            if g:
                cells_good += 1
            if single:
                cells_single += 1
            if g and single:
                cells_res += 1
                res_here.append(c)
        if not res_here:
            all_resolvable = False
            if first_bad is None:
                first_bad = (depth, sorted(cells_of(n, col).keys()))
        if tid not in res_here:
            target_resolvable_all = False
            if res_here:
                widening_needed += 1

    verdict = 'Y' if all_resolvable else 'N'
    tv = 'Y' if target_resolvable_all else 'N'
    flag = ''
    if all_resolvable and widening_needed:
        flag = f'   <<< WIDENING LOAD-BEARING at {widening_needed} node(s)'
    elif not all_resolvable:
        flag = '   <<<< NOT RESOLVABLE (see first-bad)'
    print(f"  {name:24s} n={n:<4d} nodes={nodes:<3d} cells={cells_tot:<4d} "
          f"good={cells_good:<4d} single={cells_single:<4d} resolvable={cells_res:<4d}  "
          f"ALL-NODES={verdict}  TARGET-ALWAYS={tv}{flag}")
    if first_bad:
        print(f"        first unresolvable node: depth {first_bad[0]}, cells {first_bad[1]}")


def main():
    print("W2 STEP 0 — does `ResolvableCellAt` hold at every reached node?")
    print("  ALL-NODES=Y     : every reached non-discrete node has a good-anchored single-orbit cell")
    print("  TARGET-ALWAYS=Y : the TARGET cell is always one of them (⟹ the old route would do)")
    print("  single-orbit is a POSITIVE certificate only; 'no' may be incompleteness of the gens.")
    print(f"BFS depth {DEPTH}, <={BRANCH} members/node, leafcap {LEAFCAP}.")
    print()
    base = cubic(8, seed=8)
    run("CFI cubic m=8 pl", *build_cfi_base(base, 8, twist=False))
    run("CFI cubic m=8 tw", *build_cfi_base(base, 8, twist=True))
    run("rand multipede V=6 W=5", *build_mp(rand_incidence(6, 5, 3, 1)))
    run("MIXED multipede", *build_mp(MIXED))
    run("circ(5) multipede", *build_mp(circ(5)))
    run("mp7 Fano multipede", *build_mp(FANO))
    run("G8 cubic non-VT", *g8())
    run("S(K5)", *subdivision(*complete(5)))
    run("S(Petersen)", *subdivision(*petersen()))
    print()
    if SKIPS:
        print(f">>> SKIPPED {len(SKIPS)}, none silently:")
        for nm, why in sorted(set(SKIPS)):
            print(f"      {nm}: {why}")
    else:
        print(">>> no witness skipped")


if __name__ == '__main__':
    main()
