#!/usr/bin/env python3
"""
IS THE SECONDARY GUARD (§8/§9 of DeepenGuardComplete) STRICTLY WEAKER **IN PRACTICE**?

Lean has:
  CertifiedG deepenSupply adj chi  <->  Tinhofer adj chi          (every anchor GOOD)
  GoodOrIsolated inv adj chi       :=   every anchor GOOD or ISOLATED-by-inv
  goodOrIsolated_of_certifiedG     :   CertifiedG => GoodOrIsolated     (weaker, proved)

Proved-weaker is not measured-weaker.  This asks whether the second disjunct ever FIRES:
is there a witness where some anchor is BAD but `stepSum` isolates it, so the secondary
guard is OPEN where the primary is SHUT?

`stepSum` here is the Python analogue of Lean's `Deepen.stepSum` -- the sum of the refined
colour ranks after individualizing u.  Refinement details differ slightly from
`warmRefineVec`, so read this as a concept check on the DISJUNCT, not as a port of the
Lean invariant's exact fibres.

Columns:
  cell      root branch cell size
  orb       number of TRUE Aut-orbits inside that cell
  good      anchors whose whole greedy path has single-orbit cells (= CertifiedG's conjunct)
  isol      anchors uniquely valued by stepSum inside the cell
  rigid     anchors that are TRUE Aut-fixed points (what IsolatedBy soundly stands in for)
  PRIM      CertifiedG open?      (all good)
  SEC       GoodOrIsolated open?  (all good-or-isolated)
  ***       SEC open while PRIM shut  = the strict win we are hunting
"""
import sys, random
from collections import defaultdict
sys.setrecursionlimit(10000)

from probe_dualdeepen import (circ, FANO, MIXED, rand_incidence, build_mp,
                              build_cfi_base, cubic, relabel, Ctx, canon)
from probe_polyloop import adjlist, refine, indiv, target_cell
from probe_certkey import true_orbit_partition, descend_cert


def step_sum(n, adjl, col, u):
    """Lean `Deepen.stepSum`: total of the refined colour ranks after individualizing u."""
    return sum(indiv(n, adjl, col, u))


def analyse(name, n, adj):
    adjl = adjlist(n, adj)
    col = refine(n, adjl, [0] * n)
    cid, C = target_cell(n, col)
    if cid is None:
        print(f"{name:34s}  discrete root -- no branch cell")
        return None

    orb = true_orbit_partition(n, adj, col)
    norb = len({orb[v] for v in C})
    # a TRUE fixed point of Aut(adj,col): its orbit block has size 1
    blocksz = defaultdict(int)
    for v in range(n):
        blocksz[orb[v]] += 1
    rigid = [v for v in C if blocksz[orb[v]] == 1]

    good = [v for v in C if descend_cert(n, adj, adjl, col, v)[1]]

    sig = {v: step_sum(n, adjl, col, v) for v in C}
    cnt = defaultdict(int)
    for v in C:
        cnt[sig[v]] += 1
    isol = [v for v in C if cnt[sig[v]] == 1]

    prim = len(good) == len(C)
    sec = all((v in good) or (v in isol) for v in C)
    star = "  ***STRICT WIN***" if (sec and not prim) else ""
    print(f"{name:34s}  cell={len(C):3d} orb={norb:3d} good={len(good):3d} "
          f"isol={len(isol):3d} rigid={len(rigid):3d}  PRIM={'open' if prim else 'SHUT'} "
          f"SEC={'open' if sec else 'SHUT'}{star}")

    # soundness cross-check: an isolated vertex had better BE Aut-rigid, or
    # orbitTrivial_of_isolatedBy would be unsound for this inv.
    bad_isol = [v for v in isol if blocksz[orb[v]] != 1]
    if bad_isol:
        print(f"{'':34s}  !! UNSOUND inv: isolated but not Aut-rigid: {bad_isol}")
    return (prim, sec)


if __name__ == "__main__":
    random.seed(20260806)
    rows = []
    print("### rigid multipedes -- memory records these as 0/4 good anchors yet 'exact'")
    for (V, W, deg, seed) in [(6, 5, 3, 1), (8, 6, 3, 2), (10, 7, 3, 3), (12, 8, 3, 4)]:
        n, adj = build_mp(rand_incidence(V, W, deg, seed))
        rows.append(analyse(f"rand multipede V={V} W={W}", n, adj))
    print()
    print("### structured witnesses")
    for nm, gen in [("MIXED multipede", MIXED), ("circ(5) multipede", circ(5)),
                    ("mp7 Fano multipede", FANO)]:
        n, adj = build_mp(gen)
        rows.append(analyse(nm, n, adj))
    print()
    print("### CFI over cubic bases")
    for m in (8, 10):
        for tw in (False, True):
            n, adj = build_cfi_base(cubic(m, 11 + m), m, tw)
            rows.append(analyse(f"CFI cubic m={m} twist={tw}", n, adj))
    print()
    wins = sum(1 for r in rows if r and r[1] and not r[0])
    print(f"STRICT WINS (SEC open, PRIM shut): {wins} / {len([r for r in rows if r])}")
