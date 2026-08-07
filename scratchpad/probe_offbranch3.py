#!/usr/bin/env python3
"""
probe_offbranch3.py — AT THE OFF-BRANCH FALSIFIER, IS THE **GUARD** OPEN?     (2026-08-07)

============================================================================================
THE QUESTION THIS SETTLES
============================================================================================
`probe_offbranch2.py` found, on all four CFI witnesses at DEPTH 1, an off-branch cell whose
harvest orbit count is `(1,1)` under one labelling and `(2,)` under its own transport — i.e.
`cellNarrow ... c` has length 2 on one side and 1 on the other.  That is exactly what
`SelectNode.selColour` reads, so it breaks `①` for the RAW `deepenSupply`.

But `Publication` would never use the raw supply.  It would use `Deepen.deepenSupplyCert`,
whose guard is `CertifiedG deepenSupply` — and `DeepenGuardComplete.tinhofer_iff_certifiedG`
proves that guard EQUAL to the intrinsic `Tinhofer`, hence automatically relabelling-invariant.

So the falsifier only bites if the guard is **OPEN** at that node:

  * guard SHUT  ⟹ the supply emits `[]` on BOTH sides (invariantly, by the ↔), every cell's
                  count is |cell| on both sides, and `①` survives with NO per-cell harvest.
                  The guard did its job: it discarded a correct-but-unverifiable answer.
  * guard OPEN  ⟹ a genuine falsifier for the GUARDED supply too, and per-cell harvest (or an
                  equivalent off-branch argument) is REQUIRED for `①` at the fused object.

============================================================================================
WHAT IS COMPUTED — no orbit oracle needed
============================================================================================
`CertifiedG` is decidable from deepen's own output alone:

    CertPath S adj fuel cur  :  at each level, `chooseIdK` names the lowest non-singleton cell
                                of the WHOLE graph; require `CellIsOrbit S adj cur.col`
                                (deepen's verified gens connect every pair of that cell);
                                then step on the LOWEST-INDEX member.
    CertifiedG S adj χ       :  ∀ r ∈ branches χ, CertPath S adj n (step adj χ r)

Ports `DeepenGuard.CertPath` / `CertifiedG` directly.  Short-circuits on the first failing
level, which is why this is affordable at all.

⚠ A LEVEL BUDGET is enforced; a node that exhausts it is reported UNKNOWN, never as a pass.

    cd /workspace/scratchpad && python3 -u probe_offbranch3.py > probe_offbranch3.out 2>&1
"""
import random
import sys
from collections import defaultdict

sys.setrecursionlimit(10000)
sys.path.insert(0, '/workspace/scratchpad')

from probe_dualdeepen import circ, MIXED, build_mp, build_cfi_base, cubic
from probe_polyloop import adjlist, refine, indiv, target_cell
from probe_offbranch import deepen_gens, orbits_all, relabel

NREL = 4
DEPTH = 1
BRANCH = 3
LEVEL_BUDGET = 400      # total CellIsOrbit evaluations per CertifiedG call


class Budget(Exception):
    pass


class Ctr:
    def __init__(self, cap):
        self.n = 0
        self.cap = cap

    def tick(self):
        self.n += 1
        if self.n > self.cap:
            raise Budget()


def cell_is_orbit(n, adj, adjl, col, ctr):
    """`Consume.CellIsOrbit deepenSupply adj col` — deepen's verified gens connect the whole
    branch cell.  Vacuously true when there is no non-singleton cell."""
    ctr.tick()
    cid, C = target_cell(n, col)
    if cid is None:
        return True
    orb = orbits_all(n, deepen_gens(n, adj, adjl, col, C))
    return len({orb[v] for v in C}) == 1


def cert_path(n, adj, adjl, col, ctr):
    """`DeepenGuard.CertPath deepenSupply adj n cur` — iterative, short-circuiting."""
    for _ in range(n + 1):
        cid, C = target_cell(n, col)
        if cid is None:
            return True
        if not cell_is_orbit(n, adj, adjl, col, ctr):
            return False
        col = indiv(n, adjl, col, min(C))
    return True


def certifiedG(n, adj, adjl, col):
    """`DeepenGuard.CertifiedG deepenSupply adj χ`.  Returns True/False, or None if budgeted out."""
    cid, C = target_cell(n, col)
    if cid is None:
        return True
    ctr = Ctr(LEVEL_BUDGET)
    try:
        for r in sorted(C):
            if not cert_path(n, adj, adjl, indiv(n, adjl, col, r), ctr):
                return False
        return True
    except Budget:
        return None


def profile(n, adj, adjl, col):
    cid, C = target_cell(n, col)
    if cid is None:
        return None, None
    orb = orbits_all(n, deepen_gens(n, adj, adjl, col, C))
    cells = defaultdict(list)
    for v in range(n):
        cells[col[v]].append(v)
    prof = {}
    for c, mem in cells.items():
        if len(mem) >= 2:
            b = defaultdict(int)
            for v in mem:
                b[orb[v]] += 1
            prof[c] = tuple(sorted(b.values()))
    return prof, cid


def reached(n, adjl, col0):
    out = [(0, col0)]
    frontier = [(0, col0)]
    seen = {tuple(col0)}
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
    rng = random.Random(abs(hash(name)) & 0xffff)
    sig = []
    for _ in range(NREL):
        s = list(range(n))
        rng.shuffle(s)
        sig.append((s, ) + (relabel(n, adj, s), ))
    rel = [(s, a, adjlist(n, a)) for s, a in sig]

    fails = []          # (depth, colour, profA, profB, col)
    for depth, col in reached(n, adjl, col0):
        prof, cid = profile(n, adj, adjl, col)
        if prof is None:
            continue
        for s, adj2, adjl2 in rel:
            col2 = [0] * n
            for v in range(n):
                col2[s[v]] = col[v]
            prof2, cid2 = profile(n, adj2, adjl2, col2)
            if prof2 is None:
                continue
            for c in set(prof) | set(prof2):
                if c != cid and prof.get(c) != prof2.get(c):
                    fails.append((depth, c, prof.get(c), prof2.get(c), col, adj2, adjl2, col2))
                    break
            if fails:
                break
        if fails:
            break

    if not fails:
        print(f"  {name:22s} n={n:<4d} no off-branch falsifier at depth ≤ {DEPTH}")
        return

    depth, c, pa, pb, col, adj2, adjl2, col2 = fails[0]
    gA = certifiedG(n, adj, adjl, col)
    gB = certifiedG(n, adj2, adjl2, col2)
    sA = {True: 'OPEN', False: 'SHUT', None: 'UNKNOWN(budget)'}[gA]
    sB = {True: 'OPEN', False: 'SHUT', None: 'UNKNOWN(budget)'}[gB]
    verdict = ''
    if gA is False and gB is False:
        verdict = '  ⟹ GUARD SHUTS BOTH SIDES — the falsifier does NOT bite deepenSupplyCert'
    elif gA is True or gB is True:
        verdict = '  ⟹ ⛔ GUARD OPEN — REAL falsifier for the GUARDED supply too'
    else:
        verdict = '  ⟹ inconclusive (budget)'
    print(f"  {name:22s} n={n:<4d} depth={depth} colour={c}  {pa} vs {pb}   "
          f"guard: {sA} / {sB}{verdict}")


def main():
    print("At the off-branch falsifier found by probe_offbranch2, is the GUARD open?")
    print("CertifiedG is decidable from deepen's own output — no orbit oracle is consulted.")
    print("tinhofer_iff_certifiedG makes the guard's verdict intrinsic, so both sides must agree.")
    print()
    for m in (8, 10):
        base = cubic(m, seed=m)
        for tw in (False, True):
            run(f"CFI cubic m={m} {'tw' if tw else 'pl'}", *build_cfi_base(base, m, twist=tw))
    run("MIXED multipede", *build_mp(MIXED))
    run("circ(5) multipede", *build_mp(circ(5)))


if __name__ == '__main__':
    main()
