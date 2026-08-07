#!/usr/bin/env python3
"""
probe_offbranch5.py — THE PROPOSED OBJECT: PER-CELL LIST **+** PER-CELL GUARD   (2026-08-07)

============================================================================================
WHERE THIS SITS
============================================================================================
probe_offbranch3 : node-global list (today) is REFUTED — CFI m=8/10, depth 1, guard OPEN both
                   sides, off-branch count (1,1) vs (2,).
probe_offbranch4 : per-cell list REPAIRS all four CFI rows (B fires 129/131, 198/209) but is
                   NOT sufficient alone — `rand multipede V=6 W=5` still varies (2 vs 4) with
                   B firing 0/8.

That residual failure is exactly what a guard is for: at that cell the per-cell harvest is not
guaranteed to find the relation, so the guard must SHUT and the supply emit nothing.

============================================================================================
THE OBJECT MEASURED HERE
============================================================================================
Per cell `c`, the guarded per-cell narrowing count:

    guard_c  :=  ∀ r ∈ cellList χ c,  CertPath (per-cell deepen) adj n (step adj χ r)
                 where each level requires `CellIsOrbit` of the level's own chosen cell,
                 harvested from that cell's OWN anchors.
    count_c  :=  1          if guard_c            (the cell resolves)
                 |cell c|   otherwise             (supply emits [], nothing collapses)

`count_c` is what `selColour` reads.  Note the STRUCTURAL point this probe checks empirically:
a shut guard gives `|cell c|` on BOTH sides automatically (cells correspond under transport),
so the ONLY thing that has to be invariant is the guard's VERDICT — the per-cell analogue of
`DeepenGuardComplete.tinhofer_iff_certifiedG`.

Reported: GUARD-INV (verdict invariant at every node and cell?), COUNT-INV, and open-rate.
⚠ open-rate 0 would be a vacuous pass and is flagged.

    cd /workspace/scratchpad && python3 -u probe_offbranch5.py > probe_offbranch5.out 2>&1
"""
import random
import sys
from collections import defaultdict

sys.setrecursionlimit(10000)
sys.path.insert(0, '/workspace/scratchpad')

from probe_dualdeepen import circ, FANO, MIXED, rand_incidence, build_mp, build_cfi_base, cubic
from probe_polyloop import adjlist, refine, indiv, target_cell
from probe_selfsep import g8
from probe_offbranch import deepen_gens, orbits_all, relabel, subdivision, petersen, complete

NREL = 3
DEPTH = 1
BRANCH = 2
BUDGET = 300
SKIPS = []


class Budget(Exception):
    pass


class Ctr:
    def __init__(self, cap):
        self.n, self.cap = 0, cap

    def tick(self):
        self.n += 1
        if self.n > self.cap:
            raise Budget()


def cells_of(n, col):
    d = defaultdict(list)
    for v in range(n):
        d[col[v]].append(v)
    return {c: m for c, m in d.items() if len(m) >= 2}


def cell_connected(n, adj, adjl, col, mem, ctr):
    """`CellIsOrbit` for the PER-CELL harvest: gens anchored at `mem` connect all of `mem`."""
    ctr.tick()
    orb = orbits_all(n, deepen_gens(n, adj, adjl, col, mem))
    return len({orb[v] for v in mem}) == 1


def cert_path_percell(n, adj, adjl, col, ctr):
    """`CertPath` with every level's test taken PER-CELL: the level's chosen cell must be
    connected by generators anchored in that same cell."""
    for _ in range(n + 1):
        cid, C = target_cell(n, col)
        if cid is None:
            return True
        if not cell_connected(n, adj, adjl, col, C, ctr):
            return False
        col = indiv(n, adjl, col, min(C))
    return True


def guard_cell(n, adj, adjl, col, mem):
    """Per-cell guard verdict at the cell `mem`.  None = budgeted out (never counted as pass)."""
    ctr = Ctr(BUDGET)
    try:
        if not cell_connected(n, adj, adjl, col, mem, ctr):
            return False
        for r in sorted(mem):
            if not cert_path_percell(n, adj, adjl, indiv(n, adjl, col, r), ctr):
                return False
        return True
    except Budget:
        return None


def verdicts(n, adj, adjl, col):
    cid, C = target_cell(n, col)
    if cid is None:
        return None
    out = {}
    for c, mem in cells_of(n, col).items():
        g = guard_cell(n, adj, adjl, col, mem)
        out[c] = (g, len(mem))
    return out


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
        return
    rng = random.Random(abs(hash(name)) & 0xffff)
    rel = []
    for _ in range(NREL):
        s = list(range(n))
        rng.shuffle(s)
        a2 = relabel(n, adj, s)
        rel.append((s, a2, adjlist(n, a2)))

    gok = cok = True
    gfail = None
    opened = total = unk = 0

    for depth, col in reached(n, adjl, col0):
        V = verdicts(n, adj, adjl, col)
        if V is None:
            continue
        for c, (g, sz) in V.items():
            total += 1
            if g is None:
                unk += 1
            elif g:
                opened += 1
        for s, adj2, adjl2 in rel:
            col2 = [0] * n
            for v in range(n):
                col2[s[v]] = col[v]
            V2 = verdicts(n, adj2, adjl2, col2)
            if V2 is None:
                SKIPS.append((name, 'transported node lost its target cell'))
                continue
            for c in set(V) | set(V2):
                g1, s1 = V.get(c, (None, 0))
                g2, s2 = V2.get(c, (None, 0))
                if g1 is None or g2 is None:
                    continue
                if g1 != g2:
                    if gok:
                        gfail = (depth, c, g1, g2)
                    gok = False
                n1 = 1 if g1 else s1
                n2 = 1 if g2 else s2
                if n1 != n2:
                    cok = False

    flag = ''
    if gok and opened == 0:
        flag = '   (guard never opens — VACUOUS pass)'
    elif gok and cok:
        flag = '   <<< PER-CELL LIST + PER-CELL GUARD HOLDS'
    if not gok:
        flag = '   <<<< GUARD VERDICT VARIES'
    print(f"  {name:24s} n={n:<4d} cells={total:<4d} open={opened} unknown={unk}  "
          f"GUARD-INV={'Y' if gok else 'N'}  COUNT-INV={'Y' if cok else 'N'}{flag}")
    if gfail:
        d, c, a, b = gfail
        print(f"        guard first fail: depth {d} colour {c}: {a} vs {b}")


def main():
    print("The PROPOSED object: per-cell generator list + per-cell guard.")
    print("A shut guard gives |cell| on both sides automatically, so only the VERDICT must be")
    print("invariant — the per-cell analogue of tinhofer_iff_certifiedG.  Checked here.")
    print(f"BFS depth {DEPTH}, ≤{BRANCH} members/node, {NREL} relabellings, budget {BUDGET}.")
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
