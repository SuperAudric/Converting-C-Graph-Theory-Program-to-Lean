#!/usr/bin/env python3
"""
probe_selfsep.py — IS THE ALL-ANCHOR REPAIR EXPLAINED BY "MIXED ORBITS THAT IDENTIFY
EACH OTHER"?   (user hypothesis, 2026-08-04)

============================================================================================
WHAT IS ALREADY MEASURED (do not re-run these; read them first)
============================================================================================
`probe_verdict_invariance.py`  — the ALL-ANCHOR deepen harvest partition of the branch cell
    equals the TRUE Aut-orbit partition, and transports, on 17/17 structured witnesses
    (multipedes, CFI over cubic bases, rigid multipedes).  So `Deepen.OrbitComplete`
    (`ChainDescent/DeepenComplete.lean`) is measured TRUE well beyond `Tinhofer`.
`probe_certkey.py`             — "certified-below => the greedy cert is iso-invariant" has
    0 counterexamples; but UNCERTIFIED reps do produce non-invariant certs (rand multipede
    V=12 W=8: 2; CFI cubic m=10: 4, where the cert over-splits 7 classes vs 6 orbits).

So the per-anchor object (the cert) is NOT invariant at uncertified anchors, while the
union-over-anchors RELATION is exact anyway.  **What repairs it is unexplained.**

============================================================================================
THE HYPOTHESIS UNDER TEST
============================================================================================
"These are mixed orbits that identify each other.  Two vertices fully connected to the same
copies of C3+C6, versus two connected to C4+C5: 1-WL is blind, so they share a cell — but
whichever of them you choose, individualizing it REVEALS and SEPARATES its own orbit-mates
out."

If true, replay from a NON-mate is structurally unable to follow the anchor's id sequence
(so it yields no candidate and no wrong generator), while replay from a mate can.  That
would explain exactness without any per-level Schurianity, and — being one refinement per
cell member — it is a POLY, DETECTABLE condition, i.e. a candidate guard strictly weaker
than `Tinhofer`.

Two readings are measured, at the root branch cell `C`, for every `x` in `C`:

  M1 (the hypothesis as stated) — individualizing `x` separates `x`'s OWN orbit from the rest:
        for all y in orb(x) & C, y != x, and all z in C \\ orb(x):   child[y] != child[z]
  M2 (the stronger reading)     — individualizing `x` exposes the WHOLE orbit structure of C:
        for all y,z in C:   child[y] == child[z]  =>  y,z in the same orbit

`child = refine(indiv(col, x))` — one `Deepen.step`.

Correlation reported: does M1/M2 hold exactly where the harvest is exact?  A witness where
the harvest is exact but M1 fails at some `x` REFUTES the mechanism as the explanation.

============================================================================================
SOUNDNESS
============================================================================================
* True orbits come from `Ctx`/`canon` (min-over-cell exhaustive canonical form, cert-classes
  on a cell ARE its orbits) — the same route `probe_verdict_invariance.true_partition` uses.
  NEVER from `probe_orbit_oracle` (recorded PROVEN BROKEN — it errs by merging).
* `canon` runs under `leafcap`; a witness whose search is capped returns None and is COUNTED
  AND PRINTED as a skip, never silently dropped.
* `refine`/`indiv`/`greedy_deepen`/`replay`/`twist`/`deepen_harvest` are `probe_polyloop`'s
  ports of the landed Lean objects (its header carries the correspondence table).  Fidelity
  to Lean is assumed there, not re-verified here.

    cd /workspace/scratchpad && python3 -u probe_selfsep.py > probe_selfsep.out 2>&1
"""
import sys
from collections import defaultdict

sys.setrecursionlimit(10000)
sys.path.insert(0, '/workspace/scratchpad')

from probe_dualdeepen import (circ, FANO, MIXED, rand_incidence, build_mp,
                              build_cfi_base, cubic, Ctx, canon)
from probe_polyloop import (adjlist, refine, indiv, target_cell,
                            deepen_harvest)

SKIPS = []


# ---------------------------------------------------------------- exact orbits (not the oracle)
def true_orbit_partition(n, adj, col, C):
    """TRUE Aut(adj,col)-orbit partition of C as {v: block_id}, by the same reconstruction
    `probe_verdict_invariance.true_partition` uses: union-find over the generators the
    min-over-cell search discovered.  `percert` covers only EXPLORED vertices (the search
    prunes by discovered automorphisms), so the partition cannot be read off it directly.

    Returns (partition, status).  `partition` is None when the search blew its leafcap or
    the cell moved.  ⚠ SOUNDNESS CROSS-CHECK the recorded instrument does not do: the
    cert-classes of the explored vertices must agree with the generator orbits.  If they
    disagree the search recorded too few generators and the partition OVER-SPLITS, which
    would make an `exact=Y` verdict meaningless (both sides over-splitting alike)."""
    ctx = Ctx(n, adj, prune=True, leafcap=200000)
    canon(ctx, list(col), [], root=True)
    if ctx.root is None:
        return None, 'search returned no root'
    if getattr(ctx, 'blown', False):
        return None, 'leafcap blown'
    Croot, percert, expl = ctx.root
    if sorted(Croot) != sorted(C):
        return None, 'branch cell moved'
    par = {v: v for v in Croot}

    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x

    for g, _p in ctx.gens:
        for v in Croot:
            if g[v] in par:
                a, b = f(v), f(g[v])
                if a != b:
                    par[a] = b
    ids = {}
    part = {v: ids.setdefault(f(v), len(ids)) for v in Croot}
    agree = all(part[u] == part[v]
                for u in percert for v in percert if percert[u] == percert[v])
    return part, ('ok' if agree else 'CERT/GEN DISAGREE — partition may over-split')


def harvest_partition(n, adj, adjl, col, C):
    """Orbit partition of C under the ALL-ANCHOR deepen harvest (today's `deepenGens`), as
    {v: block_id}.  Same construction as `probe_verdict_invariance.harvest_partition`."""
    gens = deepen_harvest(n, adj, adjl, col, C, anchors=len(C))
    par = {v: v for v in C}

    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x

    for g in gens:
        for v in C:
            if g[v] in par:
                a, b = f(v), f(g[v])
                if a != b:
                    par[a] = b
    ids = {}
    return {v: ids.setdefault(f(v), len(ids)) for v in C}


def blocks_of(part, C):
    d = defaultdict(set)
    for v in C:
        d[part[v]].add(v)
    return sorted((tuple(sorted(b)) for b in d.values()))


# ---------------------------------------------------------------- the mechanism tests
def mechanism(n, adjl, col, C, orb):
    """Returns (m1_ok, m2_ok, |C|, nontrivial) over every x in C.  `nontrivial` counts the x
    whose orbit has another member IN the cell — M1 is VACUOUS at an x whose orbit is a
    singleton (there is nothing to separate), so a cell of all-singleton orbits passes M1
    for free and must not be counted as evidence."""
    m1 = m2 = nontriv = 0
    for x in C:
        child = indiv(n, adjl, col, x)
        mates = {y for y in C if y != x and orb[y] == orb[x]}
        others = {z for z in C if orb[z] != orb[x]}
        if mates:
            nontriv += 1
        if all(child[y] != child[z] for y in mates for z in others):
            m1 += 1
        ok2 = True
        for y in C:
            for z in C:
                if child[y] == child[z] and orb[y] != orb[z]:
                    ok2 = False
                    break
            if not ok2:
                break
        if ok2:
            m2 += 1
    return m1, m2, len(C), nontriv


def run(name, n, adj):
    adjl = adjlist(n, adj)
    col = refine(n, adjl, [0] * n)
    cid, C = target_cell(n, col)
    if cid is None:
        print(f"  {name:30s} n={n:<5d} root DISCRETE — no branch cell, skipped")
        SKIPS.append((name, 'root discrete'))
        return
    orb, status = true_orbit_partition(n, adj, col, C)
    if orb is None:
        print(f"  {name:30s} n={n:<5d} |C|={len(C):<4d} ⚠ SKIPPED — {status}")
        SKIPS.append((name, status))
        return
    if status != 'ok':
        print(f"  {name:30s} n={n:<5d} |C|={len(C):<4d} ⚠⚠ {status}")
        SKIPS.append((name, status))
        return
    tb = blocks_of(orb, C)
    hb = blocks_of(harvest_partition(n, adj, adjl, col, C), C)
    exact = (tb == hb)
    if len(tb) == 1:
        print(f"  {name:30s} n={n:<5d} |C|={len(C):<4d} orbits=1  (single-orbit cell — "
              f"mechanism vacuous)   harvest-exact={'Y' if exact else 'N'}")
        return
    m1, m2, tot, nontriv = mechanism(n, adjl, col, C, orb)
    flag = ''
    if exact and m1 < tot:
        flag = '   <<< HARVEST EXACT BUT M1 FAILS — mechanism REFUTED as the explanation'
    print(f"  {name:30s} n={n:<5d} |C|={len(C):<4d} orbits={len(tb):<3d} "
          f"harvest-exact={'Y' if exact else 'N'}  M1={m1}/{tot}  M2={m2}/{tot}  "
          f"non-vacuous-x={nontriv}/{tot}{flag}")


# ---------------------------------------------------------------- witnesses
def g8():
    e = [(0,1),(1,2),(2,0),(3,4),(4,5),(5,3),(0,6),(3,6),(6,7),(1,7),(4,7),(2,5)]
    a = [[0]*8 for _ in range(8)]
    for i, j in e:
        a[i][j] = a[j][i] = 1
    return 8, a


def main():
    print(__doc__.split('============')[0].strip())
    print()
    print("M1 = individualizing x separates x's OWN orbit from the rest of the cell")
    print("M2 = individualizing x exposes the WHOLE orbit structure of the cell")
    print("(x/tot = how many of the cell's members satisfy it)")
    print()

    print("### the recorded rich partially-firing witness (absent from both earlier sweeps)")
    n, a = g8()
    run("G8 cubic non-VT", n, a)
    print()

    print("### rigid multipedes — multi-orbit root cells")
    for V, W, seed in [(6, 5, 1), (8, 6, 2), (10, 7, 3), (12, 8, 4)]:
        A = rand_incidence(V, W, 3, seed)
        n, a = build_mp(A)
        run(f"rand multipede V={V} W={W}", n, a)
    print()

    print("### mixed / gauge")
    for label, A in [("MIXED multipede", MIXED), ("circ(5) multipede", circ(5)),
                     ("mp7 Fano multipede", FANO)]:
        n, a = build_mp(A)
        run(label, n, a)
    print()

    print("### CFI over random cubic bases")
    for m in (8, 10, 12):
        base = cubic(m, seed=m)
        for tw in (False, True):
            n, a = build_cfi_base(base, m, twist=tw)
            run(f"CFI cubic m={m} {'tw' if tw else 'pl'}", n, a)
    print()

    if SKIPS:
        print(f">>> SKIPPED {len(SKIPS)} witness(es), none silently:")
        for nm, why in SKIPS:
            print(f"      {nm}: {why}")
    else:
        print(">>> no witness skipped")


if __name__ == '__main__':
    main()
