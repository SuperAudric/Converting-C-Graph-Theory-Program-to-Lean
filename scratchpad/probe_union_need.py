#!/usr/bin/env python3
"""
probe_union_need.py — IS A UNION-OVER-ANCHORS ARGUMENT ACTUALLY NEEDED?   (2026-08-04)

============================================================================================
WHY THIS QUESTION
============================================================================================
`ChainDescent/DeepenComplete.lean` now proves two things about `Deepen.OrbitComplete`
("deepen's verified generators realise the whole IsColAut-orbit relation on the branch cell"):

  §3  `orbitComplete_of_tinhofer`          — every anchor GOOD  =>  OrbitComplete
  §5  `orbitComplete_of_good_or_trivial`   — every anchor GOOD **or Aut-RIGID** => OrbitComplete
  §5.1 `goodAnchor_transport`              — goodness is an ORBIT property

GOOD = `GoodAnchor` = every level of that anchor's greedy deepening individualizes a cell that is a
single true Aut-orbit (probe_certkey calls this "certified-below").

§5 already explains the measured rows that §3 could not: `rand multipede V=12 W=8` has **0/4** good
anchors yet is `exact` — because all four of its orbits are SINGLETONS, where OrbitComplete is `refl`.

So the only case left uncovered is:

    >>> a NON-SINGLETON true orbit, ALL of whose anchors are BAD, on which the
    >>> all-anchors harvest is nevertheless EXACT.

On such an orbit the connecting generators must come from OTHER anchors — the genuine
union-over-anchors phenomenon, and the only thing a "union argument" would have to prove.
If no witness realises it, there is nothing further to prove: every measured `exact` verdict is
already covered by §3 + §5, and the union argument is a phantom.

============================================================================================
WHAT IS REPORTED, PER WITNESS
============================================================================================
  |C|, #true-orbits, #singleton-orbits, #good anchors
  orbit-uniformity  — every true orbit is uniformly good or uniformly bad?  (an empirical CHECK on
                      `goodAnchor_transport`; a mixed orbit would REFUTE the Lean theorem)
  covered-by-§5     — is every anchor good-or-rigid?  (then §3/§5 already explain exactness)
  BAD-BIG orbits    — non-singleton orbits that are entirely bad  <<< the discriminator
  harvest-exact     — all-anchors harvest partition == true orbit partition

A row with BAD-BIG > 0 and harvest-exact=Y is the witness a union argument would be needed for.

============================================================================================
SOUNDNESS
============================================================================================
* True orbits from `Ctx`/`canon` (min-over-cell exhaustive), never `probe_orbit_oracle` (recorded
  PROVEN BROKEN — it errs by merging).  Cross-checked: the cert-classes of explored vertices must
  agree with the generator orbits, else the partition over-splits and every verdict is meaningless.
* GOOD is decided by `probe_certkey.descend_cert`, which recomputes the TRUE orbit partition at every
  level of the greedy descent — expensive, and the reason this sweep is small.
* `refine`/`indiv`/`greedy_deepen`/`replay`/`twist` are `probe_polyloop`'s ports of the landed Lean
  objects.  Fidelity to Lean is assumed there, not re-verified here.
* Every skip is counted and printed; nothing is dropped silently.

    cd /workspace/scratchpad && python3 -u probe_union_need.py > probe_union_need.out 2>&1
"""
import sys
from collections import defaultdict

sys.setrecursionlimit(10000)
sys.path.insert(0, '/workspace/scratchpad')

from probe_dualdeepen import (circ, FANO, MIXED, rand_incidence, build_mp,
                              build_cfi_base, cubic, Ctx, canon)
from probe_polyloop import (adjlist, refine, indiv, target_cell,
                            greedy_deepen, replay, twist)
from probe_certkey import descend_cert
from probe_selfsep import true_orbit_partition, blocks_of, g8

SKIPS = []


def harvest_partition_from(n, adj, adjl, chi, C, anchors):
    """`deepenGens` restricted to a chosen ANCHOR SUBSET (probe_polyloop's takes a count)."""
    gens = []
    firsts = {r: indiv(n, adjl, chi, r) for r in C}
    for r1 in anchors:
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


def run(name, n, adj):
    adjl = adjlist(n, adj)
    col = refine(n, adjl, [0] * n)
    cid, C = target_cell(n, col)
    if cid is None:
        SKIPS.append((name, 'root discrete'))
        print(f"  {name:30s} n={n:<5d} SKIPPED — root discrete")
        return
    orb, status = true_orbit_partition(n, adj, col, C)
    if orb is None or status != 'ok':
        SKIPS.append((name, status))
        print(f"  {name:30s} n={n:<5d} SKIPPED — {status}")
        return

    blocks = defaultdict(set)
    for v in C:
        blocks[orb[v]].add(v)
    good = {u for u in C if descend_cert(n, adj, adjl, col, u, check_orbits=True)[1]}

    # empirical check on `goodAnchor_transport`: no orbit may be MIXED
    mixed = [b for b in blocks.values() if (b & good) and (b - good)]
    singl = [b for b in blocks.values() if len(b) == 1]
    badbig = [b for b in blocks.values() if len(b) > 1 and not (b & good)]
    covered5 = all((u in good) or len(blocks[orb[u]]) == 1 for u in C)

    hb = blocks_of(harvest_partition_from(n, adj, adjl, col, C, C), C)
    tb = blocks_of(orb, C)
    exact = (hb == tb)

    flag = ''
    if mixed:
        flag += '   <<<< MIXED ORBIT — REFUTES goodAnchor_transport'
    if badbig and exact:
        flag += '   <<<< UNION ARGUMENT NEEDED (bad non-singleton orbit, still exact)'
    print(f"  {name:30s} n={n:<5d} |C|={len(C):<4d} orbits={len(tb):<3d} "
          f"singleton={len(singl):<3d} good={len(good)}/{len(C):<4d} "
          f"orbit-uniform={'Y' if not mixed else 'N'}  covered-by-§5={'Y' if covered5 else 'N'}  "
          f"BAD-BIG={len(badbig):<3d} harvest-exact={'Y' if exact else 'N'}{flag}")


def main():
    print("Is a UNION-OVER-ANCHORS argument needed, or do DeepenComplete §3+§5 already cover it?")
    print("BAD-BIG = non-singleton true orbits that are ENTIRELY bad anchors (the discriminator)")
    print("covered-by-§5 = every anchor is GOOD or Aut-RIGID  =>  orbitComplete_of_good_or_trivial")
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
