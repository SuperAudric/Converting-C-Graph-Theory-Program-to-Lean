#!/usr/bin/env python3
"""
probe_w2_asymbase.py — W2 item 3b (2026-08-10): CFI over an ASYMMETRIC base.

============================================================================================
WHY
============================================================================================
`probe_w2_linear.py` (item 3a) measured four CFI witnesses and concluded that no `Aut`-block
is a single gauge-orbit, hence "even a perfect key leaves >= 2 reps".  ⚠ ALL FOUR of its bases
are SYMMETRIC — the probe prints |Aut(base)| = 12, 12, 24, 12.  The bound

      surviving reps  >=  |Aut-block| / |gauge-orbit|

is only >= 2 because Aut(CFI(G)) is strictly bigger than the gauge, and the excess is exactly
the lifted base automorphisms.  Over a base with Aut(G) = 1 there is no excess:
Aut(CFI(G)) IS the gauge, every Aut-block IS a single gauge-orbit, and the bound vanishes.

This probe measures that, and separates the two failure modes the item-3a header already names:

  (A) KEY failure   — keepMin cannot be cut down to ONE Aut-block (several blocks per cell);
  (B) SUPPLY failure — the harvest is not transitive on the block it does isolate.

★ The third regime is the interesting one for the LAYER theorem.  Three cases:

  1. base symmetric                  -> Aut-block ⊋ gauge-orbit  -> (B) is unfixable: no key helps.
  2. base asymmetric, 1-WL COARSE    -> Aut-block  = gauge-orbit, but MANY blocks per cell
                                        -> (A): open, and it is exactly "separate the base edges".
  3. base asymmetric, 1-WL DISCRETE  -> each CFI cell is ONE gauge-orbit -> ✅ FIRES TODAY,
                                        with `kernelSupply` (which IS inside `recordSupplyFast`).

Case 3 is the predicted shape of the layer theorem: *solve the CFI part, hand back the base.*

    cd /workspace/scratchpad && python3 -u probe_w2_asymbase.py > probe_w2_asymbase.out 2>&1
"""
import random
import sys
from collections import defaultdict
from itertools import product

sys.setrecursionlimit(10000)
sys.path.insert(0, '/workspace/scratchpad')

from probe_dualdeepen import build_cfi_base
from probe_polyloop import adjlist, refine, target_cell
from probe_offbranch5 import cells_of
from probe_w2_linear import (cfi_layout, cycle_space, gauge_perm, is_aut, orbits_of,
                             aut_gens)


# ---------------------------------------------------------------- exact Aut(base), any m

def base_auts(m, edges):
    """Exact |Aut| of the base by backtracking with degree + partial-adjacency pruning.

    Small m, strong pruning — exact, no heuristic.  Returns the list of automorphisms."""
    es = set(edges)
    adjset = [set() for _ in range(m)]
    for a, b in edges:
        adjset[a].add(b)
        adjset[b].add(a)
    deg = [len(adjset[i]) for i in range(m)]
    order = sorted(range(m), key=lambda v: -deg[v])
    out = []
    img = [-1] * m
    used = [False] * m

    def rec(k):
        if k == m:
            out.append(tuple(img))
            return
        v = order[k]
        for w in range(m):
            if used[w] or deg[w] != deg[v]:
                continue
            ok = True
            for j in range(k):
                u = order[j]
                if ((u in adjset[v]) != (img[u] in adjset[w])):
                    ok = False
                    break
            if ok:
                img[v] = w
                used[w] = True
                rec(k + 1)
                used[w] = False
                img[v] = -1

    rec(0)
    return out


def wl_classes(m, edges):
    """1-WL colour classes of the base (so we can say whether the base is 1-WL discrete)."""
    adjl = [[] for _ in range(m)]
    for a, b in edges:
        adjl[a].append(b)
        adjl[b].append(a)
    col = [0] * m
    while True:
        sig = [(col[v], tuple(sorted(col[u] for u in adjl[v]))) for v in range(m)]
        ranks = {s: i for i, s in enumerate(sorted(set(sig)))}
        new = [ranks[s] for s in sig]
        if new == col:
            return col
        col = new


def find_asymmetric_base(m, mindeg, seed, want_regular=None, tries=200000):
    """Random search for a base on m vertices, min degree >= mindeg, with |Aut| = 1."""
    rng = random.Random(seed)
    allp = [(a, b) for a in range(m) for b in range(a + 1, m)]
    for _ in range(tries):
        if want_regular:
            edges = random_regular(m, want_regular, rng)
            if edges is None:
                continue
        else:
            p = rng.uniform(0.35, 0.6)
            edges = [e for e in allp if rng.random() < p]
            d = [0] * m
            for a, b in edges:
                d[a] += 1
                d[b] += 1
            if min(d) < mindeg:
                continue
        if not connected(m, edges):
            continue
        if len(base_auts(m, edges)) == 1:
            return sorted(edges)
    return None


def random_regular(m, k, rng):
    """A crude random k-regular graph via pairing; returns None on failure."""
    if (m * k) % 2:
        return None
    stubs = [v for v in range(m) for _ in range(k)]
    rng.shuffle(stubs)
    edges = set()
    for i in range(0, len(stubs), 2):
        a, b = stubs[i], stubs[i + 1]
        if a == b or (min(a, b), max(a, b)) in edges:
            return None
        edges.add((min(a, b), max(a, b)))
    return sorted(edges)


def connected(m, edges):
    adjl = defaultdict(list)
    for a, b in edges:
        adjl[a].append(b)
        adjl[b].append(a)
    seen = {0}
    st = [0]
    while st:
        v = st.pop()
        for u in adjl[v]:
            if u not in seen:
                seen.add(u)
                st.append(u)
    return len(seen) == m


FRUCHT = [(0, 1), (0, 2), (0, 11), (1, 3), (1, 6), (2, 5), (2, 10), (3, 4), (3, 6),
          (4, 8), (4, 11), (5, 9), (5, 10), (6, 7), (7, 8), (7, 9), (8, 9), (10, 11)]


# ---------------------------------------------------------------- report

def run(name, base_edges, m, twist=False):
    base_edges = [(min(a, b), max(a, b)) for (a, b) in base_edges]
    n, adj = build_cfi_base(base_edges, m, twist=twist)
    wire, gadget, _ = cfi_layout(base_edges, m)
    K, beta = cycle_space(base_edges, m)

    gperms = []
    for F in K:
        p = gauge_perm(F, base_edges, m, wire, gadget, n)
        assert is_aut(n, adj, p), "gauge element is not an automorphism — encoding mismatch"
        gperms.append(p)

    adjl = adjlist(n, adj)
    col = refine(n, adjl, [0] * n)
    tid, _ = target_cell(n, col)

    gauge_cls = orbits_of(n, gperms)
    aut_cls = orbits_of(n, aut_gens(n, adj, col))

    bauts = base_auts(m, base_edges)
    bwl = wl_classes(m, base_edges)
    bdisc = len(set(bwl)) == m
    degs = defaultdict(int)
    for a, b in base_edges:
        degs[a] += 1
        degs[b] += 1

    print(f"  {name}  n={n}  m={m}  |E|={len(base_edges)}  beta={beta}  |gauge|={len(K)}")
    print(f"     base: |Aut(base)|={len(bauts)}  degrees={sorted(degs.values(), reverse=True)}  "
          f"1-WL classes={len(set(bwl))}/{m} ⟹ base is {'DISCRETE' if bdisc else 'COARSE'} under 1-WL")

    ncell = fires = keylim = blocked = 0
    for c, mem in sorted(cells_of(n, col).items()):
        if len(mem) < 2:
            continue
        ncell += 1
        blocks = defaultdict(set)
        for v in mem:
            blocks[aut_cls[v]].add(v)
        gorb = defaultdict(set)
        for v in mem:
            gorb[gauge_cls[v]].add(v)
        single = [B for B in blocks.values() if len({gauge_cls[v] for v in B}) == 1]
        kind = "wires" if all(v < 2 * len(base_edges) for v in mem) else "gadgets"
        tag = " (TARGET)" if c == tid else ""
        line = (f"     cell {c}{tag} [{kind}] |cell|={len(mem)}  "
                f"gauge-orbits={len(gorb)}  Aut-blocks={len(blocks)}")
        if not single:
            blocked += 1
            print(line + "  ⟹ ⛔ (B) NO block is one gauge-orbit — no key can fire it")
        elif len(blocks) == 1:
            fires += 1
            print(line + "  ⟹ ✅ THE WHOLE CELL IS ONE gauge-orbit ⟹ `CellOrbitAt` holds "
                         "for kernelSupply ⟹ FIRES with the shipped supply, no key work")
        else:
            keylim += 1
            print(line + f"  ⟹ ◐ (A) every block IS one gauge-orbit, but there are {len(blocks)} "
                         f"of them ⟹ firing is a KEY question (separate the blocks), not a supply one")
    print(f"     ⟹ non-singleton cells: {ncell}   ✅ fire-today {fires}   "
          f"◐ key-limited {keylim}   ⛔ blocked {blocked}")
    print()
    return fires, keylim, blocked


def walk(name, base_edges, m, depth=3, twist=False):
    """⚠ ROOT-ONLY IS NOT A PASS (standing steer).  Descend: individualize the least vertex of
    the target cell, refine, and re-measure EVERY non-singleton cell at each reached node.

    At a reached node the relevant group is the COLOUR-automorphisms, so the gauge is filtered to
    the elements that preserve χ before its orbits are taken."""
    base_edges = [(min(a, b), max(a, b)) for (a, b) in base_edges]
    n, adj = build_cfi_base(base_edges, m, twist=twist)
    wire, gadget, _ = cfi_layout(base_edges, m)
    K, _ = cycle_space(base_edges, m)
    gperms = []
    for F in K:
        p = gauge_perm(F, base_edges, m, wire, gadget, n)
        assert is_aut(n, adj, p)
        gperms.append(p)
    adjl = adjlist(n, adj)
    col = refine(n, adjl, [0] * n)

    print(f"  {name} — descent walk, {depth} levels past the root")
    for lvl in range(depth + 1):
        cells = {c: mem for c, mem in cells_of(n, col).items() if len(mem) >= 2}
        if not cells:
            print(f"     level {lvl}: DISCRETE — descent complete")
            break
        # only the gauge elements that preserve the current colouring act at this node
        gk = [p for p in gperms if all(col[p[v]] == col[v] for v in range(n))]
        gauge_cls = orbits_of(n, gk)
        aut_cls = orbits_of(n, aut_gens(n, adj, col))
        fires = keylim = blocked = 0
        worst = None
        for c, mem in sorted(cells.items()):
            blocks = defaultdict(set)
            for v in mem:
                blocks[aut_cls[v]].add(v)
            single = [B for B in blocks.values() if len({gauge_cls[v] for v in B}) == 1]
            if not single:
                blocked += 1
                worst = worst or (c, len(mem), len(blocks))
            elif len(blocks) == 1:
                fires += 1
            else:
                keylim += 1
        flag = ("✅ every cell fires on the gauge" if fires == len(cells)
                else f"◐ {keylim} key-limited / ⛔ {blocked} blocked")
        print(f"     level {lvl}: ns-cells={len(cells)}  |gauge fixing χ|={len(gk)}  "
              f"✅{fires} ◐{keylim} ⛔{blocked}  ⟹ {flag}")
        if blocked and worst:
            print(f"        first blocked cell {worst[0]}: |cell|={worst[1]}, {worst[2]} Aut-block(s)")
        tid, tmem = target_cell(n, col)
        if tid is None:
            break
        v = min(cells[tid])
        col = refine(n, adjl, [(2 * x + (1 if i == v else 0)) for i, x in enumerate(col)])
    print()


def main():
    print("W2 item 3b — CFI over an ASYMMETRIC base (does the item-3a counting bound survive?)")
    print("  item 3a's bound  reps >= |Aut-block| / |gauge-orbit| >= 2  needs Aut > gauge.")
    print("  Aut(CFI(G)) > gauge exactly when the BASE has automorphisms. All four item-3a")
    print("  witnesses had |Aut(base)| = 12, 12, 24, 12.  Here Aut(base) = 1.")
    print("  Every gauge element is verified edge-by-edge before use (same as item 3a).")
    print()

    print("=== 1. control: a SYMMETRIC base, to reproduce item 3a's verdict ===")
    k4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    run("CFI over K4  (|Aut(base)|=24)", k4, 4)

    print("=== 2. ASYMMETRIC base, NON-regular ⟹ 1-WL discrete on the base ===")
    for m in (7, 8):
        b = find_asymmetric_base(m, mindeg=3, seed=11 + m)
        if b is None:
            print(f"  (no asymmetric base found at m={m})")
            continue
        run(f"CFI over asym m={m} {b}", b, m)

    print("=== 3. ASYMMETRIC but REGULAR base (Frucht, cubic) ⟹ 1-WL COARSE on the base ===")
    print("     the case that separates 'key failure' from 'supply failure'")
    run("CFI over Frucht (cubic, |Aut(base)|=1)", FRUCHT, 12)

    print("=== 4. ⚠ ROOT-ONLY IS NOT A PASS — the same question at REACHED nodes ===")
    b7 = find_asymmetric_base(7, mindeg=3, seed=18)
    if b7:
        walk(f"CFI over asym m=7", b7, 7)
    walk("CFI over Frucht", FRUCHT, 12)
    k4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    walk("CFI over K4 (symmetric control)", k4, 4)


if __name__ == '__main__':
    main()
