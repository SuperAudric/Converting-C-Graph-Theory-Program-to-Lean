#!/usr/bin/env python3
"""probe_step2.py — S1 + S4(python): the 2-WL deepening step, and what it BUYS at the failing nodes.

docs/chain-descent-cao-propagation.md §13.5 (S1, S4).

============================================================================================
WHAT THIS IS
============================================================================================
S1.  A concrete **2-WL `Deepen.step`**: individualize `v`, run the 2-WL pair closure, read back a
     vertex colouring.  This is the object §13 says the swap is confined to — `Deepen.step`, NOT the
     descent's refiner.  The descent's nodes below are still generated with the **1-WL** step, which
     is exactly the design under scoping (swap the supply-internal step, leave `Descend`/`Refine`).

S4.  The A/B: rerun `probe_route_a.py`'s experiment with the 2-WL step inside the harvest ONLY, and
     ask what changes at the two nodes where the 1-WL harvest certified nothing —
       * the m=8 CFI **root** (cells 32, 24), and
       * **`root/id1/id9`**, the 8-cell node carrying the recorded `|C| = 16` cell (DUAL §2.1).

============================================================================================
SOUNDNESS (unchanged from probe_route_a.py — read it there)
============================================================================================
Every ✓ is a POSITIVE certificate: the harvest emits permutations, they are re-verified
(`is_aut` + colour-preservation), and transitivity is BFS closure over the verified generator SET.
"Not certified" means *this supply did not certify*, never "different orbits".  No orbit oracle is
used anywhere; `probe_orbit_oracle` (§8.2, PROVEN BROKEN) is not imported.

CALIBRATION FIRST (§8.1 discipline, and my own "validate cheap before long runs"):
`--calibrate` reproduces the doc §0.0 measurement — `net(Z₄)`, n=28, from the EXACT orbit partition:
1-WL → 5 cells, 2 mixed;  2-WL → 7 cells, 0 mixed.  If that does not reproduce, the 2-WL
implementation is wrong and nothing below means anything.

    cd /workspace/scratchpad
    python3 -u probe_step2.py --calibrate                 # ~seconds; MUST pass first
    python3 -u probe_step2.py > probe_step2.out 2>&1      # the A/B, run detached (§9)
"""

import sys
import time
from collections import defaultdict

import probe_route_a as RA
from probe_cao_cleanroom import cfi, all_isos, orbits, wl as cr_wl

T0 = time.time()


# ---------------------------------------------------------------- S1: the 2-WL pair closure
def wl2_closure(n, adj, vcol):
    """Stable 2-WL pair colouring of the vertex-coloured graph `(adj, vcol)`.

    Initial pair colour = (vcol a, vcol b, adj a b, a == b).  Round:
        c'(a,b) = (c(a,b), multiset over x of (c(a,x), c(x,b)))
    Returns a list of lists of int colour ids.
    """
    init = [[(vcol[a], vcol[b], adj[a][b], a == b) for b in range(n)] for a in range(n)]
    rk = {k: i for i, k in enumerate(sorted({init[a][b] for a in range(n) for b in range(n)}))}
    c = [[rk[init[a][b]] for b in range(n)] for a in range(n)]
    while True:
        ct = [list(col) for col in zip(*c)]          # ct[b][x] = c[x][b]  (column access, hoisted)
        sigs = [[(c[a][b], tuple(sorted(zip(c[a], ct[b])))) for b in range(n)] for a in range(n)]
        rk = {k: i for i, k in enumerate(sorted({sigs[a][b] for a in range(n) for b in range(n)}))}
        new = [[rk[sigs[a][b]] for b in range(n)] for a in range(n)]
        if new == c:
            return c
        c = new


def diag_colouring(n, pc):
    """The 2-WL vertex colouring: the DIAGONAL classes of the stable pair colouring."""
    sig = [pc[u][u] for u in range(n)]
    rk = {k: i for i, k in enumerate(sorted(set(sig)))}
    return [rk[sig[u]] for u in range(n)]


def step2(n, nbrs, adj, col, v):
    """**The 2-WL `Deepen.step`.**  Individualize `v`, close under 2-WL, read back a vertex colouring.

    The read is `(diag u, c(v,u), c(u,v))` — the diagonal refined by `v`'s row and column.  That is
    at least as fine as either alone, and it is the object `CaoRound.step2_closure` is stated about
    (`u ↦ f v u`, level sets = the `K_v`-orbits under `hsep`).

    `nbrs` is accepted (and ignored) so this is a drop-in for `probe_route_a.step`.
    """
    vc = RA.indiv(n, col, v)
    pc = wl2_closure(n, adj, vc)
    sig = [(pc[u][u], pc[v][u], pc[u][v]) for u in range(n)]
    rk = {k: i for i, k in enumerate(sorted(set(sig)))}
    return [rk[sig[u]] for u in range(n)]


# ---------------------------------------------------------------- the harvest, at either step
def harvest(n, nbrs, adj, col, cell, stepfn, budget_end=None):
    """`deepenGens` with the step as a parameter — §13.3's interface swap, in miniature.

    Faithful to DeepenSupply.lean: ALL anchors, whole-graph deepening recording chooseIdK ids,
    replay from every other representative, `coupled` footprint match, `twistOf` re-verified.
    Returns (gens, levels_seen, timed_out).
    """
    def deepen(c):
        seq = []
        for _ in range(n + 1):
            cid = RA.choose_id(c)
            if cid is None:
                return c, seq
            mem = [v for v in range(n) if c[v] == cid]
            c = stepfn(n, nbrs, adj, c, mem[0])
            seq.append(cid)
        return None

    def replay(seq, c):
        for cid in seq:
            mem = [v for v in range(n) if c[v] == cid]
            if len(mem) < 2:
                return None
            c = stepfn(n, nbrs, adj, c, mem[0])
        return c

    firsts = [(r, stepfn(n, nbrs, adj, col, r)) for r in cell]
    gens, levels = [], 0
    for r1, c1first in firsts:
        if budget_end and time.time() > budget_end:
            return gens, levels, True
        d = deepen(c1first)
        if d is None:
            continue
        col1, seq = d
        levels = max(levels, len(seq))
        K = RA.coupled(n, col, col1)
        if not K or not RA.all_singletons_k(K, col1):
            continue
        for rj, cjfirst in firsts:
            if rj == r1:
                continue
            if budget_end and time.time() > budget_end:
                return gens, levels, True
            colj = replay(seq, cjfirst)
            if colj is None:
                continue
            g = RA.twist_of(n, nbrs, adj, col, col1, K, colj)
            if g is not None:
                gens.append(g)
    return gens, levels, False


def step1(n, nbrs, adj, col, v):
    """The built 1-WL step, in the same signature."""
    return RA.step(n, nbrs, col, v)


# ---------------------------------------------------------------- the A/B at one node
def ab_node(n, nbrs, adj, col, label, per_cell_budget_s):
    d = RA.cells_of(col)
    ns = [(c, d[c]) for c in sorted(d) if len(d[c]) >= 2]
    print(f"\n  --- node {label}:  cells = {[(c, len(x)) for c, x in ns]}")
    if not ns:
        return None
    sel = ns[0][0]
    rows = []
    for cid, cell in ns:
        out = {}
        for tag, fn in (("1-WL", step1), ("2-WL", step2)):
            t = time.time()
            gens, lv, to = harvest(n, nbrs, adj, col, cell, fn,
                                   budget_end=time.time() + per_cell_budget_s)
            out[tag] = (RA.transitive_on(gens, cell), len(gens), lv, to, time.time() - t)
        rows.append((cid, len(cell), out))
        o1, o2 = out["1-WL"], out["2-WL"]
        star = "  <-- SELECTED" if cid == sel else ""
        flip = ""
        if o2[0] and not o1[0]:
            flip = "   ★★ 2-WL CERTIFIES WHERE 1-WL DOES NOT"
        elif o1[0] and not o2[0]:
            flip = "   ⚠ REGRESSION: 1-WL certifies, 2-WL does not"
        print(f"      id={cid:<4} |C|={len(cell):<4} "
              f"1-WL {'✓' if o1[0] else '✗'} (gens={o1[1]:<4} lvl={o1[2]:<3} {o1[4]:.1f}s"
              f"{' TIMEOUT' if o1[3] else ''})   "
              f"2-WL {'✓' if o2[0] else '✗'} (gens={o2[1]:<4} lvl={o2[2]:<3} {o2[4]:.1f}s"
              f"{' TIMEOUT' if o2[3] else ''}){star}{flip}")
    any1 = any(r[2]["1-WL"][0] for r in rows)
    any2 = any(r[2]["2-WL"][0] for r in rows)
    print(f"      ⟹ ANY cell certified:  1-WL = {any1},  2-WL = {any2}")
    return any1, any2


# ---------------------------------------------------------------- calibration
def calibrate():
    """Reproduce doc §0.0: net(Z4) = CFI[K4]-twisted, n=28, from the EXACT orbit partition.
    1-WL -> 5 cells, 2 mixed;  2-WL -> 7 cells, 0 mixed."""
    K4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    n, adj, _, _ = cfi(K4, 4, twisted_nodes=(0,))
    print(f"net(Z4) = CFI[K4]-tw:  n = {n}")
    A = all_isos(n, adj, cr_wl(n, adj, [0] * n), cr_wl(n, adj, [0] * n), limit=10 ** 7)
    orb = orbits(n, A)
    print(f"  |Aut| = {len(A)},  orbit partition = {sorted(_sizes(orb), reverse=True)}")

    nbrs = RA.nbrs_of(n, adj)
    for v in sorted({orb[u] for u in range(n)}):          # one rep per root orbit
        rep = next(u for u in range(n) if orb[u] == v)
        # exact Aut_v-orbits
        Av = [g for g in A if g[rep] == rep]
        tgt = orbits(n, Av)
        for tag, fn in (("1-WL", step1), ("2-WL", step2)):
            c = fn(n, nbrs, adj, orb, rep)
            cl = RA.cells_of(c)
            mixed = sum(1 for cell in cl.values() if len({tgt[u] for u in cell}) > 1)
            print(f"  rep={rep:<3} ({tag}): {len(cl)} cells, {mixed} MIXED "
                  f"(vs Aut_v-orbits {len(set(tgt))})")
        break                                              # doc quotes "either root-orbit rep"
    print("\n  EXPECTED (doc §0.0): 1-WL -> 5 cells, 2 mixed;  2-WL -> 7 cells, 0 mixed")


def node_diagnostics():
    """★ THE DECISIVE S4 DIAGNOSTIC (2026-07-31).  At each node where the 1-WL harvest certified
    NOTHING (`probe_route_a.out`), measure — against the EXACT automorphism group (`all_isos`) —

      (i)   are the node's cells single orbits at all?  (is this even consume's domain?)
      (ii)  does the 2-WL CLOSURE of the node colouring equal the orbit partition?
      (iii) does the 2-WL STEP differ from the 1-WL step along the harvest's own deepening path?

    (ii) and (iii) separate the two swaps §13 conflated: swapping the DESCENT's refiner vs swapping
    the supply-internal `Deepen.step`.
    """
    es = RA.cubic(8, 19)
    n, adj, _, _ = cfi(es, 8, twisted_nodes=(0,))
    nbrs = RA.nbrs_of(n, adj)
    root = RA.wl(n, nbrs, [0] * n)
    d = RA.cells_of(root)
    c1 = RA.step(n, nbrs, root, d[sorted(d)[1]][0])
    d1 = RA.cells_of(c1)
    node = RA.step(n, nbrs, c1, d1[9][0])

    for col, tag in ((root, "m=8 twisted ROOT"), (node, "m=8 twisted root/id1/id9")):
        A = all_isos(n, adj, col, col, limit=6 * 10 ** 6)
        orb = orbits(n, A)
        pc = wl2_closure(n, adj, col)
        dg = diag_colouring(n, pc)

        def stats(c):
            cl = RA.cells_of(c)
            return (len([x for x in cl.values() if len(x) > 1]),
                    sum(1 for x in cl.values() if len({orb[u] for u in x}) > 1))
        n1, m1 = stats(col)
        n2, m2 = stats(dg)
        print(f"\n{tag}:  |Aut_chi| = {len(A)},  orbit classes = {len(set(orb))}")
        print(f"  (i)  1-WL node colouring : {n1} non-singleton cells, {m1} MIXED"
              f"  {'⟹ NOT consume domain — force may fire here' if m1 else ''}")
        print(f"  (ii) 2-WL closure of it  : {n2} non-singleton cells, {m2} MIXED"
              f"  ⟹ {'= THE ORBIT PARTITION' if m2 == 0 else 'still mixed'}")

    # (iii) the deepening path, 1-WL step vs 2-WL step
    def part(c):
        return frozenset(frozenset(x) for x in RA.cells_of(c).values())

    def trace(fn, start, c0):
        c, out = fn(n, nbrs, adj, c0, start), []
        for _ in range(n + 1):
            out.append(part(c))
            cid = RA.choose_id(c)
            if cid is None:
                break
            mem = [v for v in range(n) if c[v] == cid]
            c = fn(n, nbrs, adj, c, mem[0])
        return out
    cell = RA.cells_of(node)[2]
    print(f"\n(iii) deepening path from the |C|={len(cell)} cell of root/id1/id9 "
          f"— 1-WL step vs 2-WL step:")
    for a in cell[:4]:
        t1, t2 = trace(step1, a, node), trace(step2, a, node)
        same = len(t1) == len(t2) and all(x == y for x, y in zip(t1, t2))
        print(f"   anchor {a}: {len(t1)} vs {len(t2)} levels, PARTITIONS IDENTICAL = {same}")
    print("\n⟹ read §13.6 of the doc for what these three together mean.")


def propagation_at_nodes(name, n, adj, depth=2, limit=6 * 10 ** 6):
    """★★ THE PROPAGATION TEST, RUN AT DESCENT NODES (user steer, 2026-07-31).

    The base case — mixed cells at a node — is **force's** job, not consume's.  What separates
    *"consume will verify on a node it should"* from *"this is a node consume should verify"* is
    **propagation**.  So: at every reached node, replace the node colouring by its **CAO start** (the
    exact `Aut(adj, χ)`-orbit partition — what force is supposed to deliver), individualize, refine,
    and ask whether the cells are still orbits of the point stabilizer.  That is doc §1's question,
    asked on the class §12.6 says was never swept: colourings **arising from individualization**,
    not orbit partitions of plain graphs.

    One representative per orbit-cell suffices: `K` is transitive on each cell of its own orbit
    partition, so all base points in one cell are conjugate and the verdict transports.

    Sound: `all_isos` is the validated complete enumeration (§8.1); every orbit here is exact, and
    no `probe_orbit_oracle` is involved.
    """
    print(f"\n=== {name}   n={n}")
    nbrs = RA.nbrs_of(n, adj)
    col0 = RA.wl(n, nbrs, [0] * n)
    tot = defaultdict(int)
    for lbl, col in RA.descend_nodes(n, nbrs, col0, depth):
        A = all_isos(n, adj, col, col, limit=limit)
        orb = orbits(n, A)
        cl_node = RA.cells_of(col)
        was_cao = all(len({orb[u] for u in x}) == 1 for x in cl_node.values())
        cells = [x for x in RA.cells_of(orb).values() if len(x) >= 2]
        tot["nodes"] += 1
        tot["cao_nodes" if was_cao else "noncao_nodes"] += 1
        if not cells:
            continue
        rows = []
        for cell in cells:
            v = cell[0]                                   # one rep per orbit-cell (see docstring)
            Av = [g for g in A if g[v] == v]
            tgt = orbits(n, Av)
            r = {}
            for tag, fn in (("1-WL", step1), ("2-WL", step2)):
                c = fn(n, nbrs, adj, orb, v)
                mixed = sum(1 for x in RA.cells_of(c).values() if len({tgt[u] for u in x}) > 1)
                r[tag] = mixed
                tot[f"{tag}:{'cao' if was_cao else 'noncao'}:" +
                    ("ok" if mixed == 0 else "FAIL")] += 1
            rows.append((len(cell), r["1-WL"], r["2-WL"]))
        flag = "CAO start" if was_cao else "NOT a CAO start (force's job)"
        bad1 = sum(1 for _, a, _ in rows if a)
        bad2 = sum(1 for _, _, b in rows if b)
        print(f"  {lbl:<22} |Aut_chi|={len(A):<5} {flag:<30} "
              f"orbit-cells={len(rows)}  propagation FAILS: 1-WL {bad1}, 2-WL {bad2}"
              + ("   ★ 2-WL REPAIRS ALL" if bad1 and not bad2 else "")
              + ("   ⛔⛔ 2-WL COUNTEREXAMPLE" if bad2 else ""))
        for sz, a, b in rows:
            if a or b:
                print(f"        cell |C|={sz:<4} mixed-after-step: 1-WL {a}, 2-WL {b}")
    print(f"  --- {name}: {dict(tot)}")
    return tot


def orbital_partition(n, auts):
    """The 2-orbits (orbitals) of `auts` acting diagonally on ordered pairs."""
    par = list(range(n * n))

    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for g in auts:
        for a in range(n):
            for b in range(n):
                i, j = f(a * n + b), f(g[a] * n + g[b])
                if i != j:
                    par[i] = j
    return [f(a * n + b) for a in range(n) for b in range(n)]


def same_part(x, y):
    mx, my = {}, {}
    for a, b in zip(x, y):
        if mx.setdefault(a, b) != b or my.setdefault(b, a) != a:
            return False
    return True


def entry_ticket(name, n, adj):
    """★ §7.2 THE ENTRY TICKET — run this before quoting ANY 2-WL sweep as evidence.

    A 2-WL vertex-level failure REQUIRES a non-schurian one-point extension: if the extension is
    schurian its diagonal classes *are* the orbits, so 2-WL cannot fail and a "0 counterexamples"
    verdict is FORCED, not evidence.  This is the recorded vacuity failure of the old 21-object
    sweep (doc §6), and it must not be repeated.

    Re-implemented here rather than imported: `probe_2wl_vacuity.py` is NOT `__main__`-guarded and
    runs its whole sweep on import (§0.1/§9's trap).
    """
    nbrs = RA.nbrs_of(n, adj)
    root = RA.wl(n, nbrs, [0] * n)
    A = all_isos(n, adj, root, root, limit=6 * 10 ** 6)
    orb = orbits(n, A)
    p2 = [c for row in wl2_closure(n, adj, root) for c in row]
    obl = orbital_partition(n, A)
    sr = same_part(p2, obl)
    exts = []
    for cell in RA.cells_of(orb).values():
        if len(cell) < 2:
            continue
        v0 = cell[0]
        A1 = [g for g in A if g[v0] == v0]
        p2e = [c for row in wl2_closure(n, adj, RA.indiv(n, orb, v0)) for c in row]
        exts.append(same_part(p2e, orbital_partition(n, A1)))
    paid = not all(exts)
    print(f"  {name:<26} |Aut|={len(A):<6} 2-WL rank={len(set(p2)):<4} orbital rank={len(set(obl)):<4} "
          f"schurian(root)={sr}  schurian(1-pt exts)={exts}")
    print(f"      ⟹ §7.2 ticket {'PAID — a 2-WL failure is POSSIBLE here' if paid else 'UNPAID — every extension is schurian, so 2-WL success is FORCED and proves nothing'}")
    return paid


def _sizes(part):
    d = defaultdict(int)
    for x in part:
        d[x] += 1
    return list(d.values())


# ---------------------------------------------------------------- driver
if __name__ == "__main__":
    if "--calibrate" in sys.argv:
        print(__doc__)
        calibrate()
        print(f"\nwall: {time.time() - T0:.1f}s")
        sys.exit(0)

    if "--ticket" in sys.argv:
        print(__doc__)
        print("§7.2 ENTRY TICKET — is a 2-WL failure even possible on this population?")
        es = RA.cubic(8, 19)
        for tw in (True, False):
            n, adj, _, _ = cfi(es, 8, twisted_nodes=(0,) if tw else ())
            entry_ticket(f"CFI cubic m=8 {'twisted' if tw else 'plain'}", n, adj)
        print(f"\nwall: {time.time() - T0:.1f}s")
        sys.exit(0)

    if "--propagate" in sys.argv:
        print(__doc__)
        es = RA.cubic(8, 19)
        for tw in (True, False):
            n, adj, _, _ = cfi(es, 8, twisted_nodes=(0,) if tw else ())
            propagation_at_nodes(f"CFI cubic m=8 {'TWISTED' if tw else 'plain'}", n, adj, depth=2)
        n, adj = RA.shrikhande()
        propagation_at_nodes("Shrikhande", n, adj, depth=2)
        print(f"\nwall: {time.time() - T0:.1f}s")
        sys.exit(0)

    if "--nodes" in sys.argv:
        print(__doc__)
        node_diagnostics()
        print(f"\nwall: {time.time() - T0:.1f}s")
        sys.exit(0)

    print(__doc__)
    PER_CELL_BUDGET = float(60 * 20)      # per (cell, step) harvest; timeouts are PRINTED, not hidden
    es = RA.cubic(8, 19)
    n, adj, _, _ = cfi(es, 8, twisted_nodes=(0,))
    nbrs = RA.nbrs_of(n, adj)
    print(f"\nCFI cubic m=8 TWISTED, n={n}, base={es}")

    # the two nodes where the 1-WL harvest certified NOTHING (probe_route_a.out)
    root = RA.wl(n, nbrs, [0] * n)
    nodes = [("root", root)]
    d = RA.cells_of(root)
    c1 = RA.step(n, nbrs, root, d[sorted(d)[1]][0])        # root/id1
    d1 = RA.cells_of(c1)
    if 9 in d1:
        nodes.append(("root/id1/id9", RA.step(n, nbrs, c1, d1[9][0])))
    else:
        print("  ⚠ cell id 9 absent at root/id1 — node reconstruction FAILED, logging and skipping")

    for lbl, c in nodes:
        ab_node(n, nbrs, adj, c, lbl, PER_CELL_BUDGET)

    print(f"\nwall: {time.time() - T0:.1f}s")
