#!/usr/bin/env python3
"""probe_route_a.py — the SELECTOR route (A), resolver-level form, at the recorded witnesses.

docs/chain-descent-cao-propagation.md §10.5 (+ §0.0 limit 2, scratchpad/DUAL_resolver_scoping.md §1.2).

============================================================================================
THE QUESTION
============================================================================================
The recorded consume obstruction (DUAL §2.1, CFI over a random cubic base, m=8, n=56) is a node
where the harvest fails to certify the cell the descent SELECTED.  §10.5's realistic form of route
(A) is *resolver-level, not selector-level*:

    "try cells, keep one where the supply certifies transitivity (poly: <= n cells x one supply
     call).  That converts 'is the selector lucky' into 'does SOME cell resolve', which is strictly
     weaker and matches Select.NodeResolved's shape."

Nobody has measured it.  This probe does, at each reached node:

    selected-cell certified?      (what the built object asks)
    ANY-cell certified?           (what the resolver-level variant would ask)

============================================================================================
SOUNDNESS — read before quoting any number
============================================================================================
* Every verdict here is a POSITIVE certificate.  The harvest emits permutations which are
  re-verified (`is_aut` + colour-preservation), and transitivity is decided by BFS closure over the
  verified generator SET, never per-pair (DUAL §2.2: a per-pair twist failure is NOT a separation).
  So "certified" is a theorem about the graph.  "not certified" means only *this supply did not
  certify it* — never "different orbits".  That asymmetry is exactly what the resolver needs, and it
  is why no orbit oracle appears below.
* `probe_orbit_oracle` (doc §8.2, PROVEN BROKEN — it errs by merging) is NOT imported and NOT used.
* The harvest is a faithful port of `ChainDescent/DeepenSupply.lean`
  (`step` / `chooseIdK` / `deepen` / `replay` / `coupled` / `allSingletonsK` / `twistOf` /
  `deepenGens`), with `deepenGens`' cell argument generalized from `Descend.branches chi` to an
  ARBITRARY cell — which is the only change the resolver-level variant needs.
* ⚠ CONVENTION LIMIT (doc §7.4 / §8.3).  Python ranks colour ids by `sorted(set(sig))`; Lean's
  `warmRefineVec` ranks by Cantor-paired `sigKey`.  The two agree on the PARTITION but need not
  agree on the ID ORDER, and `chooseIdK` picks the lowest id.  So which cell counts as "selected",
  and which cell each deepening level individualizes, may differ from the Lean object.  A POSITIVE
  result here is still a fact about the graph (the certificates are verified) but must be
  cross-checked by Lean `#eval` (§8.3) before it is claimed of the built object.

Run detached and read the log (§9 — do not pipe through `tail`):
    cd /workspace/scratchpad && python3 -u probe_route_a.py > probe_route_a.out 2>&1
"""

import random
import time
from collections import defaultdict
from itertools import combinations

from probe_cao_cleanroom import cfi

# ---------------------------------------------------------------- budget / logging discipline
T0 = time.time()
BUDGET_S = float(60 * 45)          # hard wall-clock cap; every skip is LOGGED (§9)
SKIPPED = []


def budget_left(tag):
    if time.time() - T0 > BUDGET_S:
        SKIPPED.append(tag)
        return False
    return True


# ---------------------------------------------------------------- 1-WL (adjacency lists, for speed)
def nbrs_of(n, adj):
    return [[u for u in range(n) if adj[v][u]] for v in range(n)]


def wl(n, nbrs, col):
    col = list(col)
    while True:
        sig = [(col[v], tuple(sorted(col[u] for u in nbrs[v]))) for v in range(n)]
        rank = {s: i for i, s in enumerate(sorted(set(sig)))}
        new = [rank[sig[v]] for v in range(n)]
        if new == col:
            return col
        col = new


def indiv(n, col, v):
    sig = [(col[u], u != v) for u in range(n)]
    rank = {s: i for i, s in enumerate(sorted(set(sig)))}
    return [rank[sig[u]] for u in range(n)]


def step(n, nbrs, col, v):
    """`Deepen.step` = warmRefineVec . indivOne."""
    return wl(n, nbrs, indiv(n, col, v))


def cells_of(col):
    d = defaultdict(list)
    for v, c in enumerate(col):
        d[c].append(v)
    return d


def choose_id(col):
    """`chooseIdK` over the whole graph: the lowest id among NON-singleton cells."""
    d = cells_of(col)
    ns = [c for c in sorted(d) if len(d[c]) >= 2]
    return ns[0] if ns else None


# ---------------------------------------------------------------- the harvest (DeepenSupply port)
def deepen(n, nbrs, col):
    """`deepen`: individualize the lowest-id non-singleton cell's LOWEST-INDEX member until the
    WHOLE graph is discrete, recording the cell ids.  None on fuel exhaustion."""
    seq = []
    for _ in range(n + 1):
        cid = choose_id(col)
        if cid is None:
            return col, seq
        mem = [v for v in range(n) if col[v] == cid]
        col = step(n, nbrs, col, mem[0])
        seq.append(cid)
    return None


def replay(n, nbrs, seq, col):
    """`replay`: follow a recorded id sequence from another representative."""
    for cid in seq:
        mem = [v for v in range(n) if col[v] == cid]
        if len(mem) < 2:
            return None
        col = step(n, nbrs, col, mem[0])
    return col


def coupled(n, colp, colc):
    """`coupled`: the vertices whose PARENT cell is split by the deep colouring."""
    byp = cells_of(colp)
    return [v for v in range(n) if len({colc[u] for u in byp[colp[v]]}) > 1]


def all_singletons_k(K, colc):
    d = cells_of(colc)
    return all(len(d[colc[v]]) == 1 for v in K)


def is_aut(n, nbrs, adj, s, col):
    """Verified: colour-preserving graph automorphism (`IsColAut`)."""
    for v in range(n):
        if col[s[v]] != col[v]:
            return False
    for v in range(n):
        sv = s[v]
        if len(nbrs[sv]) != len(nbrs[v]):
            return False
        for u in nbrs[v]:
            if not adj[sv][s[u]]:
                return False
    return True


def twist_of(n, nbrs, adj, col, col1, K, colj):
    """`twistOf`: match footprint colours on the coupled component, identity off it; then VERIFY."""
    Kset = set(K)
    img = list(range(n))
    for v in K:
        hit = None
        for w in K:
            if colj[w] == col1[v]:
                hit = w
                break
        img[v] = hit if hit is not None else v
    if sorted(img) != list(range(n)):          # `permOf` gate
        return None
    return img if is_aut(n, nbrs, adj, img, col) else None


def deepen_gens(n, nbrs, adj, col, cell):
    """`deepenGens`, with the cell generalized from `Descend.branches chi` to ANY cell.
    ALL anchors (the G8 falsifier forbids a single anchor)."""
    firsts = [(r, step(n, nbrs, col, r)) for r in cell]
    gens = []
    for r1, c1first in firsts:
        d = deepen(n, nbrs, c1first)
        if d is None:
            continue
        col1, seq = d
        K = coupled(n, col, col1)
        if not K or not all_singletons_k(K, col1):
            continue
        for rj, cjfirst in firsts:
            if rj == r1:
                continue
            colj = replay(n, nbrs, seq, cjfirst)
            if colj is None:
                continue
            g = twist_of(n, nbrs, adj, col, col1, K, colj)
            if g is not None:
                gens.append(g)
    return gens


def transitive_on(gens, cell):
    """`CellIsOrbit`: BFS closure over the VERIFIED generator set (never per-pair)."""
    if not cell:
        return True
    target = set(cell)
    seen = {cell[0]}
    frontier = [cell[0]]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = g[x]
                if y not in seen:
                    seen.add(y)
                    nxt.append(y)
        frontier = nxt
    return target <= seen


# ---------------------------------------------------------------- the experiment
def test_node(n, nbrs, adj, col, label):
    """At one node: the SELECTED cell's verdict vs. EVERY cell's verdict."""
    d = cells_of(col)
    ns = [(c, d[c]) for c in sorted(d) if len(d[c]) >= 2]
    if not ns:
        print(f"    {label}: discrete — no cell to resolve")
        return None
    sel_id = ns[0][0]
    verdicts = []
    for cid, cell in ns:
        if not budget_left(f"{label} cell id={cid} |C|={len(cell)}"):
            print(f"    {label}: ⚠ BUDGET EXHAUSTED — remaining cells SKIPPED (logged)")
            break
        gens = deepen_gens(n, nbrs, adj, col, cell)
        ok = transitive_on(gens, cell)
        verdicts.append((cid, len(cell), ok, len(gens)))
    sel = next((v for v in verdicts if v[0] == sel_id), None)
    any_ok = [v for v in verdicts if v[2]]
    print(f"    {label}:  cells(non-singleton) = {[(c, len(x)) for c, x in ns]}")
    for cid, sz, ok, ng in verdicts:
        mark = "✓ CERTIFIED" if ok else "✗ not certified"
        star = "   <-- SELECTED (chooseIdK)" if cid == sel_id else ""
        print(f"        id={cid:<4} |C|={sz:<4} gens={ng:<4} {mark}{star}")
    if sel is None:
        return None
    if sel[2]:
        print("        ⟹ selected cell resolves; route (A) has nothing to add HERE")
        return "sel-ok"
    if any_ok:
        print(f"        ⟹ ★ SELECTED FAILS but cell id={any_ok[0][0]} (|C|={any_ok[0][1]}) "
              f"CERTIFIES — the resolver-level variant RESOLVES this node")
        return "route-a-wins"
    print("        ⟹ NO cell certifies — route (A)'s resolver-level variant does NOT help here")
    return "all-fail"


def descend_nodes(n, nbrs, col, depth):
    """Root, then nodes reached by individualizing the lowest-index member of each non-singleton
    cell (the descent's own shape), to `depth` levels.  Bounded on purpose; skips are logged."""
    out = [("root", col)]
    frontier = [("root", col)]
    for lvl in range(depth):
        nxt = []
        for lbl, c in frontier:
            d = cells_of(c)
            for cid in sorted(d):
                if len(d[cid]) < 2:
                    continue
                nc = step(n, nbrs, c, d[cid][0])
                tag = f"{lbl}/id{cid}"
                nxt.append((tag, nc))
        out += nxt
        frontier = nxt
    return out


def run(name, n, adj, depth=1):
    print(f"\n=== {name}   n={n}")
    nbrs = nbrs_of(n, adj)
    col = wl(n, nbrs, [0] * n)
    tally = defaultdict(int)
    for lbl, c in descend_nodes(n, nbrs, col, depth):
        if not budget_left(f"{name} node {lbl}"):
            print(f"  ⚠ BUDGET EXHAUSTED — node {lbl} and the rest SKIPPED (logged)")
            break
        r = test_node(n, nbrs, adj, c, lbl)
        if r:
            tally[r] += 1
    print(f"  --- {name} tally: {dict(tally)}")
    return tally


# ---------------------------------------------------------------- witnesses
def cubic(m, seed):
    """The random cubic base of DUAL §2.1 (probe_dualdeepen.py convention: seed = 11 + m)."""
    rnd = random.Random(seed)
    for _ in range(500):
        pts = [i for i in range(m) for _ in range(3)]
        rnd.shuffle(pts)
        es, ok = set(), True
        for k in range(0, len(pts), 2):
            a, b = pts[k], pts[k + 1]
            if a == b or (min(a, b), max(a, b)) in es:
                ok = False
                break
            es.add((min(a, b), max(a, b)))
        if ok:
            return sorted(es)
    raise RuntimeError("no cubic")


def shrikhande():
    """Shrikhande = Cayley(Z4xZ4, {+-(1,0), +-(0,1), +-(1,1)})."""
    pts = [(a, b) for a in range(4) for b in range(4)]
    idx = {p: i for i, p in enumerate(pts)}
    conn = {(1, 0), (3, 0), (0, 1), (0, 3), (1, 1), (3, 3)}
    n = 16
    adj = [[0] * n for _ in range(n)]
    for p in pts:
        for d in conn:
            q = ((p[0] + d[0]) % 4, (p[1] + d[1]) % 4)
            adj[idx[p]][idx[q]] = adj[idx[q]][idx[p]] = 1
    return n, adj


if __name__ == "__main__":
    print(__doc__)
    print(f"budget: {BUDGET_S:.0f}s wall")

    # --- THE RECORDED OBSTRUCTION (DUAL §2.1): CFI over a random cubic base, m=8, n=56.
    es = cubic(8, 19)
    print(f"\ncubic base m=8 seed=19: {es}")
    for tw in (True, False):
        n, adj, _, _ = cfi(es, 8, twisted_nodes=(0,) if tw else ())
        run(f"CFI cubic m=8 {'TWISTED' if tw else 'plain'}", n, adj, depth=2)

    # --- secondary: a 1-WL CAO witness, cheap, for contrast.
    n, adj = shrikhande()
    run("Shrikhande (1-WL CAO witness)", n, adj, depth=2)

    print("\n============================================================")
    if SKIPPED:
        print(f"⚠ SKIPPED (budget), {len(SKIPPED)} items — a silent cap reads as full coverage (§9):")
        for s in SKIPPED:
            print(f"    - {s}")
    else:
        print("no items skipped: full coverage of the nodes enumerated above")
    print(f"wall: {time.time() - T0:.1f}s")
