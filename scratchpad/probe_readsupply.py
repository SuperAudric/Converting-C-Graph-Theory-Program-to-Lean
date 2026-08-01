#!/usr/bin/env python3
"""probe_readsupply.py — is the UNGUARDED deep READ a stronger CONSUME supply than the replay harvest?

Context: docs/chain-descent-cao-propagation.md §0.0 competitor list ("run force at every step of the
descent"), scratchpad/DUAL_resolver_scoping.md §2.1 (the two certified harvest falsifiers).

============================================================================================
THE QUESTION
============================================================================================
`Deepen.isColAut_of_readKey_eq` (ChainDescent/DeepenExact.lean:191) is UNCONDITIONAL:

    readKey adj (indivOne chi u) (leafOf adj n (step adj chi u)).col
      = readKey adj (indivOne chi w) (leafOf adj n (step adj chi w)).col
    ==>  EXISTS rho, IsColAut adj chi rho AND rho u = w.

Every use of it in the build is FORCE-side (DeepenExact / DeepenGuard / ForcePick).  Nothing
CONSUME-side reads it — `deepenSupply` aligns two descents by REPLAYING one anchor's cell-id
sequence at the other (`replay` + `twistOf` on the coupled component), which is a DIFFERENT
alignment from "run each anchor's own greedy descent and compare the invariant read".

So there is an unbuilt, poly, soundness-free consume supply:

    readSupply adj chi = for each ordered pair (u,w) of the cell, if the two greedy leaf READS are
                         equal, emit the leaf-colour-matching permutation (then IsColAut-verify).

This probe measures whether it certifies cells the replay harvest does not — in particular the
recorded obstruction (DUAL §2.1, second falsifier): CFI over a random cubic base, m=8, n=56, the
|C|=16 cell one refinement below the root, which IS one true orbit and which the harvest splits 8+8.

============================================================================================
SOUNDNESS — read before quoting any number
============================================================================================
* Every verdict is a POSITIVE certificate: emitted permutations are re-verified (`is_aut` +
  colour preservation), and transitivity is decided by BFS closure over the verified generator SET,
  never per-pair (DUAL §2.2).  "certified" is a theorem about the graph; "not certified" means only
  *this supply did not certify it*, never "different orbits".
* No orbit oracle is used anywhere (`probe_orbit_oracle` is PROVEN BROKEN — it errs by merging).
* The harvest half is the same port as `probe_route_a.py` (faithful to `DeepenSupply.lean`).
  The read half ports `Deepen.leafOf` (chooseIdK = lowest non-singleton cell id over the WHOLE
  graph, lowest-index member), `Descend.indivOne` (u = v ? 2c+1 : 2c) and `Deepen.readKey`
  (adjacency between every ordered pair of leaf colour classes, then each class's parent colour).
* SELF-CHECK: by the theorem above, equal reads must yield a VERIFIED automorphism.  A
  "read-equal but is_aut FAILED" line would mean the port is wrong, not that the theorem is; the
  probe counts those separately and shouts.
* CONVENTION LIMIT (as in probe_route_a.py): python ranks colour ids by `sorted(set(sig))`, Lean by
  Cantor-paired `sigKey` — same PARTITION, possibly different ID ORDER, so which cell is "selected"
  and which cell each greedy level individualizes can differ from the Lean object.  Positive
  results are still facts about the graph; cross-check by Lean `#eval` before claiming them of the
  built object.

Run detached:  cd /workspace/scratchpad && python3 -u probe_readsupply.py > probe_readsupply.out 2>&1
"""

import random
import time
from collections import defaultdict

from probe_cao_cleanroom import cfi

T0 = time.time()
BUDGET_S = float(60 * 40)
SKIPPED = []


def budget_left(tag):
    if time.time() - T0 > BUDGET_S:
        SKIPPED.append(tag)
        return False
    return True


# ---------------------------------------------------------------- 1-WL
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
    """`chooseIdK` over the whole graph: lowest id among NON-singleton cells."""
    d = cells_of(col)
    ns = [c for c in sorted(d) if len(d[c]) >= 2]
    return ns[0] if ns else None


def is_aut(n, nbrs, adj, s, col):
    """`IsColAut`: colour-preserving graph automorphism."""
    for v in range(n):
        if col[s[v]] != col[v]:
            return False
    for v in range(n):
        sv = s[v]
        for u in nbrs[v]:
            if not adj[sv][s[u]]:
                return False
    return True


def transitive_on(gens, cell):
    """`CellIsOrbit`: BFS closure over the VERIFIED generator set (never per-pair)."""
    if not cell:
        return True
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
    return set(cell) <= seen


# ---------------------------------------------------------------- A. the replay harvest (DeepenSupply)
def deepen(n, nbrs, col):
    """`deepen` / `leafOf`: individualize the lowest-id non-singleton cell's LOWEST-INDEX member
    until the whole graph is discrete, recording the cell ids.  None on fuel exhaustion."""
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
    for cid in seq:
        mem = [v for v in range(n) if col[v] == cid]
        if len(mem) < 2:
            return None
        col = step(n, nbrs, col, mem[0])
    return col


def coupled(n, colp, colc):
    byp = cells_of(colp)
    return [v for v in range(n) if len({colc[u] for u in byp[colp[v]]}) > 1]


def all_singletons_k(K, colc):
    d = cells_of(colc)
    return all(len(d[colc[v]]) == 1 for v in K)


def twist_of(n, nbrs, adj, col, col1, K, colj):
    img = list(range(n))
    for v in K:
        hit = None
        for w in K:
            if colj[w] == col1[v]:
                hit = w
                break
        img[v] = hit if hit is not None else v
    if sorted(img) != list(range(n)):
        return None
    return img if is_aut(n, nbrs, adj, img, col) else None


def deepen_gens(n, nbrs, adj, col, cell, firsts):
    """`deepenGens` (ALL anchors), cell generalized to any cell."""
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


# ---------------------------------------------------------------- B. the deep READ (unbuilt supply)
BAD_SELF_CHECK = []


def read_of(n, adj, col, v, cfirst):
    """`readKey adj (indivOne col v) (leafOf adj n (step adj col v)).col`, plus the leaf colouring.

    Returns (read, leafcol) or None when the greedy leaf is not discrete (fuel exhaustion)."""
    d = deepen(n, nbrs_cache[id(adj)], cfirst)
    if d is None:
        return None
    leaf = d[0]
    if len(set(leaf)) != n:                       # `leafOf_discrete_n` says this cannot happen
        return None
    inv = [0] * n
    for x in range(n):
        inv[leaf[x]] = x
    phi = [2 * col[x] + (1 if x == v else 0) for x in range(n)]   # `Descend.indivOne`
    read = (tuple(adj[inv[c]][inv[e]] for c in range(n) for e in range(n)),
            tuple(phi[inv[c]] for c in range(n)))
    return read, leaf


def read_gens(n, nbrs, adj, col, cell, firsts):
    """The candidate supply: equal reads ==> the leaf-colour match, IsColAut-verified."""
    reads = {}
    for r, cfirst in firsts:
        reads[r] = read_of(n, adj, col, r, cfirst)
    gens = []
    for u in cell:
        ru = reads.get(u)
        if ru is None:
            continue
        for w in cell:
            if w == u:
                continue
            rw = reads.get(w)
            if rw is None or ru[0] != rw[0]:
                continue
            leaf_u, leaf_w = ru[1], rw[1]
            inv_w = [0] * n
            for x in range(n):
                inv_w[leaf_w[x]] = x
            rho = [inv_w[leaf_u[x]] for x in range(n)]            # rho: u's leaf -> w's leaf
            if rho[u] != w or not is_aut(n, nbrs, adj, rho, col):
                BAD_SELF_CHECK.append((u, w, rho[u] == w))
                continue
            gens.append(rho)
    n_undef = sum(1 for r in cell if reads.get(r) is None)
    return gens, n_undef


# ---------------------------------------------------------------- the experiment
nbrs_cache = {}


def test_node(n, nbrs, adj, col, label):
    d = cells_of(col)
    ns = [(c, d[c]) for c in sorted(d) if len(d[c]) >= 2]
    if not ns:
        print(f"    {label}: discrete")
        return None
    print(f"    {label}:  non-singleton cells = {[(c, len(x)) for c, x in ns]}")
    verdicts = []
    for cid, cell in ns:
        if not budget_left(f"{label} cell id={cid} |C|={len(cell)}"):
            print("        ⚠ BUDGET EXHAUSTED — remaining cells SKIPPED (logged)")
            break
        firsts = [(r, step(n, nbrs, col, r)) for r in cell]       # shared by both supplies
        hg = deepen_gens(n, nbrs, adj, col, cell, firsts)
        hok = transitive_on(hg, cell)
        rg, nundef = read_gens(n, nbrs, adj, col, cell, firsts)
        rok = transitive_on(rg, cell)
        verdicts.append((cid, len(cell), hok, rok))
        tag = {(True, True): "both certify",
               (True, False): "⚠ HARVEST ONLY",
               (False, True): "★★ READ ONLY — read beats the harvest",
               (False, False): "neither certifies"}[(hok, rok)]
        print(f"        id={cid:<4} |C|={len(cell):<4} "
              f"harvest[gens={len(hg):<4} {'✓' if hok else '✗'}]  "
              f"read[gens={len(rg):<4} undef={nundef} {'✓' if rok else '✗'}]   {tag}")
    return verdicts


def descend_nodes(n, nbrs, col, depth):
    out = [("root", col)]
    frontier = [("root", col)]
    for _ in range(depth):
        nxt = []
        for lbl, c in frontier:
            d = cells_of(c)
            for cid in sorted(d):
                if len(d[cid]) < 2:
                    continue
                nxt.append((f"{lbl}/id{cid}", step(n, nbrs, c, d[cid][0])))
        out += nxt
        frontier = nxt
    return out


def run(name, n, adj, depth=1):
    print(f"\n=== {name}   n={n}")
    nbrs = nbrs_of(n, adj)
    nbrs_cache[id(adj)] = nbrs
    col = wl(n, nbrs, [0] * n)
    tally = defaultdict(int)
    for lbl, c in descend_nodes(n, nbrs, col, depth):
        if not budget_left(f"{name} node {lbl}"):
            print(f"  ⚠ BUDGET EXHAUSTED — node {lbl} and the rest SKIPPED (logged)")
            break
        v = test_node(n, nbrs, adj, c, lbl)
        for _, _, hok, rok in (v or []):
            tally[(hok, rok)] += 1
    print(f"  --- {name} tally (harvest, read): "
          f"{ {f'{k[0]}/{k[1]}': v for k, v in tally.items()} }")
    return tally


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
    pts = [(a, b) for a in range(4) for b in range(4)]
    idx = {p: i for i, p in enumerate(pts)}
    conn = {(1, 0), (3, 0), (0, 1), (0, 3), (1, 1), (3, 3)}
    n = 16
    adj = [[0] * n for _ in range(n)]
    for p in pts:
        for dd in conn:
            q = ((p[0] + dd[0]) % 4, (p[1] + dd[1]) % 4)
            adj[idx[p]][idx[q]] = adj[idx[q]][idx[p]] = 1
    return n, adj


if __name__ == "__main__":
    print(__doc__)
    print(f"budget: {BUDGET_S:.0f}s wall")

    es = cubic(8, 19)
    print(f"\ncubic base m=8 seed=19: {es}")
    for tw in (True, False):
        n, adj, _, _ = cfi(es, 8, twisted_nodes=(0,) if tw else ())
        run(f"CFI cubic m=8 {'TWISTED' if tw else 'plain'}", n, adj, depth=2)

    n, adj = shrikhande()
    run("Shrikhande (1-WL CAO witness)", n, adj, depth=2)

    print("\n============================================================")
    if BAD_SELF_CHECK:
        print(f"⚠⚠ PORT BUG: {len(BAD_SELF_CHECK)} read-equal pairs failed IsColAut — "
              f"`isColAut_of_readKey_eq` says this is impossible, so the READ PORT IS WRONG. "
              f"First few: {BAD_SELF_CHECK[:5]}")
    else:
        print("self-check ✓ every read-equal pair yielded a VERIFIED automorphism "
              "(as isColAut_of_readKey_eq requires)")
    if SKIPPED:
        print(f"⚠ SKIPPED (budget), {len(SKIPPED)} items:")
        for s in SKIPPED:
            print(f"    - {s}")
    else:
        print("no items skipped: full coverage of the nodes enumerated above")
    print(f"wall: {time.time() - T0:.1f}s")


# ================================================================================================
# C. ★ FORCE INSIDE THE SUPPLY'S OWN DESCENT (the route under investigation, reading B)
# ================================================================================================
# `deepen`/`leafOf` individualize the LOWEST-INDEX member of the chosen cell.  That index pick is
# the sole recorded cause of the harvest's falsifiers (DUAL §2.3: "cell ids transport, the per-level
# min-index pick does not — the two descents diverge at the first MIXED cell").  A mixed cell is
# precisely FORCE's domain (`forceBy_no_narrowing_on_orbit` forbids force only on single-orbit
# cells), so the route says: narrow each level's cell by an equivariant force key BEFORE picking.
#
# Inner key used here = `readKey adj (indivOne col v) (step adj col v)` — the same invariant read,
# at the ONE-STEP refinement instead of a leaf.  It is `lookaheadKey`/`holKeyFast`'s shape and is
# unconditionally equivariant (`step_transport` + `readKey_transport`), so no guard is smuggled in.
# Cost per level = |cell| refinements: the "massive but polynomial" blow-up the route pays.

def read_of_col(n, adj, phi, c2):
    """`readKey adj phi c2` — adjacency between every ordered pair of c2-classes, then each class's
    total parent colour.  Works for any colouring (not only discrete ones)."""
    d = cells_of(c2)
    ids = sorted(d)
    return (tuple(sum(adj[u][w] for u in d[a] for w in d[b]) for a in ids for b in ids),
            tuple(sum(phi[u] for u in d[a]) for a in ids))


def force_key(n, nbrs, adj, col, v):
    phi = [2 * col[x] + (1 if x == v else 0) for x in range(n)]
    return read_of_col(n, adj, phi, step(n, nbrs, col, v))


def deepen_forced(n, nbrs, adj, col):
    """`leafOf` with the per-level pick FORCE-NARROWED: keepMin by `force_key`, then lowest index
    inside the (equivariant) surviving set.  Residual ambiguity inside the surviving set is
    harmless iff that set is a single orbit — the weakened `TinhoferPath` the route buys."""
    widths = []
    for _ in range(n + 1):
        cid = choose_id(col)
        if cid is None:
            return col, widths
        mem = [v for v in range(n) if col[v] == cid]
        keys = [(force_key(n, nbrs, adj, col, v), v) for v in mem]
        best = min(k for k, _ in keys)
        kept = [v for k, v in keys if k == best]
        widths.append((len(mem), len(kept)))
        col = step(n, nbrs, col, kept[0])
    return None


def read_gens_forced(n, nbrs, adj, col, cell, firsts):
    """Same certificate as `read_gens`, over FORCE-GUIDED leaves."""
    leaves, widths = {}, []
    for r, cfirst in firsts:
        d = deepen_forced(n, nbrs, adj, cfirst)
        if d is None or len(set(d[0])) != n:
            continue
        leaves[r] = d[0]
        widths += d[1]
    gens = []
    for u, leaf_u in leaves.items():
        for w, leaf_w in leaves.items():
            if u == w:
                continue
            inv_w = [0] * n
            for x in range(n):
                inv_w[leaf_w[x]] = x
            rho = [inv_w[leaf_u[x]] for x in range(n)]
            if rho[u] == w and is_aut(n, nbrs, adj, rho, col):
                gens.append(rho)
    ties = sum(1 for a, b in widths if b > 1)
    return gens, len(leaves), ties, len(widths)
