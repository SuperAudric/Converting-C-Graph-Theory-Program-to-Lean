#!/usr/bin/env python3
"""
WHERE DOES THE EXPONENTIAL ENTER, AND IS IT AVOIDABLE?

Cost of any descent = PROD_k b_k  (b_k = branches explored at level k).

  today's `deepen`      : b_k == 1 BY FIAT (lowest-index pick)     -> poly, needs `Tinhofer`
  min-over-cell (dual)  : b_k == |C_k| minus pruning               -> invariant, PROD can blow

b_k = 1 is LEGITIMATE at level k iff one of:
  (ii)  CONSUME  — the cell is a single orbit and we hold generators transitive on it
                   (poly test: run today's deepen harvest on the cell, check transitivity)
  (iii) FORCE    — a poly equivariant key SPLITS the cell (then we refine, we don't branch:
                   the cell SHRINKS, no cost multiplier at all)

So the exponential survives ONLY at nodes where (ii) and (iii) both fail = STALL.
This probe runs the POLY LOOP and counts, per witness:
     force-steps / consume-steps / STALL nodes  and the branch factor at stalls.

Everything here is a faithful port of the landed objects:
  greedy_deepen   = DeepenSupply.deepen   (track A: whole-graph discretize, chooseIdK)
  replay          = DeepenSupply.replay
  twist           = DeepenSupply.twistOf  (coupled component, colour-match, IsColAut gate)
  lookahead_key   = Force.lookaheadKey    (individualize, refine, cell-size histogram)
"""
import sys, random
from itertools import combinations, product
from collections import defaultdict, Counter

sys.setrecursionlimit(10000)
from probe_dualdeepen import (circ, FANO, MIXED, rand_incidence, build_mp,
                              build_cfi_base, cubic, is_aut, Ctx, canon)

def true_orbits_on(n, adj, col, C):
    """TRUE Aut(adj,col)-orbit count on cell C, via the min-over-cell canonical form
    (cert-classes on a cell ARE its orbits).  Independent of the harvest."""
    ctx = Ctx(n, adj, prune=True, leafcap=200000)
    canon(ctx, list(col), [], root=True)
    if ctx.root is None: return None
    Croot, percert, expl = ctx.root
    if sorted(Croot) != sorted(C): return None
    return len(set(percert.values()))

# ---------------------------------------------------------------- fast 1-WL
def adjlist(n, adj):
    return [[u for u in range(n) if adj[v][u]] for v in range(n)]

def refine(n, adjl, col):
    col = list(col)
    while True:
        sig = [(col[v], tuple(sorted(col[u] for u in adjl[v]))) for v in range(n)]
        rank = {s: i for i, s in enumerate(sorted(set(sig)))}
        new = [rank[sig[v]] for v in range(n)]
        if new == col: return col
        col = new

def indiv(n, adjl, col, v):
    sig = [(col[u], 0 if u == v else 1) for u in range(n)]
    rank = {s: i for i, s in enumerate(sorted(set(sig)))}
    return refine(n, adjl, [rank[sig[u]] for u in range(n)])

def cellsof(n, col):
    d = defaultdict(list)
    for v in range(n): d[col[v]].append(v)
    return d

def target_cell(n, col):
    d = cellsof(n, col)
    ns = [c for c in sorted(d) if len(d[c]) >= 2]
    return (ns[0], d[ns[0]]) if ns else (None, None)

# ---------------------------------------------------------------- today's deepen (poly)
def greedy_deepen(n, adjl, col):
    """DeepenSupply.deepen — lowest-id cell, LOWEST-INDEX member, to whole-graph discreteness."""
    seq = []
    for _ in range(n + 1):
        cid, C = target_cell(n, col)
        if cid is None: return col, seq
        seq.append(cid)
        col = indiv(n, adjl, col, min(C))
    return None, seq

def replay(n, adjl, col, seq):
    """DeepenSupply.replay — follow the recorded id sequence."""
    for cid in seq:
        mem = [v for v in range(n) if col[v] == cid]
        if len(mem) < 2: return None
        col = indiv(n, adjl, col, min(mem))
    return col

def twist(n, adj, chi, leaf1, leafj):
    """DeepenSupply.twistOf — coupled component, colour-match, IsColAut gate."""
    K = [v for v in range(n) if len([u for u in range(n) if chi[u] == chi[v]]) > 1]
    pos = {}
    for w in K: pos.setdefault(leafj[w], w)
    img = [pos.get(leaf1[v], v) if v in set(K) else v for v in range(n)]
    if sorted(img) != list(range(n)): return None
    if any(chi[img[v]] != chi[v] for v in range(n)): return None
    return img if is_aut(n, adj, img) else None

def deepen_harvest(n, adj, adjl, chi, C, anchors=3):
    """DeepenSupply.deepenGens restricted to `anchors` anchors of the cell (an UNDER-
    approximation of the real all-anchor supply: it can only OVER-report stalls)."""
    gens = []
    firsts = {r: indiv(n, adjl, chi, r) for r in C}
    for r1 in C[:anchors]:
        leaf1, seq = greedy_deepen(n, adjl, firsts[r1])
        if leaf1 is None: continue
        for rj in C:
            if rj == r1: continue
            leafj = replay(n, adjl, firsts[rj], seq)
            if leafj is None: continue
            t = twist(n, adj, chi, leaf1, leafj)
            if t is not None: gens.append(t)
    return gens

def transitive_on(C, gens):
    if not C: return True
    seen = {C[0]}; fr = [C[0]]
    while fr:
        nx = []
        for x in fr:
            for g in gens:
                if g[x] not in seen: seen.add(g[x]); nx.append(g[x])
        fr = nx
    return set(C) <= seen

# ---------------------------------------------------------------- force key (poly)
def lookahead_key(n, adjl, col, v):
    """Force.lookaheadKey — individualize v, refine, take the cell-size histogram."""
    c = indiv(n, adjl, col, v)
    return tuple(sorted(Counter(c).values()))

def rref_key(n, adj, adjl, col, v):
    """A cheap second poly key: the multiset of refined colours of v's neighbourhood
    after individualization (a strictly finer, still equivariant, structural read)."""
    c = indiv(n, adjl, col, v)
    return (tuple(sorted(Counter(c).values())),
            tuple(sorted(c[u] for u in adjl[v])))

# ---------------------------------------------------------------- the POLY LOOP
def poly_loop(name, n, adj, anchors=3, verbose=True):
    adjl = adjlist(n, adj)
    col = refine(n, adjl, [0] * n)
    force_steps = consume_steps = 0
    stalls = []
    paths = 0                        # deepen paths run (the poly cost driver)
    for _ in range(n + 2):
        cid, C = target_cell(n, col)
        if cid is None: break
        # ---- (iii) FORCE: does a poly equivariant key split the cell?
        ks = {v: rref_key(n, adj, adjl, col, v) for v in C}
        if len(set(ks.values())) > 1:
            force_steps += 1
            sig = [(col[u], ks.get(u, ())) for u in range(n)]
            rank = {s: i for i, s in enumerate(sorted(set(sig)))}
            col = refine(n, adjl, [rank[sig[u]] for u in range(n)])
            continue
        # ---- (ii) CONSUME: is the cell certified a single orbit?
        gens = deepen_harvest(n, adj, adjl, col, C, anchors)
        paths += min(anchors, len(C)) * len(C)
        if transitive_on(C, gens):
            consume_steps += 1
            col = indiv(n, adjl, col, min(C))     # b_k = 1, JUSTIFIED
            continue
        # ---- STALL: neither fired. b_k > 1 here.
        orb = defaultdict(list)
        seen = {}
        for v in C:
            r = v
            for g in gens:
                pass
            seen[v] = v
        # orbit partition of C under the harvested gens = the surviving branch factor
        par = {v: v for v in C}
        def f(x):
            while par[x] != x: par[x] = par[par[x]]; x = par[x]
            return x
        for g in gens:
            for v in C:
                if g[v] in par:
                    a, b = f(v), f(g[v])
                    if a != b: par[a] = b
        bf = len({f(v) for v in C})
        tru = true_orbits_on(n, adj, col, C)
        stalls.append((len(C), bf, tru))
        col = indiv(n, adjl, col, min(C))         # continue measuring past the stall
    if verbose:
        tot = force_steps + consume_steps + len(stalls)
        print(f"  {name:<34} n={n:<4} levels={tot:<3} "
              f"FORCE={force_steps:<3} CONSUME={consume_steps:<3} STALL={len(stalls):<3} "
              f"stalls(|C|,harvest-orbits,TRUE-orbits)={stalls if stalls else '-'}  "
              f"deepen-paths={paths}")
    return force_steps, consume_steps, stalls, paths


if __name__ == "__main__":
    print("POLY LOOP — b_k=1 justified by FORCE (key splits) or CONSUME (certified orbit);")
    print("branching (exponential) survives only at STALL nodes.\n")

    print("### gauge / symmetric")
    poly_loop("mp7 Fano multipede", *build_mp(FANO))
    poly_loop("circ(5) multipede", *build_mp(circ(5)))
    poly_loop("MIXED multipede", *build_mp(MIXED))

    print("\n### CFI over random cubic bases (WL-hard)")
    for m in (8, 10, 12, 14):
        es = cubic(m, 11 + m)
        for tw in (False, True):
            n, adj = build_cfi_base(es, m, tw)
            poly_loop(f"CFI cubic m={m} {'tw' if tw else 'pl'}", n, adj)

    print("\n### rigid multipedes")
    for (V, W, deg, seed) in [(6, 5, 3, 1), (8, 6, 3, 2), (10, 7, 3, 3),
                              (12, 8, 3, 4), (14, 9, 3, 5), (16, 10, 3, 6)]:
        n, adj = build_mp(rand_incidence(V, W, deg, seed))
        poly_loop(f"rand multipede V={V} W={W}", n, adj)
