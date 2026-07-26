#!/usr/bin/env python3
"""
Testing the remaining candidate strategies for closing the seal.

S2  DEFERRED SCHEDULE ("defer the hard ordering until the object is truly rigid").
    `targetColour` currently = lowest-id non-singleton cell.  Single-orbit-ness IS
    iso-invariant, so "lowest-id SINGLE-ORBIT non-singleton cell, else lowest-id" is an
    equally legal (invariant) target rule.  Individualizing inside a single-orbit cell is
    FREE (branch factor 1, invariant up to an automorphism).  So the deferred schedule
    consumes ALL symmetry before force is ever asked to decide.
    MEASURED: how many forced decisions remain, at what depth, and is the node PURELY
    RIGID (|Aut| = 1) when the first one arrives?  (If yes, the landed whole-node-rigid
    anchor 9A-9C applies directly and 9D/9F's gauge machinery is not needed there.)

S3  ORDER-AGNOSTIC BLOCK SPLITTING.  Blocks are invariant SETS.  Any invariant function of
    a set is a legal colour -- no total order needed.  Do the cheap ones separate blocks?
      h1(B) = |B|
      h2(B) = refined colour histogram after individualizing B AS A SET
      h3(B) = h2 plus the multiset of refined colours of B's neighbourhood
"""
import sys, random
from collections import defaultdict, Counter
sys.setrecursionlimit(10000)

from probe_dualdeepen import (circ, FANO, MIXED, rand_incidence, build_mp,
                              build_cfi_base, cubic, Ctx, canon, group_order)
from probe_polyloop import adjlist, refine, indiv, target_cell

def aut_data(n, adj, col):
    """(orbit map, |Aut| of the coloured graph) via the min-over-cell canonical form."""
    ctx = Ctx(n, adj, prune=True, leafcap=200000)
    canon(ctx, list(col), [])
    gens = [g for (g, _) in ctx.gens]
    par = list(range(n))
    def f(x):
        while par[x] != x: par[x] = par[par[x]]; x = par[x]
        return x
    for g in gens:
        for i in range(n):
            a, b = f(i), f(g[i])
            if a != b: par[a] = b
    return [f(i) for i in range(n)], group_order(n, gens)

def set_indiv(n, adjl, col, B):
    sig = [(col[u], 0 if u in B else 1) for u in range(n)]
    rank = {s: i for i, s in enumerate(sorted(set(sig)))}
    return refine(n, adjl, [rank[sig[u]] for u in range(n)])

def block_keys(n, adjl, col, B):
    c = set_indiv(n, adjl, col, B)
    h1 = len(B)
    h2 = tuple(sorted(Counter(c).values()))
    h3 = (h2, tuple(sorted(c[u] for b in B for u in adjl[b])))
    return h1, h2, h3

def run(name, n, adj):
    adjl = adjlist(n, adj)
    col = refine(n, adjl, [0] * n)
    decisions = []          # (depth, |C|, #blocks, |Aut| at that node, S3 separation)
    depth = 0
    for _ in range(n + 2):
        d = defaultdict(list)
        for v in range(n): d[col[v]].append(v)
        ns = [c for c in sorted(d) if len(d[c]) >= 2]
        if not ns: break
        orb, aut = aut_data(n, adj, col)
        # S2: prefer a cell that is a SINGLE ORBIT (invariant preference)
        single = [c for c in ns if len({orb[v] for v in d[c]}) == 1]
        if single:
            col = indiv(n, adjl, col, min(d[single[0]]))     # FREE: branch factor 1
            depth += 1
            continue
        # no consumable cell anywhere -> a genuine forced decision
        cid = ns[0]; C = d[cid]
        blocks = defaultdict(set)
        for v in C: blocks[orb[v]].add(v)
        ks = [block_keys(n, adjl, col, frozenset(B)) for B in blocks.values()]
        sep = tuple(len({k[i] for k in ks}) == len(ks) for i in range(3))
        decisions.append((depth, len(C), len(blocks), aut, sep))
        col = indiv(n, adjl, col, min(C))
        depth += 1
    tot = len(decisions)
    first = decisions[0] if decisions else None
    print(f"  {name:<30} n={n:<4} forced-decisions={tot:<2} "
          f"first@depth={first[0] if first else '-':<3} "
          f"|Aut| there={first[3] if first else '-':<5} "
          f"PURELY-RIGID={'YES' if first and first[3] == 1 else ('n/a' if not first else 'no ')}  "
          f"S3 sep (|B| / setIndiv / +nbhd) = "
          f"{[sum(1 for dcn in decisions if dcn[4][i]) for i in range(3)]}/{tot}")
    return decisions


if __name__ == "__main__":
    print("S2 = deferred schedule (consume everything first); S3 = order-agnostic block keys\n")
    print("### rigid multipedes")
    for (V, W, deg, seed) in [(6, 5, 3, 1), (8, 6, 3, 2), (10, 7, 3, 3), (12, 8, 3, 4)]:
        n, adj = build_mp(rand_incidence(V, W, deg, seed))
        run(f"rand multipede V={V} W={W}", n, adj)
    print("\n### mixed / gauge")
    run("MIXED multipede", *build_mp(MIXED))
    run("circ(5) multipede", *build_mp(circ(5)))
    run("mp7 Fano multipede", *build_mp(FANO))
    print("\n### CFI cubic")
    for m in (8, 10, 12):
        n, adj = build_cfi_base(cubic(m, 11 + m), m, False)
        run(f"CFI cubic m={m}", n, adj)
