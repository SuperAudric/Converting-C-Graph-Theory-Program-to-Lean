#!/usr/bin/env python3
"""
TESTING THE CLAIM I ASSERTED (and probably got wrong):
  "ranking the orbit blocks == separating them by a poly invariant == the wall".

The counter-claim (user's option 3, made precise):

    CERTIFIED-BELOW  =>  deepen's OWN greedy single-path leaf cert is ISO-INVARIANT.

  Proof sketch.  Run the greedy descent from `a` in `adj` and from `tau a` in `tau.adj`.
  Cell ids match (chooseIdK invariant).  The min-INDEX picks differ: w vs w'.  If the
  chosen cell is a single orbit of IsColAut(adj, chi_cur) -- which is exactly what
  TinhoferPath asserts -- then there is rho in Aut fixing chi_cur with rho(w) = tau^-1(w'),
  and (tau . rho) is again an isomorphism adj -> tau.adj carrying the picks onto each other.
  Induct.  At the discrete leaf the two are related by an isomorphism, so the relabelled
  adjacency -- the cert -- is EQUAL.                                                  QED?

If that holds, then at a certified-below node:
   cert is a POLY (one greedy path per rep) EQUIVARIANT Force.Key,
   its fibres are exactly the orbits (probe_verdict_invariance: 18/18 exact),
   so it ORDERS the blocks and force fires.  No branching, no min-over-cell, no wall.

MEASURED HERE, per witness, at the root branch cell:
  (a) per rep a: is every level of a's descent a single orbit?   (certified-below)
  (b) is cert(a) invariant?   cert_{tau.adj}(tau a) == cert_adj(a) ?
  (c) does cert separate the orbit blocks (=> gives the ORDER force needs)?
  (d) correlation: does (a) predict (b)?   A certified-below rep with a NON-invariant
      cert would REFUTE the claim.
"""
import sys, random
from collections import defaultdict
sys.setrecursionlimit(10000)

from probe_dualdeepen import (circ, FANO, MIXED, rand_incidence, build_mp,
                              build_cfi_base, cubic, relabel, Ctx, canon)
from probe_polyloop import adjlist, refine, indiv, target_cell

def true_orbit_partition(n, adj, col):
    """TRUE Aut(adj,col)-orbit partition of the whole vertex set (min-over-cell canon)."""
    ctx = Ctx(n, adj, prune=True, leafcap=200000)
    canon(ctx, list(col), [])
    par = list(range(n))
    def f(x):
        while par[x] != x: par[x] = par[par[x]]; x = par[x]
        return x
    for (g, _) in ctx.gens:
        for i in range(n):
            a, b = f(i), f(g[i])
            if a != b: par[a] = b
    return [f(i) for i in range(n)]

def descend_cert(n, adj, adjl, col, a, check_orbits=True):
    """Greedy single-path descent from `a` (today's deepen).  Returns
    (cert, certified_below, levels) where certified_below = every level's chosen cell
    is a single TRUE Aut-orbit of the colouring at that level."""
    cur = indiv(n, adjl, col, a)
    certified = True; levels = 0
    for _ in range(n + 1):
        cid, C = target_cell(n, cur)
        if cid is None:
            lab = [0] * n
            for v in range(n): lab[cur[v]] = v
            return (tuple(adj[lab[i]][lab[j]] for i in range(n) for j in range(i + 1, n)),
                    certified, levels)
        if check_orbits:
            orb = true_orbit_partition(n, adj, cur)
            if len({orb[v] for v in C}) > 1: certified = False
        levels += 1
        cur = indiv(n, adjl, cur, min(C))
    return None, False, levels

def analyse(name, n, adj, trials=3, check_orbits=True):
    adjl = adjlist(n, adj)
    col = refine(n, adjl, [0] * n)
    cid, C = target_cell(n, col)
    if cid is None:
        print(f"  {name:<30} n={n}: discrete after 1-WL"); return
    res = {a: descend_cert(n, adj, adjl, col, a, check_orbits) for a in C}
    certified = {a for a in C if res[a][1]}
    # true orbit blocks of the cell
    orb = true_orbit_partition(n, adj, col)
    blocks = defaultdict(set)
    for v in C: blocks[orb[v]].add(v)
    # (c) does cert separate blocks / tie within them?
    certcls = defaultdict(set)
    for a in C: certcls[res[a][0]].add(a)
    exact = (sorted(sorted(s) for s in certcls.values())
             == sorted(sorted(s) for s in blocks.values()))
    # (b)+(d) invariance of cert under relabelling
    rnd = random.Random(5)
    bad_cert = bad_uncert = 0
    for _ in range(trials):
        s = list(range(n)); rnd.shuffle(s)
        a2 = relabel(n, adj, s); adjl2 = adjlist(n, a2)
        col2 = refine(n, adjl2, [0] * n)
        for a in C:
            c2, _, _ = descend_cert(n, a2, adjl2, col2, s[a], check_orbits=False)
            if c2 != res[a][0]:
                if a in certified: bad_cert += 1
                else: bad_uncert += 1
    print(f"  {name:<30} n={n:<4} |C|={len(C):<3} blocks={len(blocks):<3} "
          f"certified-below reps={len(certified)}/{len(C):<3} "
          f"cert-classes={len(certcls):<3} exact={'Y' if exact else 'N'}  "
          f"NON-INVARIANT certs: certified={bad_cert} uncertified={bad_uncert}")
    return bad_cert


if __name__ == "__main__":
    print("Does CERTIFIED-BELOW imply the greedy deepen cert is ISO-INVARIANT?")
    print("(a certified-below rep with a non-invariant cert REFUTES the claim)\n")
    tot = 0
    print("### rigid multipedes — the case that matters (root cell is multi-orbit)")
    for (V, W, deg, seed) in [(6, 5, 3, 1), (8, 6, 3, 2), (10, 7, 3, 3), (12, 8, 3, 4)]:
        n, adj = build_mp(rand_incidence(V, W, deg, seed))
        tot += analyse(f"rand multipede V={V} W={W}", n, adj) or 0
    print("\n### mixed / gauge")
    tot += analyse("MIXED multipede", *build_mp(MIXED)) or 0
    tot += analyse("circ(5) multipede", *build_mp(circ(5))) or 0
    tot += analyse("mp7 Fano multipede", *build_mp(FANO)) or 0
    print("\n### CFI cubic")
    for m in (8, 10):
        n, adj = build_cfi_base(cubic(m, 11 + m), m, False)
        tot += analyse(f"CFI cubic m={m}", n, adj) or 0
    print(f"\n  >>> total certified-below reps with a NON-invariant cert: {tot}"
          f"   {'(claim SURVIVES)' if tot == 0 else '(claim REFUTED)'}")
