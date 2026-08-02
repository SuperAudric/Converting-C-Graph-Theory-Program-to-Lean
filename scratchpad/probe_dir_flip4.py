#!/usr/bin/env python3
"""
PROBE v4 (2026-08-02): the user's scheme AS DESCRIBED, and the direction-flip question.

v2's mistake: it compared the whole target cell's key-multiset, so divergence fired at
depth 0 and no mixed pick ever preceded it (question never posed).  The user's scheme is
weaker and that is the point:

  - two instances; individualize u in one, w in the other; 1-WL each.
  - repeatedly: take the shared cell (same canonical colour id), individualize a vertex in
    EACH instance -- chosen independently, nothing forces them to correspond -- and 1-WL.
  - divergence = the EDGEWISE comparison over the selected sequences differs (or the colour
    signatures differ).  1-WL's opinion at that point = the lexicographic order of
    (edge vectors, signatures).
  - run to discrete with no divergence => candidate automorphism, verified.

The free variable is the pick.  Over random legal pick sequences on the SAME labelled graph,
does the emitted direction stay constant?  A LT/GT split = the direction is a function of the
picks, not of the isomorphism type -- i.e. mixed picks before identification flip it.

Clean-room; orbits by exact colour-preserving automorphism enumeration.
"""
import random, sys, itertools
from collections import defaultdict
sys.path.insert(0, "/workspace/scratchpad")
from probe_dir_flip import (refine, indiv, signature, cells, target, all_auts, orbits_of,
                            net, shrikhande, t8_chang, disjoint)

def scheme(n, adj, col, u, w, rng, orb, aset):
    selA, selB = [u], [w]
    A = refine(n, adj, indiv(n, col, u))
    B = refine(n, adj, indiv(n, col, w))
    nmixed = 0
    if signature(A) != signature(B):
        sA, sB = signature(A), signature(B)
        return ('LT' if sA < sB else 'GT'), nmixed, 0
    depth = 0
    while True:
        cidA, cellA = target(A); cidB, cellB = target(B)
        if cidA is None and cidB is None:
            inv = {c: v for v, c in enumerate(B)}
            perm = [inv[A[v]] for v in range(n)]
            ok = all({perm[y] for y in aset[v]} == aset[perm[v]] for v in range(n))
            return ('SYM' if ok else 'NOAUT'), nmixed, depth
        if cidA != cidB:
            sA, sB = signature(A), signature(B)
            return ('LT' if sA < sB else 'GT'), nmixed, depth
        if len({orb[x] for x in cellA}) > 1:
            nmixed += 1
        a = rng.choice(cellA)
        b = rng.choice(cellB)                      # <-- independent pick: the user's scheme
        eA = tuple(1 if y in aset[a] else 0 for y in selA)
        eB = tuple(1 if y in aset[b] else 0 for y in selB)
        A2 = refine(n, adj, indiv(n, A, a)); B2 = refine(n, adj, indiv(n, B, b))
        kA, kB = (eA, signature(A2)), (eB, signature(B2))
        if kA != kB:
            return ('LT' if kA < kB else 'GT'), nmixed, depth
        selA.append(a); selB.append(b)
        A, B = A2, B2
        depth += 1

def run(name, n, adj, max_prefix=1, trials=200, prefix_branch=2):
    print(f"\n{'='*78}\n{name}  n={n}\n{'='*78}")
    aset = [set(a) for a in adj]
    frontier = [([], refine(n, adj, [0]*n))]
    flips = posed = shown = 0
    for depth in range(max_prefix + 1):
        nxt = []
        for prefix, col in frontier:
            auts = all_auts(n, adj, col)
            orb = orbits_of(n, auts)
            for cid, cell in sorted(cells(col).items()):
                if len(cell) < 2: continue
                byorb = defaultdict(list)
                for v in cell: byorb[orb[v]].append(v)
                if len(byorb) < 2: continue           # want DIFFERENT-orbit pairs
                reps = [vs[0] for vs in byorb.values()]
                for u, w in itertools.combinations(reps, 2):
                    rng = random.Random(3)
                    tally = defaultdict(int); mx = 0
                    for _ in range(trials):
                        v, nm, dp = scheme(n, adj, col, u, w, rng, orb, aset)
                        tally[v] += 1; mx = max(mx, nm)
                    if mx == 0: continue              # question not posed
                    posed += 1
                    dirs = {k for k in tally if k in ('LT', 'GT')}
                    flag = "   *** DIRECTION FLIP ***" if len(dirs) > 1 else ""
                    if tally.get('SYM'):
                        flag += "   [+ spurious SYM on a different-orbit pair = UNSOUND]"
                    print(f"  prefix={prefix} cell{cid}(|{len(cell)}|) "
                          f"orbs={sorted(len(v) for v in byorb.values())} pair=({u},{w})")
                    print(f"     {dict(sorted(tally.items()))}  mixedPicksBefore<={mx}{flag}")
                    if len(dirs) > 1: flips += 1
                    shown += 1
                    if shown >= 12: return flips, posed
            if depth < max_prefix:
                cid, cell = target(col)
                if cid is not None:
                    for b in cell[:prefix_branch]:
                        nxt.append((prefix + [b], refine(n, adj, indiv(n, col, b))))
        frontier = nxt
    return flips, posed

if __name__ == "__main__":
    F = P = 0
    for nm, (n, a), mp in [("net(Z4)=CFI[K4]tw", net(4), 1),
                           ("Shrikhande", shrikhande(), 1),
                           ("Chang-2", t8_chang([tuple(sorted((i,(i+1)%8))) for i in range(8)]), 1),
                           ("Shrikhande+Shrikhande", disjoint(16, shrikhande()[1], 16, shrikhande()[1]), 1),
                           ("net(Z6)", net(6), 0)]:
        f, p = run(nm, n, a, max_prefix=mp)
        F += f; P += p
    print(f"\n>>> pairs where the question was POSED (>=1 mixed pick first): {P}")
    print(f">>> DIRECTION FLIPS: {F}")
