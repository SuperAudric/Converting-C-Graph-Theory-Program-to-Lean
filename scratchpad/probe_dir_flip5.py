#!/usr/bin/env python3
"""
PROBE v5 (2026-08-02): the direction-flip question, POSED AT LAST.

Habitat: two 1-WL-EQUIVALENT but NON-ISOMORPHIC objects side by side.
  rook4x4 + Shrikhande   (both SRG(16,6,2,2))   -> n=32, ONE 1-WL cell of 32, orbits [16,16]
  net(Z4) + net(Z2^2)    (= CFI[K4] twisted + untwisted) -> n=56, cells [24,32], each 2 orbits

Every vertex of one object shares a 1-WL cell with every vertex of the other, so a pair
(u,w) across the two objects is a DIFFERENT-ORBIT pair that 1-WL cannot separate at depth 0
-- separating them requires telling the two objects apart, which takes several
individualizations.  So the paired descent must survive MIXED PICKS before any divergence:
exactly the user's muddy case.

Orbits are known exactly by hand (each component is vertex-transitive / point- and
line-transitive, and the components are non-isomorphic), so no automorphism enumeration is
needed and no oracle is involved.

Scheme = the user's, as described: independent picks in each instance, divergence = first
mismatch of (edge vector to the selected sequence, 1-WL signature).
"""
import random, sys, itertools
from collections import defaultdict
sys.path.insert(0, "/workspace/scratchpad")
from probe_dir_flip import (refine, indiv, signature, cells, target, net, shrikhande, disjoint)
from probe_dir_flip4 import scheme

def rook4():
    n = 16; adj = [[] for _ in range(n)]
    def i(x, y): return 4*x + y
    for x in range(4):
        for y in range(4):
            for z in range(4):
                if z != y: adj[i(x,y)].append(i(x,z))
                if z != x: adj[i(x,y)].append(i(z,y))
    return n, [sorted(a) for a in adj]

def run(name, n, adj, orb, trials=300, maxpairs=6):
    print(f"\n{'='*78}\n{name}  n={n}\n{'='*78}")
    aset = [set(a) for a in adj]
    col = refine(n, adj, [0]*n)
    flips = posed = 0
    for cid, cell in sorted(cells(col).items()):
        if len(cell) < 2: continue
        byorb = defaultdict(list)
        for v in cell: byorb[orb[v]].append(v)
        if len(byorb) < 2: continue
        print(f"  cell{cid}: size {len(cell)}, orbit sizes {sorted(len(v) for v in byorb.values())}")
        groups = list(byorb.values())
        pairs = [(a, b) for a in groups[0][:3] for b in groups[1][:3]][:maxpairs]
        for u, w in pairs:
            rng = random.Random(3)
            tally = defaultdict(int); mx = 0
            for _ in range(trials):
                v, nm, dp = scheme(n, adj, col, u, w, rng, orb, aset)
                tally[v] += 1; mx = max(mx, nm)
            posed += 1 if mx > 0 else 0
            dirs = {k for k in tally if k in ('LT', 'GT')}
            flag = ""
            if len(dirs) > 1:
                flag = "   *** DIRECTION FLIP ***"; flips += 1
            if tally.get('SYM'):
                flag += "   [SPURIOUS SYM across non-isomorphic objects = UNSOUND]"
            if mx == 0:
                flag += "   (no mixed pick before verdict)"
            print(f"    pair=({u},{w})  {dict(sorted(tally.items()))}  mixedPicksBefore<={mx}{flag}")
    return flips, posed

if __name__ == "__main__":
    F = P = 0
    n1, a1 = rook4(); n2, a2 = shrikhande()
    n, a = disjoint(n1, a1, n2, a2)
    orb = [0]*16 + [1]*16                      # rook is VT; Shrikhande is VT; not isomorphic
    f, p = run("rook4x4 + Shrikhande", n, a, orb); F += f; P += p

    n3, a3 = net(4); n4, a4 = net(2, 'Z2')     # 16 points then 12 lines, in that order
    n, a = disjoint(n3, a3, n4, a4)
    orb = [0]*16 + [1]*12 + [2]*16 + [3]*12    # points/lines of each net are single orbits
    f, p = run("net(Z4) + net(Z2^2)  [CFI[K4] tw + untw]", n, a, orb, trials=200); F += f; P += p

    print(f"\n>>> pairs where the question was POSED (>=1 mixed pick first): {P}")
    print(f">>> DIRECTION FLIPS: {F}")
