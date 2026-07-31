#!/usr/bin/env python3
"""Is the measured 'separation always at round 3' FORCED?  Two claims to check before proving.

C1  ROUND-1 = the v-AUGMENTED colouring.  Round 1 of the extension should give each pair exactly
    its triangle type through v, i.e. the partition of round-1 equals that of
        zAug(a,b) = (X(a,b), X(a,v), X(v,b)).
C2  ROUND-2 BARRIER.  On v's ROW the round-2 colouring should STILL not separate: writing
        sig(zAug) v u = map over x of ((X v x, X v v, X v x), (X x u, X x v, X v u)),
    the transpose axiom makes X x v a function of X v x, so this is the image of sig(X) v u under a
    fixed map -- equal for u,w whenever X(v,u) = X(v,w), by coherence.  So separation cannot happen
    before round 3, which is exactly what M3 measured 11/11.
"""
import sys
from collections import defaultdict
sys.path.insert(0, "/workspace/scratchpad")
from probe_cao_cleanroom import wl, all_isos, orbits
from probe_cao_induction import orbital_partition, shrikhande, chang
from probe_cao_net import net
from probe_cao_diameter import prounds, init_pairs
from probe_cao_cause import close_pairs
from probe_cao_cause2 import shr_prod

def same_part(a, b):
    ma, mb = {}, {}
    for x, y in zip(a, b):
        if ma.setdefault(x, y) != y or mb.setdefault(y, x) != x:
            return False
    return True

def check(lab, n, adj, gens, v=0):
    orb = orbits(n, gens); m = {}
    oc = [m.setdefault(orb[x], len(m)) for x in range(n)]
    X = close_pairs(n, init_pairs(n, adj, oc))[-1]
    orbl = orbital_partition(n, gens)
    byc = defaultdict(set)
    for i in range(n*n): byc[X[i]].add(orbl[i])
    fused = {c for c, o in byc.items() if len(o) > 1}
    if not fused:
        print(f"  {lab:26s} schurian root -- skipped"); return
    # the extension, round by round
    ini, col0 = {}, [0]*(n*n)
    for a in range(n):
        for b in range(n):
            k = (X[a*n+b], a == v, b == v)
            col0[a*n+b] = ini.setdefault(k, len(ini))
    rounds = close_pairs(n, col0)
    # C1: round-1 partition vs zAug
    zi, zAug = {}, [0]*(n*n)
    for a in range(n):
        for b in range(n):
            k = (X[a*n+b], X[a*n+v], X[v*n+b], a == v, b == v)
            zAug[a*n+b] = zi.setdefault(k, len(zi))
    c1 = same_part(rounds[1], zAug) if len(rounds) > 1 else None
    # C2: does ANY fused target separate at round 1 or 2?
    early = []
    for c in sorted(fused):
        fib = defaultdict(list)
        for x in range(n):
            if X[v*n+x] == c: fib[orbl[v*n+x]].append(x)
        if len(fib) < 2: continue
        reps = [y[0] for y in fib.values()]
        for r in (1, 2):
            if r < len(rounds) and len({rounds[r][v*n+u] for u in reps}) > 1:
                early.append((c, r))
    # transpose axiom holds for X?
    T = {}
    tr = all(T.setdefault(X[a*n+b], X[b*n+a]) == X[b*n+a] for a in range(n) for b in range(n))
    print(f"  {lab:26s} rounds={len(rounds)-1}  C1 round1==zAug: {c1}   "
          f"transpose-closed: {tr}   C2 separations before r3: "
          f"{early if early else 'NONE'}")

if __name__ == "__main__":
    print("C1: is round 1 exactly the v-augmented colouring?   C2: any separation before round 3?")
    for lab, (nn, aa) in [("Shrikhande", shrikhande()), ("net(Z4)", net((4,))[:2]),
                          ("Chang-2", chang([(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,0)]))]:
        A = all_isos(nn, aa, wl(nn, aa, [0]*nn), wl(nn, aa, [0]*nn), limit=3_000_000)
        check(lab, nn, aa, A)
    for m in (3, 5):
        N, A2, gens = shr_prod(m)
        check(f"Shrikhande [] C_{m}", N, A2, gens)
