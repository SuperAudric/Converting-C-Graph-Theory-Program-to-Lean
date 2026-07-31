#!/usr/bin/env python3
"""DOES SEPARATION *MUST* HAPPEN AT ROUND 3?  (and R1c: the sharp Cayley population)

`CaoRound.round2_barrier_real` proves separation cannot occur BEFORE round 3.  Two questions:
  Q1  is 3 even the right constant -- does any deficient root need round >= 4?
  Q2  does any deficient root NEVER separate?  (that would REFUTE the crux outright)

A Cayley graph over a TRANSITIVE group satisfies CAO at the root automatically (one fibre = one
orbit), so non-schurian S-rings are exactly the sharp inputs (doc R1c).  Sweeps groups of order 8
and 16 over all inverse-closed connection sets; rounds counted from the COHERENT X (doc §12.3's
convention box -- counting from raw conflates the unbounded 'build X' term).
"""
import sys
from collections import defaultdict
sys.path.insert(0, "/workspace/scratchpad")
from probe_cao_cleanroom import wl, all_isos, orbits
from probe_cao_induction import orbital_partition
from probe_cao_diameter import prounds, init_pairs
from probe_cao_cause import close_pairs
from probe_2wl_sring import (g_cyclic, g_direct, g_semidirect_cyclic, g_dicyclic,
                             cayley_adj, check_group)

def ext_round(n, adj, A, v=0):
    """Return (n_fused_on_row, max separation round, n_never) from the coherent X."""
    orb = orbits(n, A); m = {}
    oc = [m.setdefault(orb[x], len(m)) for x in range(n)]
    X = close_pairs(n, init_pairs(n, adj, oc))[-1]
    orbl = orbital_partition(n, A)
    byc = defaultdict(set)
    for i in range(n*n): byc[X[i]].add(orbl[i])
    fused = {c for c, o in byc.items() if len(o) > 1}
    if not fused: return 0, None, 0
    ini, col0 = {}, [0]*(n*n)
    for a in range(n):
        for b in range(n):
            k = (X[a*n+b], a == v, b == v)
            col0[a*n+b] = ini.setdefault(k, len(ini))
    rounds = close_pairs(n, col0)
    tot, mx, never = 0, 0, 0
    for c in sorted(fused):
        fib = defaultdict(list)
        for x in range(n):
            if X[v*n+x] == c: fib[orbl[v*n+x]].append(x)
        if len(fib) < 2: continue
        tot += 1
        reps = [y[0] for y in fib.values()]
        r = next((i for i in range(len(rounds))
                  if len({rounds[i][v*n+u] for u in reps}) == len(reps)), None)
        if r is None: never += 1
        else: mx = max(mx, r)
    return tot, (mx if tot else None), never

GROUPS = {
    "Z8": g_cyclic(8), "Z4xZ2": g_direct(g_cyclic(4), g_cyclic(2)),
    "Z2^3": g_direct(g_cyclic(2), g_direct(g_cyclic(2), g_cyclic(2))),
    "D8": g_semidirect_cyclic(4, 3), "Q8": g_dicyclic(2),
    "Z16": g_cyclic(16), "Z4^2": g_direct(g_cyclic(4), g_cyclic(4)),
    "Z8xZ2": g_direct(g_cyclic(8), g_cyclic(2)),
    "Z4xZ2^2": g_direct(g_cyclic(4), g_direct(g_cyclic(2), g_cyclic(2))),
    "Z2^4": g_direct(g_direct(g_cyclic(2), g_cyclic(2)), g_direct(g_cyclic(2), g_cyclic(2))),
    "D16": g_semidirect_cyclic(8, 7), "SD16": g_semidirect_cyclic(8, 3),
    "M16": g_semidirect_cyclic(8, 5), "Q16": g_dicyclic(4),
    "D8xZ2": g_direct(g_semidirect_cyclic(4, 3), g_cyclic(2)),
}

if __name__ == "__main__":
    print("sharp Cayley sweep -- separation round of DEFICIENT roots, counted from coherent X")
    hist, skipped, tested, defic = defaultdict(int), 0, 0, 0
    never_tot = 0
    for gname, mul in GROUPS.items():
        check_group(mul, gname)
        n = len(mul)
        inv = [next(y for y in range(n) if mul[x][y] == 0) for x in range(n)]
        cls, seen = [], set()
        for x in range(1, n):
            if x in seen: continue
            c = {x, inv[x]}; seen |= c; cls.append(sorted(c))
        gd, gs, gn = 0, 0, 0
        for mask in range(1, 2**len(cls)):
            S = [e for i, c in enumerate(cls) if mask >> i & 1 for e in c]
            nn, adj = cayley_adj(mul, S)
            if any(sum(r) == 0 for r in adj): continue
            try:
                A = all_isos(nn, adj, wl(nn, adj, [0]*nn), wl(nn, adj, [0]*nn), limit=300_000)
            except RuntimeError:
                skipped += 1; continue
            tested += 1
            t, mx, nv = ext_round(nn, adj, A)
            if t:
                gd += 1; defic += 1; hist[mx] += 1; gn += nv; never_tot += nv
                gs = max(gs, mx)
        print(f"  {gname:9s} n={n:2d}  deficient roots: {gd:4d}   max sep round: {gs}"
              + (f"   ⚠ NEVER-separating: {gn}" if gn else ""))
    print(f"\n  tested={tested}  deficient={defic}  skipped(aut budget)={skipped}")
    print(f"  separation-round histogram (from coherent X): {dict(sorted(hist.items()))}")
    print(f"  NEVER separates (would REFUTE the crux): {never_tot}")
