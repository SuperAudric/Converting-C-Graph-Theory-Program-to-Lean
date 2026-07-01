#!/usr/bin/env python3
"""
NON-VACUITY CHECK for the bounded-multiplicity δ′ revival (2026-07-01).

Question (recovery route ITEM B, δ′ thread): the raw δ′ engine targets interNum=1 (forced
triangle pins γ to a SINGLETON) — walled on VO^ε (2-pt cut leaves ~q^{d-2} POINTS, not 1).
The WEAKER recovery target only needs the forced-triangle filter to have BOUNDED ORBIT
MULTIPLICITY: #{Stab(S)-orbits in a WL cell} = bᵢ ≤ poly(q). The dimensional wall bounds the
POINT count, not the ORBIT count — under the large residual stabiliser the q^{d-2} filter points
may form only ~poly(q) orbits.

THE TEST: measure  B := max_cell #{Stab(S)-orbits within one 1-WL cell}  at every base level of
a greedy spanning anisotropic descent, over (q,d). Does B stay poly(q) UNIFORM in d (revival
non-vacuous, route on-track) or GROW with d (→ quasipoly, route fails)?  This is bᵢ measured
statically per level (no branch-harvest recursion), so it reaches past the descent probe's
per-node-cost wall.

Faithful to source (same as model_gap.py): schemeAdj rel = isoClass(y-x) ∈ {0,1,2} (rank-3
similitude scheme); Stab(S)-orbit = exact-Gram profile at anisotropic base; 1-WL = CellsAreOrbits
model.  Vacuity-trap caution (MEMORY steer on BoundedConfusionMultiplicity): report the FULL
distribution, not just a pass/fail, so a trivially-small or trivially-large B is visible.
"""
import itertools, sys, time, gc
from collections import defaultdict
from model_gap import (make_Q, add, sub, polar, span_of, orbit_part,
                        isoclass, first_indep_anis)

def wl1_light(V, Q, q, d, S):
    """1-WL on the rank-3 isoClass scheme + individualize S — MEMORY-LIGHT (no n×n matrix).
    Relations computed on the fly from iso_of[difference] (n entries); per-round signatures are
    HASHED so only O(n) 64-bit keys are stored (probe-grade; collision prob negligible at n~1e4)."""
    n = len(V); idx = {v: i for i, v in enumerate(V)}
    iso_of = {w: isoclass(Q, q, d, w) for w in V}      # O(n), keyed by difference vector
    col = [0]*n
    for p, s in enumerate(S): col[idx[s]] = p+1
    for _ in range(n):
        sigh = [0]*n
        for i in range(n):
            vi = V[i]; ci = col[i]
            row = sorted((iso_of[sub(vi, V[j], q, d)], col[j]) for j in range(n) if j != i)
            sigh[i] = hash((ci, tuple(row)))            # tuple transient (O(n)), only hash kept
        o = {}; nc = [0]*n; k = 0
        for i in range(n):
            h = sigh[i]
            if h not in o: o[h] = k; k += 1
            nc[i] = o[h]
        if nc == col: break
        col = nc
    return {V[i]: col[i] for i in range(n)}

def max_orbits_per_cell(V, cells, orbits):
    """B at this level = max over WL cells of #{distinct orbit-labels inside the cell}."""
    by_cell = defaultdict(set)
    for v in V:
        by_cell[cells[v]].add(orbits[v])
    sizes = [len(s) for s in by_cell.values()]
    return max(sizes), sizes

def run(d, q, eps, cap=None):
    n = q ** d
    if cap and n > cap:
        print(f"  VO^{'+' if eps>0 else '-'}_{d}({q}): SKIP (n={n} > cap {cap})", flush=True)
        return
    t0 = time.time()
    V = list(itertools.product(range(q), repeat=d)); Q = make_Q(d, q, eps)
    nm = f"VO^{'+' if eps>0 else '-'}_{d}({q})"
    anis = first_indep_anis(V, Q, q, d, d)
    origin = tuple([0]*d)
    B = 0; rows = []
    # base levels: {0}, {0,a1}, {0,a1,a2}, ... {0,a1..a_{d-1}} (leaf, spanning)
    for k in range(0, d):
        S = [origin] + anis[:k]
        spandim = _spandim(q, S, d)
        orb = orbit_part(V, Q, q, S, d); norb = len(set(orb.values()))
        cells = wl1_light(V, Q, q, d, S); ncell = len(set(cells.values()))
        mb, _ = max_orbits_per_cell(V, cells, orbits=orb)
        B = max(B, mb)
        rows.append((len(S), spandim, norb, ncell, mb))
    print(f"  {nm}  [n={n}, {time.time()-t0:.1f}s]  B=max bᵢ={B}   (q={q}, q²={q*q})", flush=True)
    for (sz, sd, norb, ncell, mb) in rows:
        print(f"      |S|={sz} span={sd:2d}: orbits={norb:5d} cells={ncell:5d}  max_orbits_per_cell(bᵢ)={mb}", flush=True)
    return B

def _spandim(q, S, d):
    sp = span_of(q, S, d)
    # dim = log_q |span|
    import math
    return round(math.log(len(sp), q)) if len(sp) > 1 else 0

if __name__ == "__main__" and len(sys.argv) == 4:
    # single-case mode:  python3 forced_triangle_mult.py <d> <q> <eps>   (run under ulimit -v)
    d, q, eps = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    run(d, q, eps, cap=None)
    sys.exit(0)

if __name__ == "__main__":
    print("=== NON-VACUITY: max orbits-per-cell (bᵢ) across base levels, does B stay poly(q) in d? ===", flush=True)
    print("--- d-scaling at fixed q (the poly-vs-quasipoly test): compare B across d ---", flush=True)
    results = {}
    # fixed q=3, grow d: the decisive d-scaling test
    for d in [4, 6, 8]:
        for eps in [-1, +1]:
            b = run(d, 3, eps, cap=7000)
            if b is not None: results[(3, d, eps)] = b
    # fixed q=5, grow d
    for d in [4, 6]:
        for eps in [-1, +1]:
            b = run(d, 5, eps, cap=7000)
            if b is not None: results[(5, d, eps)] = b
    # q-scaling at fixed d=4 (does B grow with q? model_gap saw the gap grow with q)
    for q in [7, 9, 11]:
        for eps in [-1, +1]:
            b = run(4, q, eps, cap=7000)
            if b is not None: results[(q, 4, eps)] = b
    print("\n=== VERDICT TABLE (B = max bᵢ) ===", flush=True)
    for k in sorted(results):
        q, d, eps = k
        print(f"  q={q} d={d} eps={eps:+d}: B={results[k]}", flush=True)
