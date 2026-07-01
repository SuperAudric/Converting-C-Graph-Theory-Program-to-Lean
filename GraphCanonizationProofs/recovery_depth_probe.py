#!/usr/bin/env python3
"""
ROUTE-A DIRECTION CHECK — WL round-depth to recover orbits at span-dim-2 (2026-07-01).

Route A (recovery doc §6 ITEM B) wants: `bᵢ=1` at span-dim ≥ 2, i.e. iterated 1-WL on the rank-3
isoClass scheme recovers the Stab(S)-orbits once the base spans ≥ 2 anisotropic directions.
`forced_triangle_mult.py` already showed this HOLDS (bᵢ=1 at |S|≥3). Route A stalled as a *proof*
(it is the Gauss-counting `s(C)` recovery — the seal only discharges it per-instance via `decide`).

DECISIVE crackability question (`ScratchWallKernel` §redirected-3c): does the recovery need only
`O(1)` WL ROUNDS (⟹ a bounded-round / bounded-depth argument is plausible — crackable) or a number
of rounds GROWING with `d` (⟹ the frontier, banked quasipoly)?

THE TEST: at a span-dim-2 base `{0,a₁,a₂}`, run 1-WL round-by-round; report the FIRST round `r*` at
which cells = orbits (recovery depth). Scale over `(q,d)`: does `r*` stay `O(1)` as `d` grows?
Also report whether 1-WL recovers at all (vs needing 2-WL). Memory-light + `ulimit -v` guarded
(pure-Python WL is O(n²)/round; walls at n≈2500).

Faithful to source (model_gap.py): rank-3 isoClass scheme, exact-Gram Stab(S)-orbits.
"""
import itertools, sys, time
from collections import defaultdict
from model_gap import make_Q, sub, orbit_part, isoclass, first_indep_anis

def wl1_rounds(V, Q, q, d, S, orb, max_rounds):
    """Iterated 1-WL; after each round, test cells==orbits. Return (recovery_round or None, #rounds_to_stable).
    Memory-light: relations via iso_of[difference] (O(n)); signatures HASHED (O(n) keys)."""
    n = len(V); idx = {v: i for i, v in enumerate(V)}
    iso_of = {w: isoclass(Q, q, d, w) for w in V}
    orbl = [orb[V[i]] for i in range(n)]
    col = [0]*n
    for p, s in enumerate(S): col[idx[s]] = p+1
    def cells_eq_orbits(c):
        m = {}
        for i in range(n):
            if c[i] in m:
                if m[c[i]] != orbl[i]: return False
            else: m[c[i]] = orbl[i]
        return True
    rec = None
    if cells_eq_orbits(col): rec = 0
    for r in range(1, max_rounds+1):
        sigh = [0]*n
        for i in range(n):
            vi = V[i]; ci = col[i]
            row = sorted((iso_of[sub(vi, V[j], q, d)], col[j]) for j in range(n) if j != i)
            sigh[i] = hash((ci, tuple(row)))
        o = {}; nc = [0]*n; k = 0
        for i in range(n):
            h = sigh[i]
            if h not in o: o[h] = k; k += 1
            nc[i] = o[h]
        stable = (nc == col)
        col = nc
        if rec is None and cells_eq_orbits(col): rec = r
        if stable: return rec, r
    return rec, max_rounds

def run(d, q, eps, cap=2600):
    n = q ** d
    if n > cap:
        print(f"  VO^{'+' if eps>0 else '-'}_{d}({q}): SKIP (n={n}>{cap})", flush=True); return
    t0 = time.time()
    V = list(itertools.product(range(q), repeat=d)); Q = make_Q(d, q, eps)
    nm = f"VO^{'+' if eps>0 else '-'}_{d}({q})"
    anis = first_indep_anis(V, Q, q, d, d)
    S = [tuple([0]*d)] + anis[:2]        # span-dim-2 base {0, a1, a2}
    orb = orbit_part(V, Q, q, S, d); norb = len(set(orb.values()))
    rec, stab = wl1_rounds(V, Q, q, d, S, orb, max_rounds=2*d+8)
    verdict = f"recovered @round {rec}" if rec is not None else "1-WL does NOT recover (needs 2-WL)"
    print(f"  {nm} [n={n},{time.time()-t0:.1f}s] span-dim-2: orbits={norb}, {verdict}, stabilised @round {stab}", flush=True)
    return rec

if __name__ == "__main__":
    if len(sys.argv) == 4:
        run(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), cap=10**9); sys.exit(0)
    print("=== ROUTE-A DIRECTION: 1-WL round-depth r* to recover orbits at span-dim-2 — O(1) in d? ===", flush=True)
    for d in [4, 6]:              # d-scaling at q=3 (n=81, 729)
        for eps in [-1, +1]: run(d, 3, eps)
    for q in [5, 7]:              # q-scaling at d=4 (n=625, 2401)
        for eps in [-1, +1]: run(4, q, eps)
    print("VERDICT: r* flat in d ⟹ bounded-round recovery (crackable); r* grows ⟹ frontier.", flush=True)
