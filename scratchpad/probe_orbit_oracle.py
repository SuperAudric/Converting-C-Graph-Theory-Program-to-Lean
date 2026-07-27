#!/usr/bin/env python3
"""
PROBE: is deepen (`DeepenAnchor` + `ReplayDeepening` + `twistOf`) a PERFECT ORBIT ORACLE?

The hypothesis under test (user, 2026-07-27):
    "when the harvest FAILS on a pair (a,b) it has produced cert(a) != cert(b), which is a
     PROOF that a and b are in different orbits.  Hence same orbit ==> it must succeed."

That is exactly the statement "the harvest has NO FALSE NEGATIVES", i.e.

    same-orbit(a,b)  ==>  twist(a,b) verifies.

This probe measures the false-negative rate DIRECTLY, per pair, against an exact orbit
oracle, for BOTH variants:

    SINGLE-anchor  = the C# `HarvestTwists(p, part, cell, cell[0])`
    ALL-anchor     = the Lean `Deepen.deepenGens` (loops every rep)

and correlates every false negative with `AmenablePath` ("certified-below"): at every
deepening level, is the chosen cell a single orbit of the CURRENT stabiliser?

Exact orbit oracle: a ~ b  iff  canon(adj, indiv(chi,a)) == canon(adj, indiv(chi,b))
(Karp 1977 / Booth-Colbourn 1979). `canon` = min-over-cell exhaustive canonical form
with automorphism pruning (from probe_dualdeepen.canon), which is exact by construction.

Also reports LEVELS (the §11.4 vacuity check: certification with 0 levels is empty).
"""
import sys, time
from collections import defaultdict
from itertools import product

sys.path.insert(0, "/workspace/scratchpad")
from probe_dualdeepen import (refine, indiv, target_cell, is_aut, relabel,
                              build_mp, build_cfi, build_cfi_base, cubic, circ,
                              rand_incidence, FANO, MIXED, Ctx, canon)

# ───────────────────────────────────────────────────────── exact canonical form
_CANON_CACHE = {}

def canonform(n, adj, col, leafcap=200000):
    """Exact canonical form of the COLOURED graph (min over cell, aut-pruned)."""
    key = (tuple(tuple(r) for r in adj), tuple(col))   # content-keyed: id() is recycled
    if key in _CANON_CACHE: return _CANON_CACHE[key]
    ctx = Ctx(n, adj, prune=True, leafcap=leafcap)
    r = canon(ctx, list(col), [])
    out = (None if ctx.blown else r[0])
    _CANON_CACHE[key] = out
    return out

def orbit_partition(n, adj, col, cell):
    """TRUE orbits of Aut(adj,col) restricted to `cell`, via the Karp reduction."""
    cf = {}
    for v in cell:
        c = canonform(n, adj, indiv(n, col, v))
        if c is None: return None
        cf[v] = c
    blocks = defaultdict(list)
    for v in cell: blocks[cf[v]].append(v)
    return {v: min(b) for b in blocks.values() for v in b}      # v -> block rep

# ───────────────────────────────────────────── deepen / replay / twist (faithful)
def deepen(n, adj, col, fuel=None):
    """DeepenAnchor, track A: whole-graph discretize, lowest-id cell, LOWEST-INDEX member.
    Returns (leafcol, seq) or None."""
    if fuel is None: fuel = n
    cur = list(col); seq = []
    for _ in range(fuel):
        cid, C = target_cell(n, cur)
        if cid is None: return cur, seq
        cur = refine(n, adj, indiv(n, cur, min(C)))
        seq.append(cid)
    return None

def replay(n, adj, col, seq):
    """ReplayDeepening: follow the recorded ids; None if a level cannot be followed."""
    cur = list(col)
    for cid in seq:
        mem = [v for v in range(n) if cur[v] == cid]
        if len(mem) < 2: return None
        cur = refine(n, adj, indiv(n, cur, min(mem)))
    return cur

def coupled(n, chi_p, chi_c):
    out = []
    for v in range(n):
        cls = [u for u in range(n) if chi_p[u] == chi_p[v]]
        if len(set(chi_c[u] for u in cls)) > 1: out.append(v)
    return out

def twist_of(n, adj, chi, chi1, K, chij):
    """twistOf: colour-match on K, identity off it; permOf gate + IsColAut verify."""
    img = list(range(n))
    for v in K:
        w = next((w for w in K if chij[w] == chi1[v]), None)
        if w is None: return None
        img[v] = w
    if len(set(img)) != n: return None
    return img if is_aut(n, adj, img, chi) else None

def harvest_from(n, adj, chi, anchor, firsts):
    """One anchor's harvest: returns dict rj -> perm|None  (None = FAILED)."""
    d = deepen(n, adj, firsts[anchor])
    if d is None: return {}
    chi1, seq = d
    K = coupled(n, chi, chi1)
    if not K or any(sum(1 for u in range(n) if chi1[u] == chi1[v]) != 1 for v in K):
        return {}
    out = {}
    for rj, cj in firsts.items():
        if rj == anchor: continue
        dj = replay(n, adj, cj, seq)
        out[rj] = None if dj is None else twist_of(n, adj, chi, chi1, K, dj)
    return out

# ───────────────────────────────────────────── AmenablePath ("certified below")
def amenable_path(n, adj, col, oracle_cap=200000):
    """Walk deepen's path from `col`; at each level test whether the CHOSEN CELL is a
    single orbit of Aut(adj, cur).  Returns (levels, all_certified, first_bad_level)."""
    cur = list(col); levels = 0; bad = None
    for _ in range(n + 1):
        cid, C = target_cell(n, cur)
        if cid is None: return levels, (bad is None), bad
        op = orbit_partition(n, adj, cur, C)
        if op is None: return levels, None, None          # oracle blew up
        if len(set(op.values())) > 1 and bad is None: bad = levels
        levels += 1
        cur = refine(n, adj, indiv(n, cur, min(C)))
    return levels, False, bad

# ───────────────────────────────────────────────────────────────── the measurement
def measure(name, n, adj, leafcap=200000, verbose=True):
    t0 = time.time()
    chi = refine(n, adj, [0] * n)
    cid, C = target_cell(n, chi)
    if cid is None:
        print(f"{name:34s} n={n:4d}  DISCRETE at root — no branch cell"); return None

    true_blk = orbit_partition(n, adj, chi, C)
    if true_blk is None:
        print(f"{name:34s} n={n:4d}  |C|={len(C)}  ORACLE CAPPED"); return None
    ntrue = len(set(true_blk.values()))

    firsts = {r: refine(n, adj, indiv(n, chi, r)) for r in C}

    # ---- SINGLE anchor (the C# HarvestTwists) --------------------------------
    a0 = min(C)
    h0 = harvest_from(n, adj, chi, a0, firsts)
    fn_single = [rj for rj in C if rj != a0
                 and true_blk[rj] == true_blk[a0] and h0.get(rj) is None]
    same0 = [rj for rj in C if rj != a0 and true_blk[rj] == true_blk[a0]]

    # ---- ALL anchors (the Lean deepenGens) -----------------------------------
    par = {v: v for v in C}
    def find(x):
        while par[x] != x: par[x] = par[par[x]]; x = par[x]
        return x
    gens = []
    for a in C:
        for rj, t in harvest_from(n, adj, chi, a, firsts).items():
            if t is not None:
                gens.append(t)
                ra, rb = find(a), find(rj)
                if ra != rb: par[ra] = rb
    # close the emitted relation under the group the gens generate (restricted to C)
    changed = True
    while changed:
        changed = False
        for g in gens:
            for v in C:
                if g[v] in par and find(v) != find(g[v]):
                    par[find(v)] = find(g[v]); changed = True
    nharv = len(set(find(v) for v in C))
    fn_all = sum(1 for i, a in enumerate(C) for b in C[i+1:]
                 if true_blk[a] == true_blk[b] and find(a) != find(b))
    fp_all = sum(1 for i, a in enumerate(C) for b in C[i+1:]
                 if true_blk[a] != true_blk[b] and find(a) == find(b))

    # ---- certification (AmenablePath) per anchor ------------------------------
    lv, cert = [], []
    for a in C[:min(len(C), 8)]:
        L, ok, bad = amenable_path(n, adj, firsts[a])
        lv.append(L); cert.append(ok)
    ncert = sum(1 for x in cert if x is True)

    if verbose:
        print(f"{name:34s} n={n:4d} |C|={len(C):3d} | true-orb={ntrue:3d} harv-orb={nharv:3d} "
              f"| FN(all)={fn_all:4d} FP={fp_all:2d} | anchor0: same-orb={len(same0):3d} "
              f"FN={len(fn_single):3d} | levels={lv[:6]} certified={ncert}/{len(cert)} "
              f"| {time.time()-t0:5.1f}s")
    return dict(name=name, n=n, C=len(C), ntrue=ntrue, nharv=nharv, fn_all=fn_all,
                fp_all=fp_all, fn_single=len(fn_single), same0=len(same0),
                levels=lv, ncert=ncert, ncheck=len(cert))

# ───────────────────────────────────────────────────────── extra witness families
def disjoint(gs):
    tot = sum(g[0] for g in gs); adj = [[0]*tot for _ in range(tot)]; off = 0
    for n_, a_ in gs:
        for i in range(n_):
            for j in range(n_): adj[off+i][off+j] = a_[i][j]
        off += n_
    return tot, adj

def cycle(m):
    return m, [[1 if (i-j) % m in (1, m-1) else 0 for j in range(m)] for i in range(m)]

def rook44():
    vs = [(i, j) for i in range(4) for j in range(4)]
    n = 16
    a = [[1 if (vs[i][0]==vs[j][0]) != (vs[i][1]==vs[j][1]) else 0 for j in range(n)]
         for i in range(n)]
    for i in range(n): a[i][i] = 0
    return n, a

def shrikhande():
    vs = [(i, j) for i in range(4) for j in range(4)]
    S = {(1,0),(3,0),(0,1),(0,3),(1,1),(3,3)}
    n = 16
    a = [[1 if ((vs[j][0]-vs[i][0]) % 4, (vs[j][1]-vs[i][1]) % 4) in S else 0
          for j in range(n)] for i in range(n)]
    return n, a


if __name__ == "__main__":
    print("=" * 150)
    print("PERFECT-ORBIT-ORACLE PROBE.  FN = same true orbit but harvest leaves them separate")
    print("  FN(all)   : false negatives of the ALL-ANCHOR harvest (the Lean deepenGens)")
    print("  anchor0 FN: false negatives of the SINGLE-ANCHOR harvest (the C# HarvestTwists)")
    print("  levels    : deepening levels per anchor (0 ==> certification is VACUOUS, AKRV rigid collapse)")
    print("=" * 150)

    print("\n### A. cells that provably are NOT orbits (WL-equal, non-isomorphic components)")
    measure("C3 + C4", *disjoint([cycle(3), cycle(4)]))
    measure("C3 + C4 + C5", *disjoint([cycle(3), cycle(4), cycle(5)]))
    measure("C4 + C5", *disjoint([cycle(4), cycle(5)]))
    measure("C3 + C3 + C4", *disjoint([cycle(3), cycle(3), cycle(4)]))
    measure("Shrikhande + Rook(4,4)", *disjoint([shrikhande(), rook44()]))

    print("\n### B. the recorded gauge / multipede / CFI witnesses")
    measure("mp7 = Fano multipede", *build_mp(FANO))
    measure("MIXED multipede", *build_mp(MIXED))
    measure("circ(5) multipede", *build_mp(circ(5)))
    measure("CFI over C5 plain", *build_cfi(5))
    measure("CFI over C5 twisted", *build_cfi(5, True))

    print("\n### C. rigid multipedes (AKRV: certification here must be VACUOUS or fail)")
    for (V, W, deg, seed) in [(6, 5, 3, 1), (8, 6, 3, 2), (10, 7, 3, 3), (12, 8, 3, 4)]:
        A = rand_incidence(V, W, deg, seed)
        n, adj = build_mp(A)
        measure(f"rand multipede V={V} W={W}", n, adj)

    print("\n### D. CFI over random cubic bases (WL-hard, substantive levels)")
    for m in (8, 10):
        es = cubic(m, 11 + m)
        for tw in (False, True):
            n, adj = build_cfi_base(es, m, tw)
            measure(f"CFI cubic m={m} {'tw' if tw else 'pl'}", n, adj)


# ═══════════════════════════════════════════════════════════════════════════════
# FUSION SWEEP — measure the harvest at EVERY node of a descent path, not just the
# root.  Fusion (user, 2026-07-27; Chang-A) = a genuinely same-orbit pair the harvest
# cannot consume because the symmetry is only exposed AFTER a rigid decision below.
# ═══════════════════════════════════════════════════════════════════════════════
def johnson(nn, k):
    sets = [m for m in range(1 << nn) if bin(m).count('1') == k]
    N = len(sets)
    a = [[0]*N for _ in range(N)]
    for u in range(N):
        for v in range(u+1, N):
            if bin(sets[u] & sets[v]).count('1') == k-1: a[u][v] = a[v][u] = 1
    return N, a, sets

def seidel_switch(N, adj, S):
    b = [r[:] for r in adj]
    for u in range(N):
        for v in range(u+1, N):
            if (u in S) != (v in S): b[u][v] = b[v][u] = 1 - b[u][v]
    return b

def chang(which):
    N, a, sets = johnson(8, 2)
    idx = {m: i for i, m in enumerate(sets)}
    E = {'A': [(0,1),(2,3),(4,5),(6,7)],
         'B': [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,0)],
         'C': [(0,1),(1,2),(2,0),(3,4),(4,5),(5,3)]}[which]
    S = {idx[(1 << x) | (1 << y)] for x, y in E}
    return N, seidel_switch(N, a, S)

def node_sweep(name, n, adj, maxnodes=40, verbose=True):
    """Walk deepen's own path (lowest-id cell, lowest-index member) and measure the
    harvest's false negatives at EVERY node.  Reports the first fusion hit."""
    chi = refine(n, adj, [0]*n)
    rows = []
    for depth in range(maxnodes):
        cid, C = target_cell(n, chi)
        if cid is None: break
        true_blk = orbit_partition(n, adj, chi, C)
        if true_blk is None:
            rows.append((depth, len(C), None, None, None, None)); break
        ntrue = len(set(true_blk.values()))
        firsts = {r: refine(n, adj, indiv(n, chi, r)) for r in C}
        a0 = min(C)
        h0 = harvest_from(n, adj, chi, a0, firsts)
        fn_s = sum(1 for rj in C if rj != a0 and true_blk[rj] == true_blk[a0]
                   and h0.get(rj) is None)
        par = {v: v for v in C}
        def find(x):
            while par[x] != x: par[x] = par[par[x]]; x = par[x]
            return x
        gens = []
        for a in C:
            for rj, t in harvest_from(n, adj, chi, a, firsts).items():
                if t is not None:
                    gens.append(t)
                    ra, rb = find(a), find(rj)
                    if ra != rb: par[ra] = rb
        ch = True                       # group closure = C# CoveredByPathFixingAut
        while ch:
            ch = False
            for g in gens:
                for v in C:
                    if find(v) != find(g[v]): par[find(v)] = find(g[v]); ch = True
        nh = len(set(find(v) for v in C))
        fn_a = sum(1 for i, x in enumerate(C) for y in C[i+1:]
                   if true_blk[x] == true_blk[y] and find(x) != find(y))
        fp_a = sum(1 for i, x in enumerate(C) for y in C[i+1:]
                   if true_blk[x] != true_blk[y] and find(x) == find(y))
        rows.append((depth, len(C), ntrue, nh, fn_a, fn_s, fp_a))
        chi = refine(n, adj, indiv(n, chi, a0))
    if verbose:
        bad = [r for r in rows if r[4]]
        print(f"\n--- {name}  n={n} ---")
        for r in rows:
            mark = "  <== FUSION (same orbit, harvest split)" if r[4] else ""
            print(f"   depth {r[0]:2d}: |C|={r[1]:3d} true-orb={r[2]} harv-orb={r[3]} "
                  f"FN(all)={r[4]} FN(anchor0)={r[5]} FP={r[6]}{mark}")
        print(f"   => nodes with FN(all)>0: {len(bad)} / {len(rows)}")
    return rows
