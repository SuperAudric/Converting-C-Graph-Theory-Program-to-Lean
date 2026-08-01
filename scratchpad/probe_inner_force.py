#!/usr/bin/env python3
"""
THE PROPOSAL, IMPLEMENTED EXACTLY:  run FORCE *inside* the CONSUME descent.

Today (`DeepenSupply.deepen` / `replay`, ported in probe_polyloop):
    anchor r1 : individualize, refine, then repeatedly individualize the LOWEST-INDEX member of
                the lowest-id non-singleton cell, to discreteness, recording the cell-id sequence.
    rep    rj : replay the SAME id sequence, again picking the lowest-index member.
    twist     : colour-match the two leaves on the coupled component; verify IsColAut.
MEASURED FAILURE MECHANISM (memory / DUAL §2): the two descents stay aligned through every
single-orbit cell and DIVERGE at the first MIXED cell, where the lowest-index picks land in
non-corresponding orbits.  The twist then isn't an automorphism -> consume fails.

THE PROPOSAL: before picking, run the force resolver on that cell.  If an equivariant key splits
it, REFINE by the key (the cell shrinks, no branching) and continue; only individualize when the
key ties the whole cell.  Claim: then consume cannot fail.

E-A  REPAIR TEST      : at the recorded consume-failure nodes, does the interleaved harvest
                        certify what the greedy harvest could not?
E-B  PREMISE TEST     : is there a node where the target cell is GENUINELY MIXED (>= 2 true
                        Aut-orbits) and NO equivariant key fires?  That is the exact point where
                        "force must fire somewhere on the descent" stops being a contradiction.
                        Key ladder (⚠ NOT a total order — measured incomparable, see below):
                                    K1 = Force.lookaheadKey (1-WL cell-size histogram)
                                    K2 = full 1-WL lookahead colour signature (refines K1)
                                    K3 = 2-WL lookahead pair-colour histogram (raises the WL
                                         dimension but AGGREGATES, so it does NOT refine K2)
                        ⚠⚠ MEASURED (CFI cubic m=8 pl, the |C|=16 single-orbit node): interleaving
                        repairs consume under K2 but NOT under K1 and NOT under K3.  Repair is
                        key-SPECIFIC and non-monotone in WL dimension — a key that fires more
                        eagerly at other levels changes the path and can miss the crucial split.
E-C  SCHURIAN START   : is the root colouring Schurian (every cell one orbit)?  The proposal
                        assumes it; a stall at a NON-Schurian root is out of scope, a stall
                        reached from a Schurian root is IN scope and is the real verdict.
"""
import sys, time
from collections import defaultdict, Counter

sys.setrecursionlimit(20000)
sys.path.insert(0, "/workspace/scratchpad")

from probe_dualdeepen import (circ, FANO, MIXED, rand_incidence, build_mp, build_cfi_base,
                              cubic, is_aut, Ctx, canon)
from probe_polyloop import adjlist, refine, indiv, target_cell, cellsof, twist, transitive_on
from probe_cao_2wl import twowl_fast

# ---------------------------------------------------------------- exact orbits (cert classes)
def cert_of(n, adj, col, leafcap=120000):
    ctx = Ctx(n, adj, prune=True, leafcap=leafcap)
    r = canon(ctx, list(col), [], root=True)
    if ctx.blown or r is None:
        return None
    return r[0]

def true_orbits(n, adj, adjl, col, C, leafcap=120000):
    """Exact Aut(adj,col)-orbit partition of the TARGET cell C, in ONE canonical-form run:
    canon's per-representative certs on the root target cell ARE its orbit classes (pruned
    representatives are covered by a VERIFIED automorphism, so they join an explored class).
    `col` must already be 1-WL refined, so canon's own target_cell is this same C."""
    ctx = Ctx(n, adj, prune=True, leafcap=leafcap)
    canon(ctx, list(col), [], root=True)
    if ctx.blown or ctx.root is None:
        return None
    Croot, percert, _ = ctx.root
    if sorted(Croot) != sorted(C):
        return None
    klass = defaultdict(list)
    for v, c in percert.items():
        klass[c].append(v)
    return list(klass.values())

def root_is_schurian(n, adj, adjl, col, leafcap=120000):
    """SOUND positive test: run the full canonical search once and take the VERIFIED
    automorphisms it collects at the root; if they are transitive on every cell then every
    cell is a single orbit (subgroup orbits ⊆ true orbits ⊆ cells).  Returns
    True / False(=inconclusive-or-mixed) plus the per-cell subgroup-orbit counts."""
    ctx = Ctx(n, adj, prune=True, leafcap=leafcap)
    canon(ctx, list(col), [], root=True)
    gens = [g for (g, gp) in ctx.gens if gp == ()]
    par = list(range(n))
    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]; x = par[x]
        return x
    for g in gens:
        for i in range(n):
            a, b = f(i), f(g[i])
            if a != b:
                par[a] = b
    prof = []
    for cid, C in sorted(cellsof(n, col).items()):
        if len(C) < 2:
            continue
        prof.append((len(C), len({f(v) for v in C})))
    return all(k == 1 for _, k in prof), prof

# ---------------------------------------------------------------- the key ladder (equivariant)
def K1(n, adj, adjl, col, v):
    """Force.lookaheadKey — individualize, 1-WL refine, cell-size histogram."""
    c = indiv(n, adjl, col, v)
    return tuple(sorted(Counter(c).values()))

def K2(n, adj, adjl, col, v):
    """Refines K1: the full sorted 1-WL colour signature after individualization."""
    c = indiv(n, adjl, col, v)
    return (tuple(sorted(Counter(c).values())),
            tuple(sorted((c[u], tuple(sorted(c[w] for w in adjl[u]))) for u in range(n))))

def twowl_canon(n, adj, vcol, rounds=None):
    """Oblivious 2-WL with CANONICAL colour numbering (ranks assigned by SORTING the keys, not by
    insertion order).  ⚠ `probe_cao_2wl.twowl_fast` ranks in insertion order, which is NOT
    isomorphism-invariant — reading it as an equivariant key makes it fire on single-orbit cells
    (caught by this probe's own true-orbit cross-check).  Returns the pair-colouring."""
    keys = [(0 if u == v else 1, adj[u][v], vcol[u], vcol[v]) for u in range(n) for v in range(n)]
    rank = {s: i for i, s in enumerate(sorted(set(keys)))}
    col = [rank[k] for k in keys]
    for _ in range(rounds or n * n):
        newkeys = []
        for u in range(n):
            un = u * n
            for v in range(n):
                s = sorted((col[un + w], col[w * n + v]) for w in range(n))
                newkeys.append((col[un + v], tuple(s)))
        rank = {s: i for i, s in enumerate(sorted(set(newkeys)))}
        new = [rank[k] for k in newkeys]
        if len(set(new)) == len(set(col)):
            return col
        col = new
    return col

def K3(n, adj, adjl, col, v):
    """2-WL pair-colouring invariant after individualization.  ⚠ NOT stronger than K2: it raises the
    WL dimension but reads the result as a HISTOGRAM, so the two are incomparable — measured, K2
    repairs the m=8 node and K3 does not."""
    c = indiv(n, adjl, col, v)
    d = twowl_canon(n, adj, c, rounds=4)
    return tuple(sorted(Counter(d).items()))

KEYS = [("K1-lookahead", K1), ("K2-1WLsig", K2), ("K3-2WL", K3)]

def force_fires(n, adj, adjl, col, C, keyfn):
    ks = {v: keyfn(n, adj, adjl, col, v) for v in C}
    return ks if len(set(ks.values())) > 1 else None

def apply_split(n, adjl, col, ks):
    sig = [(col[u], ks.get(u, ())) for u in range(n)]
    rank = {s: i for i, s in enumerate(sorted(set(sig)))}
    return refine(n, adjl, [rank[sig[u]] for u in range(n)])

# ---------------------------------------------------------------- greedy vs interleaved descent
def greedy_deepen(n, adjl, col, fuel=None):
    seq = []
    for _ in range(fuel or n + 1):
        cid, C = target_cell(n, col)
        if cid is None:
            return col, seq
        seq.append(cid)
        col = indiv(n, adjl, col, min(C))
    return None, seq

def greedy_replay(n, adjl, col, seq):
    for cid in seq:
        mem = [v for v in range(n) if col[v] == cid]
        if len(mem) < 2:
            return None
        col = indiv(n, adjl, col, min(mem))
    return col

def inner_force_settle(n, adj, adjl, col, keyfn, budget=200):
    """Run force to a fixpoint on the current target cell: keep splitting while the key fires."""
    for _ in range(budget):
        cid, C = target_cell(n, col)
        if cid is None:
            return col, None, None
        ks = force_fires(n, adj, adjl, col, C, keyfn)
        if ks is None:
            return col, cid, C
        col = apply_split(n, adjl, col, ks)
    return col, None, None

def interleaved_deepen(n, adj, adjl, col, keyfn, fuel=None):
    """THE PROPOSAL. Force first (refine, no branch); individualize only when the key ties."""
    seq = []
    for _ in range(fuel or 2 * n + 2):
        col, cid, C = inner_force_settle(n, adj, adjl, col, keyfn)
        if cid is None:
            return col, seq
        seq.append(cid)
        col = indiv(n, adjl, col, min(C))
    return None, seq

def interleaved_replay(n, adj, adjl, col, seq, keyfn):
    for cid in seq:
        col, cid2, C = inner_force_settle(n, adj, adjl, col, keyfn)
        if cid2 is None:
            return None
        mem = [v for v in range(n) if col[v] == cid]
        if len(mem) < 2:
            return None
        col = indiv(n, adjl, col, min(mem))
    col, cid2, _ = inner_force_settle(n, adj, adjl, col, keyfn)
    return None if cid2 is not None else col

def harvest(n, adj, adjl, chi, C, mode, keyfn=None):
    """All-anchor harvest, greedy (mode='greedy') or with force interleaved (mode='inner')."""
    gens = []
    firsts = {r: indiv(n, adjl, chi, r) for r in C}
    for r1 in C:
        if mode == 'greedy':
            leaf1, seq = greedy_deepen(n, adjl, firsts[r1])
        else:
            leaf1, seq = interleaved_deepen(n, adj, adjl, firsts[r1], keyfn)
        if leaf1 is None:
            continue
        for rj in C:
            if rj == r1:
                continue
            if mode == 'greedy':
                leafj = greedy_replay(n, adjl, firsts[rj], seq)
            else:
                leafj = interleaved_replay(n, adj, adjl, firsts[rj], seq, keyfn)
            if leafj is None:
                continue
            t = twist(n, adj, chi, leaf1, leafj)
            if t is not None:
                gens.append(t)
    return gens

# ---------------------------------------------------------------- the run
def run(name, n, adj, keyname="K2-1WLsig", verbose=True, verify=False):
    adjl = adjlist(n, adj)
    keyfn = dict(KEYS)[keyname]
    col = refine(n, adjl, [0] * n)

    print(f"\n=== {name}  n={n}   key-in-descent={keyname}")

    depth = 0
    while depth < n:
        cid, C = target_cell(n, col)
        if cid is None:
            print(f"  depth {depth}: DISCRETE — done")
            break
        # cheap first, short-circuit: does any key fire?  (FORCE needs no orbits and no harvest)
        hit = None
        for nm, kf in KEYS:
            ks = force_fires(n, adj, adjl, col, C, kf)
            if ks is not None:
                hit = (nm, ks)
                break
        if hit is not None:
            chk = ""
            if verify:
                # an EQUIVARIANT key can never split a single-orbit cell
                # (`Force.forceBy_no_narrowing_on_orbit`) — assert the cell really is mixed.
                orb = true_orbits(n, adj, adjl, col, C)
                chk = (f"  [true-orbits={len(orb)}]" if orb is not None else "  [orbits ?]")
                if orb is not None and len(orb) == 1:
                    chk += "   <<<< SOUNDNESS BUG: key split a SINGLE-ORBIT cell"
            print(f"  depth {depth}: |C|={len(C):<3} => FORCE            key={hit[0]}{chk}")
            col = apply_split(n, adjl, col, hit[1])
            continue
        # next: does today's greedy consume certify it?
        t1 = time.time()
        ok_greedy = transitive_on(C, harvest(n, adj, adjl, col, C, 'greedy'))
        if ok_greedy:
            print(f"  depth {depth}: |C|={len(C):<3} => CONSUME (greedy) [{time.time()-t1:.0f}s]")
            col = indiv(n, adjl, col, min(C))
            depth += 1
            continue
        # ---- THE NODE THAT MATTERS: no key fires AND greedy consume fails.
        orb = true_orbits(n, adj, adjl, col, C)
        norb = '?' if orb is None else len(orb)
        print(f"  depth {depth}: |C|={len(C):<3} true-orbits={norb}  no key fires, greedy consume FAILS"
              f"  -- {'SINGLE-ORBIT: force is FORBIDDEN here, only the proposal can act' if norb == 1 else 'MIXED: force is ALLOWED here but no key fires'}")
        for nm, kf in KEYS:
            t2 = time.time()
            ok = transitive_on(C, harvest(n, adj, adjl, col, C, 'inner', kf))
            print(f"      inner-force harvest @ {nm:<14} -> {'REPAIRED  <<<<' if ok else 'still fails'} [{time.time()-t2:.0f}s]")
        col = indiv(n, adjl, col, min(C))
        depth += 1


def run_eb(name, n, adj, keyname="K2-1WLsig"):
    """E-B ONLY (no harvest): walk the interleaved loop and look for a node where the target cell
    is GENUINELY MIXED (>= 2 true Aut-orbits) yet NO equivariant key in the ladder fires.  Such a
    node is exactly where the proposal's 'force must fire somewhere on the descent' stops being a
    contradiction: the cell cannot be split (no key) and must not be picked from (mixed)."""
    adjl = adjlist(n, adj)
    col = refine(n, adjl, [0] * n)
    print(f"\n=== [E-B] {name}  n={n}")
    for depth in range(n):
        cid, C = target_cell(n, col)
        if cid is None:
            print("  DISCRETE — no mixed-cell-without-key node on this path")
            return
        hit = None
        for nm, kf in KEYS:
            ks = force_fires(n, adj, adjl, col, C, kf)
            if ks is not None:
                hit = (nm, ks); break
        if hit is not None:
            col = apply_split(n, adjl, col, hit[1])
            continue
        t = time.time()
        orb = true_orbits(n, adj, adjl, col, C)
        norb = '?' if orb is None else len(orb)
        if norb == 1:
            print(f"  depth {depth}: |C|={len(C):<3} no key fires, cell is a SINGLE ORBIT -> consume's job [{time.time()-t:.0f}s]")
        else:
            print(f"  depth {depth}: |C|={len(C):<3} no key fires, true-orbits={norb}"
                  f"   <<<< MIXED CELL, WHOLE KEY LADDER TIES IT [{time.time()-t:.0f}s]")
        col = indiv(n, adjl, col, min(C))


if __name__ == "__main__":
    t0 = time.time()
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    kn = sys.argv[2] if len(sys.argv) > 2 else "K2-1WLsig"
    if which in ("all", "cfi"):
        for m in (8,):
            for tw in (False, True):
                es = cubic(m, 11 + m)
                nn, aa = build_cfi_base(es, m, tw)
                run(f"CFI cubic m={m} {'tw' if tw else 'pl'}", nn, aa, keyname=kn)
    if which in ("all", "mp"):
        run("mp7 Fano multipede", *build_mp(FANO), keyname=kn, verify=True)
        run("MIXED multipede", *build_mp(MIXED), keyname=kn, verify=True)
        run("circ(5) multipede", *build_mp(circ(5)), keyname=kn, verify=True)
    if which == "eb":
        for m in (8, 10, 12, 14):
            for tw in (False, True):
                es = cubic(m, 11 + m)
                nn, aa = build_cfi_base(es, m, tw)
                run_eb(f"CFI cubic m={m} {'tw' if tw else 'pl'}", nn, aa)
        for (V, W, deg, seed) in [(6,5,3,1),(8,6,3,2),(10,7,3,3),(12,8,3,4),(14,9,3,5),(16,10,3,6)]:
            nn, aa = build_mp(rand_incidence(V, W, deg, seed))
            run_eb(f"rand multipede V={V} W={W}", nn, aa)
        run_eb("mp7 Fano multipede", *build_mp(FANO))
        run_eb("MIXED multipede", *build_mp(MIXED))
        run_eb("circ(5) multipede", *build_mp(circ(5)))
    if which in ("all", "rigid"):
        for (V, W, deg, seed) in [(6, 5, 3, 1), (8, 6, 3, 2)]:
            nn, aa = build_mp(rand_incidence(V, W, deg, seed))
            run(f"rand multipede V={V} W={W}", nn, aa, keyname=kn, verify=True)
    print(f"\n[{time.time()-t0:.1f}s]")
