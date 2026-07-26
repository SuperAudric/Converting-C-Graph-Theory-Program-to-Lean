#!/usr/bin/env python3
"""
THE USER'S ALGORITHM, IMPLEMENTED EXACTLY.

A cell of size > 1 is either
  - a SINGLE ORBIT  -> consume: individualize any member, FREE (branch factor 1); or
  - MIXED ORBIT     -> split it into its orbit blocks and REFINE.  No branch.
Repeat.  Cells never merge, so this is monotone; at discreteness we are done.

Blocks are ordered by the canonical form of the rooted graph (the recursive cert).
Two blocks CANNOT tie: cert(a) = cert(b)  <=>  (adj, chi+a) iso (adj, chi+b)  <=>  a,b
same orbit -- so a tie would contradict them being different blocks.  Hence the split
ALWAYS succeeds: there is no third outcome, exactly as claimed.

So the mechanism has no gap.  What this probe measures is the only thing left: COST.
  - splits          : how many mixed cells were split
  - free steps      : how many consume individualizations (branch factor 1)
  - recursive calls : total canon_split invocations  <- the real cost
  - max nesting     : deepest chain of mixed cells (recursion depth)
  - blocks-tied     : must be 0
  - invariance      : canonical form equal under relabelling
"""
import sys, random
from collections import defaultdict
sys.setrecursionlimit(20000)

from probe_dualdeepen import (circ, FANO, MIXED, rand_incidence, build_mp,
                              build_cfi_base, cubic, relabel, Ctx, canon)
from probe_polyloop import adjlist, refine, indiv, target_cell


def orbit_map(n, adj, col):
    """Aut(adj,col)-orbit map.  (Idealisation of the deepen harvest, which
    probe_verdict_invariance measured EXACT 18/18 at certified-below nodes.)"""
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


class St:
    def __init__(self):
        self.calls = 0; self.splits = 0; self.free = 0
        self.maxdepth = 0; self.tied = 0; self.blocksizes = []


def canon_split(n, adj, adjl, col, st, depth=0):
    st.calls += 1
    st.maxdepth = max(st.maxdepth, depth)
    col = refine(n, adjl, col)
    for _ in range(2 * n + 4):
        cid, C = target_cell(n, col)
        if cid is None:
            lab = [0] * n
            for v in range(n): lab[col[v]] = v
            return tuple(adj[lab[i]][lab[j]] for i in range(n) for j in range(i + 1, n))
        orb = orbit_map(n, adj, col)
        blocks = defaultdict(list)
        for v in C: blocks[orb[v]].append(v)
        if len(blocks) == 1:
            st.free += 1
            col = indiv(n, adjl, col, min(C))            # FREE: cell is one orbit
            continue
        # ---- MIXED CELL: split, do not branch
        st.splits += 1; st.blocksizes.append(len(blocks))
        certs = []
        for B in blocks.values():
            c = canon_split(n, adj, adjl, indiv(n, adjl, col, min(B)), st, depth + 1)
            certs.append((c, sorted(B)))
        if len({c for c, _ in certs}) != len(certs):
            st.tied += 1                                  # must never happen
        certs.sort()
        rank = {}
        for i, (_, B) in enumerate(certs):
            for v in B: rank[v] = i
        sig = [(col[u], rank.get(u, -1)) for u in range(n)]
        rk = {s: i for i, s in enumerate(sorted(set(sig)))}
        col = refine(n, adjl, [rk[sig[u]] for u in range(n)])
    return None


def run(name, n, adj, trials=2):
    adjl = adjlist(n, adj)
    st = St()
    c0 = canon_split(n, adj, adjl, [0] * n, st)
    ok = True
    rnd = random.Random(3)
    for _ in range(trials):
        s = list(range(n)); rnd.shuffle(s)
        a2 = relabel(n, adj, s)
        st2 = St()
        if canon_split(n, a2, adjlist(n, a2), [0] * n, st2) != c0: ok = False
    print(f"  {name:<30} n={n:<4} calls={st.calls:<5} splits={st.splits:<3} "
          f"free={st.free:<3} max-nesting={st.maxdepth:<2} blocks/split={st.blocksizes} "
          f"tied={st.tied}  ①={'OK' if ok else 'FAIL'}")
    return st


if __name__ == "__main__":
    print("User's algorithm: consume single-orbit cells, SPLIT mixed cells. No branching.\n")
    print("### rigid multipedes")
    for (V, W, deg, seed) in [(6, 5, 3, 1), (8, 6, 3, 2), (10, 7, 3, 3),
                              (12, 8, 3, 4), (14, 9, 3, 5), (16, 10, 3, 6)]:
        n, adj = build_mp(rand_incidence(V, W, deg, seed))
        run(f"rand multipede V={V} W={W}", n, adj)
    print("\n### mixed / gauge")
    run("MIXED multipede", *build_mp(MIXED))
    run("circ(5) multipede", *build_mp(circ(5)))
    run("mp7 Fano multipede", *build_mp(FANO))
    print("\n### CFI cubic (WL-hard)")
    for m in (8, 10, 12, 14):
        n, adj = build_cfi_base(cubic(m, 11 + m), m, False)
        run(f"CFI cubic m={m}", n, adj)
