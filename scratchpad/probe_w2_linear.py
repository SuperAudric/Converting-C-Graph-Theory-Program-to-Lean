#!/usr/bin/env python3
"""
probe_w2_linear.py — W2 item 3a (2026-08-09)

============================================================================================
THE QUESTION, restated to fit the resolver
============================================================================================
Target: *"the resolver fires SOMEWHERE on the graph when a cell is mixed due to a linear
obstruction"* (= "no stall if the residue contains a linear obstruction").

A cell fires iff `((keepMin key …).map (rep V)).dedup` has length <= 1.  Two facts pin it:
  (F1) the key is equivariant  ⟹ `keyV` is constant on Aut-orbits ⟹ keepMin is a UNION of
       Aut-orbits;
  (F2) every harvested generator is `IsColAut`-verified ⟹ H = <V> <= Aut ⟹ `rep` never merges
       across Aut-orbits, and merges INSIDE an Aut-orbit only as far as H-orbits reach.
  ⟹ FIRES  ⟺  keepMin is exactly one Aut-orbit  AND  H is transitive on it.

So there are exactly two ways to fail, and they are different problems:
  (A) no key can isolate a single Aut-orbit   — a KEY/separation failure;
  (B) H is not transitive on that Aut-orbit   — a SUPPLY/harvest failure.

This probe computes both, exactly, for CFI graphs — where the gauge H_gauge (the F2 cycle
space) is what `kernelSupply` recovers, and is the "linear" part of Aut.

============================================================================================
WHAT IS COMPUTED EXACTLY (no search, no budget)
============================================================================================
* the CFI encoding is `probe_dualdeepen.build_cfi_base` verbatim: `wire[(e,b)]` per base edge,
  `gadget[(i,bits)]` per even-parity bit-vector at base vertex i;
* the GAUGE = the F2 cycle space K = {F subset E : |F ∩ inc(i)| even for all i}.  Each F in K
  acts by swapping the two wires of every e in F and flipping the matching bit of every
  incident gadget.  ★ Every such action is VERIFIED edge-by-edge here before use, so the
  gauge-orbits are a positive certificate;
* Aut-orbits come from `Ctx`/`canon` (sound, possibly incomplete ⟹ a REFINEMENT of the truth);
* the BASE graph's own automorphism orbits on base vertices / base edges, by brute force.

★ THE DECOMPOSITION THIS BUYS.  gauge <= Aut always, so for each cell:
      #gauge-orbits  >=  #Aut-orbits.
  If they are EQUAL the cell's mixedness is entirely linear (the gauge explains everything the
  automorphism group does there).  If #Aut-orbits < #gauge-orbits, the extra merging came from
  BASE automorphisms — structure the linear layer does not see, and which no linear solver can
  supply.

    cd /workspace/scratchpad && python3 -u probe_w2_linear.py > probe_w2_linear.out 2>&1
"""
import sys
from collections import defaultdict
from itertools import product, permutations

sys.setrecursionlimit(10000)
sys.path.insert(0, '/workspace/scratchpad')

from probe_dualdeepen import build_cfi_base, cubic, Ctx, canon
from probe_polyloop import adjlist, refine, target_cell
from probe_offbranch5 import cells_of

LEAFCAP = 200000


# ---------------------------------------------------------------- the CFI encoding, re-derived

def cfi_layout(base_edges, m):
    """The same indexing `build_cfi_base` uses, returned so we can name vertices."""
    idx = 0
    wire, gadget = {}, {}
    for e in base_edges:
        wire[(e, 0)] = idx; idx += 1
        wire[(e, 1)] = idx; idx += 1
    for i in range(m):
        inc = [e for e in base_edges if i in e]
        for bits in product([0, 1], repeat=len(inc)):
            if sum(bits) % 2 == 0:
                gadget[(i, bits)] = idx; idx += 1
    return wire, gadget, idx


def cycle_space(base_edges, m):
    """F2 cycle space = even degree at every base vertex.  Returned as a list of edge-subsets."""
    E = len(base_edges)
    rows = []
    for i in range(m):
        rows.append([1 if i in e else 0 for e in base_edges])
    # null space over F2 by Gaussian elimination on the incidence matrix
    piv, mat = [], [r[:] for r in rows]
    r = 0
    for c in range(E):
        p = next((k for k in range(r, len(mat)) if mat[k][c]), None)
        if p is None:
            continue
        mat[r], mat[p] = mat[p], mat[r]
        for k in range(len(mat)):
            if k != r and mat[k][c]:
                mat[k] = [a ^ b for a, b in zip(mat[k], mat[r])]
        piv.append(c); r += 1
    free = [c for c in range(E) if c not in piv]
    basis = []
    for f in free:
        v = [0] * E
        v[f] = 1
        for ri, c in enumerate(piv):
            if mat[ri][f]:
                v[c] = 1
        basis.append(v)
    out = []
    for coeffs in product([0, 1], repeat=len(basis)):
        v = [0] * E
        for k, cf in enumerate(coeffs):
            if cf:
                v = [a ^ b for a, b in zip(v, basis[k])]
        out.append(tuple(v))
    return sorted(set(out)), len(basis)


def gauge_perm(F, base_edges, m, wire, gadget, n):
    """The permutation induced by flipping the edge set F (as a 0/1 vector over base_edges)."""
    p = list(range(n))
    for k, e in enumerate(base_edges):
        if F[k]:
            p[wire[(e, 0)]] = wire[(e, 1)]
            p[wire[(e, 1)]] = wire[(e, 0)]
    for i in range(m):
        inc = [e for e in base_edges if i in e]
        for bits in product([0, 1], repeat=len(inc)):
            if sum(bits) % 2:
                continue
            nb = tuple(b ^ F[base_edges.index(e)] for b, e in zip(bits, inc))
            p[gadget[(i, bits)]] = gadget[(i, nb)]
    return p


def is_aut(n, adj, p):
    return all(adj[u][v] == adj[p[u]][p[v]] for u in range(n) for v in range(n))


def orbits_of(n, perms):
    par = list(range(n))

    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x

    for p in perms:
        for v in range(n):
            a, b = f(v), f(p[v])
            if a != b:
                par[a] = b
    return [f(v) for v in range(n)]


def aut_gens(n, adj, col):
    ctx = Ctx(n, adj, prune=True, leafcap=LEAFCAP)
    canon(ctx, list(col), [], root=True)
    return [g for (g, p) in ctx.gens]


def base_aut_edge_orbits(base_edges, m):
    """Brute-force Aut(base) and its orbits on base EDGES (m is small)."""
    es = set(base_edges)
    gens = []
    for p in permutations(range(m)):
        if all((min(p[a], p[b]), max(p[a], p[b])) in es for (a, b) in base_edges):
            gens.append(p)
    par = {e: e for e in base_edges}

    def f(e):
        while par[e] != e:
            par[e] = par[par[e]]
            e = par[e]
        return e

    for p in gens:
        for (a, b) in base_edges:
            e2 = (min(p[a], p[b]), max(p[a], p[b]))
            x, y = f((a, b)), f(e2)
            if x != y:
                par[x] = y
    sizes = defaultdict(int)
    for e in base_edges:
        sizes[f(e)] += 1
    return len(gens), sorted(sizes.values(), reverse=True)


# ---------------------------------------------------------------- report

def run(name, base_edges, m, twist):
    n, adj = build_cfi_base(base_edges, m, twist=twist)
    wire, gadget, _ = cfi_layout(base_edges, m)
    K, beta = cycle_space(base_edges, m)

    gperms = []
    for F in K:
        p = gauge_perm(F, base_edges, m, wire, gadget, n)
        assert is_aut(n, adj, p), "gauge element is not an automorphism — encoding mismatch"
        gperms.append(p)

    adjl = adjlist(n, adj)
    col = refine(n, adjl, [0] * n)
    tid, _ = target_cell(n, col)

    gauge_cls = orbits_of(n, gperms)
    aut_cls = orbits_of(n, aut_gens(n, adj, col))

    nga, nba = base_aut_edge_orbits(base_edges, m)
    print(f"  {name}  n={n}  |E|={len(base_edges)}  beta=dim(cycle space)={beta}  |gauge|={len(K)}")
    print(f"     base graph: |Aut(base)|={nga}, edge-orbit sizes {nba}")
    for c, mem in sorted(cells_of(n, col).items()):
        g = defaultdict(int)
        a = defaultdict(int)
        for v in mem:
            g[gauge_cls[v]] += 1
            a[aut_cls[v]] += 1
        gs = sorted(g.values(), reverse=True)
        as_ = sorted(a.values(), reverse=True)
        kind = "wires" if all(v < 2 * len(base_edges) for v in mem) else "gadgets"
        linear = (len(g) == len(a))
        tag = " (TARGET)" if c == tid else ""
        print(f"     cell {c}{tag} [{kind}]: |cell|={len(mem)}")
        print(f"        gauge-orbits: {len(g)} sizes={gs}")
        print(f"        Aut-orbits  : {len(a)} sizes={as_}")
        if linear:
            print(f"        ⟹ MIXEDNESS IS ENTIRELY LINEAR (gauge explains all of Aut here)")
        else:
            print(f"        ⟹ ⛔ NOT linear: Aut merges {len(g)} gauge-orbits into {len(a)} blocks")
            print(f"           the extra merging is BASE automorphism structure, which no linear")
            print(f"           solver supplies — so even a perfect key leaves {min(as_)//max(1,min(gs))}+ reps")
        # Can the cell fire on the gauge alone?  keepMin is a union of Aut-orbits (F1) and `rep`
        # merges only within harvest-orbits (F2), so the cell fires iff SOME Aut-block is a single
        # gauge-orbit — then a key isolating that block leaves exactly one representative.
        blocks = defaultdict(set)
        for v in mem:
            blocks[aut_cls[v]].add(v)
        good = [sorted(B) for B in blocks.values() if len({gauge_cls[v] for v in B}) == 1]
        if good:
            print(f"        ⟹ ✅ {len(good)} Aut-block(s) ARE a single gauge-orbit "
                  f"(sizes {sorted((len(B) for B in good), reverse=True)}) — a key isolating one "
                  f"leaves exactly 1 rep ⟹ THE CELL CAN FIRE")
        else:
            worst = min(len(B) // len({gauge_cls[v] for v in B}) for B in blocks.values())
            print(f"        ⟹ ⛔ NO Aut-block is a single gauge-orbit — every block splits into "
                  f">= {min(len({gauge_cls[v] for v in B}) for B in blocks.values())} gauge-orbits, "
                  f"so even a PERFECT key leaves >= 2 reps ⟹ THE CELL CANNOT FIRE on the gauge "
                  f"(block/gauge ratio {worst})")
    print()


def main():
    print("W2 item 3a — is a mixed cell's mixedness LINEAR, and can the gauge fire on it?")
    print("  FIRES ⟺ keepMin is exactly one Aut-orbit ∧ the harvest is transitive on it.")
    print("  gauge <= Aut always ⟹ #gauge-orbits >= #Aut-orbits; EQUAL means the mixedness is")
    print("  entirely linear.  Every gauge element is verified edge-by-edge before use.")
    print()
    base = cubic(8, seed=8)
    run("CFI cubic m=8 pl", base, 8, False)
    run("CFI cubic m=8 tw", base, 8, True)
    print("=== a SYMMETRIC base — removes the base's own asymmetry from the picture ===")
    k4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    run("CFI over K4", k4, 4, False)
    c6 = [(i, (i + 1) % 6) for i in range(6)]
    c6 = [(min(a, b), max(a, b)) for (a, b) in c6]
    run("CFI over C6", c6, 6, False)


if __name__ == '__main__':
    main()
