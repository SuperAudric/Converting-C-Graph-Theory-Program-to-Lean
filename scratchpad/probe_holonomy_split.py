#!/usr/bin/env python3
"""
probe_holonomy_split.py — 2026-08-11.  THE SPLITTER, not the symmetry detector.

============================================================================================
WHY — the soundness direction is INVERTED relative to consume, and that is the whole point
============================================================================================
`chain-descent-divergence-lift.md` measured the descent-comparison as a *symmetry detector*
and as a source of a *direction* opinion.  Both fail:  §4.1 fires on a one-orbit pair
(97/200), §4.2 flips under one mixed pick, §4.3 reaches a leaf with a matching comparison and
a non-automorphic map (`NOAUT`).

This probe measures the SAME computation used the OTHER way round.  Define, on a cell `C`:

    u ~_d w   :=   the depth-`d` matched-descent FOOTPRINT SETS of u and w INTERSECT

where a footprint is the sequence of (target cell id, canonical 1-WL signature) produced by
individualizing u and then making d further picks.

  ★ SOUNDNESS (a proof, not a hope).  If sigma is a colour-automorphism with sigma(u) = w then
    sigma maps every descent from u to a descent from w with an IDENTICAL footprint (signatures
    are permutation-invariant).  Hence

              SameOrbit  ⊆  ~_d     for every d.

    So  ¬(u ~_d w)  ⟹  u and w are in DIFFERENT ORBITS — a sound negative — and the classes of
    ~_d are a sound COARSENING of the orbit partition.  Over-merging is HARMLESS here.

  ⟹ `NOAUT` (divergence-lift §4.3), which is fatal for a symmetry detector, is FREE for a
    splitter.  Consume must never over-merge; the splitter must never over-SPLIT, and the
    exhaustive relation provably cannot.

WHAT IS MEASURED (per root cell, against EXACT colour-preserving Aut — clean-room, no oracle):

  S  SOUNDNESS      is every Aut-orbit inside one ~_d class?   MUST hold; a violation is a bug.
  N  NON-VACUITY    does ~_d have more than one class, i.e. does it SPLIT the cell at all?
  E  EXACTNESS      does ~_d equal the orbit partition?
  P  THE CAO PRICE  the SINGLE-PATH variant (one pick per level) is what the design computes if
                    2-WL CAO propagation is assumed.  It is NOT sound a priori.  Count the
                    over-splits — those are exactly the pairs where the CAO hypothesis is doing
                    load-bearing work.
  D  CERTIFIED DEPTH  on a single-path descent, the depth of the FIRST mixed-orbit target cell
                    (divergence-lift §9 item 1 — the one remaining measurable question there).

FALSIFIERS
  * S fails            -> the soundness argument or this code is wrong.  Stop.
  * N is 1 everywhere  -> the relation is vacuous at every reachable depth; the splitter has
                          nothing to deliver and the design dies here (the `Linked` outcome).
  * P is 0 everywhere  -> the CAO hypothesis is not load-bearing on these witnesses, i.e. they
                          do not pose the question (see divergence-lift §6, three vacuous probe
                          generations).  Need a habitat where it IS non-zero.

    cd /workspace/scratchpad && python3 -u probe_holonomy_split.py > probe_holonomy_split.out 2>&1
"""
import sys
import itertools
from collections import defaultdict

sys.setrecursionlimit(10000)
sys.path.insert(0, '/workspace/scratchpad')

from probe_dir_flip import (refine, indiv, signature, cells, target, all_auts, orbits_of,
                            net, shrikhande, t8_chang, disjoint)


# ------------------------------------------------------------------ extra witnesses
def rook4():
    """4x4 rook = L(K_{4,4}); SRG(16,6,2,2), the Shrikhande partner."""
    n = 16
    adj = [[] for _ in range(n)]
    idx = lambda x, y: 4 * x + y
    for x in range(4):
        for y in range(4):
            for z in range(4):
                if z != y:
                    adj[idx(x, y)].append(idx(x, z))
                if z != x:
                    adj[idx(x, y)].append(idx(z, y))
    return n, [sorted(set(a)) for a in adj]


def cfi(base_edges, m, twist=()):
    """Standard CFI over a base with `m` vertices.  Gadget of v = even subsets of the
    incident-edge set; wire of e = two vertices e^0, e^1; gadget vertex S ~ e^{[e in S]}.
    `twist` = a set of base-edge indices whose wire labels are swapped."""
    inc = defaultdict(list)
    for i, (a, b) in enumerate(base_edges):
        inc[a].append(i)
        inc[b].append(i)
    verts, gad = [], {}
    for v in range(m):
        es = inc[v]
        for r in range(0, len(es) + 1, 2):
            for S in itertools.combinations(es, r):
                gad.setdefault(v, []).append(len(verts))
                verts.append(('g', v, frozenset(S)))
    wire = {}
    for i in range(len(base_edges)):
        wire[i] = (len(verts), len(verts) + 1)
        verts += [('w', i, 0), ('w', i, 1)]
    n = len(verts)
    adj = [[] for _ in range(n)]

    def E(a, b):
        adj[a].append(b)
        adj[b].append(a)

    for k, t in enumerate(verts):
        if t[0] != 'g':
            continue
        _, v, S = t
        for e in inc[v]:
            bit = 1 if e in S else 0
            if e in twist and v == base_edges[e][1]:
                bit ^= 1
            E(k, wire[e][bit])
    return n, [sorted(a) for a in adj]


# ------------------------------------------------------------------ footprints
def footprint_set(n, adj, col, u, depth, cap=200000):
    """All depth-`depth` matched-descent footprints reachable from individualizing `u`.
    Footprint = ((cid_0, sig_0), (cid_1, sig_1), ...) — every entry canonical."""
    start = refine(n, adj, indiv(n, col, u))
    out = set()

    def rec(c, fp, d):
        if len(out) >= cap:
            return
        cid, cell = target(c)
        if d == 0 or cid is None:
            out.add(fp)
            return
        for b in cell:
            c2 = refine(n, adj, indiv(n, c, b))
            rec(c2, fp + ((cid, signature(c2)),), d - 1)

    rec(start, ((-1, signature(start)),), depth)
    return out


def single_path_footprint(n, adj, col, u, depth):
    """The design's cheap read: ONE pick per level (min index).  Equals the exhaustive
    read under CAO propagation, and is what the object would actually compute."""
    c = refine(n, adj, indiv(n, col, u))
    fp = [(-1, signature(c))]
    for _ in range(depth):
        cid, cell = target(c)
        if cid is None:
            break
        c = refine(n, adj, indiv(n, c, min(cell)))
        fp.append((cid, signature(c)))
    return tuple(fp)


def certified_footprint_set(n, adj, col, u, depth, incap=5000):
    """★ THE DESIGN ITSELF (L1/L2).  Branch over the whole cell ONLY at levels whose target
    cell is genuinely MIXED; take a single pick at levels certified single-orbit.

    Soundness of the collapse: at a single-orbit level all picks are Aut-related, so they
    yield the SAME footprint set — the level costs 1 instead of |cell| with no loss.  That
    collapse is exactly what 2-WL CAO propagation asserts holds at EVERY level.

    ⚠ The single-orbit test here uses a CAPPED exact enumeration, so it can under-report
    automorphisms and call a single-orbit level "mixed".  That is CONSERVATIVE — it branches
    more than necessary and cannot make the result unsound.

    Returns (footprint set, #refine calls, #levels that had to branch)."""
    start = refine(n, adj, indiv(n, col, u))
    out, stat = set(), [0, 0]

    def rec(c, fp, d):
        cid, cell = target(c)
        if d == 0 or cid is None:
            out.add(fp)
            return
        orb = orbits_of(n, all_auts(n, adj, c, cap=incap))
        mixed = len({orb[x] for x in cell}) > 1
        if mixed:
            stat[1] += 1
        for b in (cell if mixed else [min(cell)]):
            c2 = refine(n, adj, indiv(n, c, b))
            stat[0] += 1
            rec(c2, fp + ((cid, signature(c2)),), d - 1)

    rec(start, ((-1, signature(start)),), depth)
    return out, stat[0], stat[1]


def partition_from(pairs, elems):
    """union-find -> list of frozensets"""
    p = {v: v for v in elems}

    def f(x):
        while p[x] != x:
            p[x] = p[p[x]]
            x = p[x]
        return x

    for a, b in pairs:
        ra, rb = f(a), f(b)
        if ra != rb:
            p[ra] = rb
    d = defaultdict(set)
    for v in elems:
        d[f(v)].add(v)
    return sorted((frozenset(s) for s in d.values()), key=lambda s: (len(s), sorted(s)))


def refines(fine, coarse):
    """every block of `fine` is contained in some block of `coarse`"""
    return all(any(b <= c for c in coarse) for b in fine)


# ------------------------------------------------------------------ certified depth
def certified_depth(n, adj, col, maxdepth=6, cap=200000):
    """Walk the min-pick descent; at each level ask whether the TARGET CELL is a single
    orbit of the node stabiliser.  Return (depth of first mixed target cell, levels walked).
    `None` = never mixed within maxdepth (the Tinhofer-path case)."""
    c = list(col)
    for d in range(maxdepth):
        cid, cell = target(c)
        if cid is None:
            return None, d
        auts = all_auts(n, adj, c, cap=cap)
        orb = orbits_of(n, auts)
        if len({orb[x] for x in cell}) > 1:
            return d, d
        c = refine(n, adj, indiv(n, c, min(cell)))
    return None, maxdepth


# ------------------------------------------------------------------ report
def run(name, n, adj, depths=(1, 2), maxcell=40, autcap=400000):
    print('=' * 92)
    print(f'{name}   n = {n}')
    root = refine(n, adj, [0] * n)
    cs = cells(root)
    ns = [c for c in sorted(cs) if len(cs[c]) > 1]
    if not ns:
        print('  1-WL DISCRETE at the root — no cell to split, nothing to measure.')
        return
    auts = all_auts(n, adj, root, cap=autcap)
    orb = orbits_of(n, auts)
    print(f'  root cells: {[len(cs[c]) for c in sorted(cs) if len(cs[c])>1]}   '
          f'|Aut_chi| enumerated = {len(auts)}{"  (CAPPED)" if len(auts)>=autcap else ""}')

    dfirst, walked = certified_depth(n, adj, root, cap=autcap)
    print(f'  D  certified depth: first MIXED target cell at depth '
          f'{"none within " + str(walked) if dfirst is None else dfirst}')

    for cid in ns:
        C = cs[cid]
        if len(C) > maxcell:
            print(f'  cell {cid} (size {len(C)}) SKIPPED (> maxcell)')
            continue
        true_part = partition_from([(u, v) for u in C for v in C if orb[u] == orb[v]], C)
        print(f'  cell {cid}: size {len(C)}   Aut-orbit blocks = {[len(b) for b in true_part]}')

        for d in depths:
            fps = {u: footprint_set(n, adj, root, u, d) for u in C}
            pairs = [(u, v) for u in C for v in C if fps[u] & fps[v]]
            part = partition_from(pairs, C)
            sound = refines(true_part, part)
            exact = part == true_part
            print(f'    ~_{d}  classes = {str([len(b) for b in part]):<28} '
                  f'S={"ok" if sound else "**VIOLATION**":<15} '
                  f'N={"splits" if len(part) > 1 else "vacuous":<8} '
                  f'E={"exact" if exact else "coarser"}')

            cert = {}
            ccost = cbranch = 0
            for u in C:
                s, rc, br = certified_footprint_set(n, adj, root, u, d)
                cert[u] = s
                ccost += rc
                cbranch += br
            cpairs = [(u, v) for u in C for v in C if cert[u] & cert[v]]
            cpart = partition_from(cpairs, C)
            print(f'    C_{d}  certified-path classes = {str([len(b) for b in cpart]):<15} '
                  f'S={"ok" if refines(true_part, cpart) else "**OVER-SPLIT**":<15} '
                  f'{"MATCHES ~_%d" % d if cpart == part else "DIFFERS from ~_%d" % d}   '
                  f'refines={ccost} branchlevels={cbranch}')

            sp = {u: single_path_footprint(n, adj, root, u, d) for u in C}
            sppairs = [(u, v) for u in C for v in C if sp[u] == sp[v]]
            sppart = partition_from(sppairs, C)
            spsound = refines(true_part, sppart)
            over = sum(1 for u in C for v in C
                       if u < v and orb[u] == orb[v] and sp[u] != sp[v])
            print(f'    ^_{d}  single-path classes = {str([len(b) for b in sppart]):<15} '
                  f'S={"ok" if spsound else "**OVER-SPLIT**":<15} '
                  f'P={over} same-orbit pairs separated')


def main():
    n, a = t8_chang([tuple(sorted((i, (i + 1) % 8))) for i in range(8)])
    run('Chang-2  (C8 switching of T(8)) — divergence-lift §4.2 habitat', n, a)

    n1, a1 = rook4()
    n2, a2 = shrikhande()
    n, a = disjoint(n1, a1, n2, a2)
    run('rook4x4 ⊔ Shrikhande — the NOAUT habitat (§4.3)', n, a)

    n, a = shrikhande()
    run('Shrikhande', n, a)

    n, a = net(4, 'Z')
    run('net(Z4)', n, a)

    n, a = net(4, 'V')
    run('net(Z2xZ2)', n, a)

    K4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    n, a = cfi(K4, 4)
    run('CFI(K4) untwisted', n, a, autcap=200000)
    n, a = cfi(K4, 4, twist={0})
    run('CFI(K4) twisted', n, a, autcap=200000)


if __name__ == '__main__':
    main()
