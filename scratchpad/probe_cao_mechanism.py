#!/usr/bin/env python3
"""Mechanism dissection for the CFI[K4]-tw CAO-propagation counterexample."""
import sys
from collections import defaultdict
sys.path.insert(0, "/workspace/scratchpad")
from probe_cao_cleanroom import (cfi, wl, individualize, cells, all_isos, orbits,
                       orbit_colouring, is_perm_aut)

K4 = [(i, j) for i in range(4) for j in range(i + 1, 4)]


def components(n, adj):
    seen = [-1] * n
    c = 0
    for s in range(n):
        if seen[s] >= 0:
            continue
        stack = [s]
        seen[s] = c
        while stack:
            v = stack.pop()
            for u in range(n):
                if adj[v][u] and seen[u] < 0:
                    seen[u] = c
                    stack.append(u)
        c += 1
    return c, seen


def group_closed(n, A):
    S = set(A)
    idp = tuple(range(n))
    if idp not in S:
        return False, "no identity"
    import random
    rnd = random.Random(0)
    L = list(S)
    for _ in range(3000):
        g, h = rnd.choice(L), rnd.choice(L)
        if tuple(g[h[i]] for i in range(n)) not in S:
            return False, "not closed"
    return True, "closed (sampled) + identity"


def analyse(label, twisted_nodes):
    n, adj, names, idx = cfi(K4, 4, twisted_nodes)
    nc, comp = components(n, adj)
    A = all_isos(n, adj, wl(n, adj, [0] * n), wl(n, adj, [0] * n))
    ok, why = group_closed(n, A)
    print(f"\n=== {label} ===  n={n} components={nc} |Aut|={len(A)}  group-check: {ok} ({why})")
    assert all(is_perm_aut(n, adj, g) for g in A)

    wires = [v for v in range(n) if names[v][0] == 'E']
    pair_of = {}
    for v in wires:
        _, e, b = names[v]
        pair_of[v] = idx[('E', e, 1 - b)]

    # is the wire-pair partition a BLOCK SYSTEM (preserved setwise by every aut)?
    broken = []
    for g in A:
        for v in wires:
            if g[pair_of[v]] != pair_of[g[v]]:
                broken.append((g, v))
                break
    print(f"  wire-pairs are blocks: {not broken}   ({len(A) - len(broken)}/{len(A)} auts preserve them)")
    if broken:
        g, v = broken[0]
        print(f"    e.g. an aut sends the pair {{{v},{pair_of[v]}}} = "
              f"{{{names[v]},{names[pair_of[v]]}}}  ->  "
              f"{{{names[g[v]]},{names[g[pair_of[v]]]}}}")

    # induced action on base edges / base nodes
    edge_imgs = set()
    for g in A:
        m = {}
        good = True
        for v in wires:
            e = names[v][1]
            f = names[g[v]][1]
            if m.setdefault(e, f) != f:
                good = False
        edge_imgs.add(tuple(sorted(m.items())) if good else None)
    print(f"  auts inducing a well-defined base-edge permutation: "
          f"{'ALL' if None not in edge_imgs else 'NOT all'}"
          f"  (distinct induced edge-perms: {len([x for x in edge_imgs if x])})")

    # gadget cell: does any aut move a gadget of node i to a gadget of node j?
    gad = [v for v in range(n) if names[v][0] == 'V']
    node_moves = set()
    for g in A:
        node_moves.add(tuple(sorted({(names[v][1], names[g[v]][1]) for v in gad})))
    print(f"  distinct induced node-maps: {len(node_moves)}")

    # stabiliser of wire 0
    oc = orbit_colouring(n, orbits(n, A))
    c1 = wl(n, adj, individualize(n, oc, 0))
    A1 = all_isos(n, adj, c1, c1)
    o1 = orbits(n, A1)
    print(f"  after individualizing 0 = {names[0]}: |stab| = {len(A1)}")
    print(f"    1-WL cells   : {sorted(len(v) for v in cells(c1).values())}")
    ob = defaultdict(list)
    for v in range(n):
        ob[o1[v]].append(v)
    print(f"    stab orbits  : {sorted(len(b) for b in ob.values())}")
    p = pair_of[0]
    print(f"    partner of 0 is {p} = {names[p]}; its stab-orbit = "
          f"{sorted(ob[o1[p]])} -> {[names[x] for x in sorted(ob[o1[p]])]}")
    mixed = [c for c in cells(c1).values() if len({o1[x] for x in c}) > 1]
    print(f"    mixed cells  : {[sorted(c) for c in mixed]}")
    return n, adj, names, idx, A


analyse("CFI[K4] UNTWISTED", ())
analyse("CFI[K4] TWISTED (node 0 odd)", (0,))
