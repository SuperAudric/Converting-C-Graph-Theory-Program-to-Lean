#!/usr/bin/env python3
"""FULL INDEPENDENT VERIFICATION of the T2 witnesses found by probe_vt_hunt5.py.

Claim to check, for Cay(Z12 :_k Z2, S) with k in {5, 7}, n = 24:

  (1) the group is a genuine group of order 24 (associativity + inverses checked)
  (2) the graph is VERTEX-TRANSITIVE  (checked TWICE: by the regular representation,
      and independently by exact pairwise isomorphism tests -- not merely "it's a Cayley
      graph so it must be")
  (3) 1-WL root is a single cell  => CellsAreOrbits holds at the root (VT)
  (4) after individualizing ONE vertex, |Aut(adj, chi)| = 2  -- by COMPLETE enumeration,
      no budget
  (5) EVERY non-singleton 1-WL cell at that node fails to be a single orbit
        => `CellSingleOrbit` fails for every possible `chooseIdK` outcome
        => `TinhoferPath` is False whatever the colour-id convention
        => `Tinhofer` is False, and the nauty-style BACKTRACKING selector has no legal move
  (6) explicit witness pairs (u, w): same cell, no automorphism u -> w.

If (1)-(6) hold, `VT => Tinhofer` is refuted at depth 1 by a 24-vertex Cayley graph.
"""
import sys
from collections import defaultdict
sys.path.insert(0, "/workspace/scratchpad")
from probe_cao_cleanroom import wl, individualize, cells, all_isos, orbits, is_perm_aut
from probe_cao_vtcover import iso_exists


def build(k):
    """Z12 :_k Z2 = <a,b | a^12, b^2, b a b^-1 = a^k>, elements (r, s)."""
    n_, m = 12, 2
    assert pow(k, m, n_) == 1
    els = [(r, s) for r in range(n_) for s in range(m)]
    mul = lambda x, y: ((x[0] + pow(k, x[1], n_) * y[0]) % n_, (x[1] + y[1]) % m)
    e = (0, 0)
    # (1) genuine group: associativity, identity, inverses
    for x in els:
        assert mul(e, x) == x == mul(x, e)
    for x in els:
        for y in els:
            for z in els:
                assert mul(mul(x, y), z) == mul(x, mul(y, z)), (k, x, y, z)
    inv = {x: next(y for y in els if mul(x, y) == e) for x in els}
    assert len(set(inv.values())) == len(els)
    return els, mul, e, inv


def cay(els, mul, S):
    ix = {g: i for i, g in enumerate(els)}
    n = len(els)
    adj = [[0] * n for _ in range(n)]
    for g in els:
        for s in S:
            a, b = ix[g], ix[mul(g, s)]
            adj[a][b] = adj[b][a] = 1
    return n, adj, ix


def check(k, S):
    els, mul, e, inv = build(k)
    assert all(inv[s] in S for s in S), "connection set must be inverse-closed"
    assert e not in S
    n, adj, ix = cay(els, mul, S)
    print(f"\n=== Cay(Z12 :_{k} Z2, S) ===  n = {n}, |S| = {len(S)}")
    print(f"  S = {sorted(S)}")
    print(f"  degrees: {sorted({sum(r) for r in adj})}")

    # (2a) VT via the regular representation: g -> (x -> gx) is an automorphism
    reg = []
    for g in els:
        p = [ix[mul(g, x)] for x in els]
        assert is_perm_aut(n, adj, p), "left translation is not an automorphism!"
        reg.append(tuple(p))
    assert len({p[0] for p in reg}) == n
    print(f"  VT via regular representation: {len(reg)} left translations, all verified "
          f"automorphisms, transitive: True")

    # (2b) VT independently, by exact pairwise isomorphism search
    root = wl(n, adj, [0] * n)
    vt2 = all(iso_exists(n, adj, individualize(n, root, 0),
                         individualize(n, root, v)) is True for v in range(n))
    print(f"  VT re-checked by exact pairwise iso search: {vt2}")

    # (3) root
    print(f"  1-WL root cells: {sorted(len(c) for c in cells(root).values())}  "
          f"=> CellsAreOrbits at the root: {len(set(root)) == 1}")

    # (4) full Aut and the depth-1 stabiliser, COMPLETE enumeration (no budget)
    A = all_isos(n, adj, root, root, limit=10 ** 9)
    print(f"  |Aut(G)| = {len(A)}  (complete enumeration)   |Aut|/n = {len(A) / n}")
    c1 = wl(n, adj, individualize(n, root, 0))
    Av = all_isos(n, adj, c1, c1, limit=10 ** 9)
    ov = orbits(n, Av)
    blocks = defaultdict(list)
    for v in range(n):
        blocks[ov[v]].append(v)
    print(f"  after individualizing v=0:  |Aut_v| = {len(Av)}  (complete enumeration)")
    print(f"    1-WL cells      : {sorted(len(c) for c in cells(c1).values())}")
    print(f"    stabiliser orbits: {sorted(len(b) for b in blocks.values())}")

    # (5) EVERY non-singleton cell mixed?
    ns = [(cid, cell) for cid, cell in sorted(cells(c1).items()) if len(cell) > 1]
    allmixed = True
    print(f"    non-singleton cells: {len(ns)}")
    for cid, cell in ns:
        reps = {ov[v] for v in cell}
        mixed = len(reps) > 1
        allmixed &= mixed
        print(f"      colour {cid:3d} cell {sorted(cell)}  -> {len(reps)} orbits  "
              f"MIXED={mixed}")
    print(f"    ==> EVERY non-singleton cell is mixed: {allmixed}")

    # (6) explicit witness pairs, re-verified by independent iso search
    if allmixed:
        print("    witness pairs (same cell, NO automorphism between them):")
        for cid, cell in ns:
            for i in range(len(cell)):
                done = False
                for j in range(i + 1, len(cell)):
                    u, w = cell[i], cell[j]
                    if ov[u] != ov[w]:
                        ex = iso_exists(n, adj, individualize(n, c1, u),
                                        individualize(n, c1, w))
                        byenum = any(g[u] == w for g in Av)
                        print(f"      colour {cid:3d}: u={u}, w={w} -> iso_exists={ex}, "
                              f"in-enumerated-group={byenum} (both must be False)")
                        done = True
                        break
                if done:
                    break
    return allmixed


# the two hits, rebuilt from scratch
els5, mul5, e5, inv5 = build(5)
els7, mul7, e7, inv7 = build(7)


def classes(els, e, inv):
    out, used = [], set()
    for x in els:
        if x == e or x in used:
            continue
        used.add(x)
        used.add(inv[x])
        out.append((x,) if inv[x] == x else (x, inv[x]))
    return out


import itertools
found = []
for k, size in ((5, 5), (7, 7)):
    els, mul, e, inv = build(k)
    cls = classes(els, e, inv)
    for r in range(1, 5):
        for combo in itertools.combinations(cls, r):
            S = [x for c in combo for x in c]
            if len(S) != size:
                continue
            n, adj, _ = cay(els, mul, S)
            root = wl(n, adj, [0] * n)
            if len(set(root)) != 1:
                continue
            c1 = wl(n, adj, individualize(n, root, 0))
            if len(set(c1)) == n:
                continue
            try:
                Av = all_isos(n, adj, c1, c1, limit=1500)
            except RuntimeError:
                continue
            o = orbits(n, Av)
            ns = [c for c in cells(c1).values() if len(c) > 1]
            if ns and all(len({o[v] for v in c}) > 1 for c in ns):
                found.append((k, tuple(sorted(S))))
print(f"candidate T2 witnesses rediscovered from scratch: {len(found)}")
seen = set()
for k, S in found:
    if (k, S) in seen:
        continue
    seen.add((k, S))
    ok = check(k, list(S))
    print(f"  >>> VERDICT for k={k}: T2 CONFIRMED = {ok}")
