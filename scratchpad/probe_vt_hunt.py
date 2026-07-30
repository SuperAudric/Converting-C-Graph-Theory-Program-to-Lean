#!/usr/bin/env python3
"""HUNT: a vertex-transitive graph that is NOT `Tinhofer`.   (2026-07-30)

Two targets, increasing strength:
  T1  the LOWEST-ID cell (= Lean `chooseIdK`) is mixed at some node of the faithful descent
      -> refutes the literal `VT => Tinhofer`.
  T2  EVERY non-singleton cell is mixed at some reachable node
      -> refutes it under ANY selector, INCLUDING the nauty-style backtracking selector
      ("pick a cell; if it fails, pick another").   T2  <=>  EXISTS-Tinhofer is False.

Why a small stabiliser is the cheap T2 generator: orbit sizes divide |Aut_chi|, so if no
non-singleton cell size divides |Aut_chi|, EVERY cell is mixed at once (Lagrange).  The
extremal case is a node with TRIVIAL stabiliser: there, any non-discrete colouring is T2.
That node need not be at depth 1 -- the stabiliser shrinks as the descent proceeds, so the
search walks the whole descent tree.

Habitat: Cayley graphs (vertex-transitive FOR FREE -- no group computation needed to certify
VT), over groups built from explicit multiplication rules (orders asserted), plus non-Cayley
VT graphs.  Cheap pre-filter: a graph whose 1-WL discretizes after one individualization is
Tinhofer outright, so only non-discretizing graphs are analysed.
"""
import sys, itertools
from collections import defaultdict
sys.path.insert(0, "/workspace/scratchpad")
from probe_cao_cleanroom import wl, individualize, cells, all_isos, orbits

sys.setrecursionlimit(100000)


# ---------------------------------------------------------------- groups (explicit rules)
class Grp:
    def __init__(self, name, els, mul, e):
        self.name, self.els, self.mul, self.e = name, els, mul, e
        self.inv = {}
        for g in els:
            for h in els:
                if mul(g, h) == e:
                    self.inv[g] = h
                    break
        assert len(self.inv) == len(els), name

    def __len__(self):
        return len(self.els)


def G_abelian(mods):
    els = list(itertools.product(*[range(m) for m in mods]))
    mul = lambda a, b: tuple((x + y) % m for x, y, m in zip(a, b, mods))
    return Grp("Z" + "xZ".join(map(str, mods)), els, mul, tuple(0 for _ in mods))


def G_semidirect(n, m, k, name):
    """Z_n :_k Z_m  --  (r,s)(r',s') = (r + k^s r', s+s').  Requires k^m = 1 mod n."""
    assert pow(k, m, n) == 1, (n, m, k)
    els = [(r, s) for r in range(n) for s in range(m)]
    mul = lambda a, b: ((a[0] + pow(k, a[1], n) * b[0]) % n, (a[1] + b[1]) % m)
    return Grp(name, els, mul, (0, 0))


def G_dicyclic(n):
    """Dic_n, order 4n:  a^2n = 1, b^2 = a^n, b a b^-1 = a^-1."""
    els = [(i, e) for i in range(2 * n) for e in (0, 1)]

    def mul(x, y):
        i, e = x
        j, f = y
        if e == 0:
            return ((i + j) % (2 * n), f)
        return ((i - j + (n if f else 0)) % (2 * n), 1 - f)
    return Grp(f"Dic{n}", els, mul, (0, 0))


def G_perm(name, gens, deg):
    idp = tuple(range(deg))
    seen, frontier = {idp}, [idp]
    while frontier:
        nxt = []
        for g in frontier:
            for h in gens:
                k = tuple(g[h[i]] for i in range(deg))
                if k not in seen:
                    seen.add(k)
                    nxt.append(k)
        frontier = nxt
    els = sorted(seen)
    return Grp(name, els, lambda a, b: tuple(a[b[i]] for i in range(deg)), idp)


def cyc(deg, cycles):
    p = list(range(deg))
    for c in cycles:
        for i in range(len(c)):
            p[c[i]] = c[(i + 1) % len(c)]
    return tuple(p)


GROUPS = []
for mods in [(8,), (9,), (10,), (12,), (14,), (15,), (16,), (18,), (20,), (21,), (24,), (27,),
             (4, 2), (2, 2, 2), (4, 4), (8, 2), (4, 2, 2), (2, 2, 2, 2), (3, 3), (6, 2),
             (9, 3), (3, 3, 3), (6, 3), (10, 2), (12, 2), (2, 2, 2, 3)]:
    GROUPS.append(G_abelian(mods))
for n in (4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14):
    GROUPS.append(G_semidirect(n, 2, n - 1, f"D{n}"))              # dihedral, order 2n
for n in (2, 3, 4, 5, 6, 7):
    GROUPS.append(G_dicyclic(n))                                    # order 4n
for (n, m, k, nm) in [(8, 2, 3, "SD16"), (8, 2, 5, "M16"), (5, 4, 2, "F20"),
                      (7, 3, 2, "F21"), (9, 3, 4, "Z9:Z3"), (13, 3, 3, "F39"),
                      (7, 6, 3, "F42"), (3, 4, 2, "Z3:Z4"), (5, 2, 4, "D5b"),
                      (12, 2, 5, "Z12:Z2"), (12, 2, 7, "Z12:Z2b"), (12, 2, 11, "D12")]:
    try:
        GROUPS.append(G_semidirect(n, m, k, nm))
    except AssertionError:
        pass
GROUPS.append(G_perm("S4", [cyc(4, [[0, 1, 2, 3]]), cyc(4, [[0, 1]])], 4))
GROUPS.append(G_perm("A4", [cyc(4, [[0, 1, 2]]), cyc(4, [[0, 1], [2, 3]])], 4))
GROUPS.append(G_perm("S3xZ3", [cyc(6, [[0, 1, 2]]), cyc(6, [[0, 1]]), cyc(6, [[3, 4, 5]])], 6))
GROUPS = [g for g in GROUPS if 8 <= len(g) <= 28]
print(f"groups: {len(GROUPS)}")
for g in GROUPS:
    print(f"   {g.name:12s} order {len(g)}")


def cayley(G, S):
    ix = {e: i for i, e in enumerate(G.els)}
    n = len(G.els)
    adj = [[0] * n for _ in range(n)]
    for g in G.els:
        for s in S:
            a, b = ix[g], ix[G.mul(g, s)]
            adj[a][b] = adj[b][a] = 1
    return n, adj


def connected(n, adj):
    seen, st = {0}, [0]
    while st:
        v = st.pop()
        for u in range(n):
            if adj[v][u] and u not in seen:
                seen.add(u)
                st.append(u)
    return len(seen) == n


def _blocks(o):
    d = defaultdict(list)
    for v, r in enumerate(o):
        d[r].append(v)
    return list(d.values())


# ---------------------------------------------------------------- the descent analysis
def analyse(n, adj, budget=300000):
    """Exact, via stabiliser enumeration at every node of the descent tree.
    Returns (depth1_mixed, lowest_id_ok, exists_ok, stab_order, detail)."""
    root = wl(n, adj, [0] * n)
    if len(set(root)) != 1:
        return None
    c1 = wl(n, adj, individualize(n, root, 0))
    if len(set(c1)) == n:
        return "discrete"
    try:
        Av = all_isos(n, adj, c1, c1, limit=budget)
    except RuntimeError:
        return "blown"
    ov = orbits(n, Av)
    d1 = [len(c) for c in cells(c1).values() if len({ov[v] for v in c}) > 1]
    memo = {}

    def node(col):
        key = tuple(col)
        if key in memo:
            return memo[key]
        d = cells(col)
        ns = [c for c in sorted(d) if len(d[c]) > 1]
        if not ns:
            memo[key] = (True, True)
            return memo[key]
        try:
            A = all_isos(n, adj, col, col, limit=budget)
        except RuntimeError:
            memo[key] = (True, True)          # unknown -> assume clean (conservative for a HUNT)
            return memo[key]
        o = orbits(n, A)
        ex, lo = False, False
        for i, c in enumerate(ns):
            cell = d[c]
            if len({o[v] for v in cell}) > 1:
                continue                       # mixed: this pick is illegal
            e2, l2 = node(wl(n, adj, individualize(n, col, cell[0])))
            ex = ex or e2
            if i == 0:
                lo = l2
        memo[key] = (ex, lo)
        return memo[key]

    ex, lo = node(c1)
    return (d1, lo, ex, len(Av),
            f"|Aut_v|={len(Av)} cells={sorted(len(c) for c in cells(c1).values())} "
            f"stab-orbits={sorted(len(g) for g in _blocks(ov))}")


if __name__ == "__main__":
    print("\nsweeping Cayley graphs (VT for free) ...")
    mixed_hits, t1, t2 = [], [], []
    tested = nondisc = 0
    census = defaultdict(int)
    for G in GROUPS:
        idp = G.e
        classes, used = [], set()
        for e in G.els:
            if e == idp or e in used:
                continue
            ie = G.inv[e]
            used.add(e)
            used.add(ie)
            classes.append((e,) if e == ie else (e, ie))
        for r in range(1, min(len(classes), 5) + 1):
            for combo in itertools.combinations(classes, r):
                S = [x for c in combo for x in c]
                if not (2 <= len(S) <= 8):
                    continue
                n, adj = cayley(G, S)
                if not connected(n, adj):
                    continue
                root = wl(n, adj, [0] * n)
                if len(set(root)) != 1:
                    continue
                tested += 1
                c1 = wl(n, adj, individualize(n, root, 0))
                if len(set(c1)) == n:
                    census[("discrete", None)] += 1
                    continue
                nondisc += 1
                res = analyse(n, adj)
                if not isinstance(res, tuple):
                    census[(res, None)] += 1
                    continue
                d1, lo, ex, stab, detail = res
                census[("nondiscrete", stab if stab <= 4 else ">4")] += 1
                tag = f"{G.name}(|S|={len(S)}) n={n}  {detail}"
                if d1:
                    mixed_hits.append(tag)
                if lo is False:
                    t1.append(tag)
                if ex is False:
                    t2.append(tag)

    print(f"\nCayley graphs tested (VT): {tested}")
    print(f"  1-WL DISCRETIZES after one individualization (=> Tinhofer, skipped): "
          f"{census[('discrete', None)]}")
    print(f"  NON-discretizing (the only place a hit can live): {nondisc}")
    print("  census of non-discretizing by |Aut_v|:",
          {k[1]: v for k, v in sorted(census.items()) if k[0] == 'nondiscrete'})
    print(f"\n  depth-1 MIXED cell (Shrikhande class): {len(mixed_hits)}")
    for h in sorted(set(mixed_hits))[:20]:
        print(f"     {h}")
    print(f"\n  T1  chooseIdK picks a mixed cell: {len(t1)}")
    for h in sorted(set(t1))[:20]:
        print(f"     * {h}")
    print(f"\n  T2  every cell mixed at a reachable node (defeats backtracking): {len(t2)}")
    for h in sorted(set(t2))[:20]:
        print(f"     ** {h}")
