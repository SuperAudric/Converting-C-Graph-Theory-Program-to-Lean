#!/usr/bin/env python3
"""HUNT #1c — the NON-RIGID multipede.   (2026-07-30)

The handoff excludes "multipedes / rigid graphs" via `Cascade.recoverableAt_base_iff_discrete`:
rigid => orbit partition discrete => the CAO start is discrete => vacuous.  That argument
covers RIGID multipedes only.  A multipede whose F2 incidence matrix has a **1-dimensional
kernel spanned by the all-ones vector** is NOT rigid:

    Aut = the flip group {x in F2^W : A x = 0} = ker A,  |Aut| = 2,
    orbit partition = ALL pairs {a_w, b_w} and the paired middles  (coarse, nothing discrete)

so the CAO start is a genuine 2-element-orbit partition -- and one individualization kills
the whole group:

    individualize a_0  =>  Aut trivial  =>  EVERY orbit is a singleton
                       =>  ANY non-singleton cell is AUTOMATICALLY MIXED  (Lagrange, T2 form)

No orbit oracle is needed for the verdict -- only (i) |Aut| = 2, and (ii) does the k-WL
closure discretize?  And multipedes are exactly the objects built so that WL cannot see the
F2 parity: with every row of even size >= 4, pinning one segment gives each remaining
a_w / b_w the SAME local counts, so unit propagation is stuck at the very first row.

This is the CFI mechanism applied to ORBIT RECOVERY rather than graph distinguishing.  The
earlier CFI attempts failed because a CFI graph's gauge group is huge (2^{|E|-|V|+1}), so the
orbits stay coarse and WL matches them.  Here the group is order 2 while the blindness is the
full F2 parity -- that asymmetry is the whole point.
"""
import sys, time
from collections import defaultdict
from itertools import combinations
sys.path.insert(0, "/workspace/scratchpad")
from probe_cao_cleanroom import wl, individualize, cells, all_isos, orbits, is_perm_aut
from probe_cao_vtcover import iso_exists

sys.setrecursionlimit(100000)


def f2_kernel(rows, W):
    """Basis of {x in F2^W : every row has even intersection with supp(x)}."""
    M = [[1 if w in r else 0 for w in range(W)] for r in rows]
    piv = {}
    R = [row[:] for row in M]
    r = 0
    for c in range(W):
        pr = next((i for i in range(r, len(R)) if R[i][c]), None)
        if pr is None:
            continue
        R[r], R[pr] = R[pr], R[r]
        for i in range(len(R)):
            if i != r and R[i][c]:
                R[i] = [a ^ b for a, b in zip(R[i], R[r])]
        piv[c] = r
        r += 1
    free = [c for c in range(W) if c not in piv]
    basis = []
    for fc in free:
        x = [0] * W
        x[fc] = 1
        for c, rr in piv.items():
            x[c] = R[rr][fc]
        basis.append(x)
    return basis, r


def multipede(rows, W):
    names = [('a', w) for w in range(W)] + [('b', w) for w in range(W)]
    for i, r in enumerate(rows):
        rl = sorted(r)
        for k in range(0, len(rl) + 1, 2):
            for c in combinations(rl, k):
                names.append(('m', i, frozenset(c)))
    ix = {nm: i for i, nm in enumerate(names)}
    n = len(names)
    adj = [[0] * n for _ in range(n)]
    for nm in names:
        if nm[0] != 'm':
            continue
        _, i, c = nm
        for w in sorted(rows[i]):
            t = ix[('a', w)] if w in c else ix[('b', w)]
            adj[ix[nm]][t] = adj[t][ix[nm]] = 1
    return n, adj, names, ix


def flip_perm(x, rows, names, ix):
    """The automorphism induced by flipping the segments in supp(x) (needs A x = 0)."""
    sigma = [None] * len(names)
    for k, nm in enumerate(names):
        if nm[0] == 'a':
            sigma[k] = ix[('b', nm[1])] if x[nm[1]] else ix[('a', nm[1])]
        elif nm[0] == 'b':
            sigma[k] = ix[('a', nm[1])] if x[nm[1]] else ix[('b', nm[1])]
        else:
            _, i, c = nm
            flip = {w for w in rows[i] if x[w]}
            sigma[k] = ix[('m', i, frozenset(c ^ flip))]
    return sigma


def twowl_vertex(n, adj, vcol, cap_rounds=30):
    col = [0] * (n * n)
    init = {}
    for u in range(n):
        for v in range(n):
            k = (0 if u == v else 1, adj[u][v], vcol[u], vcol[v])
            col[u * n + v] = init.setdefault(k, len(init))
    for _ in range(cap_rounds):
        rank, new = {}, [0] * (n * n)
        for u in range(n):
            un = u * n
            for v in range(n):
                s = sorted((col[un + w], col[w * n + v]) for w in range(n))
                key = (col[un + v], tuple(s))
                r = rank.get(key)
                if r is None:
                    r = rank[key] = len(rank)
                new[un + v] = r
        if len(rank) == len(set(col)):
            break
        col = new
    return [col[u * n + u] for u in range(n)]


def nontrivial_aut_exists(n, adj, col, budget=400000):
    """Is there a non-identity automorphism preserving `col`?  (bounded, complete search)"""
    cnt = [budget]

    def rec(c):
        cnt[0] -= 1
        if cnt[0] <= 0:
            raise RuntimeError("budget")
        c = wl(n, adj, c)
        d = cells(c)
        big = [k for k in sorted(d) if len(d[k]) > 1]
        if not big:
            pos = {c[v]: v for v in range(n)}
            sig = [pos[c[v]] for v in range(n)]
            return sig if (sig != list(range(n)) and is_perm_aut(n, adj, sig)) else None
        k0 = big[0]
        x = d[k0][0]
        for y in d[k0]:
            r = rec(individualize(n, wl(n, adj, individualize(n, c, x)), y) if False
                    else individualize(n, c, y))
            if r is not None:
                return r
        return None

    # search for an automorphism mapping the first cell's first member elsewhere
    c0 = wl(n, adj, col)
    d = cells(c0)
    big = [k for k in sorted(d) if len(d[k]) > 1]
    if not big:
        return False
    k0 = big[0]
    x = d[k0][0]
    for y in d[k0]:
        if y == x:
            continue
        r = iso_exists(n, adj, individualize(n, c0, x), individualize(n, c0, y),
                       budget=[budget])
        if r is True:
            return True
    return False



def rank_f2(rows, W):
    return f2_kernel(rows, W)[1]


def search(W, V, weight, seed, tries=4000):
    """Random weight-`weight` rows with rank exactly W-1 (=> kernel is <all-ones> alone)."""
    import random
    rnd = random.Random(seed)
    cols = list(range(W))
    for _ in range(tries):
        rows = []
        seen = set()
        while len(rows) < V:
            c = frozenset(rnd.sample(cols, weight))
            if c not in seen:
                seen.add(c)
                rows.append(c)
        basis, r = f2_kernel(rows, W)
        if r == W - 1 and len(basis) == 1 and basis[0] == [1] * W:
            return rows
    return None


print("=== non-rigid multipedes: searching for kernel = <all-ones> exactly ===")
print("    (every row even => all-ones in ker; rank W-1 => ker is EXACTLY <all-ones>)")
CASES = [(6, 5, 4), (6, 7, 4), (7, 6, 4), (7, 9, 4), (8, 7, 4), (8, 10, 4), (8, 12, 4),
         (9, 8, 4), (9, 12, 4), (10, 9, 4), (10, 14, 4)]
for (W, V, weight) in CASES:
    for seed in range(4):
        rows = search(W, V, weight, seed)
        if rows is None:
            continue
        n, adj, names, ix = multipede(rows, W)
        if n > 130:
            print(f"  W={W} V={V} wt={weight} seed={seed}: n={n} too big, skipped")
            break
        sigma = flip_perm([1] * W, rows, names, ix)
        assert is_perm_aut(n, adj, sigma), "flip is not an automorphism"
        t0 = time.time()
        try:
            A = all_isos(n, adj, wl(n, adj, [0]*n), wl(n, adj, [0]*n), limit=2_000_000)
        except RuntimeError:
            print(f"  W={W} V={V} wt={weight} seed={seed}: n={n} Aut budget blown, skip")
            continue
        if len(A) > 4000:
            print(f"  W={W} V={V} wt={weight} seed={seed}: n={n} |Aut|={len(A)} too symmetric")
            continue
        orb = orbits(n, A)
        m = {}
        oc = [m.setdefault(orb[v], len(m)) for v in range(n)]
        szs = defaultdict(int)
        for c in oc:
            szs[c] += 1
        v0 = ix[('a', 0)]
        col1 = individualize(n, oc, v0)
        c1 = wl(n, adj, col1)
        d2 = twowl_vertex(n, adj, col1)
        dd = defaultdict(list)
        for v, c in enumerate(d2):
            dd[c].append(v)
        A1 = [g for g in A if g[v0] == v0]
        o1 = orbits(n, A1)
        m1 = [c for c in cells(c1).values() if len({o1[x] for x in c}) > 1]
        m2 = [c for c in dd.values() if len({o1[x] for x in c}) > 1]
        print(f"  W={W} V={V} wt={weight} s={seed}: n={n} |Aut|={len(A)} "
              f"orbit-start sizes {sorted(set(szs.values()))} | after indiv a_0: "
              f"|Aut_v|={len(A1)} 1-WL cells={len(set(c1))} mixed={len(m1)} "
              f"| 2-WL cells={len(dd)} mixed={len(m2)}"
              + ("   <<<<<< 2-WL COUNTEREXAMPLE" if m2 else ""))
        break
