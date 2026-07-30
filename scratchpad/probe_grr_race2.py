#!/usr/bin/env python3
"""
PROBE 4c — the collapse race, done cheaply.

KEY SIMPLIFICATION over probe_grr_race.py (which was far too slow: it called the exhaustive
canon oracle ~14k times at n=32).  For the refutation we never need the orbit partition:

    trivial vertex stabiliser  =>  every orbit is a SINGLETON
                               =>  ANY non-singleton 1-WL cell is automatically MIXED.

So the whole test is two cheap predicates at the node `indiv(root, 0)` refined:

    (b) is the colouring NON-DISCRETE?                      -- one 1-WL run
    (a) is there NO non-identity automorphism fixing it?    -- bounded backtracking

(a) and (b) together  =>  `RigidObstructionAt`  =>  REFUTES `VT => Tinhofer`.

`VT => Tinhofer` is exactly the claim that (a) and (b) never hold together, i.e. that as the
connection set grows, the stabiliser never collapses to trivial before 1-WL discretizes.
"""
import sys, random
from collections import defaultdict
from itertools import product

sys.path.insert(0, "/workspace/scratchpad")
from probe_dualdeepen import refine, indiv

# ────────────────────────────────────── cheap: any non-identity colour-preserving aut?
def nontrivial_aut(n, adj, col, node_cap=200000):
    """Backtracking search for a non-identity automorphism preserving `col`.
    Returns the permutation, or None if the stabiliser is trivial. (None + non-discrete
    colouring = a rigid obstruction.)"""
    bycol = defaultdict(list)
    for v in range(n):
        bycol[col[v]].append(v)
    order = sorted(range(n), key=lambda v: (len(bycol[col[v]]), col[v], v))
    nbr = [set(u for u in range(n) if adj[v][u]) for v in range(n)]
    img = [None] * n
    used = [False] * n
    budget = [node_cap]

    def rec(i, moved):
        if budget[0] <= 0:
            return None
        budget[0] -= 1
        if i == len(order):
            return list(img) if moved else None
        v = order[i]
        for w in bycol[col[v]]:
            if used[w]:
                continue
            ok = True
            for u in range(n):
                if img[u] is None:
                    continue
                if (u in nbr[v]) != (img[u] in nbr[w]):
                    ok = False
                    break
            if not ok:
                continue
            img[v] = w
            used[w] = True
            r = rec(i + 1, moved or (w != v))
            if r is not None:
                return r
            img[v] = None
            used[w] = False
        return None

    return rec(0, False)

def cayley_z2k(k, S):
    els = list(product(range(2), repeat=k))
    idx = {e: i for i, e in enumerate(els)}
    n = len(els)
    adj = [[0] * n for _ in range(n)]
    for e in els:
        for s in S:
            f = tuple((a + b) % 2 for a, b in zip(e, s))
            adj[idx[e]][idx[f]] = adj[idx[f]][idx[e]] = 1
    return n, adj

def cayley_group(els, mul, S):
    idx = {e: i for i, e in enumerate(els)}
    n = len(els)
    adj = [[0] * n for _ in range(n)]
    for e in els:
        for s in S:
            f = mul(e, s)
            if f != e:
                adj[idx[e]][idx[f]] = adj[idx[f]][idx[e]] = 1
    return n, adj

def dihedral(m):
    els = [(r, s) for s in range(2) for r in range(m)]
    def mul(a, b):
        r1, s1 = a; r2, s2 = b
        return ((r1 + r2) % m, s2) if s1 == 0 else ((r1 - r2) % m, (s1 + s2) % 2)
    return els, mul

def semidihedral16():
    """SD16 = <a,b | a^8, b^2, bab^-1 = a^3> — non-abelian, GRR-admitting territory."""
    els = [(i, j) for j in range(2) for i in range(8)]
    def mul(x, y):
        i, j = x; k, l = y
        return (((i + k) % 8, l) if j == 0 else ((i + 3 * k) % 8, (j + l) % 2))
    return els, mul

def inv_closed(els, mul, S):
    ident = next(e for e in els if all(mul(e, x) == x for x in els))
    out = set(S)
    for s in S:
        out.add(next(t for t in els if mul(s, t) == ident))
    out.discard(ident)
    return sorted(out)

random.seed(4242)
print("(a) stabiliser trivial   (b) 1-WL non-discrete after ONE individualization")
print("(a) AND (b)  =>  refutes  VT => Tinhofer")
print()
print(f"{'group':>12s} {'|S|':>4s} {'n':>3s} {'cols':>5s} {'nondisc(b)':>11s} "
      f"{'stabTrivial(a)':>15s}  verdict")
print("-" * 84)

FAMS = [("Z2^4", *(lambda: (list(product(range(2), repeat=4)),
                            lambda a, b: tuple((x + y) % 2 for x, y in zip(a, b))))()),
        ("Z2^5", *(lambda: (list(product(range(2), repeat=5)),
                            lambda a, b: tuple((x + y) % 2 for x, y in zip(a, b))))()),
        ("D8", *dihedral(8)), ("D9", *dihedral(9)), ("D12", *dihedral(12)),
        ("SD16", *semidihedral16())]

refutations = []
grr_hits = 0
for gname, els, mul in FAMS:
    n = len(els)
    nonid = [e for e in els if not all(mul(e, x) == x for x in els)]
    for sz in range(2, min(len(nonid), 14) + 1):
        rows = []
        for trial in range(25):
            S = inv_closed(els, mul, random.sample(nonid, min(sz, len(nonid))))
            if not S:
                continue
            n_, adj = cayley_group(els, mul, S)
            root = refine(n_, adj, [0] * n_)
            if len(set(root)) != 1:
                continue                              # 1-WL splits => not VT
            c1 = refine(n_, adj, indiv(n_, root, 0))
            ncol = len(set(c1))
            nondisc = (ncol != n_)
            a = nontrivial_aut(n_, adj, c1)
            stab_trivial = (a is None)
            if stab_trivial:
                grr_hits += 1
            rows.append((nondisc, stab_trivial, ncol, S))
            if nondisc and stab_trivial:
                refutations.append((gname, len(S), n_, ncol, S))
        if not rows:
            continue
        # report the most informative row for this (group, size)
        rows.sort(key=lambda r: (r[0] and r[1], r[1], r[0]), reverse=True)
        nondisc, st, ncol, S = rows[0]
        v = ("★★★ REFUTES VT=>Tinhofer" if (nondisc and st)
             else ("GRR + discrete -> consistent" if st else "stab nontrivial"))
        print(f"{gname:>12s} {len(S):4d} {n:3d} {ncol:5d} {str(nondisc):>11s} "
              f"{str(st):>15s}  {v}")

print("-" * 84)
print(f"trivial-stabiliser (GRR-like) instances reached: {grr_hits}")
print(f"REFUTATIONS (non-discrete AND trivial stabiliser): {len(refutations)}")
for g, s, n_, c, S in refutations[:6]:
    print(f"  ★ {g} n={n_} |S|={s} colours={c} S={S}")
if grr_hits == 0:
    print("  ⚠⚠ zero GRR-like instances — habitat still wrong, sharp case UNTESTED")
