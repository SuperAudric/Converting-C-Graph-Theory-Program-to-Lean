#!/usr/bin/env python3
"""M2 ANSWERED NEGATIVELY BY CONSTRUCTION (user, 2026-07-30).

Claim: the separation ROUND count cannot be bounded by a constant.  Take a VT family of
increasing diameter -- Johnson J(m,k), diameter k.  Refinement propagates ~one hop per round,
so recovering the Aut_v-orbits needs ~diameter rounds.

For J(m,k) the Aut_v-orbits ARE the distance classes: Stab(v) = S_k x S_{m-k} acts with orbits
{A : |A n v| = i}, and d(A,B) = k - |A n B|.  So the target partition has exactly k+1 classes
and needs no orbit oracle -- which makes this cheap to measure at growing k.

Reported: rounds for the 2-WL extension of (J(m,k), orbit partition = one cell, individualize v)
to reach k+1 diagonal classes.  If that grows with k, a constant round bound is refuted.
"""
import sys
from itertools import combinations
from collections import defaultdict

def johnson(m, k):
    S = list(combinations(range(m), k))
    n = len(S)
    adj = [[0]*n for _ in range(n)]
    for i in range(n):
        for j in range(i+1, n):
            if len(set(S[i]) & set(S[j])) == k-1:
                adj[i][j] = adj[j][i] = 1
    return n, adj, S

def bfs_ecc(n, adj, s):
    d = [-1]*n; d[s] = 0; q = [s]
    while q:
        nq = []
        for a in q:
            for b in range(n):
                if adj[a][b] and d[b] < 0:
                    d[b] = d[a]+1; nq.append(b)
        q = nq
    return max(d)

def prounds(n, col, cap=25):
    """Yield (round, colouring) for the oblivious 2-WL pair refinement."""
    yield 0, col
    for r in range(1, cap+1):
        rank, new = {}, [0]*(n*n)
        for a in range(n):
            an = a*n
            for b in range(n):
                s = sorted((col[an+x], col[x*n+b]) for x in range(n))
                key = (col[an+b], tuple(s))
                q = rank.get(key)
                if q is None: q = rank[key] = len(rank)
                new[an+b] = q
        stable = len(rank) == len(set(col))
        col = new
        yield r, col
        if stable: return

def init_pairs(n, adj, vcol):
    col = [0]*(n*n); ini = {}
    for a in range(n):
        for b in range(n):
            k = (0 if a == b else 1, adj[a][b], vcol[a], vcol[b])
            col[a*n+b] = ini.setdefault(k, len(ini))
    return col

def run(m, k):
    n, adj, S = johnson(m, k)
    diam = bfs_ecc(n, adj, 0)
    vcol = [1 if i == 0 else 0 for i in range(n)]        # individualize vertex 0
    target = k+1                                          # |A n v| = 0..k
    hit = None
    last = 0
    for r, col in prounds(n, init_pairs(n, adj, vcol)):
        diagc = len({col[i*n+i] for i in range(n)})
        last = r
        if hit is None and diagc >= target:
            hit = r
        if diagc >= target and r >= (hit or 0):
            break
    # verify the recovered partition IS the distance/intersection partition
    ok = None
    for r, col in prounds(n, init_pairs(n, adj, vcol)):
        if r == hit:
            byd = defaultdict(set)
            for i in range(n):
                byd[len(set(S[i]) & set(S[0]))].add(col[i*n+i])
            ok = all(len(v) == 1 for v in byd.values()) and \
                 len({next(iter(v)) for v in byd.values()}) == target
            break
    print(f"  J({m},{k}): n={n:4d} diameter={diam}  ->  Aut_v-orbits ({target} classes) "
          f"recovered at ROUND {hit}   (partition == |A∩v| classes: {ok})")

if __name__ == "__main__":
    print("Johnson J(m,k): diameter = k, Aut_v-orbits = the k+1 intersection classes")
    for m, k in [(6,2), (6,3), (8,4), (10,5)]:
        run(m, k)
