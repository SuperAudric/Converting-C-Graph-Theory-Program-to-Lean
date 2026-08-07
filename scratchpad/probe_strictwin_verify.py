#!/usr/bin/env python3
"""Independent verification of the n=10 strict win by EXHAUSTIVE automorphism search
(no canon, no generator harvesting, no orbit oracle) -- 10! with early pruning."""
import sys
from itertools import permutations
from collections import defaultdict
sys.setrecursionlimit(100000)
from probe_polyloop import adjlist, refine, indiv, target_cell

rows = ['0000010011','0001100001','0000000111','0100100100','0101001000',
        '1000001100','0000110010','0011010000','1010001000','1110000000']
n = len(rows)
adj = [[int(c) for c in r] for r in rows]
assert all(adj[i][j] == adj[j][i] for i in range(n) for j in range(n)), "not symmetric"
assert all(adj[i][i] == 0 for i in range(n)), "has a loop"
print("degrees:", [sum(r) for r in adj])

def auts_of(colouring):
    """ALL permutations preserving adjacency and the given colouring. Exhaustive."""
    out = []
    for p in permutations(range(n)):
        if any(colouring[i] != colouring[p[i]] for i in range(n)): continue
        if all(adj[i][j] == adj[p[i]][p[j]] for i in range(n) for j in range(i+1, n)):
            out.append(p)
    return out

adjl = adjlist(n, adj)
col = refine(n, adjl, [0]*n)
cid, C = target_cell(n, col)
print(f"1-WL branch cell = {C}  (size {len(C)})")

A = auts_of(col)
print(f"|Aut(G, 1-WL colouring)| = {len(A)}  (EXHAUSTIVE)")
orb = {}
for v in range(n):
    orb[v] = frozenset(p[v] for p in A)
blocks = {}
for v in C: blocks.setdefault(orb[v], []).append(v)
print("true orbits inside the cell:", sorted(map(sorted, blocks.keys())) if False else
      [sorted(b) for b in blocks.values()])
rigid = [v for v in C if len(orb[v]) == 1]
print("Aut-rigid cell members:", rigid)

def good(a):
    """greedy descent from a; every chosen cell a single TRUE orbit (exhaustive Aut each level)"""
    cur = indiv(n, adjl, col, a)
    for _ in range(n + 2):
        c2, C2 = target_cell(n, cur)
        if c2 is None: return True
        Al = auts_of(cur)
        ob = {v: frozenset(p[v] for p in Al) for v in C2}
        if len({ob[v] for v in C2}) > 1: return False
        cur = indiv(n, adjl, cur, min(C2))
    return False

G = [v for v in C if good(v)]
print(f"good anchors (exhaustive): {G}   bad: {[v for v in C if v not in G]}")
sig = {v: sum(indiv(n, adjl, col, v)) for v in C}
cnt = defaultdict(int)
for v in C: cnt[sig[v]] += 1
isol = [v for v in C if cnt[sig[v]] == 1]
print(f"stepSum-isolated: {isol}")
unsound = [v for v in isol if len(orb[v]) != 1]
prim = len(G) == len(C); sec = all((v in G) or (v in isol) for v in C)
print(f"\nCertifiedG={'open' if prim else 'SHUT'}  GoodOrIsolated={'open' if sec else 'SHUT'}"
      f"  unsound-isolations={unsound}")
print("VERDICT:", "*** STRICT WIN CONFIRMED ***" if (sec and not prim and not unsound)
      else "not a win / unsound")
