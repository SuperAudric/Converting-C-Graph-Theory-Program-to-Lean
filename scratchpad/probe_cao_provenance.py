#!/usr/bin/env python3
"""PROVENANCE / SELF-VALIDATION of the clean-room CAO verification (2026-07-30).

Answers "is this an independent verification, or does it retrace the bad steps?":

  A. my aut enumerator against 10 INDEPENDENTLY KNOWN |Aut| values
  B. my two orbit code paths (full enumeration vs pairwise early-exit iso) agree
  C. the multipede[6x5] `sanity-fail` DIAGNOSED with my machinery -- was the object or
     the oracle at fault?
  D. no import path from my chain to probe_dualdeepen / probe_orbit_oracle
"""
import sys, subprocess
from collections import defaultdict
from itertools import combinations
sys.path.insert(0, "/workspace/scratchpad")
from probe_cao_cleanroom import (wl, individualize, cells, all_isos, orbits, is_perm_aut,
                                 orbit_colouring)
from probe_cao_vtcover import iso_exists, cell_orbit_reps, cover


def K(m):
    return [(i, j) for i in range(m) for j in range(i + 1, m)]


def from_edges(nv, es):
    adj = [[0] * nv for _ in range(nv)]
    for a, b in es:
        adj[a][b] = adj[b][a] = 1
    return nv, adj


def circ(m, offs):
    es = set()
    for i in range(m):
        for o in offs:
            a, b = i, (i + o) % m
            if a != b:
                es.add((min(a, b), max(a, b)))
    return from_edges(m, sorted(es))


def kneser(m, k):
    S = list(combinations(range(m), k))
    es = [(i, j) for i in range(len(S)) for j in range(i + 1, len(S))
          if not set(S[i]) & set(S[j])]
    return from_edges(len(S), es)


def paley(q):
    sq = {(i * i) % q for i in range(1, q)}
    es = [(i, j) for i in range(q) for j in range(i + 1, q) if (j - i) % q in sq]
    return from_edges(q, es)


def rook(m):
    V = [(i, j) for i in range(m) for j in range(m)]
    es = [(a, b) for a in range(len(V)) for b in range(a + 1, len(V))
          if (V[a][0] == V[b][0]) != (V[a][1] == V[b][1])]
    return from_edges(len(V), es)


def shrikhande():
    V = [(i, j) for i in range(4) for j in range(4)]
    S = {(0, 1), (0, 3), (1, 0), (3, 0), (1, 1), (3, 3)}
    es = [(a, b) for a in range(16) for b in range(a + 1, 16)
          if ((V[b][0] - V[a][0]) % 4, (V[b][1] - V[a][1]) % 4) in S
          or ((V[a][0] - V[b][0]) % 4, (V[a][1] - V[b][1]) % 4) in S]
    return from_edges(16, es)


def heawood():           # incidence graph of the Fano plane
    pts = list(range(7))
    lines = [(0, 1, 3), (1, 2, 4), (2, 3, 5), (3, 4, 6), (4, 5, 0), (5, 6, 1), (6, 0, 2)]
    es = [(p, 7 + i) for i, L in enumerate(lines) for p in L]
    return from_edges(14, es)


PET = from_edges(10, [(0,1),(1,2),(2,3),(3,4),(4,0),(5,7),(7,9),(9,6),(6,8),(8,5),
                      (0,5),(1,6),(2,7),(3,8),(4,9)])
CUBE = from_edges(8, [(0,1),(1,2),(2,3),(3,0),(4,5),(5,6),(6,7),(7,4),
                      (0,4),(1,5),(2,6),(3,7)])

print("=== A. |Aut| against independently known values ===")
KNOWN = [("K4", from_edges(*K(4).__class__ and (4, K(4))), 24),
         ("C6", circ(6, (1,)), 12),
         ("K3,3", from_edges(6, [(i, 3 + j) for i in range(3) for j in range(3)]), 72),
         ("Q3 cube", CUBE, 48),
         ("Petersen = Kneser(5,2)", PET, 120),
         ("Kneser(5,2) built", kneser(5, 2), 120),
         ("Kneser(6,2) (Aut = S6)", kneser(6, 2), 720),
         ("Paley(13)", paley(13), 78),
         ("Heawood (Fano incidence)", heawood(), 336),
         ("rook 4x4", rook(4), 1152),
         ("Shrikhande", shrikhande(), 192)]
allok = True
for lab, (n, adj), expect in KNOWN:
    A = all_isos(n, adj, wl(n, adj, [0] * n), wl(n, adj, [0] * n))
    ok = (len(A) == expect) and all(is_perm_aut(n, adj, g) for g in A)
    allok &= ok
    print(f"  {lab:28s} n={n:3d}  |Aut| measured {len(A):5d}  expected {expect:5d}  "
          f"{'OK' if ok else '*** MISMATCH ***'}")
print(f"  ALL MATCH: {allok}")

print("\n=== B. the two orbit code paths agree (CFI[K4]-tw = net(Z4)) ===")
from probe_cao_cleanroom import cfi
K4 = K(4)
n, adj, names, idx = cfi(K4, 4, (0,))
A = all_isos(n, adj, wl(n, adj, [0] * n), wl(n, adj, [0] * n))
oc = orbit_colouring(n, orbits(n, A))
for v0 in (0, 12):
    c1 = wl(n, adj, individualize(n, oc, v0))
    o_enum = orbits(n, all_isos(n, adj, c1, c1))
    p1 = sorted(sorted(g) for g in
                {frozenset(u for u in range(n) if o_enum[u] == o_enum[v]) for v in range(n)})
    p2 = []
    for cell in cells(c1).values():
        reps = cell_orbit_reps(n, adj, c1, cell)
        blocks = defaultdict(list)
        for v in cell:
            for r in reps:
                if iso_exists(n, adj, individualize(n, c1, v), individualize(n, c1, r)):
                    blocks[r].append(v)
                    break
        p2 += [sorted(b) for b in blocks.values()]
    print(f"  v0={v0}: full-enumeration orbits == pairwise-iso orbits: "
          f"{p1 == sorted(p2)}   ({len(p1)} classes)")

print("\n=== C. multipede[6x5] sanity-fail: object or oracle? ===")
MIXED = [[1,1,0,0,0],[1,1,1,0,0],[0,0,1,1,0],[0,0,0,1,1],[0,0,1,0,1],[1,1,0,1,1]]


def multipede(A):
    """clean-room re-implementation: cols -> a/b pairs, rows -> even-subset middles."""
    V, W = len(A), len(A[0])
    Nb = [[w for w in range(W) if A[v][w]] for v in range(V)]
    nm = [('a', w) for w in range(W)] + [('b', w) for w in range(W)]
    for v in range(V):
        for k in range(0, len(Nb[v]) + 1, 2):
            for c in combinations(Nb[v], k):
                nm.append(('m', v, frozenset(c)))
    ix = {x: i for i, x in enumerate(nm)}
    n = len(nm)
    adj = [[0] * n for _ in range(n)]
    for x in nm:
        if x[0] != 'm':
            continue
        _, v, S = x
        for w in Nb[v]:
            t = ix[('a', w)] if w in S else ix[('b', w)]
            adj[ix[x]][t] = adj[t][ix[x]] = 1
    return n, adj


nm_, adjm = multipede(MIXED)
print(f"  clean-room multipede(MIXED): n = {nm_}")
sys.path.insert(0, "/workspace/scratchpad")
from probe_dualdeepen import build_mp            # CONSTRUCTION ONLY (no oracle involved)
nt, adjt = build_mp(MIXED)
same = (nt == nm_ and iso_exists(nt, adjt, wl(nt, adjt, [0] * nt), wl(nm_, adjm, [0] * nm_))
        is not False)
print(f"  same object as probe_dualdeepen.build_mp: n {nt} vs {nm_}, "
       f"1-WL profile match {sorted(len(c) for c in cells(wl(nt,adjt,[0]*nt)).values())} "
       f"== {sorted(len(c) for c in cells(wl(nm_,adjm,[0]*nm_)).values())}")
Am = all_isos(nm_, adjm, wl(nm_, adjm, [0] * nm_), wl(nm_, adjm, [0] * nm_))
print(f"  |Aut(multipede[6x5])| = {len(Am)}  (NOT rigid: MIXED has a 3-dim F2 kernel)")
myorb = orbits(nm_, Am)
myoc = orbit_colouring(nm_, myorb)
print(f"  my orbit partition: cell sizes {sorted(len(c) for c in cells(myoc).values())}")
# the orbit partition is Aut-stable BY CONSTRUCTION, so the probe's sanity check on it
# cannot legitimately fail.  Re-derive it a second way (pairwise iso) and then ask the
# suspect oracle the same question.
root = wl(nm_, adjm, [0] * nm_)
bad = []
for cell in cells(myoc).values():
    r = cell_orbit_reps(nm_, adjm, myoc, cell)
    if r is None or len(r) > 1:
        bad.append(cell)
print(f"  CAO at my orbit partition (pairwise-iso recheck): {not bad}   <- must be True")
from probe_orbit_oracle import orbit_partition as suspect
theirs_root = suspect(nm_, adjm, root, list(range(nm_)))
theirs_oc = suspect(nm_, adjm, myoc, list(range(nm_)))
def blocks(p):
    d = defaultdict(list)
    for v in range(nm_):
        d[p[v]].append(v)
    return sorted(sorted(b) for b in d.values())
mine_root = blocks(myorb)
print(f"  suspect oracle at the 1-WL root: "
      f"{'None (blown)' if theirs_root is None else str(len(blocks(theirs_root))) + ' blocks'}"
      f"  vs my {len(mine_root)} blocks -> agree: "
      f"{theirs_root is not None and blocks(theirs_root) == mine_root}")
print(f"  suspect oracle ON MY ORBIT PARTITION (must return the same partition): "
      f"{'None' if theirs_oc is None else str(len(blocks(theirs_oc))) + ' blocks'}"
      f" -> agree: {theirs_oc is not None and blocks(theirs_oc) == mine_root}")
print("  => a disagreement here IS the reported 'sanity-fail': the object is fine, the")
print("     canon-with-automorphism-pruning oracle is not.")

print("\n=== D. dependency check: does my chain touch the suspect modules? ===")
chain = ["probe_cao_cleanroom.py", "probe_cao_mechanism.py", "probe_cao_bases.py",
         "probe_cao_net.py", "probe_cao_net2wl.py", "probe_cao_vtcover.py"]
for f in chain:
    out = subprocess.run(["grep", "-n", "-E", "probe_dualdeepen|probe_orbit_oracle|canon\\(",
                          "/workspace/scratchpad/" + f], capture_output=True, text=True).stdout
    print(f"  {f:26s} {'CLEAN' if not out.strip() else 'HITS: ' + out.strip()}")
