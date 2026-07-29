#!/usr/bin/env python3
"""
PROBE: the user's C3/C4 witness (2026-07-29), untested when proposed.

  "two disjoint copies of a vertex fully connected to two 1-WL blind groups, C3 and C4.
   Running consume on the two apexes, down one greedy descent it can go into C3 first in
   the first copy and C4 in the other."

Measures: (a) is the 14-cell 1-WL blind, (b) are the two apexes really ONE orbit,
(c) do the two greedy descents diverge, and (d) at which level, and was the cell there mixed.
"""
import sys
from collections import defaultdict

sys.path.insert(0, "/workspace/scratchpad")
from probe_dualdeepen import refine, indiv, target_cell
from probe_orbit_oracle import orbit_partition

def build(k1=3, k2=4, copies=2):
    """Each copy: apex joined to all of C_k1 and C_k2."""
    per = 1 + k1 + k2
    n = per * copies
    adj = [[0] * n for _ in range(n)]
    def E(a, b):
        adj[a][b] = adj[b][a] = 1
    for c in range(copies):
        b = c * per
        apex = b
        c3 = [b + 1 + i for i in range(k1)]
        c4 = [b + 1 + k1 + i for i in range(k2)]
        for i in range(k1):
            E(c3[i], c3[(i + 1) % k1])
        for i in range(k2):
            E(c4[i], c4[(i + 1) % k2])
        for v in c3 + c4:
            E(apex, v)
    return n, adj, [c * per for c in range(copies)], per, k1

def cells(col):
    d = defaultdict(list)
    for v, c in enumerate(col):
        d[c].append(v)
    return dict(d)

def greedy(n, adj, col, start):
    """Individualize `start`, then greedily individualize the min-index vertex of the
    target cell.  Returns the trace [(level, cell_id, cell, pick)]."""
    col = refine(n, adj, indiv(n, col, start))
    trace = []
    lvl = 0
    while True:
        cid, cell = target_cell(n, col)
        if cid is None:
            return trace, col
        pick = min(cell)
        trace.append((lvl, cid, list(cell), pick, list(col)))
        col = refine(n, adj, indiv(n, col, pick))
        lvl += 1

n, adj, apexes, per, k1 = build()
root = refine(n, adj, [0] * n)
print(f"n = {n}, apexes = {apexes}")
print(f"1-WL root cells: { {c: len(v) for c, v in sorted(cells(root).items())} }")

part = orbit_partition(n, adj, root, list(range(n)))
blocks = defaultdict(list)
for v in range(n):
    blocks[part[v]].append(v)
print(f"true Aut-orbits at root: {sorted(len(b) for b in blocks.values())}")
print(f"apexes same orbit? {part[apexes[0]] == part[apexes[1]]}")

# which 1-WL cell is overmerged?
for cid, cell in sorted(cells(root).items()):
    orbs = {part[v] for v in cell}
    if len(orbs) > 1:
        sizes = sorted(sum(1 for v in cell if part[v] == o) for o in orbs)
        print(f"  ★ root cell {cid} (size {len(cell)}) is OVERMERGED: orbit sizes {sizes}")

print()
tA, leafA = greedy(n, adj, root, apexes[0])
tB, leafB = greedy(n, adj, root, apexes[1])
print(f"descent from {apexes[0]}: {len(tA)} levels, picks {[t[3] for t in tA]}")
print(f"descent from {apexes[1]}: {len(tB)} levels, picks {[t[3] for t in tB]}")

def side(v):
    return "C3" if 1 <= (v % per) <= k1 else ("C4" if (v % per) > k1 else "apex")

print()
print(f"{'lvl':>3s} {'cellA':>16s} {'pickA':>6s} {'':4s} {'cellB':>16s} {'pickB':>6s}  cell mixed?")
for lvl in range(max(len(tA), len(tB))):
    a = tA[lvl] if lvl < len(tA) else None
    b = tB[lvl] if lvl < len(tB) else None
    if a is None or b is None:
        print(f"{lvl:3d}  *** one descent ended: lenA={len(tA)} lenB={len(tB)} ***")
        break
    pa = orbit_partition(n, adj, a[4], a[2])
    mixed = len({pa[v] for v in a[2]}) > 1
    tag = f"{side(a[3])}/{side(b[3])}"
    flag = "  <<< SPLIT PICK" if side(a[3]) != side(b[3]) else ""
    print(f"{lvl:3d} {str(a[2])[:16]:>16s} {a[3]:>6d} {tag:>4s} "
          f"{str(b[2])[:16]:>16s} {b[3]:>6d}  {mixed}{flag}")

# ── labelling sweep: does the min-index pick misalign under relabelling? ──────
import random
from probe_dualdeepen import relabel
random.seed(7)
div = aligned = 0
first_bad = None
for trial in range(300):
    sig = list(range(n)); random.shuffle(sig)
    a2 = relabel(n, adj, sig)
    ap = [sig[x] for x in apexes]
    r2 = refine(n, a2, [0]*n)
    p2 = orbit_partition(n, a2, r2, list(range(n)))
    if p2[ap[0]] != p2[ap[1]]:
        continue                                   # sanity: still one orbit
    tA2, _ = greedy(n, a2, r2, ap[0])
    tB2, _ = greedy(n, a2, r2, ap[1])
    # the two descents "align" iff the picked vertices correspond orbit-wise at every level
    ok = len(tA2) == len(tB2)
    if ok:
        for x, y in zip(tA2, tB2):
            pp = orbit_partition(n, a2, x[4], sorted(set(x[2]) | set(y[2])))
            if pp is None or pp[x[3]] != pp[y[3]]:
                ok = False; break
    if ok: aligned += 1
    else:
        div += 1
        if first_bad is None: first_bad = trial
print()
print(f"labelling sweep (300 random relabellings of the SAME graph):")
print(f"  descents ALIGNED (replay would verify):  {aligned}")
print(f"  descents DIVERGED (false negative):      {div}")
print(f"  => the same graph, same true orbits, outcome depends ONLY on the labelling")
