#!/usr/bin/env python3
"""HUNT (targeted): VT graphs whose descent reaches a SMALL-stabiliser non-discrete node.

The expensive sweeps waste all their time enumerating LARGE stabilisers -- which are exactly
the cases that cannot be hits.  Lagrange: a cell of size c is a single orbit only if
c | |Aut_chi|, so the sharp case is |Aut_chi| SMALL while the colouring is still coarse.
So: enumerate the stabiliser with a small budget and SKIP on blow-up (big group => not sharp).

  T1  chooseIdK (lowest id) picks a mixed cell            -> refutes the literal Lean lemma
  T2  every non-singleton cell mixed at a reachable node  -> refutes it under ANY selector,
      backtracking included.  T2 <=> a reachable node has stabiliser too small for any of its
      cells (extremal case: trivial stabiliser + non-discrete colouring).

Reports the NEAR-MISS census even when there are no hits: for each analysed graph, the
smallest stabiliser reached on a legal descent, and the largest mixed-cell fraction seen.
"""
import sys, itertools
from collections import defaultdict
sys.path.insert(0, "/workspace/scratchpad")
from probe_cao_cleanroom import wl, individualize, cells, all_isos, orbits
from probe_vt_hunt import GROUPS, cayley, connected

sys.setrecursionlimit(100000)
SMALL = 1500            # stabiliser-enumeration budget; blow-up => group too big to be sharp


def stab(n, adj, col):
    try:
        return all_isos(n, adj, col, col, limit=SMALL)
    except RuntimeError:
        return None


def analyse(n, adj):
    """Walk the descent tree. Returns (t1_ok, t2_ok, minstab, worst_mixed_fraction, note)."""
    root = wl(n, adj, [0] * n)
    c1 = wl(n, adj, individualize(n, root, 0))
    if len(set(c1)) == n:
        return None                                     # discretizes => Tinhofer
    memo, seen = {}, []

    def node(col):
        key = tuple(col)
        if key in memo:
            return memo[key]
        d = cells(col)
        ns = [c for c in sorted(d) if len(d[c]) > 1]
        if not ns:
            memo[key] = (True, True)
            return memo[key]
        A = stab(n, adj, col)
        if A is None:
            memo[key] = (True, True)                    # big group: not the sharp case
            seen.append((None, len(ns), 0))
            return memo[key]
        o = orbits(n, A)
        nm = sum(1 for c in ns if len({o[v] for v in d[c]}) > 1)
        seen.append((len(A), len(ns), nm))
        ex, lo = False, False
        for i, c in enumerate(ns):
            cell = d[c]
            if len({o[v] for v in cell}) > 1:
                continue
            e2, l2 = node(wl(n, adj, individualize(n, col, cell[0])))
            ex = ex or e2
            if i == 0:
                lo = l2
        memo[key] = (ex, lo)
        return memo[key]

    ex, lo = node(c1)
    known = [s for s in seen if s[0] is not None]
    minstab = min((s[0] for s in known), default=None)
    worst = max((s[2] / s[1] for s in known), default=0.0)
    return (lo, ex, minstab, worst, f"nodes={len(seen)} unknown={len(seen)-len(known)}")


print("targeted sweep over Cayley graphs (VT for free)")
tested = nondisc = 0
t1, t2, near = [], [], []
census = defaultdict(int)
for G in GROUPS:
    classes, used = [], set()
    for e in G.els:
        if e == G.e or e in used:
            continue
        ie = G.inv[e]
        used.add(e)
        used.add(ie)
        classes.append((e,) if e == ie else (e, ie))
    for r in range(1, min(len(classes), 4) + 1):
        for combo in itertools.combinations(classes, r):
            S = [x for c in combo for x in c]
            if not (2 <= len(S) <= 7):
                continue
            n, adj = cayley(G, S)
            if not connected(n, adj):
                continue
            root = wl(n, adj, [0] * n)
            if len(set(root)) != 1:
                continue
            tested += 1
            res = analyse(n, adj)
            if res is None:
                census["discretizes"] += 1
                continue
            nondisc += 1
            lo, ex, minstab, worst, note = res
            census[f"minstab={minstab}"] += 1
            tag = (f"{G.name}(|S|={len(S)}) n={n} minstab={minstab} "
                   f"worst-mixed-frac={worst:.2f} {note}")
            if worst > 0:
                near.append(tag)
            if lo is False:
                t1.append(tag)
            if ex is False:
                t2.append(tag)
    print(f"  ...{G.name:12s} done   tested={tested} nondisc={nondisc} "
          f"near={len(near)} T1={len(t1)} T2={len(t2)}", flush=True)

print(f"\nVT Cayley graphs tested: {tested}")
print(f"  1-WL discretizes after one individualization (=> Tinhofer): {census['discretizes']}")
print(f"  non-discretizing (the only place a hit can live): {nondisc}")
print("  census by smallest stabiliser reached on a legal descent:")
for k, v in sorted(census.items()):
    if k != "discretizes":
        print(f"      {k:16s} {v}")
print(f"\n  NEAR MISS (some reachable node has a mixed cell): {len(set(near))}")
for h in sorted(set(near))[:20]:
    print(f"     {h}")
print(f"\n  T1 (chooseIdK picks a mixed cell): {len(set(t1))}")
for h in sorted(set(t1))[:20]:
    print(f"     * {h}")
print(f"\n  T2 (every cell mixed at a reachable node -- defeats backtracking): {len(set(t2))}")
for h in sorted(set(t2))[:20]:
    print(f"     ** {h}")
