#!/usr/bin/env python3
"""
PROBE 4b — repair of probe_grr_blind.py, which was VACUOUS.

probe 4 tested 594 VT Cay(Z2^k,S) and found **0 GRRs**: every stabiliser orbit profile was
large ([2,4,6,16], [2,3,24], ...), i.e. the vertex stabiliser was never trivial.  Cause:
|S| was capped at k+3, far too small -- a small connection set always retains GL(k,2)
symmetry (a basis of size k has an S_k stabiliser).  So the user's sharp case
(GRR = trivial stabiliser) was NEVER REACHED.

The sharp question is a RACE between two collapses as |S| grows:

    (a) Stab(S) collapses to trivial   -> the graph becomes a GRR
    (b) 1-WL starts discretizing after ONE individualization

If (a) ever happens while (b) has not, `VT => Tinhofer` is REFUTED.
If they always collapse together, that is real (partial) evidence FOR the lemma.

This probe sweeps |S| upward and reports both quantities side by side.
"""
import sys, random
from collections import defaultdict
from itertools import product

sys.path.insert(0, "/workspace/scratchpad")
from probe_dualdeepen import refine, indiv
from probe_orbit_oracle import orbit_partition

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

def cells(col):
    d = defaultdict(list)
    for v, c in enumerate(col):
        d[c].append(v)
    return list(d.values())

random.seed(11)
print("Race: does Stab collapse to trivial BEFORE 1-WL discretizes?")
print(f"{'k':>2s} {'|S|':>4s} {'n':>3s} {'cols after indiv':>17s} {'discrete?':>10s} "
      f"{'max stab orbit':>15s} {'GRR?':>5s}  verdict")
print("-" * 92)

refutations = []
grr_seen = 0
for k in (4, 5):
    n = 2 ** k
    els = [e for e in product(range(2), repeat=k) if any(e)]
    for sz in range(k, min(len(els), 3 * k) + 1):
        best = None
        for trial in range(40):
            S = random.sample(els, sz)
            n_, adj = cayley_z2k(k, S)
            root = refine(n_, adj, [0] * n_)
            if len(set(root)) != 1:
                continue
            c1 = refine(n_, adj, indiv(n_, root, 0))
            ncol = len(set(c1))
            disc = (ncol == n_)
            part = orbit_partition(n_, adj, c1, list(range(n_)))
            if part is None:
                continue
            mx = max(sum(1 for u in range(n_) if part[u] == part[v]) for v in range(n_))
            grr = (mx == 1)
            mixed = [c for c in cells(c1) if len({part[v] for v in c}) > 1]
            # keep the most informative trial for this (k, sz): prefer GRR, then non-discrete
            score = (2 if grr else 0) + (1 if not disc else 0)
            if best is None or score > best[0]:
                best = (score, ncol, disc, mx, grr, [len(c) for c in mixed], S)
            if grr:
                grr_seen += 1
            if mixed:
                refutations.append((k, sz, S, ncol, [len(c) for c in mixed]))
        if best is None:
            continue
        _, ncol, disc, mx, grr, mixed, S = best
        v = ("★★★ REFUTES VT=>Tinhofer" if mixed else
             ("GRR and discrete -> consistent" if grr else
              ("stab still nontrivial" if not grr else "")))
        print(f"{k:2d} {sz:4d} {n:3d} {ncol:17d} {str(disc):>10s} {mx:15d} "
              f"{str(grr):>5s}  {v}")

print("-" * 92)
print(f"GRR instances reached: {grr_seen}   refutations: {len(refutations)}")
if refutations:
    for k, sz, S, ncol, ms in refutations[:5]:
        print(f"  ★ k={k} |S|={sz} cols={ncol} mixed={ms} S={S}")
elif grr_seen == 0:
    print("  ⚠⚠ STILL ZERO GRRs — Z2^k is the wrong habitat; the sharp case remains UNTESTED.")
