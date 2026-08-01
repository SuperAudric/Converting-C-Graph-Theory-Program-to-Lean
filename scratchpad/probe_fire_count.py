#!/usr/bin/env python3
"""Does pre-running force at every level of the inner descent actually FIRE?
Counts key-firings per inner descent at the CFI m=8 pl node (|C|=16, one true orbit)."""
import sys
sys.setrecursionlimit(20000); sys.path.insert(0, "/workspace/scratchpad")
from probe_dualdeepen import build_cfi_base, cubic
from probe_polyloop import adjlist, refine, indiv, target_cell
from probe_inner_force import KEYS, force_fires, apply_split
from probe_inner_mech import node_of_interest

n, adj = build_cfi_base(cubic(8, 19), 8, False)
adjl = adjlist(n, adj)
col, cid, C = node_of_interest(n, adj)
print(f"node cell |C|={len(C)}")
for nm, kf in KEYS:
    fires = levels = 0
    c = indiv(n, adjl, col, min(C))          # anchor descent
    for _ in range(2 * n):
        cid2, C2 = target_cell(n, c)
        if cid2 is None: break
        ks = force_fires(n, adj, adjl, c, C2, kf)
        if ks is not None:
            fires += 1; c = apply_split(n, adjl, c, ks)
        else:
            levels += 1; c = indiv(n, adjl, c, min(C2))
    print(f"  {nm:<14}: key FIRED {fires} times, {levels} individualizations, reached discreteness={cid2 is None}")
