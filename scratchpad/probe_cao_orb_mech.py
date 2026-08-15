"""Does a(c,i) determine c?  If yes, ORB <=> `M`-2-WL complete, and section 6e.2's trap box is RIGHT.

MECHANISM (to be confirmed numerically).  In M(c) the payload is a CLIQUE, so for ANY slot k the pair
(p(i), f(k,t)) has common payload neighbours {j in k : c_k = t} -- size 2 (or 1 if i in k) when
c_k = t, and 0 otherwise.  So ONE refinement round makes the pair colour see c_k, for every slot,
including slots NOT containing i.  Hence a(c,i) reads off the whole of c.
"""
import sys
from itertools import permutations
import numpy as np
import probe_cao_lemma_check_np as base

L, NS = base.L, base.NS
diag, prof = base.build()
dflat, pflat = diag.reshape(-1), prof.reshape(-1, 2 * NS)

# (1) does the labelled profile a(c,i) determine the copy c?
lab = {}
bad = 0
for c in range(base.NC):
    for i in range(L):
        key = (i, tuple(prof[c, i].tolist()))
        if key in lab and lab[key] != c:
            bad += 1
        lab[key] = c
print(f"(1) a(c,i) determines c (labelled): {bad == 0}   [{bad} collisions]")

# (2) how many S_L-orbits do the profiles have, vs (graph, marked vertex) iso classes?
idx = {}
for k, (i, j) in enumerate(base.PAIRS):
    idx[(i, j)] = idx[(j, i)] = k
perms = []
for p in permutations(range(L)):
    m = np.empty(2 * NS, dtype=np.int64)
    for k, (a, b) in enumerate(base.PAIRS):
        kk = idx[(p[a], p[b])]
        for t in (0, 1):
            m[2 * k + t] = 2 * kk + t
    perms.append(m)
perms = np.stack(perms)
orbs = set()
for r in range(len(pflat)):
    orbs.add(min(tuple(v) for v in pflat[r][perms].tolist()))
print(f"(2) S_L-orbits of a(c,i): {len(orbs)}      mu-classes: {len(set(dflat.tolist()))}")
print(f"    ==> orbit of a is {'AS FINE AS' if len(orbs) == len(set(dflat.tolist())) else 'FINER THAN'} mu")
