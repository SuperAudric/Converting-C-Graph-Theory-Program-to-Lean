import sys
from itertools import combinations, permutations
import numpy as np
import probe_cao_lemma_check_np as base

L = base.L; NS = base.NS
idx = {}
for k,(i,j) in enumerate(base.PAIRS): idx[(i,j)]=idx[(j,i)]=k
# canonical form of (graph c, marked vertex i) under S_L
def canon(c, i):
    # relabel by p: the image graph has edge {p[a],p[b]} iff c has edge {a,b}; marked vertex p[i]
    best = None
    for p in permutations(range(L)):
        bits = 0
        for k,(a,b) in enumerate(base.PAIRS):
            if (c >> k) & 1: bits |= (1 << idx[(p[a],p[b])])
        key = (p[i], bits)
        if best is None or key < best: best = key
    return best
iso = {canon(c,i) for c in range(base.NC) for i in range(L)}
diag,_ = base.build()
mu = len(set(diag.reshape(-1).tolist()))
print(f"L={L}:  (graph, marked vertex) ISO CLASSES = {len(iso)}   mu-CLASSES = {mu}")
print(f"  ==> M-2WL is {'COMPLETE (vacuous!)' if len(iso)==mu else 'INCOMPLETE — informative'} at L={L}")
