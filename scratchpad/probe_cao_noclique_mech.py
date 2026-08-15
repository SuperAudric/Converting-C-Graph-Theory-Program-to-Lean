"""Does dropping the payload clique break the mechanism that made a(c,i) complete?"""
import sys
from itertools import permutations
import numpy as np
import probe_cao_noclique as base

L, NS = base.L, base.NS
diag, prof = base.build()
dflat, pflat = diag.reshape(-1), prof.reshape(-1, 2*NS)
seen, clash = {}, 0
for c in range(base.NC):
    for i in range(L):
        k = (i, tuple(prof[c, i].tolist()))
        if k in seen and seen[k] != c: clash += 1
        seen[k] = c
print(f"(1) a(c,i) determines c: {clash==0}   [{clash} collisions]")
srt = np.sort(pflat, axis=1)
inj = int((srt[:,1:] != srt[:,:-1]).all(axis=1).sum())
print(f"(2) injective on typed slots: {inj} / {len(pflat)}")
idx = {}
for k,(i,j) in enumerate(base.PAIRS): idx[(i,j)]=idx[(j,i)]=k
perms=[]
for p in permutations(range(L)):
    m=np.empty(2*NS,dtype=np.int64)
    for k,(a,b) in enumerate(base.PAIRS):
        kk=idx[(p[a],p[b])]
        for t in (0,1): m[2*k+t]=2*kk+t
    perms.append(m)
perms=np.stack(perms)
orbs={min(tuple(w) for w in pflat[r][perms].tolist()) for r in range(len(pflat))}
print(f"(3) S_L-orbits of a: {len(orbs)}    mu-classes: {len(set(dflat.tolist()))}")
