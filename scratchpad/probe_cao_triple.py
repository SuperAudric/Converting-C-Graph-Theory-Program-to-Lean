"""probe_cao_triple.py — the reader's TRIPLE-slot extension: does raising the slot arity help?

Slots are TRIPLES T instead of pairs; each slot carries a 4-value gauge (a P4 "line"), and every
payload vertex i in T attaches to the gauge vertex matching that triple's label.  Copies are
arbitrary labellings lab : triples -> {0,1,2,3} (that is what makes a gauge group act at all --
see the note in the report; triple EDGE-COUNTS are not closed under a shift).

THE ONE QUESTION THAT MATTERS.  Doc section 6e.4b: the pair-slot encoding dies because
(p(i), f(k,t)) counts common payload neighbours {j in k} exactly when c_k = t, so ONE round reveals
every slot's value and a(c,i) reads off the whole payload.  With triples the same count is |T \\ {i}|
= 3 (or 2) versus 0.  If a(c,i) still determines lab, the extension changes nothing.
"""
import sys, time
from itertools import combinations
import numpy as np

L = int(sys.argv[1]) if len(sys.argv) > 1 else 4
SAMPLE = int(sys.argv[2]) if len(sys.argv) > 2 else 0     # 0 = all labellings
TRIP = list(combinations(range(L), 3))
NT = len(TRIP)
NV = L + 4 * NT
ROUNDS = 12

rng = np.random.default_rng(0)
if SAMPLE:
    labs = rng.integers(0, 4, size=(SAMPLE, NT))
else:
    labs = np.array([[(c >> (2 * t)) & 3 for t in range(NT)] for c in range(4 ** NT)])
NC = len(labs)

adj = np.zeros((NC, NV, NV), dtype=bool)
for a in range(L):
    for b in range(L):
        if a != b:
            adj[:, a, b] = True                                   # payload clique
for t in range(NT):
    for m in range(3):                                            # the P4 "line" gauge
        adj[:, L + 4 * t + m, L + 4 * t + m + 1] = True
        adj[:, L + 4 * t + m + 1, L + 4 * t + m] = True
for t, T in enumerate(TRIP):
    for m in range(4):
        hit = labs[:, t] == m
        for i in T:
            adj[hit, i, L + 4 * t + m] = True
            adj[hit, L + 4 * t + m, i] = True

sort = np.zeros(NV, dtype=np.int64)
sort[L:] = 1 + (np.arange(L, NV) - L) % 4                          # gauge position on the line
eye = np.eye(NV, dtype=bool)
col = (((sort[:, None] * 6 + sort[None, :]) * 2 + eye)[None, :, :] * 2 + adj).astype(np.int64)
_, col = np.unique(col, return_inverse=True); col = col.reshape(NC, NV, NV)

t0 = time.time()
prev = -1
for r in range(ROUNDS):
    C = int(col.max()) + 1
    rows = np.concatenate([col[:, :, :, None].transpose(0, 1, 3, 2) * 0 + 0], axis=0)  # placeholder
    k = np.sort(col[:, :, None, :] * C + col.transpose(0, 2, 1)[:, None, :, :], axis=3)
    key = np.concatenate([col[:, :, :, None], k], axis=3).reshape(-1, NV + 1)
    v = np.ascontiguousarray(key).view([('', np.int64)] * (NV + 1)).ravel()
    tab = np.unique(v)
    col = np.searchsorted(tab, v).reshape(NC, NV, NV)
    if len(tab) == prev:
        break
    prev = len(tab)

prof = col[:, :L, L:]
seen, clash = {}, 0
for c in range(NC):
    for i in range(L):
        key = (i, tuple(prof[c, i].tolist()))
        if key in seen and not np.array_equal(labs[seen[key]], labs[c]):
            clash += 1
        seen[key] = c
srt = np.sort(prof.reshape(-1, 4 * NT), axis=1)
inj = int((srt[:, 1:] != srt[:, :-1]).all(axis=1).sum())
print(f"L={L}, {NT} triples, {NC} labellings, M3 = {NV} vertices  ({time.time()-t0:.1f}s)")
print(f"  a(c,i) determines the labelling: {clash == 0}   [{clash} collisions]")
print(f"  profiles injective on all {4*NT} gauge vertices: {inj} / {len(srt)}")
