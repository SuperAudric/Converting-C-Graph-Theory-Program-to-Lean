"""probe_cao_lemma_check.py — PHASE 0 of the item-1 proof plan: does the lemma hold beyond L=4?

THE LEMMA (section 6d.8).  Write a(c,i) for the slot profile (k,t) -> M(c)-colour of (p(i), f(k,t)),
and mu_c(i,i) for the M-diagonal colour.  Then for fixed (c,i) the multiset

    Phi(c,i) = {{ ( mu_{c'}(l,l),  Align( a(c,i), b(c',l) ) )  :  c' in {0,1}^S,  l in [L] }}
    Align(a,b) = the contingency table {{ (a_kt, b_kt) : (k,t) }}

is determined by mu_c(i,i).

★ THE POINT OF RUNNING IT HERE: the lemma mentions only M-data.  No ensemble, no 2^d-vertex graph.
So it can be tested at L=5 (1024 copies, M = 25 vertices each) even though the L=5 ensemble (6164
vertices at 2-WL) is far out of reach.  The section 6d collapse was only ever verified at L=4; if the
lemma fails at L=5 then the collapse fails there too, and every M-based verdict (Shrikhande/rook,
CFI[K4]) stops being about the ensemble.

Falsification form: for each mu-class take up to REPS representatives and compare their Phi.  Any
disagreement refutes the lemma outright; agreement across all classes is evidence, not proof.
"""

import sys
from itertools import combinations

L = int(sys.argv[1]) if len(sys.argv) > 1 else 5
REPS = int(sys.argv[2]) if len(sys.argv) > 2 else 3
PAIRS = list(combinations(range(L), 2))
NS = len(PAIRS)
NC = 1 << NS
SLOT = {}
for k, (i, j) in enumerate(PAIRS):
    SLOT[(i, j)] = SLOT[(j, i)] = k
ROUNDS = 10

NV = L + 2 * NS
BASE_NBR = [[] for _ in range(NV)]
for a in range(L):
    for b in range(L):
        if a != b:
            BASE_NBR[a].append(b)
for k in range(NS):
    BASE_NBR[L + 2 * k].append(L + 2 * k + 1)
    BASE_NBR[L + 2 * k + 1].append(L + 2 * k)

FCLS = {}
for k in range(NS):
    for t in (0, 1):
        for kk in range(NS):
            for tt in (0, 1):
                FCLS[(k, t, kk, tt)] = (t, tt, len(set(PAIRS[k]) & set(PAIRS[kk])))


def m_colours(c, intern):
    """2-WL on M(c) with the frame frozen; returns (diagonal colours, slot profiles a(i))."""
    adj = set()
    for a in range(L):
        for b in range(L):
            if a != b:
                adj.add((a, b))
    for k, (i, j) in enumerate(PAIRS):
        f = L + 2 * k + ((c >> k) & 1)
        for x in (i, j):
            adj.add((x, f))
            adj.add((f, x))
    for k in range(NS):
        adj.add((L + 2 * k, L + 2 * k + 1))
        adj.add((L + 2 * k + 1, L + 2 * k))

    n = NV
    col = [0] * (n * n)
    frozen = [False] * (n * n)
    for x in range(n):
        for y in range(n):
            p = x * n + y
            if x >= L and y >= L:
                key = ('F',) + FCLS[((x - L) // 2, (x - L) % 2, (y - L) // 2, (y - L) % 2)] + (x == y,)
                frozen[p] = True
            else:
                key = (x == y, (x, y) in adj, x < L, y < L,
                       -1 if x < L else (x - L) % 2, -1 if y < L else (y - L) % 2)
            col[p] = intern.setdefault(key, len(intern))
    rng = range(n)
    for _ in range(ROUNDS):
        C = max(col) + 1
        new = [0] * (n * n)
        for a in rng:
            ra = col[a * n:(a + 1) * n]
            for b in rng:
                p = a * n + b
                if frozen[p]:
                    new[p] = col[p]
                    continue
                cnt = {}
                for z in rng:
                    kk = ra[z] * C + col[z * n + b]
                    cnt[kk] = cnt.get(kk, 0) + 1
                new[p] = intern.setdefault((col[p], tuple(sorted(cnt.items()))), len(intern))
        col = new
    diag = [col[i * n + i] for i in range(L)]
    prof = [tuple(col[i * n + (L + j)] for j in range(2 * NS)) for i in range(L)]
    return diag, prof


def align(a, b):
    t = {}
    for x, y in zip(a, b):
        t[(x, y)] = t.get((x, y), 0) + 1
    return tuple(sorted(t.items()))


if __name__ == '__main__':
    print(f'L={L}: {NC} copies, M(c) = {NV} vertices, {REPS} representatives per mu-class',
          flush=True)
    intern = {}
    diag, prof = {}, {}
    for c in range(NC):
        d, p = m_colours(c, intern)
        for i in range(L):
            diag[(c, i)] = d[i]
            prof[(c, i)] = p[i]
        if c % 256 == 0:
            print(f'  ...M({c})', flush=True)
    classes = {}
    for k, v in diag.items():
        classes.setdefault(v, []).append(k)
    print(f'M-diagonal classes: {len(classes)}   (payload vertices: {len(diag)})', flush=True)

    allkeys = list(prof)
    bad = 0
    checked = 0
    for v, members in sorted(classes.items()):
        reps = members[:REPS]
        if len(reps) < 2:
            continue
        sigs = []
        for (c, i) in reps:
            a = prof[(c, i)]
            ms = {}
            for (cp, l) in allkeys:
                kk = (diag[(cp, l)], align(a, prof[(cp, l)]))
                ms[kk] = ms.get(kk, 0) + 1
            sigs.append(tuple(sorted(ms.items())))
        checked += 1
        if len(set(sigs)) > 1:
            bad += 1
            if bad <= 3:
                print(f'  ⛔ mu-class {v} (size {len(members)}): Phi DIFFERS across representatives',
                      flush=True)
    print(f'\nmu-classes with >=2 members checked: {checked}')
    print(f'==> LEMMA HOLDS at L={L} (on the checked representatives): {bad == 0}'
          f'   [{bad} violations]')
