"""probe_cao_ensemble_audit.py — AUDIT of section 6's "the ensemble is passive" verdict.

section 6 concluded, from ONE pair (C6 vs 2C3 landing in the same cell 218), that the full rung-1
ensemble "gives 1-WL nothing beyond the two-copy model".  That inference has two holes and this
probe measures both.

HOLE 1 -- the ensemble's 1-WL may be far WEAKER than the two-copy model, not equal to it.
  In the ensemble the frame is SHARED: only 30 frame vertices carry all 2^15 copies.  S_6 is
  transitive on slots and m(0) marks type 0, so the frame can only ever hold TWO colours, forever.
  A payload vertex p(c,i) then sees:  5 clique neighbours (all of them, K6 -- so adjacency is NOT
  visible there) + one frame neighbour per slot, contributing only a COUNT of type-0.  That count
  is deg_{G_c}(i).  Iterating adds the multiset of the other five colours.  So the fixpoint should
  be exactly
                       colour(c,i)  =  (degree sequence of G_c,  deg(i))
  i.e. the ensemble's 1-WL sees the degree sequence and NOTHING else.  PREDICTION: 292 cells.

HOLE 2 -- the witness pair cannot detect hole 1.  C6 and 2C3 are both 2-REGULAR, so they are
  identical under the weakest invariant there is.  A test whose witness is degree-blind cannot
  distinguish "the ensemble equals the two-copy model" from "the ensemble sees only degrees".

CONTROL -- the two-copy disjoint frame model (probe_cao_triangle_frame.py's `disjoint` shape, which
  is what the payload admission test is calibrated on) has a PRIVATE frame vertex per pair per copy,
  so those DO refine.  Count its payload classes.  If it is strictly finer than the ensemble, the
  admission test is calibrated on a strictly stronger object than the construction.
"""

from itertools import combinations

L = 6
PAIRS = list(combinations(range(L), 2))
NS = len(PAIRS)
NC = 1 << NS


def degs(c):
    d = [0] * L
    for k, (i, j) in enumerate(PAIRS):
        if (c >> k) & 1:
            d[i] += 1
            d[j] += 1
    return d


# ---------------------------------------------------------------- prediction for the ensemble
pred = set()
pred_of = {}
for c in range(NC):
    d = degs(c)
    ds = tuple(sorted(d))
    for i in range(L):
        pred.add((ds, d[i]))
        pred_of[(c, i)] = (ds, d[i])
print(f'PREDICTED ensemble payload cells  (degree sequence, own degree) : {len(pred)}')
print('  section 6 measured                                            : 292')


# ---------------------------------------------------------------- true Aut_v = S_6 orbits
SLOT = {}
for k, (i, j) in enumerate(PAIRS):
    SLOT[(i, j)] = SLOT[(j, i)] = k


def s6_orbits():
    """union-find on payload vertices p(c,i) under two generators of S_6 -- the same routine
    probe_cao_ensemble.py uses, so the 544 being reproduced here is a genuine cross-check of it."""
    gens = [[1, 0, 2, 3, 4, 5], [1, 2, 3, 4, 5, 0]]
    par = list(range(L * NC))

    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x

    for pi in gens:
        smap = [SLOT[(pi[i], pi[j])] for (i, j) in PAIRS]
        for c in range(NC):
            cc = 0
            for k in range(NS):
                if (c >> k) & 1:
                    cc |= 1 << smap[k]
            for i in range(L):
                a, b = find(c * L + i), find(cc * L + pi[i])
                if a != b:
                    par[a] = b
    return {(c, i): find(c * L + i) for c in range(NC) for i in range(L)}


canon = s6_orbits()
orbits = set(canon.values())
print(f'TRUE Aut_v = S_6 orbits on the payload                          : {len(orbits)}')
print('  section 6 measured                                            : 544')

mixed = {}
for k, p in pred_of.items():
    mixed.setdefault(p, set()).add(canon[k])
nmixed = sum(1 for o in mixed.values() if len(o) > 1)
print(f'MIXED cells under the prediction                                : {nmixed}')
print('  section 6 measured                                            : 100')


# ------------------------------------------- the two-copy DISJOINT frame model, same 1-WL question
NBR = [[] for _ in range(L + NS)]
for a in range(L):
    for b in range(L):
        if a != b:
            NBR[a].append(b)                      # K_L payload: adjacency lives ONLY in the frame
for k, (i, j) in enumerate(PAIRS):
    NBR[i].append(L + k)
    NBR[j].append(L + k)
    NBR[L + k] += [i, j]

# ⚠ every component must be refined for the SAME number of rounds.  Components are disjoint, so
# per-component refinement with a global intern dict is 1-WL on the union -- but only in lockstep:
# stopping each component at its own fixpoint returns colours from different rounds, which are
# different namespaces and are NOT comparable.  (That bug made this read 520 on the first run.)
ROUNDS = L + NS + 1


def frame_colours(c, intern):
    """1-WL on ONE encoded copy: L payload forming a clique + a PRIVATE typed frame vertex on every
    pair -- probe_cao_triangle_frame.py's `disjoint` shape, i.e. what the admission test is
    calibrated on."""
    col = [0] * L + [1 + ((c >> k) & 1) for k in range(NS)]
    for _ in range(ROUNDS):
        new = []
        for v in range(L + NS):
            cnt = {}
            for z in NBR[v]:
                cnt[col[z]] = cnt.get(col[z], 0) + 1
            key = (col[v], tuple(sorted(cnt.items())))
            new.append(intern.setdefault(key, len(intern)))
        col = new
    return col[:L]


intern = {}
fm = {}
for c in range(NC):
    cc = frame_colours(c, intern)
    for i in range(L):
        fm[(c, i)] = cc[i]
print(f'TWO-COPY DISJOINT frame model, payload cells                    : {len(set(fm.values()))}')

fmix = {}
for k, p in fm.items():
    fmix.setdefault(p, set()).add(canon[k])
print(f'  mixed cells under it                                          : '
      f'{sum(1 for o in fmix.values() if len(o) > 1)}')

# is the frame model strictly finer than the ensemble?
refines = all(len({pred_of[k] for k in fm_keys}) == 1
              for fm_keys in
              [[k for k in fm if fm[k] == v] for v in set(fm.values())])
print(f'  frame model refines the ensemble prediction                   : {refines}')
c6 = sum(1 << SLOT[e] for e in [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (0, 5)])
c33 = sum(1 << SLOT[e] for e in [(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5)])
print(f'  C6 vs 2C3 under the frame model: cells {sorted({fm[(c6, i)] for i in range(L)})} '
      f'vs {sorted({fm[(c33, i)] for i in range(L)})}')
print(f'  C6 and 2C3 are both 2-regular  : {sorted(degs(c6)) == sorted(degs(c33)) == [2]*6}')
