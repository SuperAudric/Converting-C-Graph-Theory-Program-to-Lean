"""probe_cao_frame_tinhofer.py — is the BARE triangle frame Tinhofer, and where does the GROUP
individualization version break?

THE READER'S CLAIM (2026-08-13), two halves.

  (A) POSITIVE.  The bare frame -- L payload vertices plus one vertex per slot {a,b}, incidence only
      (this is the subdivision of K_L; its slot part is the triangular graph T(L) = J(L,2)) -- is
      TINHOFER: for EVERY set of individualized vertices, 1-WL reaches the orbit partition of the
      pointwise stabilizer.  Individualizing a payload vertex splits by distance; individualizing a
      slot vertex acts like individualizing its two endpoints to a COMMON colour.

  (B) THE STATED GAP.  "Tinhofer under any individualizations" vs "under any GROUP individualizations",
      where a SET of vertices receives one shared new colour (a cell split, not a point
      individualization).  Verified by the reader at group sizes 1 and 2; open at 3+.

WHAT THIS PROBE DOES.

  (A) For L = 5, 6: every subset of M's vertices of size <= 3, individualized POINTWISE (distinct
      colours), 1-WL to stability, cells vs the orbits of the pointwise stabilizer in S_L.
      Any single failure refutes (A).

  (B) Group-individualize a SET T of slot vertices to one shared colour.  ★ THE OBSERVATION THAT
      MAKES THIS DECIDABLE: a set of slots IS a graph H on the labels (T = E(H)), and the stabilizer
      of T in S_L is exactly Aut(H).  So (B) at group size |T| asks precisely whether 1-WL on the
      frame reaches Aut(H)-orbits -- i.e. whether every graph with |T| edges is 1-WL-orbit-correct.
      Swept exhaustively over all labelled H on 5 and 6 vertices, reporting the MINIMUM edge count
      at which it fails, then the named witness at 7.

Orbits are computed by brute force over S_L (L <= 7 => 5040 perms), so nothing here is heuristic.
"""

import sys
from itertools import combinations, permutations

ROUNDS = 30


def frame(L):
    """The bare frame: payload i -> ('p', i); slot {a,b} -> ('s', a, b) with a < b.  Incidence only."""
    verts = [('p', i) for i in range(L)] + [('s', a, b) for a, b in combinations(range(L), 2)]
    adj = {v: set() for v in verts}
    for a, b in combinations(range(L), 2):
        for x in (a, b):
            adj[('p', x)].add(('s', a, b))
            adj[('s', a, b)].add(('p', x))
    return verts, adj


def act(sigma, v):
    if v[0] == 'p':
        return ('p', sigma[v[1]])
    a, b = sigma[v[1]], sigma[v[2]]
    return ('s', min(a, b), max(a, b))


def wl1(verts, adj, col0):
    """1-WL to stability; returns the final colouring as a dict."""
    col = dict(col0)
    for _ in range(ROUNDS):
        key = {v: (col[v], tuple(sorted(col[u] for u in adj[v]))) for v in verts}
        table, new = {}, {}
        for v in verts:
            new[v] = table.setdefault(key[v], len(table))
        if len(set(new.values())) == len(set(col.values())):
            return new
        col = new
    return col


def orbits_of(perms, verts):
    """Orbit partition of `verts` under the given permutations of the labels."""
    idx = {v: i for i, v in enumerate(verts)}
    parent = list(range(len(verts)))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for s in perms:
        for v in verts:
            a, b = find(idx[v]), find(idx[act(s, v)])
            if a != b:
                parent[a] = b
    return {v: find(idx[v]) for v in verts}


def same_partition(a, b, keys):
    m1, m2 = {}, {}
    for k in keys:
        if m1.setdefault(a[k], b[k]) != b[k] or m2.setdefault(b[k], a[k]) != a[k]:
            return False
    return True


# ---------------------------------------------------------------- (A) pointwise individualization
def test_pointwise(L, maxset):
    verts, adj = frame(L)
    allperm = list(permutations(range(L)))
    bad = 0
    tested = 0
    for k in range(0, maxset + 1):
        for S in combinations(verts, k):
            tested += 1
            col0 = {v: 0 for v in verts}
            for j, v in enumerate(S):
                col0[v] = j + 1
            cells = wl1(verts, adj, col0)
            stab = [s for s in allperm if all(act(s, v) == v for v in S)]
            orb = orbits_of(stab, verts)
            if not same_partition(cells, orb, verts):
                bad += 1
                if bad <= 3:
                    print(f'  ⛔ L={L} pointwise {S}: cells != orbits '
                          f'({len(set(cells.values()))} vs {len(set(orb.values()))})', flush=True)
    print(f'  L={L}: {tested} individualization sets of size <= {maxset} -> '
          f'FAILURES {bad}   [(A) holds here: {bad == 0}]', flush=True)
    return bad


# ------------------------------------------------------- (B) group individualization of a slot set
def test_group(L, edge_cap=None, verbose_first=True):
    """T ranges over sets of slots; T = E(H), and the stabilizer of T is Aut(H)."""
    verts, adj = frame(L)
    slots = [v for v in verts if v[0] == 's']
    allperm = list(permutations(range(L)))
    ns = len(slots)
    first_fail = None
    fails = 0
    total = 0
    for mask in range(1 << ns):
        T = [slots[i] for i in range(ns) if mask >> i & 1]
        if edge_cap is not None and len(T) > edge_cap:
            continue
        total += 1
        Ts = set(T)
        col0 = {v: (1 if v in Ts else 0) for v in verts}
        cells = wl1(verts, adj, col0)
        stab = [s for s in allperm if {act(s, v) for v in T} == Ts]
        orb = orbits_of(stab, verts)
        if not same_partition(cells, orb, verts):
            fails += 1
            if first_fail is None or len(T) < first_fail[0]:
                first_fail = (len(T), T)
    print(f'  L={L}: {total} slot-sets tested -> FAILURES {fails}', flush=True)
    if first_fail and verbose_first:
        k, T = first_fail
        print(f'      ★ smallest failing GROUP SIZE at L={L}: {k}   T = '
              f'{[(t[1], t[2]) for t in T]}', flush=True)
    return first_fail


def named_witness(L, edges):
    """A specific H, embedded in L labels, checked as a group individualization."""
    verts, adj = frame(L)
    allperm = list(permutations(range(L)))
    T = [('s', min(a, b), max(a, b)) for a, b in edges]
    Ts = set(T)
    col0 = {v: (1 if v in Ts else 0) for v in verts}
    cells = wl1(verts, adj, col0)
    stab = [s for s in allperm if {act(s, v) for v in T} == Ts]
    orb = orbits_of(stab, verts)
    pay = [v for v in verts if v[0] == 'p']
    ok = same_partition(cells, orb, verts)
    print(f'  L={L}, |T|={len(T)}: |Aut|={len(stab)}  1-WL cells {len(set(cells.values()))} vs '
          f'orbits {len(set(orb.values()))}  -> Tinhofer: {ok}', flush=True)
    print(f'      payload: {len({cells[v] for v in pay})} cells vs '
          f'{len({orb[v] for v in pay})} orbits', flush=True)
    return ok


if __name__ == '__main__':
    which = sys.argv[1] if len(sys.argv) > 1 else 'all'

    if which in ('all', 'A'):
        print('=== (A) BARE FRAME, POINTWISE INDIVIDUALIZATION ===', flush=True)
        test_pointwise(4, 3)
        test_pointwise(5, 3)
        test_pointwise(6, 2)

    if which in ('all', 'B'):
        print('\n=== (B) GROUP INDIVIDUALIZATION OF A SLOT SET (T = E(H), stabilizer = Aut(H)) ===',
              flush=True)
        test_group(4)
        test_group(5)
        test_group(6, edge_cap=7)

        print('\n=== NAMED WITNESS: T = E(C3 disjoint-union C4), 7 slots, on L = 7 labels ===',
              flush=True)
        named_witness(7, [(0, 1), (1, 2), (2, 0),
                          (3, 4), (4, 5), (5, 6), (6, 3)])
        print('  control -- T = E(C3 + C3) on L = 6 (Aut IS transitive on the 6):', flush=True)
        named_witness(6, [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3)])
