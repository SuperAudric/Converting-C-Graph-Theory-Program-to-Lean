"""Does the PATH-MULTISET CONDENSATION claim hold at a CAO residue?

The claim under test (user, 2026-08-05):
  "after you have a fibre-Schurian/CellsAreOrbits residue, the multiset of paths of
   length n between a and b is held within [StartingOrbit, isConnected, EndingOrbit]"

Operationalised at a CAO root (cells = Aut-orbits by construction):
  P_orb    = the exact Aut-orbital partition of V x V          (the truth)
  P_2wl    = the 2-WL pair closure                             (what 2-WL condenses to)
  P_walk   = walk counts (A^k)_{ab}, k = 0..n                  (path multisets, unannotated)
  P_v4     = V4's own recursion, faithfully ported from
             Archive/V4/CanonGraphOrdererV4.cs:70-75 / 294-301  (the built object)
  P_cell   = [cell(a), adj(a,b), cell(b)]                      (the literal length-1 object)

CONDENSATION HOLDS iff P_walk (or P_v4) is no finer than P_cell AND P_cell = P_orb.
The interesting failure is P_orb strictly finer than all the others.

No orbit oracle: automorphisms come from probe_cao_cleanroom.all_isos (complete I-R
enumeration, every leaf re-verified as a permutation automorphism).
"""
import sys
from itertools import product
from probe_cao_cleanroom import wl, all_isos, orbits, is_perm_aut


# ----------------------------------------------------------------- constructions
def cayley(group_elems, add, S):
    n = len(group_elems)
    idx = {g: i for i, g in enumerate(group_elems)}
    adj = [[0] * n for _ in range(n)]
    for g in group_elems:
        for s in S:
            adj[idx[g]][idx[add(g, s)]] = 1
    for i in range(n):
        for j in range(n):
            adj[i][j] = adj[j][i] = max(adj[i][j], adj[j][i])
        adj[i][i] = 0
    return n, adj


def shrikhande():
    E = [(i, j) for i in range(4) for j in range(4)]
    S = [(1, 0), (3, 0), (0, 1), (0, 3), (1, 1), (3, 3)]
    return cayley(E, lambda a, b: ((a[0] + b[0]) % 4, (a[1] + b[1]) % 4), S)


def rook44():
    E = [(i, j) for i in range(4) for j in range(4)]
    n = 16
    idx = {g: i for i, g in enumerate(E)}
    adj = [[0] * n for _ in range(n)]
    for a in E:
        for b in E:
            if a != b and (a[0] == b[0] or a[1] == b[1]):
                adj[idx[a]][idx[b]] = 1
    return n, adj


def net_z4():
    """net(Z_4): the (point, line) incidence graph of the net over Z_4.  n = 28.
    Points = Z4 x Z4 (16), lines = 3 parallel classes + ... built as in probe_cao_net."""
    pts = [(i, j) for i in range(4) for j in range(4)]
    lines = []
    for c in range(4):                      # verticals
        lines.append([(c, j) for j in range(4)])
    for r in range(4):                      # horizontals
        lines.append([(i, r) for i in range(4)])
    for s in range(4):                      # one slope class
        lines.append([(i, (i + s) % 4) for i in range(4)])
    n = len(pts) + len(lines)
    pidx = {p: i for i, p in enumerate(pts)}
    adj = [[0] * n for _ in range(n)]
    for li, L in enumerate(lines):
        for p in L:
            a, b = pidx[p], len(pts) + li
            adj[a][b] = adj[b][a] = 1
    return n, adj


# ----------------------------------------------------------------- partitions on pairs
def rank_partition(vals):
    """vals : dict (a,b) -> hashable  ->  dict (a,b) -> int, dense-ranked."""
    reps = {v: i for i, v in enumerate(sorted(set(vals.values()), key=repr))}
    return {k: reps[v] for k, v in vals.items()}


def npairclasses(part):
    return len(set(part.values()))


def finer_or_equal(P, Q):
    """True iff P refines Q (every P-class lies inside a Q-class)."""
    seen = {}
    for k, p in P.items():
        q = Q[k]
        if p in seen and seen[p] != q:
            return False
        seen[p] = q
    return True


def same(P, Q):
    return finer_or_equal(P, Q) and finer_or_equal(Q, P)


# ----------------------------------------------------------------- the four objects
def orbital_partition(n, auts):
    par = {}

    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for a in range(n):
        for b in range(n):
            par[(a, b)] = (a, b)
    for g in auts:
        for a in range(n):
            for b in range(n):
                x, y = find((a, b)), find((g[a], g[b]))
                if x != y:
                    par[x] = y
    return rank_partition({(a, b): find((a, b)) for a in range(n) for b in range(n)})


def wl2_pair_closure(n, adj, cap=60):
    c = {(a, b): (0 if a == b else 1 + adj[a][b]) for a in range(n) for b in range(n)}
    c = rank_partition(c)
    for _ in range(cap):
        nxt = {}
        for a in range(n):
            for b in range(n):
                nxt[(a, b)] = (c[(a, b)],
                               tuple(sorted((c[(a, x)], c[(x, b)]) for x in range(n))))
        nxt = rank_partition(nxt)
        if same(nxt, c):
            return c
        c = nxt
    return c


def walk_partition(n, adj, maxlen=None):
    """Multiset of walks a->b of every length 0..n, i.e. the vector ((A^k)_ab)_k."""
    maxlen = maxlen or n
    P = [[1 if a == b else 0 for b in range(n)] for a in range(n)]
    layers = [[[P[a][b]] for b in range(n)] for a in range(n)]
    for _ in range(maxlen):
        Q = [[sum(P[a][x] * adj[x][b] for x in range(n)) for b in range(n)] for a in range(n)]
        for a in range(n):
            for b in range(n):
                layers[a][b].append(Q[a][b])
        P = Q
    return rank_partition({(a, b): tuple(layers[a][b]) for a in range(n) for b in range(n)})


def v4_pair_partition(n, adj, vcol):
    """Faithful port of CanonGraphOrdererV4.InitializePaths + ComparePathsBetween.

        P_0(a,b) = [bottom(a)] if a == b else []
        P_d(a,b) = {{ ( rank P_{d-1}(a,mid), adj(mid,b) ) : mid }}
        rank at depth d sorts by ( vcol[b], the multiset above )

    Returns the depth-(n-1) pair ranking, plus the join over all depths.
    """
    prev = rank_partition({(a, b): (vcol[b], 0 if a == b else 1) for a in range(n) for b in range(n)})
    joined = {(a, b): (prev[(a, b)],) for a in range(n) for b in range(n)}
    for _ in range(1, n):
        cur = {}
        for a in range(n):
            for b in range(n):
                cur[(a, b)] = (vcol[b],
                               tuple(sorted((prev[(a, mid)], adj[mid][b]) for mid in range(n))))
        cur = rank_partition(cur)
        joined = {k: joined[k] + (cur[k],) for k in joined}
        prev = cur
    return rank_partition(prev), rank_partition(joined)


def cell_partition(n, adj, vcol):
    return rank_partition({(a, b): (vcol[a], adj[a][b], a == b, vcol[b])
                           for a in range(n) for b in range(n)})


# ----------------------------------------------------------------- driver
def analyse(label, n, adj):
    print('=' * 74)
    print(f'{label}   n = {n}')
    uni = [0] * n
    auts = all_isos(n, adj, uni, uni)
    print(f'  |Aut| = {len(auts)}   (complete enumeration, every leaf re-verified)')
    orb = orbits(n, auts)
    vcol = rank_partition({(v, v): orb[v] for v in range(n)})
    vcol = [vcol[(v, v)] for v in range(n)]
    ncells = len(set(vcol))
    print(f'  CAO root: {ncells} orbit-cell(s)  sizes {sorted(vcol.count(c) for c in set(vcol))}')

    P_orb = orbital_partition(n, auts)
    P_2wl = wl2_pair_closure(n, adj)
    P_walk = walk_partition(n, adj)
    P_v4d, P_v4j = v4_pair_partition(n, adj, vcol)
    P_cell = cell_partition(n, adj, vcol)

    rows = [('orbitals (TRUTH)', P_orb), ('2-WL pair closure', P_2wl),
            ('walk counts A^k', P_walk), ('V4 recursion (deepest)', P_v4d),
            ('V4 recursion (all depths)', P_v4j), ('[cell,adj,cell]', P_cell)]
    print(f'  {"object":28s} classes  refines-orbitals  =orbitals')
    for name, P in rows:
        print(f'  {name:28s} {npairclasses(P):5d}      {str(finer_or_equal(P, P_orb)):5s}'
              f'            {str(same(P, P_orb)):5s}')

    print(f'  CONDENSATION (walk multiset determined by [cell,adj,cell])? '
          f'{finer_or_equal(P_cell, P_walk)}')
    print(f'  CONDENSATION (V4 all-depths determined by [cell,adj,cell])? '
          f'{finer_or_equal(P_cell, P_v4j)}')
    print(f'  root SCHURIAN (2-WL pair classes = orbitals)? {same(P_2wl, P_orb)}')
    return auts, orb, P_orb, P_2wl, P_walk, P_v4j


if __name__ == '__main__':
    for label, build in [('Shrikhande', shrikhande), ('rook 4x4', rook44), ('net(Z4)', net_z4)]:
        try:
            n, adj = build()
            analyse(label, n, adj)
        except Exception as e:
            print(f'{label}: FAILED {type(e).__name__}: {e}')
        sys.stdout.flush()
