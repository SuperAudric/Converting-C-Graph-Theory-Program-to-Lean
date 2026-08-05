"""Q2: how can far vertices be INDEXED by same-orbit intermediates?

Rung 1 (1-WL fails): the address is a PAIR inside N(v). Aut_v is transitive on the
points of N(v) but NOT on its pairs, so the address carries information the individual
intermediates do not.  Measured here as an explicit pullback.

Rung 2 (what a 2-WL failure would need): the address must be a TRIPLE, with the local
group transitive on pairs but not triples. Checked on A5 = PSL(2,5) on 6 points, plus
the 2-closure obstruction that says no binary structure on the cell can expose it.
"""
import sys
from itertools import combinations, permutations
from probe_pathcondense import shrikhande, rook44
from probe_cao_cleanroom import all_isos, orbits


def orbit_partition_on(tuples, group):
    """Orbits of `group` (list of images) on a list of tuples."""
    idx = {t: i for i, t in enumerate(tuples)}
    par = list(range(len(tuples)))

    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for g in group:
        for t in tuples:
            img = tuple(g[c] for c in t)
            key = img if img in idx else tuple(sorted(img))
            if key not in idx:
                continue
            a, b = f(idx[t]), f(idx[key])
            if a != b:
                par[a] = b
    cls = {}
    for t in tuples:
        cls.setdefault(f(idx[t]), []).append(t)
    return list(cls.values())


def rung1(label, n, adj):
    auts = all_isos(n, adj, [0] * n, [0] * n)
    v = 0
    stab = [g for g in auts if g[v] == v]
    korb = orbits(n, stab)
    N = [x for x in range(n) if adj[v][x]]
    far = [x for x in range(n) if x != v and not adj[v][x]]
    print(f'--- {label}: n={n} |Aut|={len(auts)} |Aut_v|={len(stab)}')
    print(f'    N(v) = {N}   far = {len(far)} vertices')

    # shape induced on N(v)
    degs = sorted(sum(adj[x][y] for y in N) for x in N)
    print(f'    degrees inside N(v): {degs}')
    pts = orbit_partition_on([(x,) for x in N], stab)
    print(f'    Aut_v orbits on POINTS of N(v): {sorted(len(o) for o in pts)}'
          f'   (transitive? {len(pts) == 1})')
    prs = orbit_partition_on([tuple(sorted(p)) for p in combinations(N, 2)], stab)
    print(f'    Aut_v orbits on PAIRS  of N(v): {sorted(len(o) for o in prs)}'
          f'   (transitive? {len(prs) == 1})')
    for o in sorted(prs, key=len):
        x, y = o[0]
        print(f'        pair-orbit size {len(o):2d}  representative {o[0]}  adjacent? {adj[x][y]}')

    # the attachment map: far vertex -> its common neighbours with v
    addr = {u: tuple(sorted(x for x in N if adj[u][x])) for u in far}
    sizes = sorted({len(a) for a in addr.values()})
    print(f'    attachment |N(v) cap N(u)| for far u: {sizes}   '
          f'injective? {len(set(addr.values())) == len(far)}')
    pairidx = {}
    for i, o in enumerate(sorted(prs, key=len)):
        for p in o:
            pairidx[p] = i
    pull = {}
    for u in far:
        if len(addr[u]) == 2:
            pull.setdefault(pairidx[addr[u]], []).append(u)
    print(f'    PULLBACK: far vertices grouped by their pair-orbit: '
          f'{sorted(len(g) for g in pull.values())}')
    farorb = {}
    for u in far:
        farorb.setdefault(korb[u], []).append(u)
    print(f'    TRUE Aut_v-orbits on far cell         : '
          f'{sorted(len(g) for g in farorb.values())}')
    match = sorted(sorted(g) for g in pull.values()) == sorted(sorted(g) for g in farorb.values())
    print(f'    pullback == true far-cell split? {match}')
    sys.stdout.flush()


def psl25():
    """A5 = PSL(2,5) acting on the projective line over F5: 6 points {0..4, inf=5}."""
    P = list(range(6))

    def act(a, b, c, d):
        img = []
        for x in P:
            if x == 5:
                num, den = a, c
            else:
                num, den = (a * x + b) % 5, (c * x + d) % 5
            img.append(5 if den % 5 == 0 else (num * pow(den, 3, 5)) % 5)
        return tuple(img)
    gens = [act(1, 1, 0, 1), act(0, 4, 1, 0)]
    G = {tuple(P)}
    frontier = [tuple(P)]
    while frontier:
        g = frontier.pop()
        for h in gens:
            comp = tuple(h[g[i]] for i in range(6))
            if comp not in G:
                G.add(comp)
                frontier.append(comp)
    return sorted(G)


def rung2():
    G = psl25()
    print(f'--- A5 = PSL(2,5) on 6 points:  |G| = {len(G)}')
    for k, name in [(1, 'POINTS'), (2, 'PAIRS'), (3, 'TRIPLES')]:
        tups = [tuple(sorted(c)) for c in combinations(range(6), k)]
        o = orbit_partition_on(tups, G)
        print(f'    orbits on {name:8s}: {sorted(len(x) for x in o)}   '
              f'transitive? {len(o) == 1}')
    # ORDERED pairs -> orbitals -> the 2-closure
    orb2 = orbit_partition_on([(a, b) for a in range(6) for b in range(6)], G)
    print(f'    ORBITALS (orbits on ordered pairs): {sorted(len(x) for x in orb2)}')
    off = [o for o in orb2 if o[0][0] != o[0][1]]
    print(f'    non-diagonal orbitals: {len(off)}  '
          f'==> any G-invariant binary relation is monochromatic off the diagonal')
    closure = [p for p in permutations(range(6))
               if all(any((p[a], p[b]) in set(o) for o in [oo] ) for oo in orb2
                      for (a, b) in [oo[0]])]
    print(f'    2-CLOSURE of G = {len(closure)} elements  (|S6| = 720)')
    print('    ==> G is 2-transitive but NOT 2-closed: no edge-coloured graph on the')
    print('        cell can have G as its automorphism group. Rung 2 has no graph carrier.')
    sys.stdout.flush()


if __name__ == '__main__':
    n, adj = shrikhande(); rung1('Shrikhande (CAO FAILS at 1-WL)', n, adj)
    print()
    n, adj = rook44();     rung1('rook 4x4 (CAO propagates)', n, adj)
    print()
    rung2()
