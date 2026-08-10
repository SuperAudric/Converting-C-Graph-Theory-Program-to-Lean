"""probe_cao_wl_ladder.py

Part A -- what 2-WL actually is, on the reader's own test cases.
   1-WL: C6 vs 2*C3      2-WL: C8 vs 2*C4      2-WL: Shrikhande vs rook 4x4
Part B -- the "obscure the copy relation" variants of the Q4 carrier construction:
   (a) replace the corner<->centre edge (and the carrier edge) by a PATH of length L
   (b) 6 copies in 3 sibling pairs; pair -> semi-central -> central, and the carrier
       coincidence becomes "siblings" rather than "same copy"
Both are checked for (i) is it still a 1-WL CAO counterexample, (ii) does 2-WL repair it.

Standard 2-WL: colours ORDERED PAIRS.  c0(x,y) = (x==y, edge colour).
   c'(x,y) = (c(x,y), multiset over ALL z of (c(x,z), c(z,y)))
Vertex colours are the diagonal.  Note the z ranges over every vertex, so non-adjacent
pairs are refined too -- which is why 2-WL knows the whole distance matrix.
"""

from collections import deque
from probe_cao_hypercube import cosets, patterns, key

BITS = [1, 2, 4, 8]
ALL = 15


# ---------- generic WL ----------

def wl1(n, ecol, init=None):
    col = list(init) if init else [0] * n
    nbr = [[] for _ in range(n)]
    for (a, b), c in ecol.items():
        nbr[a].append((b, c))
    while True:
        ids, new = {}, [0] * n
        for v in range(n):
            k = (col[v], tuple(sorted((c, col[w]) for w, c in nbr[v])))
            new[v] = ids.setdefault(k, len(ids))
        if len(ids) == len(set(col)):
            return col
        col = new


def wl2(n, ecol, init=None):
    """Colours are ints in a flat n*n list; every signature is hashed to an int as it is
    built, so nothing of size O(n^3) is ever retained."""
    ids, col = {}, [0] * (n * n)
    for a in range(n):
        for b in range(n):
            k = (a == b, ecol.get((a, b), 0), init[a] if init else 0, init[b] if init else 0)
            col[a * n + b] = ids.setdefault(k, len(ids))
    while True:
        K = max(col) + 1
        cols = [col[b::n] for b in range(n)]          # cols[b][z] = col(z,b)
        ids, new = {}, [0] * (n * n)
        for a in range(n):
            rowa = col[a * n:(a + 1) * n]             # rowa[z]   = col(a,z)
            for b in range(n):
                # hashed, so the O(n) signature is transient rather than retained as a key
                sig = hash((col[a * n + b],
                            tuple(sorted(x * K + y for x, y in zip(rowa, cols[b])))))
                new[a * n + b] = ids.setdefault(sig, len(ids))
        if len(ids) == len(set(col)):
            return col
        col = new


def distinguishes(dim, n1, e1, n2, e2):
    """Run WL on the disjoint union and compare the two parts' colour multisets."""
    n = n1 + n2
    e = dict(e1)
    for (a, b), c in e2.items():
        e[(a + n1, b + n1)] = c
    if dim == 1:
        col = wl1(n, e)
        return sorted(col[:n1]) != sorted(col[n1:])
    col = wl2(n, e)
    m1 = sorted(col[a * n + b] for a in range(n1) for b in range(n1))
    m2 = sorted(col[a * n + b] for a in range(n1, n) for b in range(n1, n))
    return m1 != m2


def cycle_edges(off, m):
    e = {}
    for i in range(m):
        a, b = off + i, off + (i + 1) % m
        e[(a, b)] = e[(b, a)] = 1
    return e


def union_cycles(*ms):
    e, off = {}, 0
    for m in ms:
        e.update(cycle_edges(off, m))
        off += m
    return sum(ms), e


def srg16(kind):
    vs = [(i, j) for i in range(4) for j in range(4)]
    idx = {v: i for i, v in enumerate(vs)}
    e = {}
    for x in vs:
        for y in vs:
            if x == y:
                continue
            d = ((x[0] - y[0]) % 4, (x[1] - y[1]) % 4)
            if kind == 'shrikhande':
                adj = d in {(1, 0), (3, 0), (0, 1), (0, 3), (1, 1), (3, 3)}
            else:
                adj = (x[0] == y[0]) or (x[1] == y[1])
            if adj:
                e[(idx[x], idx[y])] = 1
    return 16, e


# ---------- the constructions ----------

def build(sub_c=1, sub_g=1, sibling=False):
    """sub_c/sub_g: path length for the corner<->centre and carrier<->corner links.
       sibling: 6 copies in 3 pairs, pair -> semi-central -> central."""
    ncopy = 6 if sibling else 3
    verts, ecol = [], {}
    seen = set()

    def V(x):
        if x not in seen:
            seen.add(x)
            verts.append(x)
        return x

    def link(u, w, c, L, tag):
        """path of length L between u and w; interior vertices are PLAIN."""
        if L == 1:
            ecol[(u, w)] = ecol[(w, u)] = c
            return
        prev = u
        for t in range(L - 1):
            m = V(('path', tag, t))
            ecol[(prev, m)] = ecol[(m, prev)] = 1
            prev = m
        ecol[(prev, w)] = ecol[(w, prev)] = 1

    for p in range(16):
        V(('centre', p))
        for c in range(ncopy):
            V(('corner', p, c))
        if sibling:
            for s in range(3):
                V(('semi', p, s))

    for p in range(16):
        if sibling:
            for s in range(3):
                ecol[(('semi', p, s), ('centre', p))] = 7
                ecol[(('centre', p), ('semi', p, s))] = 7
                for c in (2 * s, 2 * s + 1):
                    link(('corner', p, c), ('semi', p, s), 6, sub_c, ('cs', p, c))
        else:
            for c in range(ncopy):
                link(('corner', p, c), ('centre', p), 6, sub_c, ('cs', p, c))
        for i, b in enumerate(BITS):
            q = p ^ b
            if p < q:
                for c in range(ncopy):
                    ecol[(('corner', p, c), ('corner', q, c))] = i + 2
                    ecol[(('corner', q, c), ('corner', p, c))] = i + 2

    carriers = []
    for R in cosets():
        for phi in (sib_patterns(R) if sibling else patterns(R)):
            g = V(key(phi))
            carriers.append((g, phi))
            for pos, c in phi.items():
                link(g, ('corner', pos, c), 8, sub_g, ('cg', tuple(sorted(phi.items())), pos))
    return verts, ecol, carriers


def sib_patterns(R):
    """One complementary position-pair carries two SIBLING copies (2s, 2s+1);
       the other carries one copy from each of the two remaining sibling pairs."""
    a = min(R)
    P = (a, a ^ ALL)
    O = tuple(sorted(x for x in R if x not in P))
    for which in (0, 1):
        SP, OP = (P, O) if which == 0 else (O, P)
        for s in range(3):
            rest = [t for t in range(3) if t != s]
            for order in (0, 1):
                for m0 in (0, 1):
                    for m1 in (0, 1):
                        for n0 in (0, 1):
                            t0, t1 = (rest if order == 0 else rest[::-1])
                            yield {SP[0]: 2 * s + m0, SP[1]: 2 * s + (1 - m0),
                                   OP[0]: 2 * t0 + m1, OP[1]: 2 * t1 + n0}


def report(tag, sub_c, sub_g, sibling, run2wl=True):
    verts, ecol, carriers = build(sub_c, sub_g, sibling)
    idx = {v: i for i, v in enumerate(verts)}
    n = len(verts)
    e = {(idx[a], idx[b]): c for (a, b), c in ecol.items()}
    init = [1 if v == ('centre', 0) else 0 for v in verts]

    c1 = wl1(n, e, init)
    cells = {}
    for g, _ in carriers:
        cells.setdefault(c1[idx[g]], []).append(g)
    print(f'{tag}: n={n}  carriers={len(carriers)}  '
          f'1-WL carrier cells={sorted(len(x) for x in cells.values())}')

    # positions 3 and 12 are complementary (3 xor 12 = 1111).  Compare the pair
    # (corner@3, corner@12) when the two corners COINCIDE (same copy / siblings) against
    # when they do not -- this is the coincidence the construction is trying to hide.
    dist = bfs(n, e, idx[('corner', 3, 0)])
    tgt_same = ('corner', 12, 1 if sibling else 0)
    tgt_cross = ('corner', 12, 2)
    nbr = {}
    for (a, b) in e:
        nbr.setdefault(a, set()).add(b)

    def cn(u, w):
        return len(nbr[idx[u]] & nbr[idx[w]])

    lab = 'A-sibling' if sibling else 'A'
    print(f'    corner(3,A) -> corner(12,{lab}) : dist={dist[idx[tgt_same]]} '
          f'commonNbrs={cn(("corner", 3, 0), tgt_same)}   '
          f'-> corner(12,other) : dist={dist[idx[tgt_cross]]} '
          f'commonNbrs={cn(("corner", 3, 0), tgt_cross)}')

    if run2wl:
        c2 = wl2(n, e, init)
        d = {}
        for g, _ in carriers:
            d.setdefault(c2[idx[g] * n + idx[g]], []).append(g)
        print(f'    2-WL carrier cells={sorted(len(x) for x in d.values())}')


def bfs(n, e, src):
    nbr = [[] for _ in range(n)]
    for (a, b) in e:
        nbr[a].append(b)
    d = [-1] * n
    d[src] = 0
    q = deque([src])
    while q:
        x = q.popleft()
        for y in nbr[x]:
            if d[y] < 0:
                d[y] = d[x] + 1
                q.append(y)
    return d


if __name__ == '__main__':
    import sys
    if 'b2wl' in sys.argv:                     # the 544-vertex run, separately
        report('(b) sibling hierarchy, 6 copies', 1, 1, True, run2wl=True)
        sys.exit(0)

    print('== PART A: where the WL ladder actually sits ==')
    n1, e1 = union_cycles(6)
    n2, e2 = union_cycles(3, 3)
    print('1-WL  C6 vs 2*C3 :', 'DISTINGUISHED' if distinguishes(1, n1, e1, n2, e2) else 'blind')
    print('2-WL  C6 vs 2*C3 :', 'DISTINGUISHED' if distinguishes(2, n1, e1, n2, e2) else 'blind')
    n1, e1 = union_cycles(8)
    n2, e2 = union_cycles(4, 4)
    print('1-WL  C8 vs 2*C4 :', 'DISTINGUISHED' if distinguishes(1, n1, e1, n2, e2) else 'blind')
    print('2-WL  C8 vs 2*C4 :', 'DISTINGUISHED' if distinguishes(2, n1, e1, n2, e2) else 'blind')
    n1, e1 = union_cycles(20)
    n2, e2 = union_cycles(10, 10)
    print('2-WL  C20 vs 2*C10 (long paths):',
          'DISTINGUISHED' if distinguishes(2, n1, e1, n2, e2) else 'blind')
    a, b = srg16('shrikhande'), srg16('rook')
    print('1-WL  Shrikhande vs rook4x4 :',
          'DISTINGUISHED' if distinguishes(1, *a, *b) else 'blind')
    print('2-WL  Shrikhande vs rook4x4 :',
          'DISTINGUISHED' if distinguishes(2, *a, *b) else 'blind  <- THE 2-WL blind spot')

    print()
    print('== PART B: obscuring the copy relation ==')
    report('baseline (direct corner-centre link)', 1, 1, False)
    report('(a) corner-centre link = path of length 2', 2, 1, False)
    report('(a) corner-centre link = path of length 3', 3, 1, False)
    report('(b) sibling hierarchy, 6 copies', 1, 1, True, run2wl=False)
