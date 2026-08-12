"""probe_cao_gadget_variants.py — which gadget shapes keep the LABEL group after individualization?

The doubling ("two cubes per edge, so it is reversible") is usually explained as root symmetry.  The
real obligation is stronger: the central vertex m must attach to exactly ONE corner per cube -- that
is what makes it a gauge choice -- and the label transposition (i j) must still be an automorphism
FIXING m, or Aut_m loses its transpositions and the construction's T4 ("every cube automorphic to
every other, after individualization") fails.

Three shapes, small ensemble (L labels, all 2^slots copies and centrals):
  both     one frame object per (slot,type); BOTH endpoints attach to it        <- the reduction
  ordered1 one cube, two ends; i->end0, j->end1 by the min-label rule;
           m attaches to ONE end (faithful: m picks one corner per cube)
  ordered2 TWO cubes with opposite orientations; m picks one corner per cube    <- the original

Reported per shape: is the gauge an automorphism, is the transposition (0 1) an automorphism, and
does that transposition FIX m(0).  All three are needed.
"""

from itertools import combinations

L = 4
PAIRS = list(combinations(range(L), 2))
NS = len(PAIRS)
SLOT = {}
for k, (i, j) in enumerate(PAIRS):
    SLOT[(i, j)] = SLOT[(j, i)] = k
NC = 1 << NS


def build(shape):
    """returns (verts, adj set of ordered pairs, frame index helper)"""
    adj, verts = set(), []

    def add(u, w):
        adj.add((u, w))
        adj.add((w, u))

    for c in range(NC):
        for i in range(L):
            verts.append(('p', c, i))
        for a in range(L):
            for b in range(a + 1, L):
                add(('p', c, a), ('p', c, b))
    for g in range(NC):
        verts.append(('m', g))

    if shape == 'both':
        slots = [(k, t) for k in range(NS) for t in (0, 1)]
        verts += [('f', k, t) for (k, t) in slots]
        for c in range(NC):
            for k, (i, j) in enumerate(PAIRS):
                t = (c >> k) & 1
                add(('p', c, i), ('f', k, t))
                add(('p', c, j), ('f', k, t))
        for g in range(NC):
            for k in range(NS):
                add(('m', g), ('f', k, (g >> k) & 1))
    elif shape == 'ordered1':
        verts += [('f', k, t, e) for k in range(NS) for t in (0, 1) for e in (0, 1)]
        for k in range(NS):
            for t in (0, 1):
                add(('f', k, t, 0), ('f', k, t, 1))          # the cube
        for c in range(NC):
            for k, (i, j) in enumerate(PAIRS):
                t = (c >> k) & 1
                add(('p', c, i), ('f', k, t, 0))             # min label -> end 0
                add(('p', c, j), ('f', k, t, 1))
        for g in range(NC):
            for k in range(NS):
                add(('m', g), ('f', k, (g >> k) & 1, 0))     # m picks ONE corner
    else:                                                     # ordered2: two cubes
        verts += [('f', k, t, cu, e) for k in range(NS) for t in (0, 1)
                  for cu in (0, 1) for e in (0, 1)]
        for k in range(NS):
            for t in (0, 1):
                for cu in (0, 1):
                    add(('f', k, t, cu, 0), ('f', k, t, cu, 1))
        for c in range(NC):
            for k, (i, j) in enumerate(PAIRS):
                t = (c >> k) & 1
                add(('p', c, i), ('f', k, t, 0, 0))
                add(('p', c, j), ('f', k, t, 0, 1))
                add(('p', c, i), ('f', k, t, 1, 1))           # mirror cube
                add(('p', c, j), ('f', k, t, 1, 0))
        for g in range(NC):
            for k in range(NS):
                t = (g >> k) & 1
                add(('m', g), ('f', k, t, 0, 0))              # one corner per cube
                add(('m', g), ('f', k, t, 1, 0))
    return verts, adj


def gauge(shape, h):
    def f(v):
        if v[0] == 'p':
            return ('p', v[1] ^ h, v[2])
        if v[0] == 'm':
            return ('m', v[1] ^ h, )
        k = v[1]
        return (v[0], k, v[2] ^ ((h >> k) & 1)) + v[3:]
    return f


def relabel(shape, pi):
    smap = [SLOT[(pi[i], pi[j])] for (i, j) in PAIRS]

    def cmap(c):
        cc = 0
        for k in range(NS):
            if (c >> k) & 1:
                cc |= 1 << smap[k]
        return cc

    def endmap(k, e):
        """end 0 belongs to min(slot); after relabelling, does that endpoint stay minimal?"""
        i, j = PAIRS[k]
        a, b = pi[i], pi[j]
        src = i if e == 0 else j
        tgt = pi[src]
        ni, nj = min(a, b), max(a, b)
        return 0 if tgt == ni else 1

    def two_cube(k, cu, e):
        """ordered2: frame (cu,e) is attached to the slot's MIN label iff cu == e.  A relabelling
        that flips a label's min/max role must therefore swap the CUBE, not the end -- that is what
        keeps m (which holds one corner per cube) fixed."""
        i, j = PAIRS[k]
        attached = i if cu == e else j
        a, b = PAIRS[smap[k]]
        is_min = (pi[attached] == min(a, b))
        flip = (attached == i) != is_min
        cu2 = cu ^ (1 if flip else 0)
        return cu2, (cu2 if is_min else 1 - cu2)

    def f(v):
        if v[0] == 'p':
            return ('p', cmap(v[1]), pi[v[2]])
        if v[0] == 'm':
            return ('m', cmap(v[1]))
        k = v[1]
        if shape == 'both':
            return ('f', smap[k], v[2])
        if shape == 'ordered1':
            return ('f', smap[k], v[2], endmap(k, v[3]))
        cu2, e2 = two_cube(k, v[3], v[4])
        return ('f', smap[k], v[2], cu2, e2)
    return f


def is_aut(verts, adj, f):
    img = {}
    for v in verts:
        img[v] = f(v)
    if len(set(img.values())) != len(verts) or set(img.values()) != set(verts):
        return False
    for (u, w) in adj:
        if (img[u], img[w]) not in adj:
            return False
    return True


if __name__ == '__main__':
    tau = [1, 0] + list(range(2, L))                       # the transposition (0 1)
    print(f'{"shape":9s} {"|V|":>6s}  gauge aut   transposition aut   fixes m(0)   ALL THREE')
    for shape in ('both', 'ordered1', 'ordered2'):
        verts, adj = build(shape)
        g_ok = all(is_aut(verts, adj, gauge(shape, h)) for h in (1, 2, 1 << (NS - 1)))
        rf = relabel(shape, tau)
        r_ok = is_aut(verts, adj, rf)
        fixes = rf(('m', 0)) == ('m', 0)
        print(f'{shape:9s} {len(verts):6d}  {str(g_ok):^9s}  {str(r_ok):^17s}  {str(fixes):^10s}   '
              f'{"PASS" if (g_ok and r_ok and fixes) else "FAIL"}')
