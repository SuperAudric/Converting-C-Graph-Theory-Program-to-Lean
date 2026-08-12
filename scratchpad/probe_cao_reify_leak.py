"""probe_cao_reify_leak.py — does the "switchable 2-WL-blind pair" gadget survive reification?

Reader proposal: take a 2-WL-indistinguishable pair (Shrikhande, rook 4x4), present each as
16 points + 120 pair-vertices (one per unordered pair, joined to its two endpoints), with the
pair-vertices 2-coloured "edge" / "non-edge".  Individualization elsewhere is supposed to flip
which colouring each copy carries; the claim is that 2-WL "is definitionally blind" to which.

The claim to test is NOT "2-WL cannot distinguish Shrikhande from rook" (true, calibrated
below) but "2-WL cannot distinguish their REIFIED forms".  Reifying pairs as vertices lets a
pair-level tool reach 4-point statistics of the original: for two disjoint edge-vertices
e={a,b}, f={c,d}, the round-1 count of g with |g^e|=|g^f|=1 and colour(g)=edge IS the number
of cross edges, so K4s become visible.  Shrikhande has 0 K4s, rook 4x4 has 8.

Also runs the reader's proposed SMALL test (C6 vs C3+C3, the 1-WL-blind pair) at 1-WL, to see
whether the small model predicts the large one.
"""

from itertools import combinations


def shrikhande():
    V = [(i, j) for i in range(4) for j in range(4)]
    S = {(1, 0), (3, 0), (0, 1), (0, 3), (1, 1), (3, 3)}
    E = set()
    for a in V:
        for s in S:
            b = ((a[0] + s[0]) % 4, (a[1] + s[1]) % 4)
            E.add(frozenset((V.index(a), V.index(b))))
    return 16, E


def rook():
    V = [(i, j) for i in range(4) for j in range(4)]
    E = set()
    for a, b in combinations(range(16), 2):
        if (V[a][0] == V[b][0]) != (V[a][1] == V[b][1]):
            E.add(frozenset((a, b)))
    return 16, E


def cycle(n, offset=0):
    return {frozenset((offset + i, offset + (i + 1) % n)) for i in range(n)}


def srg_params(n, E):
    adj = {v: set() for v in range(n)}
    for e in E:
        a, b = tuple(e)
        adj[a].add(b)
        adj[b].add(a)
    k = {len(adj[v]) for v in range(n)}
    lam = {len(adj[a] & adj[b]) for a, b in combinations(range(n), 2) if b in adj[a]}
    mu = {len(adj[a] & adj[b]) for a, b in combinations(range(n), 2) if b not in adj[a]}
    k4 = sum(1 for q in combinations(range(n), 4)
             if all(y in adj[x] for x, y in combinations(q, 2)))
    return (n, k, lam, mu), k4


def reify(n, E, complete=True):
    """points 0..n-1 (colour 0); one vertex per pair (complete) or per edge (subdivision)."""
    pairs = list(combinations(range(n), 2)) if complete else [tuple(sorted(e)) for e in E]
    vcol = [0] * n
    adj = {v: set() for v in range(n)}
    for idx, (a, b) in enumerate(pairs):
        w = n + idx
        adj[w] = {a, b}
        adj[a].add(w)
        adj[b].add(w)
        vcol.append(1 if frozenset((a, b)) in E else 2)
    return len(vcol), adj, vcol


def wl_lockstep(objs, dim):
    """Refine all objects in one shared colour space.  Returns per-object colour multisets."""
    states = []
    for n, adj, vcol in objs:
        if dim == 1:
            states.append({(a,): (vcol[a],) for a in range(n)})
        else:
            states.append({(a, b): (a == b, b in adj[a], vcol[a], vcol[b])
                           for a in range(n) for b in range(n)})
    while True:
        sigs, before = [], sum(len(set(s.values())) for s in states)
        for (n, adj, vcol), col in zip(objs, states):
            if dim == 1:
                sigs.append({(a,): (col[(a,)], tuple(sorted(col[(w,)] for w in adj[a])))
                             for a in range(n)})
            else:
                rng = range(n)
                sigs.append({(a, b): (col[(a, b)],
                                      tuple(sorted((col[(a, z)], col[(z, b)]) for z in rng)))
                             for a in rng for b in rng})
        pool = sorted({s for sg in sigs for s in sg.values()}, key=repr)
        rk = {s: i for i, s in enumerate(pool)}
        states = [{p: (rk[s],) for p, s in sg.items()} for sg in sigs]
        if sum(len(set(s.values())) for s in states) == before:
            break
    return [sorted(s.values()) for s in states]


def distinguishes(objA, objB, dim):
    a, b = wl_lockstep([objA, objB], dim)
    return a != b


if __name__ == '__main__':
    nS, ES = shrikhande()
    nR, ER = rook()
    print('CALIBRATION  Shrikhande', srg_params(nS, ES), ' rook4x4', srg_params(nR, ER))

    plainS = (nS, {v: {w for e in ES if v in e for w in e if w != v} for v in range(nS)}, [0] * nS)
    plainR = (nR, {v: {w for e in ER if v in e for w in e if w != v} for v in range(nR)}, [0] * nR)
    print('CALIBRATION  2-WL distinguishes them as PLAIN graphs:',
          distinguishes(plainS, plainR, 2), '(must be False)')

    sub = (reify(nS, ES, complete=False), reify(nR, ER, complete=False))
    print('2-WL distinguishes the SUBDIVISIONS (16+48):', distinguishes(*sub, 2))

    full = (reify(nS, ES, complete=True), reify(nR, ER, complete=True))
    print('2-WL distinguishes the REIFIED gadgets (16+120):', distinguishes(*full, 2))

    # the reader's proposed small test: C6 vs C3+C3, the 1-WL-blind pair, at 1-WL
    E6, E33 = cycle(6), cycle(3) | cycle(3, 3)
    p6 = (6, {v: {w for e in E6 if v in e for w in e if w != v} for v in range(6)}, [0] * 6)
    p33 = (6, {v: {w for e in E33 if v in e for w in e if w != v} for v in range(6)}, [0] * 6)
    print('SMALL MODEL  1-WL distinguishes C6 vs C3+C3 plain:', distinguishes(p6, p33, 1))
    small = (reify(6, E6, complete=True), reify(6, E33, complete=True))
    print('SMALL MODEL  1-WL distinguishes the REIFIED gadgets (6+15):',
          distinguishes(*small, 1))
    print('SMALL MODEL  2-WL distinguishes the REIFIED gadgets (6+15):',
          distinguishes(*small, 2))
